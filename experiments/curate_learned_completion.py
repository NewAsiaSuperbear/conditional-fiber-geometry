#!/usr/bin/env python3
"""Curate learned-completion CSV tables into a safe, public NumPy archive.

The source evaluations are kept outside this release repository because they
contain many columns that are not used by the manuscript.  This script keeps
only the per-case quantities needed to reproduce the reported learned-model
comparisons.  It also checks the frozen experimental design and verifies the
published mask-level means against the three per-case tables.

The resulting compressed NPZ contains only numeric and fixed-width Unicode
arrays.  It can therefore be opened with ``numpy.load(..., allow_pickle=False)``.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np


HERE = Path(__file__).resolve().parent
DEFAULT_OUTPUT = HERE / "results" / "learned_completion" / "per_case_metrics.npz"

EXPECTED_SEEDS = (20260911, 20260912, 20260913)
EXPECTED_SAMPLE_COUNT = 400
EXPECTED_MASK_COUNT = 21
EXPECTED_NOISES = (0.0, 1.0e-4, 3.0e-4, 1.0e-3)

# These are the public per-case quantities needed for the learned-completion
# claims.  In particular, no predictions, ground truths, or checkpoint state
# are placed in the release artifact.
METRICS = (
    "edm_missing_error",
    "edm_projected_missing_error",
    "edm_single_missing_error",
    "unet_missing_error",
    "projected_energy_score",
    "projected_coverage_90",
    "projected_interval_width",
    "physical_row_sum_error",
    "projected_physical_row_sum_error",
)

TRAINING_COLUMNS = (
    "training_score",
    "training_sigma_min_mean",
    "training_rank_1e-3_mean",
)

PER_CASE_COORDINATES = (
    "network_seed",
    "sample",
    "mask_index",
    "category",
    "noise",
)
MASK_LEVEL_COORDINATES = ("mask_index", "category", "noise")


def _require_columns(
    path: Path, fieldnames: Iterable[str] | None, required: Sequence[str]
) -> None:
    available = set(fieldnames or ())
    missing = sorted(set(required) - available)
    if missing:
        raise ValueError(f"{path}: missing required CSV columns: {missing}")


def _parse_int(raw: str, *, path: Path, line: int, column: str) -> int:
    try:
        value = int(raw)
    except (TypeError, ValueError) as exc:
        raise ValueError(
            f"{path}:{line}: {column} must be an integer, got {raw!r}"
        ) from exc
    return value


def _parse_float(raw: str, *, path: Path, line: int, column: str) -> float:
    try:
        value = float(raw)
    except (TypeError, ValueError) as exc:
        raise ValueError(
            f"{path}:{line}: {column} must be numeric, got {raw!r}"
        ) from exc
    if not np.isfinite(value):
        raise ValueError(f"{path}:{line}: {column} must be finite")
    return value


def _expected_category(mask_index: int) -> str:
    return "selected" if mask_index == 0 else "random"


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _validate_nonnegative_metrics(values: np.ndarray) -> None:
    for metric_index, metric in enumerate(METRICS):
        metric_values = values[..., metric_index]
        if metric == "projected_coverage_90":
            if np.any((metric_values < 0.0) | (metric_values > 1.0)):
                raise ValueError("projected_coverage_90 must lie in [0, 1]")
        elif np.any(metric_values < 0.0):
            raise ValueError(f"{metric} must be nonnegative")


def curate_metrics(
    per_case_csvs: Sequence[Path],
    mask_level_csv: Path,
    output: Path,
    *,
    expected_seeds: Sequence[int] = EXPECTED_SEEDS,
    expected_sample_count: int = EXPECTED_SAMPLE_COUNT,
    expected_mask_count: int = EXPECTED_MASK_COUNT,
    expected_noises: Sequence[float] = EXPECTED_NOISES,
) -> dict[str, np.ndarray]:
    """Validate the source tables, write the compressed archive, and return it.

    The keyword-only design arguments make small synthetic unit tests possible.
    The command-line interface deliberately uses the frozen public-study values.
    """

    paths = tuple(Path(path) for path in per_case_csvs)
    mask_level_path = Path(mask_level_csv)
    output_path = Path(output)
    seeds = tuple(int(seed) for seed in expected_seeds)
    noises = tuple(float(noise) for noise in expected_noises)

    if len(paths) != len(seeds):
        raise ValueError(
            f"expected {len(seeds)} per-case CSV files, got {len(paths)}"
        )
    if expected_sample_count <= 0 or expected_mask_count < 2:
        raise ValueError("sample count must be positive and mask count at least two")
    if not noises or len(set(noises)) != len(noises):
        raise ValueError("expected noise levels must be nonempty and unique")
    if len(set(seeds)) != len(seeds):
        raise ValueError("expected network seeds must be unique")

    seed_slot = {seed: index for index, seed in enumerate(seeds)}
    noise_slot = {noise: index for index, noise in enumerate(noises)}
    shape = (
        len(seeds),
        expected_sample_count,
        expected_mask_count,
        len(noises),
    )
    values = np.full(shape + (len(METRICS),), np.nan, dtype=np.float64)
    seen = np.zeros(shape, dtype=bool)
    file_seeds: list[int] = []

    for path in paths:
        seeds_in_file: set[int] = set()
        with path.open(newline="", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            _require_columns(path, reader.fieldnames, PER_CASE_COORDINATES + METRICS)
            for line, row in enumerate(reader, start=2):
                seed = _parse_int(
                    row["network_seed"], path=path, line=line, column="network_seed"
                )
                sample = _parse_int(
                    row["sample"], path=path, line=line, column="sample"
                )
                mask = _parse_int(
                    row["mask_index"], path=path, line=line, column="mask_index"
                )
                noise = _parse_float(
                    row["noise"], path=path, line=line, column="noise"
                )
                category = row["category"]

                if seed not in seed_slot:
                    raise ValueError(f"{path}:{line}: unexpected network seed {seed}")
                if not 0 <= sample < expected_sample_count:
                    raise ValueError(f"{path}:{line}: sample index out of range: {sample}")
                if not 0 <= mask < expected_mask_count:
                    raise ValueError(f"{path}:{line}: mask index out of range: {mask}")
                if noise not in noise_slot:
                    raise ValueError(f"{path}:{line}: unexpected noise level {noise}")
                if category != _expected_category(mask):
                    raise ValueError(
                        f"{path}:{line}: category {category!r} is inconsistent "
                        f"with mask {mask}"
                    )

                index = (seed_slot[seed], sample, mask, noise_slot[noise])
                if seen[index]:
                    raise ValueError(
                        f"{path}:{line}: duplicate seed/sample/mask/noise coordinate"
                    )
                seen[index] = True
                seeds_in_file.add(seed)
                for metric_index, metric in enumerate(METRICS):
                    values[index + (metric_index,)] = _parse_float(
                        row[metric], path=path, line=line, column=metric
                    )
        if len(seeds_in_file) != 1:
            raise ValueError(
                f"{path}: each per-case file must contain exactly one network seed"
            )
        file_seeds.append(next(iter(seeds_in_file)))

    if len(set(file_seeds)) != len(seeds):
        raise ValueError(
            "per-case files must represent each expected network seed exactly once"
        )
    if not np.all(seen):
        missing_count = int(seen.size - np.count_nonzero(seen))
        raise ValueError(
            f"per-case tensor is incomplete: {missing_count} coordinates are missing"
        )
    if not np.all(np.isfinite(values)):
        raise ValueError("per-case metric tensor contains non-finite values")
    _validate_nonnegative_metrics(values)

    mask_seen = np.zeros((expected_mask_count, len(noises)), dtype=bool)
    mask_means = np.full(
        (expected_mask_count, len(noises), len(METRICS)), np.nan, dtype=np.float64
    )
    training = np.full(
        (expected_mask_count, len(noises), len(TRAINING_COLUMNS)),
        np.nan,
        dtype=np.float64,
    )
    with mask_level_path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        _require_columns(
            mask_level_path,
            reader.fieldnames,
            MASK_LEVEL_COORDINATES + TRAINING_COLUMNS + METRICS,
        )
        for line, row in enumerate(reader, start=2):
            mask = _parse_int(
                row["mask_index"],
                path=mask_level_path,
                line=line,
                column="mask_index",
            )
            noise = _parse_float(
                row["noise"], path=mask_level_path, line=line, column="noise"
            )
            if not 0 <= mask < expected_mask_count:
                raise ValueError(
                    f"{mask_level_path}:{line}: mask index out of range: {mask}"
                )
            if noise not in noise_slot:
                raise ValueError(
                    f"{mask_level_path}:{line}: unexpected noise level {noise}"
                )
            if row["category"] != _expected_category(mask):
                raise ValueError(
                    f"{mask_level_path}:{line}: category is inconsistent with mask {mask}"
                )
            index = (mask, noise_slot[noise])
            if mask_seen[index]:
                raise ValueError(f"{mask_level_path}:{line}: duplicate mask/noise row")
            mask_seen[index] = True
            for metric_index, metric in enumerate(METRICS):
                mask_means[index + (metric_index,)] = _parse_float(
                    row[metric], path=mask_level_path, line=line, column=metric
                )
            for column_index, column in enumerate(TRAINING_COLUMNS):
                training[index + (column_index,)] = _parse_float(
                    row[column], path=mask_level_path, line=line, column=column
                )

    if not np.all(mask_seen):
        missing_count = int(mask_seen.size - np.count_nonzero(mask_seen))
        raise ValueError(
            f"mask-level table is incomplete: {missing_count} rows are missing"
        )
    if not np.all(np.isfinite(mask_means)) or not np.all(np.isfinite(training)):
        raise ValueError("mask-level table contains non-finite values")
    if np.any(training[..., 1] <= 0.0):
        raise ValueError("training_sigma_min_mean must be strictly positive")
    if np.any(training[..., 2] < 0.0):
        raise ValueError("training_rank_1e-3_mean must be nonnegative")

    # Training-only geometry is fixed before evaluation and must consequently
    # be identical in every repeated noise row.
    repeated_training = training[:, :1, :]
    if not np.allclose(training, repeated_training, rtol=0.0, atol=0.0):
        raise ValueError("training geometry changes across noise levels")

    recomputed_means = np.mean(values, axis=(0, 1))
    if not np.allclose(mask_means, recomputed_means, rtol=5.0e-12, atol=5.0e-14):
        difference = np.abs(mask_means - recomputed_means)
        location = np.unravel_index(int(np.argmax(difference)), difference.shape)
        mask, noise_index, metric_index = location
        raise ValueError(
            "mask-level mean does not match per-case data for "
            f"mask={mask}, noise={noises[noise_index]}, metric={METRICS[metric_index]}"
        )

    categories = np.asarray(
        [_expected_category(mask) for mask in range(expected_mask_count)],
        dtype="<U8",
    )
    archive: dict[str, np.ndarray] = {
        "schema_version": np.asarray(1, dtype=np.int64),
        "network_seeds": np.asarray(seeds, dtype=np.int64),
        "samples": np.arange(expected_sample_count, dtype=np.int64),
        "mask_indices": np.arange(expected_mask_count, dtype=np.int64),
        "mask_category": categories,
        "noises": np.asarray(noises, dtype=np.float64),
        "metric_names": np.asarray(METRICS, dtype="<U40"),
        "training_score": training[:, 0, 0].copy(),
        "training_sigma": training[:, 0, 1].copy(),
        "training_rank": training[:, 0, 2].copy(),
        "training_sigma_definition": np.asarray("training_sigma_min_mean"),
        "training_rank_definition": np.asarray("training_rank_1e-3_mean"),
        "scope_note": np.asarray(
            "held-out learned-completion evidence; not a d-r diffusion-rate result"
        ),
    }
    for metric_index, metric in enumerate(METRICS):
        archive[metric] = values[..., metric_index].copy()

    source_paths = (*paths, mask_level_path)
    archive["source_labels"] = np.asarray(
        [
            *(f"per_case_seed_{seed}" for seed in file_seeds),
            "mask_level_metrics",
        ],
        dtype="<U32",
    )
    archive["source_sha256"] = np.asarray(
        [_sha256(path) for path in source_paths], dtype="<U64"
    )

    for name, array in archive.items():
        if np.asarray(array).dtype.hasobject:
            raise AssertionError(f"unsafe object array prepared for key {name}")

    if output_path.suffix != ".npz":
        raise ValueError("output path must end in .npz")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(output_path, **archive)

    # Reopen every member under the public loading policy before reporting
    # success.  Accessing each array is important because object-array failures
    # occur lazily in NumPy's NPZ reader.
    with np.load(output_path, allow_pickle=False) as check:
        for name in check.files:
            loaded = check[name]
            if loaded.dtype.hasobject:
                raise AssertionError(f"unsafe object dtype written for key {name}")
    return archive


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "per_case_csvs",
        type=Path,
        nargs=3,
        metavar=("SEED11_CSV", "SEED12_CSV", "SEED13_CSV"),
        help="the three per_case_metrics.csv files (order is arbitrary)",
    )
    parser.add_argument("mask_level_csv", type=Path, help="mask_level_metrics.csv")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    archive = curate_metrics(
        args.per_case_csvs,
        args.mask_level_csv,
        args.output,
    )
    report = {
        "output": str(args.output),
        "network_seeds": archive["network_seeds"].tolist(),
        "metric_shape": list(archive[METRICS[0]].shape),
        "metrics": list(METRICS),
        "allow_pickle": False,
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
