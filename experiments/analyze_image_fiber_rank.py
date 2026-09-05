"""Curate and summarize full-map Jacobian ranks for the image-fiber bound.

The mathematical refinement in the manuscript uses
``rank(DF|ker(DH))``.  Since ``H = P F``, this rank equals
``rank(DF) - rank(DH)`` whenever the two ranks are locally constant.  This
script records the numerical rank of the complete-data Jacobian ``DF`` in
previously completed population studies.  It is a finite-difference
diagnostic, not evidence of exact or fiber-global constant rank.

By default the script only summarizes the committed CSV.  Supplying one or
more ``--source SEED=ARCHIVE`` arguments recreates that CSV from parent-study
``population_jacobians.npz`` archives and records their content hashes without
recording machine-specific paths.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from collections import Counter
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
DEFAULT_OUTPUT_DIR = HERE / "results" / "image_fiber_rank"
CSV_NAME = "full_map_spectra.csv"
SUMMARY_NAME = "summary.json"
PARAMETERS_NAME = "parameters.json"
DEFAULT_RELATIVE_RANK_THRESHOLD = 1.0e-3
SINGULAR_VALUE_FIELDS = tuple(f"sigma_{index}" for index in range(1, 9))


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _parse_source(value: str) -> tuple[int, Path]:
    try:
        seed_text, path_text = value.split("=", 1)
        seed = int(seed_text)
    except (TypeError, ValueError) as exc:
        raise argparse.ArgumentTypeError(
            "source must have the form SEED=ARCHIVE"
        ) from exc
    path = Path(path_text)
    if not path.is_file():
        raise argparse.ArgumentTypeError(f"source archive does not exist: {path}")
    return seed, path


def curate_sources(
    sources: list[tuple[int, Path]],
    output_dir: Path,
    *,
    threshold: float,
    train_count: int,
) -> None:
    """Write a path-free singular-spectrum table from completed archives."""

    if not sources:
        return
    if not 0.0 < threshold < 1.0:
        raise ValueError("threshold must lie in (0, 1)")

    rows: list[dict[str, object]] = []
    source_records: list[dict[str, object]] = []
    seen_seeds: set[int] = set()
    for seed, source in sources:
        if seed in seen_seeds:
            raise ValueError(f"duplicate source seed: {seed}")
        seen_seeds.add(seed)
        with np.load(source, allow_pickle=False) as archive:
            if "jacobians" not in archive.files:
                raise ValueError(f"archive has no jacobians array: {source}")
            jacobians = np.asarray(archive["jacobians"], dtype=float)
        if jacobians.ndim != 3 or jacobians.shape[2] != 8:
            raise ValueError(
                f"expected jacobians with shape (samples, outputs, 8), got "
                f"{jacobians.shape}"
            )
        if not 0 <= train_count <= jacobians.shape[0]:
            raise ValueError("train_count is incompatible with a source archive")
        if not np.all(np.isfinite(jacobians)):
            raise ValueError(f"non-finite Jacobian in source archive: {source}")

        spectra = np.linalg.svd(jacobians, compute_uv=False)
        if np.any(spectra[:, 0] <= 0.0):
            raise ValueError(
                f"source archive contains a zero leading singular value: {source}"
            )
        relative = spectra / spectra[:, :1]
        ranks = np.count_nonzero(relative > threshold, axis=1)
        for sample_index, (spectrum, relative_spectrum, rank) in enumerate(
            zip(spectra, relative, ranks, strict=True)
        ):
            row: dict[str, object] = {
                "population_seed": seed,
                "sample_index": sample_index,
                "split": "train" if sample_index < train_count else "test",
                "numerical_rank": int(rank),
                "relative_sigma_8": float(relative_spectrum[-1]),
            }
            for index, singular_value in enumerate(spectrum, start=1):
                row[f"sigma_{index}"] = float(singular_value)
            rows.append(row)
        source_records.append(
            {
                "population_seed": seed,
                "archive_sha256": _sha256(source),
                "samples": int(jacobians.shape[0]),
                "output_dimension": int(jacobians.shape[1]),
                "parameter_dimension": int(jacobians.shape[2]),
            }
        )

    output_dir.mkdir(parents=True, exist_ok=True)
    fieldnames = list(rows[0])
    with (output_dir / CSV_NAME).open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    parameters = {
        "study": "post-hoc full-map numerical-rank audit",
        "relative_rank_threshold": threshold,
        "train_samples_per_population": train_count,
        "source_archives": source_records,
        "interpretation": (
            "Finite-difference numerical ranks only; exact rank and constant "
            "rank on complete observation fibers are not inferred."
        ),
    }
    (output_dir / PARAMETERS_NAME).write_text(
        json.dumps(parameters, indent=2) + "\n", encoding="utf-8"
    )


def summarize(csv_path: Path, *, threshold: float) -> dict[str, object]:
    """Return a deterministic summary of a curated spectrum table."""

    if not 0.0 < threshold < 1.0:
        raise ValueError("threshold must lie in (0, 1)")
    with csv_path.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    if not rows:
        raise ValueError("full-map spectrum table is empty")

    try:
        spectra = np.asarray(
            [
                [float(row[field]) for field in SINGULAR_VALUE_FIELDS]
                for row in rows
            ],
            dtype=float,
        )
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("spectrum table contains an invalid singular value") from exc
    if np.any(~np.isfinite(spectra)) or np.any(spectra < 0.0):
        raise ValueError("spectrum table contains an invalid singular value")
    if np.any(spectra[:, 0] <= 0.0):
        raise ValueError("spectrum table contains a zero leading singular value")
    if np.any(np.diff(spectra, axis=1) > 0.0):
        raise ValueError("singular values must be recorded in nonincreasing order")

    relative_spectra = spectra / spectra[:, :1]
    ranks = np.count_nonzero(relative_spectra > threshold, axis=1)
    relative_sigma = relative_spectra[:, -1]
    sigma_8 = spectra[:, -1]
    seeds = sorted({int(row["population_seed"]) for row in rows})

    # The committed table caches the thresholded rank and final relative
    # singular value for convenient inspection.  Validate those cached fields
    # at the release threshold, while allowing callers to recompute a genuinely
    # different threshold from the full spectrum.
    try:
        cached_relative_sigma = np.asarray(
            [float(row["relative_sigma_8"]) for row in rows], dtype=float
        )
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("spectrum table has an invalid relative_sigma_8 cache") from exc
    if not np.allclose(
        cached_relative_sigma, relative_sigma, rtol=1.0e-12, atol=0.0
    ):
        raise ValueError("relative_sigma_8 cache is inconsistent with the spectrum")
    if threshold == DEFAULT_RELATIVE_RANK_THRESHOLD:
        try:
            cached_ranks = np.asarray(
                [int(row["numerical_rank"]) for row in rows], dtype=int
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError("spectrum table has an invalid numerical_rank cache") from exc
        if not np.array_equal(cached_ranks, ranks):
            raise ValueError(
                "numerical_rank cache is inconsistent with the release threshold"
            )

    rank_counts = Counter(int(rank) for rank in ranks)
    return {
        "study": "post-hoc full-map numerical-rank audit",
        "population_seeds": seeds,
        "sample_count": len(rows),
        "relative_rank_threshold": threshold,
        "numerical_rank_counts": {
            str(rank): count for rank, count in sorted(rank_counts.items())
        },
        "all_numerical_ranks_equal_parameter_dimension": bool(np.all(ranks == 8)),
        "sigma_8": {
            "minimum": float(np.min(sigma_8)),
            "median": float(np.median(sigma_8)),
            "tenth_percentile": float(np.quantile(sigma_8, 0.1)),
        },
        "relative_sigma_8": {
            "minimum": float(np.min(relative_sigma)),
            "median": float(np.median(relative_sigma)),
            "tenth_percentile": float(np.quantile(relative_sigma, 0.1)),
        },
        "image_fiber_interpretation": (
            "At the sampled Jacobians the complete map has numerical rank 8, "
            "so the numerical rank-difference diagnostic gives 8-r rather than "
            "a stricter exponent. This does not verify either rank on a complete "
            "fiber neighborhood."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source",
        action="append",
        type=_parse_source,
        default=[],
        metavar="SEED=ARCHIVE",
        help="completed population archive to curate; may be repeated",
    )
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument(
        "--threshold", type=float, default=DEFAULT_RELATIVE_RANK_THRESHOLD
    )
    parser.add_argument("--train-count", type=int, default=80)
    args = parser.parse_args()

    curate_sources(
        args.source,
        args.output_dir,
        threshold=args.threshold,
        train_count=args.train_count,
    )
    summary = summarize(args.output_dir / CSV_NAME, threshold=args.threshold)
    (args.output_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
