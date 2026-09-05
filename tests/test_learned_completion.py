from __future__ import annotations

import csv
import hashlib
import sys
from pathlib import Path

import numpy as np
import pytest


EXPERIMENTS = Path(__file__).resolve().parents[1] / "experiments"
sys.path.insert(0, str(EXPERIMENTS))

from analyze_learned_completion import (  # noqa: E402
    METRICS,
    analyze_arrays,
    average_ranks,
    crossed_ratio_interval,
    make_figure,
    validate_archive,
)
from curate_learned_completion import curate_metrics  # noqa: E402


def _synthetic_archive() -> dict[str, np.ndarray]:
    shape = (2, 3, 4, 2)
    arrays: dict[str, np.ndarray] = {
        "schema_version": np.asarray(1, dtype=np.int64),
        "network_seeds": np.array([11, 12]),
        "samples": np.arange(3),
        "mask_indices": np.arange(4),
        "mask_category": np.array(["selected", "random", "random", "random"]),
        "noises": np.array([0.0, 1.0e-3]),
        "metric_names": np.asarray(METRICS),
        "source_labels": np.array(["per_case", "mask_level"]),
        "source_sha256": np.array(["0" * 64, "1" * 64]),
        "training_score": np.array([10.0, 1.0, 2.0, 3.0]),
        "training_sigma": np.array([0.8, 0.1, 0.2, 0.3]),
        "training_rank": np.array([6.0, 4.0, 5.0, 6.0]),
    }
    for metric in METRICS:
        arrays[metric] = np.ones(shape, dtype=float)

    # Constant seed and polygon effects make every bootstrap replicate equal
    # to the exact population ratio while retaining nonconstant mask effects.
    arrays["edm_missing_error"][...] = np.array([2.0, 6.0, 4.0, 2.0])[None, None, :, None]
    arrays["edm_projected_missing_error"][...] = np.array(
        [1.5, 5.0, 3.0, 1.0]
    )[None, None, :, None]
    arrays["edm_single_missing_error"][...] = np.array(
        [6.0, 9.0, 6.0, 3.0]
    )[None, None, :, None]
    arrays["unet_missing_error"][...] = np.array([4.0, 3.0, 2.0, 1.0])[
        None, None, :, None
    ]
    arrays["projected_energy_score"][...] = np.array([1.0, 3.0, 2.0, 1.0])[
        None, None, :, None
    ]
    arrays["projected_coverage_90"][...] = np.array([0.9, 0.8, 0.8, 0.8])[
        None, None, :, None
    ]
    arrays["projected_interval_width"][...] = 0.2
    arrays["physical_row_sum_error"][...] = np.array([10.0, 8.0, 6.0, 4.0])[
        None, None, :, None
    ]
    arrays["projected_physical_row_sum_error"][...] = np.array(
        [2.0, 2.0, 2.0, 2.0]
    )[None, None, :, None]
    return arrays


def test_archive_shape_validation_rejects_a_misaligned_metric() -> None:
    arrays = _synthetic_archive()
    validate_archive(arrays)

    malformed = dict(arrays)
    malformed["edm_missing_error"] = arrays["edm_missing_error"][:, :, :-1, :]
    with pytest.raises(ValueError, match="edm_missing_error has shape"):
        validate_archive(malformed)


def test_archive_validation_enforces_schema_and_metric_order() -> None:
    malformed = _synthetic_archive()
    malformed["schema_version"] = np.asarray(2, dtype=np.int64)
    with pytest.raises(ValueError, match="schema_version"):
        validate_archive(malformed)

    malformed = _synthetic_archive()
    malformed["metric_names"] = malformed["metric_names"][::-1]
    with pytest.raises(ValueError, match="metric_names"):
        validate_archive(malformed)


def test_archive_validation_enforces_aligned_lowercase_source_hashes() -> None:
    malformed = _synthetic_archive()
    malformed["source_sha256"] = malformed["source_sha256"][:1]
    with pytest.raises(ValueError, match="aligned nonempty vectors"):
        validate_archive(malformed)

    for invalid_digest in ("a" * 63, "A" * 64, "g" * 64):
        malformed = _synthetic_archive()
        malformed["source_sha256"] = np.array([invalid_digest, "1" * 64])
        with pytest.raises(ValueError, match="64-character lowercase hex"):
            validate_archive(malformed)


def test_archive_validation_rejects_duplicate_noise_coordinates() -> None:
    malformed = _synthetic_archive()
    malformed["noises"] = np.array([0.0, 0.0])
    with pytest.raises(ValueError, match="noises must contain unique coordinates"):
        validate_archive(malformed)


def test_average_ranks_handles_ties_deterministically() -> None:
    values = np.array([4.0, 1.0, 1.0, 3.0])
    assert average_ranks(values) == pytest.approx([4.0, 1.5, 1.5, 3.0])


def test_crossed_ratio_bootstrap_preserves_an_exact_pointwise_ratio() -> None:
    denominator = np.array([[1.0, 2.0, 4.0], [3.0, 5.0, 8.0]])
    result = crossed_ratio_interval(
        2.0 * denominator,
        denominator,
        np.random.default_rng(20261001),
        bootstrap_samples=97,
        batch_size=13,
    )
    assert result["ratio"] == pytest.approx(2.0)
    assert result["ci95"] == pytest.approx([2.0, 2.0])


def test_statistical_summary_has_expected_ratios_ranks_and_scope() -> None:
    report = analyze_arrays(
        _synthetic_archive(), bootstrap_samples=31, seed=20261001
    )
    zero = report["noise"]["0e+00"]

    assert zero["mask_comparison"]["edm_missing_error"]["ratio"] == pytest.approx(
        2.0
    )
    assert zero["mask_geometry"]["edm_missing_error"][
        "spearman_random"
    ] == pytest.approx(-1.0)
    assert zero["model_comparison"]["selected_unet_over_edm"][
        "ratio"
    ] == pytest.approx(2.0)
    assert zero["model_comparison"]["random_edm_over_unet"][
        "ratio"
    ] == pytest.approx(2.0)
    assert zero["model_comparison"]["selected_single_over_ensemble"][
        "ratio"
    ] == pytest.approx(3.0)
    assert zero["physics_projection"]["selected_row_sum_reduction"][
        "ratio"
    ] == pytest.approx(5.0)
    assert zero["physics_projection"]["selected_projected_over_unprojected_error"][
        "ratio"
    ] == pytest.approx(0.75)
    assert "d-r diffusion convergence rate" in report["interpretation"][
        "not_supported"
    ]


def _write_small_source_tables(
    directory: Path,
) -> tuple[list[Path], Path, np.ndarray]:
    seeds = (20260911, 20260912, 20260913)
    noises = (0.0, 0.1)
    sample_count = 2
    mask_count = 3
    values = np.empty((len(seeds), sample_count, mask_count, len(noises), len(METRICS)))
    paths: list[Path] = []
    per_case_fields = [
        "network_seed",
        "sample",
        "mask_index",
        "category",
        "noise",
        *METRICS,
    ]
    for seed_index, seed in enumerate(seeds):
        path = directory / f"seed_{seed}.csv"
        paths.append(path)
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=per_case_fields)
            writer.writeheader()
            for sample in range(sample_count):
                for mask in range(mask_count):
                    for noise_index, noise in enumerate(noises):
                        base = 1.0 + seed_index + sample / 10 + mask / 100 + noise
                        row: dict[str, object] = {
                            "network_seed": seed,
                            "sample": sample,
                            "mask_index": mask,
                            "category": "selected" if mask == 0 else "random",
                            "noise": noise,
                        }
                        for metric_index, metric in enumerate(METRICS):
                            value = base + metric_index / 1000
                            if metric == "projected_coverage_90":
                                value = 0.5 + 0.01 * seed_index + 0.01 * sample
                            values[seed_index, sample, mask, noise_index, metric_index] = value
                            row[metric] = value
                        writer.writerow(row)

    mask_path = directory / "mask_level_metrics.csv"
    mask_fields = [
        "mask_index",
        "category",
        "noise",
        "training_score",
        "training_sigma_min_mean",
        "training_rank_1e-3_mean",
        *METRICS,
    ]
    means = np.mean(values, axis=(0, 1))
    with mask_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=mask_fields)
        writer.writeheader()
        for mask in range(mask_count):
            for noise_index, noise in enumerate(noises):
                row = {
                    "mask_index": mask,
                    "category": "selected" if mask == 0 else "random",
                    "noise": noise,
                    "training_score": 3.0 - mask,
                    "training_sigma_min_mean": 0.5 / (mask + 1),
                    "training_rank_1e-3_mean": 6.0 - mask,
                }
                for metric_index, metric in enumerate(METRICS):
                    row[metric] = means[mask, noise_index, metric_index]
                writer.writerow(row)
    return paths, mask_path, values


def test_curator_writes_complete_pickle_free_archive(tmp_path: Path) -> None:
    paths, mask_path, expected = _write_small_source_tables(tmp_path)
    output = tmp_path / "curated.npz"
    shuffled_paths = paths[::-1]
    curate_metrics(
        shuffled_paths,
        mask_path,
        output,
        expected_seeds=(20260911, 20260912, 20260913),
        expected_sample_count=2,
        expected_mask_count=3,
        expected_noises=(0.0, 0.1),
    )

    with np.load(output, allow_pickle=False) as archive:
        for name in archive.files:
            assert not archive[name].dtype.hasobject
        assert archive["edm_missing_error"].shape == (3, 2, 3, 2)
        assert archive["edm_missing_error"] == pytest.approx(expected[..., 0])
        assert archive["training_score"] == pytest.approx([3.0, 2.0, 1.0])
        assert archive["training_sigma"] == pytest.approx([0.5, 0.25, 1.0 / 6.0])
        assert archive["training_rank"] == pytest.approx([6.0, 5.0, 4.0])
        assert archive["source_labels"].tolist()[:3] == [
            "per_case_seed_20260913",
            "per_case_seed_20260912",
            "per_case_seed_20260911",
        ]
        first_digest = hashlib.sha256(shuffled_paths[0].read_bytes()).hexdigest()
        assert archive["source_sha256"][0] == first_digest


@pytest.mark.filterwarnings("ignore::DeprecationWarning")
def test_pdf_generation_is_byte_reproducible(tmp_path: Path) -> None:
    pytest.importorskip("matplotlib")
    arrays = _synthetic_archive()
    report = analyze_arrays(arrays, bootstrap_samples=11, seed=20261001)
    first = tmp_path / "first.pdf"
    second = tmp_path / "second.pdf"

    assert make_figure(arrays, report, first)
    assert make_figure(arrays, report, second)
    assert first.read_bytes() == second.read_bytes()
