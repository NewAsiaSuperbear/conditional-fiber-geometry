#!/usr/bin/env python3
"""Reproduce learned-completion summaries from the curated public NPZ.

The analysis uses NumPy only for all statistical calculations.  Confidence
intervals independently resample the network-seed and held-out-polygon axes;
mask-score correlations are computed only across the 20 score-trimmed random
control masks.  If the optional Matplotlib dependency is installed, the script
also writes a PDF.

These are empirical completion and calibration comparisons.  They neither
estimate an intrinsic image-fiber dimension nor establish a ``d-r`` diffusion
convergence rate.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
from typing import Mapping

import numpy as np


HERE = Path(__file__).resolve().parent
DEFAULT_DATA = HERE / "results" / "learned_completion" / "per_case_metrics.npz"
DEFAULT_JSON = HERE / "results" / "learned_completion" / "summary.json"
DEFAULT_PDF = HERE / "results" / "learned_completion" / "learned_completion.pdf"

BOOTSTRAP_SEED = 20261001
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
GEOMETRY_METRICS = (
    "edm_missing_error",
    "unet_missing_error",
    "projected_energy_score",
)
COORDINATE_KEYS = (
    "network_seeds",
    "samples",
    "mask_indices",
    "mask_category",
    "noises",
    "training_score",
    "training_sigma",
    "training_rank",
)
METADATA_KEYS = (
    "schema_version",
    "metric_names",
    "source_labels",
    "source_sha256",
)
SOURCE_SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")


def load_archive(path: Path) -> dict[str, np.ndarray]:
    """Load every NPZ member with pickle disabled and validate its shapes."""

    try:
        with np.load(path, allow_pickle=False) as archive:
            arrays = {name: archive[name] for name in archive.files}
    except ValueError as exc:
        raise ValueError(f"{path}: archive is not safe with allow_pickle=False") from exc
    validate_archive(arrays)
    return arrays


def validate_archive(arrays: Mapping[str, np.ndarray]) -> None:
    """Validate the coordinate arrays and all per-case metric tensor shapes."""

    missing = sorted(set(COORDINATE_KEYS + METADATA_KEYS + METRICS) - set(arrays))
    if missing:
        raise ValueError(f"curated archive is missing arrays: {missing}")
    for name, value in arrays.items():
        if np.asarray(value).dtype.hasobject:
            raise ValueError(f"archive member {name!r} has unsafe object dtype")

    schema_version = np.asarray(arrays["schema_version"])
    if (
        schema_version.shape != ()
        or schema_version.dtype.kind not in "iu"
        or int(schema_version) != 1
    ):
        raise ValueError("schema_version must be the integer scalar 1")

    metric_names = np.asarray(arrays["metric_names"])
    if metric_names.ndim != 1 or tuple(metric_names.astype(str)) != METRICS:
        raise ValueError("metric_names must exactly match METRICS in order")

    source_labels = np.asarray(arrays["source_labels"])
    source_sha256 = np.asarray(arrays["source_sha256"])
    if (
        source_labels.ndim != 1
        or source_sha256.ndim != 1
        or source_labels.size == 0
        or source_labels.shape != source_sha256.shape
    ):
        raise ValueError(
            "source_labels and source_sha256 must be aligned nonempty vectors"
        )
    labels = source_labels.astype(str)
    digests = source_sha256.astype(str)
    if np.unique(labels).size != labels.size or np.any(labels == ""):
        raise ValueError("source_labels must be nonempty and unique")
    if any(SOURCE_SHA256_PATTERN.fullmatch(digest) is None for digest in digests):
        raise ValueError("source_sha256 entries must be 64-character lowercase hex")

    seeds = np.asarray(arrays["network_seeds"])
    samples = np.asarray(arrays["samples"])
    masks = np.asarray(arrays["mask_indices"])
    categories = np.asarray(arrays["mask_category"])
    noises = np.asarray(arrays["noises"], dtype=float)
    if any(array.ndim != 1 for array in (seeds, samples, masks, categories, noises)):
        raise ValueError("coordinate arrays must all be one-dimensional")
    if min(seeds.size, samples.size, masks.size, noises.size) == 0:
        raise ValueError("coordinate arrays must be nonempty")
    if categories.shape != masks.shape:
        raise ValueError("mask_category must have one entry per mask")
    for name, coordinate in (
        ("network_seeds", seeds),
        ("samples", samples),
        ("mask_indices", masks),
        ("noises", noises),
    ):
        if np.unique(coordinate).size != coordinate.size:
            raise ValueError(f"{name} must contain unique coordinates")
    if not np.all(np.isfinite(noises)):
        raise ValueError("noise coordinates must be finite")

    category_values = categories.astype(str)
    selected_count = int(np.count_nonzero(category_values == "selected"))
    random_count = int(np.count_nonzero(category_values == "random"))
    if selected_count != 1 or random_count != masks.size - 1 or random_count < 2:
        raise ValueError("archive must contain one selected and at least two random masks")

    for name in ("training_score", "training_sigma", "training_rank"):
        value = np.asarray(arrays[name], dtype=float)
        if value.shape != masks.shape:
            raise ValueError(f"{name} must have shape ({masks.size},)")
        if not np.all(np.isfinite(value)):
            raise ValueError(f"{name} must be finite")
    if np.any(np.asarray(arrays["training_sigma"], dtype=float) <= 0.0):
        raise ValueError("training_sigma must be strictly positive")
    if np.any(np.asarray(arrays["training_rank"], dtype=float) < 0.0):
        raise ValueError("training_rank must be nonnegative")

    expected_shape = (seeds.size, samples.size, masks.size, noises.size)
    for metric in METRICS:
        value = np.asarray(arrays[metric], dtype=float)
        if value.shape != expected_shape:
            raise ValueError(
                f"{metric} has shape {value.shape}; expected {expected_shape}"
            )
        if not np.all(np.isfinite(value)):
            raise ValueError(f"{metric} must contain only finite values")
        if metric == "projected_coverage_90":
            if np.any((value < 0.0) | (value > 1.0)):
                raise ValueError("projected_coverage_90 must lie in [0, 1]")
        elif np.any(value < 0.0):
            raise ValueError(f"{metric} must be nonnegative")


def average_ranks(values: np.ndarray) -> np.ndarray:
    """Return one-based average ranks with stable, deterministic tie handling."""

    array = np.asarray(values, dtype=float)
    if array.ndim != 1 or array.size == 0:
        raise ValueError("rank input must be a nonempty one-dimensional array")
    if not np.all(np.isfinite(array)):
        raise ValueError("rank input must be finite")
    order = np.argsort(array, kind="stable")
    sorted_values = array[order]
    sorted_ranks = np.arange(1, array.size + 1, dtype=float)
    start = 0
    while start < array.size:
        stop = start + 1
        while stop < array.size and sorted_values[stop] == sorted_values[start]:
            stop += 1
        sorted_ranks[start:stop] = 0.5 * (start + 1 + stop)
        start = stop
    ranks = np.empty(array.size, dtype=float)
    ranks[order] = sorted_ranks
    return ranks


def _row_average_ranks(values: np.ndarray) -> np.ndarray:
    """Vectorize average ranks over rows, looping only over rows with ties."""

    array = np.asarray(values, dtype=float)
    if array.ndim != 2 or array.shape[1] == 0:
        raise ValueError("row-rank input must be a nonempty two-dimensional array")
    if not np.all(np.isfinite(array)):
        raise ValueError("row-rank input must be finite")
    order = np.argsort(array, axis=1, kind="stable")
    sorted_values = np.take_along_axis(array, order, axis=1)
    sorted_ranks = np.broadcast_to(
        np.arange(1, array.shape[1] + 1, dtype=float), array.shape
    ).copy()
    tied_rows = np.flatnonzero(np.any(np.diff(sorted_values, axis=1) == 0.0, axis=1))
    for row in tied_rows:
        start = 0
        while start < array.shape[1]:
            stop = start + 1
            while (
                stop < array.shape[1]
                and sorted_values[row, stop] == sorted_values[row, start]
            ):
                stop += 1
            sorted_ranks[row, start:stop] = 0.5 * (start + 1 + stop)
            start = stop
    ranks = np.empty_like(sorted_ranks)
    np.put_along_axis(ranks, order, sorted_ranks, axis=1)
    return ranks


def rowwise_spearman(score: np.ndarray, metric_rows: np.ndarray) -> np.ndarray:
    """Compute one Spearman correlation per row using NumPy only."""

    x = np.asarray(score, dtype=float)
    y = np.asarray(metric_rows, dtype=float)
    if x.ndim != 1 or y.ndim != 2 or y.shape[1] != x.size:
        raise ValueError("score and metric rows have incompatible shapes")
    x_rank = average_ranks(x)
    x_centered = x_rank - np.mean(x_rank)
    y_rank = _row_average_ranks(y)
    y_centered = y_rank - np.mean(y_rank, axis=1, keepdims=True)
    numerator = np.sum(y_centered * x_centered[None, :], axis=1)
    denominator = np.sqrt(
        np.sum(x_centered**2) * np.sum(y_centered**2, axis=1)
    )
    if np.any(denominator == 0.0):
        raise ValueError("Spearman correlation is undefined for a constant input")
    return numerator / denominator


def spearman(score: np.ndarray, metric: np.ndarray) -> float:
    """Compute a scalar Spearman rank correlation using NumPy only."""

    return float(rowwise_spearman(score, np.asarray(metric)[None, :])[0])


def crossed_ratio_interval(
    numerator: np.ndarray,
    denominator: np.ndarray,
    rng: np.random.Generator,
    bootstrap_samples: int,
    batch_size: int = 250,
) -> dict[str, object]:
    """Bootstrap a ratio over crossed network-seed and polygon effects."""

    top = np.asarray(numerator, dtype=float)
    bottom = np.asarray(denominator, dtype=float)
    if top.shape != bottom.shape or top.ndim != 2 or min(top.shape) == 0:
        raise ValueError("paired arrays must have shape (network_seed, polygon)")
    if not np.all(np.isfinite(top)) or not np.all(np.isfinite(bottom)):
        raise ValueError("paired arrays must be finite")
    if bootstrap_samples <= 0 or batch_size <= 0:
        raise ValueError("bootstrap_samples and batch_size must be positive")
    if np.mean(bottom) == 0.0:
        raise ValueError("ratio denominator has zero mean")

    seed_count, polygon_count = top.shape
    ratios = np.empty(bootstrap_samples, dtype=float)
    for start in range(0, bootstrap_samples, batch_size):
        stop = min(start + batch_size, bootstrap_samples)
        count = stop - start
        seed_draw = rng.integers(0, seed_count, (count, seed_count))
        polygon_draw = rng.integers(0, polygon_count, (count, polygon_count))
        sampled_top = top[seed_draw[:, :, None], polygon_draw[:, None, :]]
        sampled_bottom = bottom[
            seed_draw[:, :, None], polygon_draw[:, None, :]
        ]
        bottom_means = np.mean(sampled_bottom, axis=(1, 2))
        if np.any(bottom_means == 0.0):
            raise ValueError("a bootstrap replicate has zero denominator mean")
        ratios[start:stop] = np.mean(sampled_top, axis=(1, 2)) / bottom_means
    return {
        "ratio": float(np.mean(top) / np.mean(bottom)),
        "ci95": [
            float(np.quantile(ratios, 0.025)),
            float(np.quantile(ratios, 0.975)),
        ],
    }


def crossed_spearman_interval(
    score: np.ndarray,
    seed_by_polygon_by_mask: np.ndarray,
    rng: np.random.Generator,
    bootstrap_samples: int,
    batch_size: int = 100,
) -> list[float]:
    """Bootstrap a mask correlation over crossed seed and polygon effects."""

    x = np.asarray(score, dtype=float)
    metric = np.asarray(seed_by_polygon_by_mask, dtype=float)
    if metric.ndim != 3 or min(metric.shape) == 0:
        raise ValueError("metric must have shape (network_seed, polygon, mask)")
    if x.shape != (metric.shape[2],):
        raise ValueError("mask scores do not align with the metric tensor")
    if not np.all(np.isfinite(metric)):
        raise ValueError("metric tensor must be finite")
    if bootstrap_samples <= 0 or batch_size <= 0:
        raise ValueError("bootstrap_samples and batch_size must be positive")

    seed_count, polygon_count, mask_count = metric.shape
    correlations = np.empty(bootstrap_samples, dtype=float)
    mask_draw = np.arange(mask_count)[None, None, None, :]
    for start in range(0, bootstrap_samples, batch_size):
        stop = min(start + batch_size, bootstrap_samples)
        count = stop - start
        seed_draw = rng.integers(0, seed_count, (count, seed_count))
        polygon_draw = rng.integers(0, polygon_count, (count, polygon_count))
        sampled = metric[
            seed_draw[:, :, None, None],
            polygon_draw[:, None, :, None],
            mask_draw,
        ]
        mask_means = np.mean(sampled, axis=(1, 2))
        correlations[start:stop] = rowwise_spearman(x, mask_means)
    return [
        float(np.quantile(correlations, 0.025)),
        float(np.quantile(correlations, 0.975)),
    ]


def _noise_key(noise: float) -> str:
    return f"{noise:.0e}"


def analyze_arrays(
    arrays: Mapping[str, np.ndarray],
    *,
    bootstrap_samples: int = 10000,
    seed: int = BOOTSTRAP_SEED,
) -> dict[str, object]:
    """Compute all public summaries from validated curated arrays."""

    validate_archive(arrays)
    if bootstrap_samples <= 0:
        raise ValueError("bootstrap_samples must be positive")
    rng = np.random.default_rng(seed)
    categories = np.asarray(arrays["mask_category"]).astype(str)
    selected_index = int(np.flatnonzero(categories == "selected")[0])
    random_indices = np.flatnonzero(categories == "random")
    score = np.asarray(arrays["training_score"], dtype=float)
    noises = np.asarray(arrays["noises"], dtype=float)

    report: dict[str, object] = {
        "schema_version": 1,
        "analysis": {
            "bootstrap": "crossed network-seed and held-out-polygon resampling",
            "bootstrap_seed": int(seed),
            "bootstrap_samples": int(bootstrap_samples),
            "correlations": "Spearman average ranks across score-trimmed random controls only",
        },
        "design": {
            "network_seeds": np.asarray(arrays["network_seeds"]).astype(int).tolist(),
            "held_out_polygons": int(np.asarray(arrays["samples"]).size),
            "mask_count": int(categories.size),
            "random_mask_count": int(random_indices.size),
            "noise_levels": noises.tolist(),
            "selected_mask": {
                "mask_index": int(np.asarray(arrays["mask_indices"])[selected_index]),
                "training_score": float(score[selected_index]),
                "training_sigma": float(
                    np.asarray(arrays["training_sigma"], dtype=float)[selected_index]
                ),
                "training_rank": float(
                    np.asarray(arrays["training_rank"], dtype=float)[selected_index]
                ),
            },
            "random_training_score_range": [
                float(np.min(score[random_indices])),
                float(np.max(score[random_indices])),
            ],
            "random_training_sigma_range": [
                float(
                    np.min(
                        np.asarray(arrays["training_sigma"], dtype=float)[
                            random_indices
                        ]
                    )
                ),
                float(
                    np.max(
                        np.asarray(arrays["training_sigma"], dtype=float)[
                            random_indices
                        ]
                    )
                ),
            ],
            "random_training_rank_range": [
                float(
                    np.min(
                        np.asarray(arrays["training_rank"], dtype=float)[
                            random_indices
                        ]
                    )
                ),
                float(
                    np.max(
                        np.asarray(arrays["training_rank"], dtype=float)[
                            random_indices
                        ]
                    )
                ),
            ],
        },
        "interpretation": {
            "supported": (
                "held-out empirical learned-completion, uncertainty, mask-score, "
                "and physical-projection comparisons"
            ),
            "not_supported": (
                "The experiment does not establish a d-r diffusion convergence "
                "rate, score-learning theorem, or intrinsic image-fiber dimension."
            ),
        },
        "noise": {},
    }

    for noise_index, noise in enumerate(noises):
        descriptive: dict[str, object] = {}
        selected_by_metric: dict[str, np.ndarray] = {}
        random_by_metric: dict[str, np.ndarray] = {}
        for metric in METRICS:
            values = np.asarray(arrays[metric], dtype=float)[..., noise_index]
            selected = values[:, :, selected_index]
            random = np.mean(values[:, :, random_indices], axis=2)
            selected_by_metric[metric] = selected
            random_by_metric[metric] = random
            descriptive[metric] = {
                "selected_mean": float(np.mean(selected)),
                "random_mean": float(np.mean(random)),
            }

        geometry: dict[str, object] = {}
        for metric in GEOMETRY_METRICS:
            values = np.asarray(arrays[metric], dtype=float)[..., noise_index]
            random_tensor = values[:, :, random_indices]
            random_mask_means = np.mean(random_tensor, axis=(0, 1))
            geometry[metric] = {
                "spearman_random": spearman(
                    score[random_indices], random_mask_means
                ),
                "crossed_bootstrap_ci95": crossed_spearman_interval(
                    score[random_indices],
                    random_tensor,
                    rng,
                    bootstrap_samples,
                ),
                "selected_mean": float(
                    np.mean(values[:, :, selected_index])
                ),
                "random_mean": float(np.mean(random_mask_means)),
            }

        # Keep the generator call order fixed: all correlation replicates are
        # drawn first, followed by all paired-ratio replicates.  Together with
        # the recorded seed this makes the public JSON exactly reproducible.
        mask_comparison: dict[str, object] = {}
        for metric in GEOMETRY_METRICS:
            mask_comparison[metric] = crossed_ratio_interval(
                random_by_metric[metric],
                selected_by_metric[metric],
                rng,
                bootstrap_samples,
            )

        report["noise"][_noise_key(float(noise))] = {  # type: ignore[index]
            "descriptive_metrics": descriptive,
            "mask_geometry": geometry,
            "mask_comparison": mask_comparison,
            "model_comparison": {
                "selected_unet_over_edm": crossed_ratio_interval(
                    selected_by_metric["unet_missing_error"],
                    selected_by_metric["edm_missing_error"],
                    rng,
                    bootstrap_samples,
                ),
                "random_edm_over_unet": crossed_ratio_interval(
                    random_by_metric["edm_missing_error"],
                    random_by_metric["unet_missing_error"],
                    rng,
                    bootstrap_samples,
                ),
                "selected_single_over_ensemble": crossed_ratio_interval(
                    selected_by_metric["edm_single_missing_error"],
                    selected_by_metric["edm_missing_error"],
                    rng,
                    bootstrap_samples,
                ),
            },
            "physics_projection": {
                "selected_row_sum_reduction": crossed_ratio_interval(
                    selected_by_metric["physical_row_sum_error"],
                    selected_by_metric["projected_physical_row_sum_error"],
                    rng,
                    bootstrap_samples,
                ),
                "selected_projected_over_unprojected_error": (
                    crossed_ratio_interval(
                        selected_by_metric["edm_projected_missing_error"],
                        selected_by_metric["edm_missing_error"],
                        rng,
                        bootstrap_samples,
                    )
                ),
            },
        }
    return report


def _configure_matplotlib() -> bool:
    try:
        import matplotlib as mpl
    except ImportError:  # pragma: no cover - depends on optional dependency
        return False
    mpl.rcParams.update(
        {
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
            "font.family": "sans-serif",
            "font.sans-serif": ["DejaVu Sans"],
            "font.size": 9,
            "axes.titlesize": 10,
            "axes.labelsize": 9,
            "legend.fontsize": 8,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
            "figure.dpi": 150,
            "savefig.bbox": "tight",
        }
    )
    return True


def make_figure(
    arrays: Mapping[str, np.ndarray], report: Mapping[str, object], output: Path
) -> bool:
    """Write the four-panel public summary PDF when Matplotlib is available."""

    if not _configure_matplotlib():
        return False
    import matplotlib.pyplot as plt

    categories = np.asarray(arrays["mask_category"]).astype(str)
    selected_index = int(np.flatnonzero(categories == "selected")[0])
    random_indices = np.flatnonzero(categories == "random")
    score = np.asarray(arrays["training_score"], dtype=float)
    noises = np.asarray(arrays["noises"], dtype=float)
    zero_index = int(np.argmin(np.abs(noises)))
    zero_key = _noise_key(float(noises[zero_index]))
    noise_report = report["noise"]  # type: ignore[index]

    colors = ("#0072B2", "#E69F00", "#009E73")
    markers = ("o", "s", "^")
    figure, axes = plt.subplots(2, 2, figsize=(10.2, 7.2), constrained_layout=True)
    ax_edm, ax_energy, ax_ratio, ax_coverage = axes.flat

    for axis, metric, ylabel, panel in (
        (ax_edm, "edm_missing_error", "EDM missing-entry error", "(a)"),
        (
            ax_energy,
            "projected_energy_score",
            "projected energy score",
            "(b)",
        ),
    ):
        values = np.asarray(arrays[metric], dtype=float)[..., zero_index]
        mask_means = np.mean(values, axis=(0, 1))
        axis.scatter(
            score[random_indices],
            mask_means[random_indices],
            s=30,
            color=colors[0],
            alpha=0.8,
            label="score-trimmed random controls",
        )
        axis.scatter(
            [score[selected_index]],
            [mask_means[selected_index]],
            s=125,
            marker="*",
            color="#D55E00",
            label="training-selected",
            zorder=3,
        )
        correlation = noise_report[zero_key]["mask_geometry"][metric][  # type: ignore[index]
            "spearman_random"
        ]
        axis.text(
            0.04,
            0.96,
            rf"control-only $\rho_s={float(correlation):.2f}$",
            transform=axis.transAxes,
            va="top",
        )
        axis.set(
            title=f"{panel} Training geometry and held-out loss",
            xlabel="regularized Gram log-determinant score",
            ylabel=ylabel,
        )
        axis.legend(frameon=False)

    x = np.arange(noises.size)
    labels = ["0" if noise == 0 else f"{noise:.0e}" for noise in noises]
    for color, marker, metric, label in zip(
        colors,
        markers,
        GEOMETRY_METRICS,
        ("EDM error", "U-Net error", "energy score"),
        strict=True,
    ):
        ratios = [
            float(
                noise_report[_noise_key(float(noise))]["mask_comparison"][metric][
                    "ratio"
                ]
            )
            for noise in noises
        ]
        ax_ratio.plot(x, ratios, color=color, marker=marker, label=label)
    ax_ratio.axhline(1.0, color="black", linestyle="--", linewidth=0.9)
    ax_ratio.set(
        title="(c) Control/selected held-out loss",
        xlabel="normalized observation noise s.d.",
        ylabel="ratio (values above one favor selected)",
        xticks=x,
        xticklabels=labels,
    )
    ax_ratio.legend(frameon=False)

    coverage = np.asarray(arrays["projected_coverage_90"], dtype=float)
    selected_coverage = np.mean(coverage[:, :, selected_index, :], axis=(0, 1))
    random_coverage = np.mean(
        coverage[:, :, random_indices, :], axis=(0, 1, 2)
    )
    ax_coverage.plot(x, selected_coverage, color=colors[0], marker="o", label="selected")
    ax_coverage.plot(x, random_coverage, color=colors[1], marker="s", label="controls")
    ax_coverage.axhline(0.9, color="black", linestyle="--", linewidth=0.9)
    ax_coverage.set(
        title="(d) Projected 90% interval calibration",
        xlabel="normalized observation noise s.d.",
        ylabel="empirical coverage",
        xticks=x,
        xticklabels=labels,
        ylim=(0.0, 1.0),
    )
    ax_coverage.legend(frameon=False)

    for axis in axes.flat:
        axis.grid(True, color="#B8B8B8", linewidth=0.55, alpha=0.45)
        axis.set_axisbelow(True)
    figure.suptitle(
        "Learned completion evidence (empirical; not a d-r diffusion-rate test)",
        fontsize=11,
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    figure.savefig(
        output,
        metadata={
            "Title": "Learned Completion Evidence",
            "Author": "Weiyan Wu",
            "Subject": "Held-out conditional EDM and U-Net comparisons",
            "Keywords": "EIT, learned completion, mask design, empirical evidence",
            "Creator": "analyze_learned_completion.py",
            "Producer": "Matplotlib",
            "CreationDate": None,
            "ModDate": None,
        },
    )
    plt.close(figure)
    return True


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, nargs="?", default=DEFAULT_DATA)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--output-pdf", type=Path, default=DEFAULT_PDF)
    parser.add_argument("--bootstrap-samples", type=int, default=10000)
    parser.add_argument("--seed", type=int, default=BOOTSTRAP_SEED)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    arrays = load_archive(args.archive)
    report = analyze_arrays(
        arrays,
        bootstrap_samples=args.bootstrap_samples,
        seed=args.seed,
    )
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    figure_written = make_figure(arrays, report, args.output_pdf)
    print(
        json.dumps(
            {
                "input": str(args.archive),
                "output_json": str(args.output_json),
                "output_pdf": str(args.output_pdf) if figure_written else None,
                "bootstrap_seed": args.seed,
                "bootstrap_samples": args.bootstrap_samples,
                "scope": report["interpretation"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
