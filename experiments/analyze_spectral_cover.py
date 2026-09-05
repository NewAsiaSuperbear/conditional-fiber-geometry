#!/usr/bin/env python3
"""Report per-scale diagnostics for the finite-cloud covering comparison.

The underlying point clouds contain 360 points.  Fine scales can therefore
saturate at a cover count of 360 and induce many ties.  This script makes the
per-scale correlations, saturation fraction, and the pre-existing usable-scale
criterion explicit.  It summarizes a completed experiment; it does not rerun
the EIT solver or estimate a continuum covering dimension.
"""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
DEFAULT_INPUT = HERE / "results" / "spectral_validation" / "linear_spectral_cover.csv"
DEFAULT_OUTPUT = HERE / "results" / "spectral_validation" / "cover_scale_diagnostics.csv"
DEFAULT_SUMMARY = HERE / "results" / "spectral_validation" / "cover_scale_summary.json"


def average_ranks(values: np.ndarray) -> np.ndarray:
    """Return one-based average ranks with deterministic tie handling."""

    array = np.asarray(values, dtype=float)
    if array.ndim != 1 or array.size == 0 or not np.all(np.isfinite(array)):
        raise ValueError("rank input must be a finite, nonempty vector")
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
    result = np.empty_like(sorted_ranks)
    result[order] = sorted_ranks
    return result


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    """Compute Spearman correlation or reject a constant ranked input."""

    left = average_ranks(x)
    right = average_ranks(y)
    left -= np.mean(left)
    right -= np.mean(right)
    denominator = np.linalg.norm(left) * np.linalg.norm(right)
    if denominator == 0.0:
        raise ValueError("Spearman correlation is undefined for a constant input")
    return float(np.dot(left, right) / denominator)


def analyze(table: np.ndarray, *, point_count: int) -> list[dict[str, object]]:
    """Return one diagnostic record per covering scale."""

    required = {
        "mask_index",
        "epsilon",
        "cover_count",
        "log_cover_count",
        "full_spectrum_log_predictor",
        "sigma_min_only_log_predictor",
    }
    names = set(table.dtype.names or ())
    missing = sorted(required - names)
    if missing:
        raise ValueError(f"cover table is missing columns: {missing}")
    if point_count <= 0:
        raise ValueError("point_count must be positive")

    mask_indices = np.asarray(table["mask_index"], dtype=float)
    epsilons = np.asarray(table["epsilon"], dtype=float)
    counts = np.asarray(table["cover_count"], dtype=float)
    log_counts = np.asarray(table["log_cover_count"], dtype=float)
    if not all(
        np.all(np.isfinite(values))
        for values in (mask_indices, epsilons, counts, log_counts)
    ):
        raise ValueError("mask, scale, and cover-count columns must be finite")
    if np.any(mask_indices != np.floor(mask_indices)):
        raise ValueError("mask indices must be integers")
    if np.any(counts != np.floor(counts)):
        raise ValueError("cover counts must be integers")
    if np.any((counts < 1) | (counts > point_count)):
        raise ValueError("cover counts must lie between one and point_count")
    if not np.allclose(log_counts, np.log(counts), rtol=1.0e-12, atol=1.0e-12):
        raise ValueError("log_cover_count must equal log(cover_count)")

    all_masks = set(mask_indices.astype(np.int64).tolist())
    for epsilon in np.unique(epsilons):
        scale_masks = mask_indices[epsilons == epsilon].astype(np.int64)
        if np.unique(scale_masks).size != scale_masks.size:
            raise ValueError(f"duplicate mask at epsilon={epsilon}")
        missing_masks = sorted(all_masks - set(scale_masks.tolist()))
        if missing_masks:
            raise ValueError(
                f"epsilon={epsilon} is missing masks present at other scales: "
                f"{missing_masks}"
            )

    records: list[dict[str, object]] = []
    for epsilon in np.unique(epsilons):
        selected = table[epsilons == epsilon]
        counts = np.asarray(selected["cover_count"], dtype=float)
        median_count = float(np.median(counts))
        saturated = int(np.count_nonzero(counts == point_count))
        records.append(
            {
                "epsilon": float(epsilon),
                "mask_count": int(selected.size),
                "point_count": int(point_count),
                "median_cover_count": median_count,
                "saturated_mask_count": saturated,
                "saturated_mask_fraction": saturated / int(selected.size),
                "usable_scale": int(
                    0.1 * point_count < median_count < 0.9 * point_count
                ),
                "full_spectrum_spearman": spearman(
                    selected["full_spectrum_log_predictor"],
                    selected["log_cover_count"],
                ),
                "sigma_min_only_spearman": spearman(
                    selected["sigma_min_only_log_predictor"],
                    selected["log_cover_count"],
                ),
            }
        )
    return records


def summarize(records: list[dict[str, object]]) -> dict[str, object]:
    """Summarize the declared usable scales without hiding saturation."""

    usable = [record for record in records if int(record["usable_scale"]) == 1]
    if not usable:
        raise ValueError("no scale satisfies the usable-scale criterion")
    return {
        "scale_count": len(records),
        "usable_scale_count": len(usable),
        "usable_criterion": "0.1*n < median_cover_count < 0.9*n",
        "mean_usable_full_spectrum_spearman": float(
            np.mean([float(record["full_spectrum_spearman"]) for record in usable])
        ),
        "mean_usable_sigma_min_only_spearman": float(
            np.mean([float(record["sigma_min_only_spearman"]) for record in usable])
        ),
        "interpretation": (
            "Finite-cloud diagnostic only; fine-scale saturation and shared "
            "linear-spectrum construction remain visible in the per-scale table."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY)
    parser.add_argument("--point-count", type=int, default=360)
    args = parser.parse_args()

    table = np.atleast_1d(
        np.genfromtxt(args.input, delimiter=",", names=True, encoding="utf-8")
    )
    records = analyze(table, point_count=args.point_count)
    summary = summarize(records)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(records[0]), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(records)
    args.summary.write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
