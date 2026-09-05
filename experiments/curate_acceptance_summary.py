"""Extract path-free continuation acceptance data from the archived run summary.

This one-time curation helper does not rerun the EIT solver.  It retains the
attempt counts and diagnostics that were recorded for accepted clouds while
dropping point clouds, long PCA spectra, and machine-specific source paths.
The original run did not retain rejected points or their singular spectra.
"""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path


def _row(
    *,
    cohort: str,
    test_index: int,
    stratum: str,
    rank: int,
    base_margin_score: float,
    base_boundary_margin: float,
    cloud: dict[str, object],
    rank_diagnostic: dict[str, object],
) -> dict[str, object]:
    return {
        "cohort": cohort,
        "test_index": test_index,
        "stratum": stratum,
        "rank": rank,
        "base_margin_score": base_margin_score,
        "base_boundary_margin": base_boundary_margin,
        "attempts": int(cloud["attempts"]),
        "accepted_excluding_base": int(cloud["accepted_excluding_base"]),
        "acceptance_fraction": float(cloud["acceptance_fraction"]),
        "maximum_accepted_constraint_residual": float(
            cloud["maximum_constraint_residual"]
        ),
        "redifferentiated_points_including_base": int(
            rank_diagnostic["points_checked"]
        ),
        "minimum_sigma_r_over_redifferentiated_points": float(
            rank_diagnostic["minimum_sigma_r"]
        ),
        "minimum_relative_sigma_r_over_redifferentiated_points": float(
            rank_diagnostic["minimum_relative_sigma_r"]
        ),
        "all_redifferentiated_thresholded_ranks_stable": int(
            bool(rank_diagnostic["all_thresholded_ranks_equal_expected"])
        ),
    }


def extract(source: Path) -> list[dict[str, object]]:
    payload = json.loads(source.read_text(encoding="utf-8"))
    rows: list[dict[str, object]] = []
    base_diagnostics = {
        int(base["test_index"]): (
            float(base["margin_score"]),
            float(base["admissibility"]["boundary_margin"]),
        )
        for base in payload["replicated_fibers"]["details"]
    }
    endpoint = payload["rank8_isolated_endpoint"]
    paired_test_index = int(endpoint["test_index"])
    paired_margin_score, paired_boundary_margin = base_diagnostics[
        paired_test_index
    ]

    paired = payload["independent_generator_paired_control"]
    for rank_text in sorted(paired, key=int):
        record = paired[rank_text]
        rows.append(
            _row(
                cohort="paired_full_start_control",
                test_index=paired_test_index,
                stratum="paired_control",
                rank=int(rank_text),
                base_margin_score=paired_margin_score,
                base_boundary_margin=paired_boundary_margin,
                cloud=record["independent_full_start"],
                rank_diagnostic=record["rank_along_independent_cloud"],
            )
        )

    for base in payload["replicated_fibers"]["details"]:
        margin_score, boundary_margin = base_diagnostics[int(base["test_index"])]
        for rank_text in sorted(base["ranks"], key=int):
            record = base["ranks"][rank_text]
            rows.append(
                _row(
                    cohort="stratified_replication",
                    test_index=int(base["test_index"]),
                    stratum=str(base["stratum"]),
                    rank=int(rank_text),
                    base_margin_score=margin_score,
                    base_boundary_margin=boundary_margin,
                    cloud=record["cloud"],
                    rank_diagnostic=record["rank_along_cloud"],
                )
            )

    rows.append(
        _row(
            cohort="rank8_endpoint",
            test_index=int(endpoint["test_index"]),
            stratum="endpoint_control",
            rank=int(endpoint["rank"]),
            base_margin_score=paired_margin_score,
            base_boundary_margin=paired_boundary_margin,
            cloud=endpoint["cloud"],
            rank_diagnostic=endpoint["rank_along_cloud"],
        )
    )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    rows = extract(args.source)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(rows[0]), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)
    print(args.output)


if __name__ == "__main__":
    main()
