from __future__ import annotations

import importlib.util
from pathlib import Path


def _load_script_module():
    script = Path(__file__).parents[1] / "experiments" / "curate_acceptance_summary.py"
    spec = importlib.util.spec_from_file_location("curate_acceptance_summary", script)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _record(attempts: int, accepted: int) -> dict[str, object]:
    return {
        "independent_full_start": {
            "attempts": attempts,
            "accepted_excluding_base": accepted,
            "acceptance_fraction": accepted / attempts,
            "maximum_constraint_residual": 2.0e-8,
        },
        "rank_along_independent_cloud": {
            "points_checked": accepted + 1,
            "minimum_sigma_r": 0.4,
            "minimum_relative_sigma_r": 0.2,
            "all_thresholded_ranks_equal_expected": True,
        },
    }


def test_row_keeps_attempts_separate_from_base_point() -> None:
    module = _load_script_module()
    record = _record(attempts=12, accepted=9)
    row = module._row(
        cohort="test",
        test_index=3,
        stratum="interior",
        rank=4,
        base_margin_score=0.3,
        base_boundary_margin=0.2,
        cloud=record["independent_full_start"],
        rank_diagnostic=record["rank_along_independent_cloud"],
    )

    assert row["attempts"] == 12
    assert row["accepted_excluding_base"] == 9
    assert row["base_margin_score"] == 0.3
    assert row["base_boundary_margin"] == 0.2
    assert row["redifferentiated_points_including_base"] == 10
    assert row["minimum_sigma_r_over_redifferentiated_points"] == 0.4
    assert row["minimum_relative_sigma_r_over_redifferentiated_points"] == 0.2
    assert row["all_redifferentiated_thresholded_ranks_stable"] == 1
