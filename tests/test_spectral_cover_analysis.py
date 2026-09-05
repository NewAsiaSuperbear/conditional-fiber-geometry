from __future__ import annotations

import importlib.util
from pathlib import Path

import numpy as np
import pytest


def _load_script_module():
    script = Path(__file__).parents[1] / "experiments" / "analyze_spectral_cover.py"
    spec = importlib.util.spec_from_file_location("analyze_spectral_cover", script)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_per_scale_summary_exposes_saturation_and_usable_rule() -> None:
    module = _load_script_module()
    dtype = [
        ("mask_index", float),
        ("epsilon", float),
        ("cover_count", float),
        ("log_cover_count", float),
        ("full_spectrum_log_predictor", float),
        ("sigma_min_only_log_predictor", float),
    ]
    table = np.array(
        [
            (0, 0.1, 10, np.log(10), 1, 3),
            (1, 0.1, 10, np.log(10), 2, 2),
            (2, 0.1, 8, np.log(8), 3, 1),
            (0, 0.2, 8, np.log(8), 3, 1),
            (1, 0.2, 5, np.log(5), 2, 2),
            (2, 0.2, 2, np.log(2), 1, 3),
        ],
        dtype=dtype,
    )
    records = module.analyze(table, point_count=10)

    assert records[0]["saturated_mask_count"] == 2
    assert records[0]["usable_scale"] == 0
    assert records[1]["saturated_mask_count"] == 0
    assert records[1]["usable_scale"] == 1
    assert records[1]["full_spectrum_spearman"] == pytest.approx(1.0)
    assert records[1]["sigma_min_only_spearman"] == pytest.approx(-1.0)

    summary = module.summarize(records)
    assert summary["scale_count"] == 2
    assert summary["usable_scale_count"] == 1


def _valid_cover_table() -> np.ndarray:
    dtype = [
        ("mask_index", float),
        ("epsilon", float),
        ("cover_count", float),
        ("log_cover_count", float),
        ("full_spectrum_log_predictor", float),
        ("sigma_min_only_log_predictor", float),
    ]
    return np.array(
        [
            (0, 0.1, 8, np.log(8), 3, 1),
            (1, 0.1, 5, np.log(5), 2, 2),
            (2, 0.1, 2, np.log(2), 1, 3),
            (0, 0.2, 7, np.log(7), 3, 1),
            (1, 0.2, 4, np.log(4), 2, 2),
            (2, 0.2, 1, np.log(1), 1, 3),
        ],
        dtype=dtype,
    )


def test_cover_validation_rejects_duplicate_and_missing_masks() -> None:
    module = _load_script_module()

    duplicate = _valid_cover_table()
    duplicate[5]["mask_index"] = 1
    with pytest.raises(ValueError, match="duplicate mask"):
        module.analyze(duplicate, point_count=10)

    missing = _valid_cover_table()[np.arange(6) != 5]
    with pytest.raises(ValueError, match="missing masks"):
        module.analyze(missing, point_count=10)


def test_cover_validation_rejects_fractional_counts_and_inconsistent_logs() -> None:
    module = _load_script_module()

    fractional = _valid_cover_table()
    fractional[0]["cover_count"] = 7.5
    with pytest.raises(ValueError, match="cover counts must be integers"):
        module.analyze(fractional, point_count=10)

    inconsistent_log = _valid_cover_table()
    inconsistent_log[0]["log_cover_count"] += 0.01
    with pytest.raises(ValueError, match=r"log_cover_count must equal log"):
        module.analyze(inconsistent_log, point_count=10)
