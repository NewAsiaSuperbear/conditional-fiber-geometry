from __future__ import annotations

import csv
from pathlib import Path

import pytest


def _load_script_module():
    import importlib.util

    script = Path(__file__).parents[1] / "experiments" / "analyze_image_fiber_rank.py"
    spec = importlib.util.spec_from_file_location("analyze_image_fiber_rank", script)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_image_fiber_rank_summary_preserves_negative_result(tmp_path: Path) -> None:
    module = _load_script_module()
    table = tmp_path / "full_map_spectra.csv"
    fieldnames = [
        "population_seed",
        "sample_index",
        "split",
        "numerical_rank",
        "relative_sigma_8",
        *[f"sigma_{index}" for index in range(1, 9)],
    ]
    with table.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for sample, relative in enumerate((0.02, 0.04, 0.08)):
            spectrum = (1.0, 0.8, 0.6, 0.4, 0.3, 0.2, 0.1, relative)
            writer.writerow(
                {
                    "population_seed": 7,
                    "sample_index": sample,
                    "split": "test",
                    "numerical_rank": 8,
                    "relative_sigma_8": relative,
                    **{
                        f"sigma_{index}": value
                        for index, value in enumerate(spectrum, start=1)
                    },
                }
            )

    result = module.summarize(table, threshold=1.0e-3)
    assert result["sample_count"] == 3
    assert result["numerical_rank_counts"] == {"8": 3}
    assert result["all_numerical_ranks_equal_parameter_dimension"] is True
    assert result["relative_sigma_8"]["median"] == pytest.approx(0.04)
    assert "rather than a stricter exponent" in result["image_fiber_interpretation"]


def test_image_fiber_rank_summary_recomputes_a_changed_threshold(
    tmp_path: Path,
) -> None:
    module = _load_script_module()
    table = tmp_path / "full_map_spectra.csv"
    fieldnames = [
        "population_seed",
        "sample_index",
        "split",
        "numerical_rank",
        "relative_sigma_8",
        *[f"sigma_{index}" for index in range(1, 9)],
    ]
    with table.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for sample, final_value in enumerate((0.02, 0.04, 0.08)):
            spectrum = (1.0, 0.8, 0.6, 0.4, 0.3, 0.2, 0.1, final_value)
            writer.writerow(
                {
                    "population_seed": 7,
                    "sample_index": sample,
                    "split": "test",
                    # This cache belongs to the release threshold, not 0.05.
                    "numerical_rank": 8,
                    "relative_sigma_8": final_value,
                    **{
                        f"sigma_{index}": value
                        for index, value in enumerate(spectrum, start=1)
                    },
                }
            )

    result = module.summarize(table, threshold=0.05)
    assert result["relative_rank_threshold"] == pytest.approx(0.05)
    assert result["numerical_rank_counts"] == {"7": 2, "8": 1}
    assert result["all_numerical_ranks_equal_parameter_dimension"] is False


def test_image_fiber_rank_summary_rejects_zero_leading_singular_value(
    tmp_path: Path,
) -> None:
    module = _load_script_module()
    table = tmp_path / "full_map_spectra.csv"
    fieldnames = [
        "population_seed",
        "sample_index",
        "split",
        "numerical_rank",
        "relative_sigma_8",
        *[f"sigma_{index}" for index in range(1, 9)],
    ]
    with table.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerow(
            {
                "population_seed": 7,
                "sample_index": 0,
                "split": "test",
                "numerical_rank": 0,
                "relative_sigma_8": 0.0,
                **{f"sigma_{index}": 0.0 for index in range(1, 9)},
            }
        )

    with pytest.raises(ValueError, match="zero leading singular value"):
        module.summarize(table, threshold=1.0e-3)


def test_image_fiber_rank_summary_rejects_stale_release_rank_cache(
    tmp_path: Path,
) -> None:
    module = _load_script_module()
    table = tmp_path / "full_map_spectra.csv"
    fieldnames = [
        "population_seed",
        "sample_index",
        "split",
        "numerical_rank",
        "relative_sigma_8",
        *[f"sigma_{index}" for index in range(1, 9)],
    ]
    spectrum = (1.0, 0.8, 0.6, 0.4, 0.3, 0.2, 0.1, 0.02)
    with table.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerow(
            {
                "population_seed": 7,
                "sample_index": 0,
                "split": "test",
                "numerical_rank": 7,
                "relative_sigma_8": 0.02,
                **{
                    f"sigma_{index}": value
                    for index, value in enumerate(spectrum, start=1)
                },
            }
        )

    with pytest.raises(ValueError, match="numerical_rank cache"):
        module.summarize(table, threshold=1.0e-3)


def test_image_fiber_rank_summary_rejects_empty_table(tmp_path: Path) -> None:
    module = _load_script_module()
    table = tmp_path / "full_map_spectra.csv"
    table.write_text(
        "population_seed,sample_index,split,numerical_rank,relative_sigma_8,sigma_8\n",
        encoding="utf-8",
    )
    with pytest.raises(ValueError, match="empty"):
        module.summarize(table, threshold=1.0e-3)
