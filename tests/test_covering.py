from __future__ import annotations

import numpy as np
import pytest

from conditional_fiber_geometry.covering import (
    full_spectrum_linear_tube_log_bound,
    relative_numerical_rank,
)


def test_relative_numerical_rank_is_threshold_explicit() -> None:
    values = np.array([10.0, 0.1, 0.009])
    assert relative_numerical_rank(values, threshold=1.0e-3) == 2
    assert relative_numerical_rank(values, threshold=5.0e-4) == 3


def test_full_spectrum_bound_uses_each_axis_and_is_tighter() -> None:
    spectrum = np.array([4.0, 2.0, 0.25])
    result = full_spectrum_linear_tube_log_bound(
        dimension=6,
        radius=0.8,
        delta=0.03,
        epsilon=0.01,
        singular_values=spectrum,
    )
    expected_normal = np.log1p(4.0 * 0.03 / (spectrum * 0.01))
    assert result["rank"] == 3
    assert result["nullity"] == 3
    assert result["normal_log_factors"] == pytest.approx(expected_normal.tolist())
    assert result["full_spectrum_log_bound"] <= result[
        "weakest_singular_value_log_bound"
    ]


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"dimension": 0}, "dimension must be positive"),
        ({"epsilon": 0.0}, "epsilon positive"),
        ({"singular_values": np.array([1.0, 0.0])}, "strictly positive"),
    ],
)
def test_full_spectrum_bound_rejects_invalid_inputs(
    kwargs: dict[str, object], message: str
) -> None:
    arguments: dict[str, object] = {
        "dimension": 3,
        "radius": 1.0,
        "delta": 0.1,
        "epsilon": 0.01,
        "singular_values": np.array([2.0, 1.0]),
    }
    arguments.update(kwargs)
    with pytest.raises(ValueError, match=message):
        full_spectrum_linear_tube_log_bound(**arguments)
