"""Computational forms of proved linear spectral covering bounds."""

from __future__ import annotations

import numpy as np


def relative_numerical_rank(
    singular_values: np.ndarray, threshold: float = 1.0e-3
) -> int:
    """Count singular values above a stated relative threshold.

    This diagnostic is not an estimator of exact differential rank.
    """
    values = np.asarray(singular_values, dtype=float)
    if values.ndim != 1:
        raise ValueError("singular_values must be one-dimensional")
    if not 0.0 < threshold < 1.0:
        raise ValueError("threshold must lie in (0, 1)")
    if values.size == 0 or values[0] <= 0.0:
        return 0
    return int(np.count_nonzero(values / values[0] > threshold))


def full_spectrum_linear_tube_log_bound(
    *,
    dimension: int,
    radius: float,
    delta: float,
    epsilon: float,
    singular_values: np.ndarray,
    covering_constant: float = 4.0,
) -> dict[str, object]:
    """Evaluate the full-spectrum product covering bound in logarithmic form."""
    spectrum = np.asarray(singular_values, dtype=float)
    if dimension < 1:
        raise ValueError("dimension must be positive")
    if spectrum.ndim != 1 or spectrum.size > dimension:
        raise ValueError("singular_values must have length at most dimension")
    if np.any(~np.isfinite(spectrum)) or np.any(spectrum <= 0.0):
        raise ValueError("singular_values must be finite and strictly positive")
    if radius < 0.0 or delta < 0.0 or epsilon <= 0.0:
        raise ValueError("radius and delta must be nonnegative and epsilon positive")
    if covering_constant <= 0.0:
        raise ValueError("covering_constant must be positive")

    rank = int(spectrum.size)
    tangent_log_factor = (dimension - rank) * np.log1p(
        covering_constant * radius / epsilon
    )
    normal_log_factors = np.log1p(
        covering_constant * delta / (spectrum * epsilon)
    )
    full_log_bound = float(tangent_log_factor + np.sum(normal_log_factors))
    weakest_log_bound = float(
        tangent_log_factor
        + rank
        * np.log1p(covering_constant * delta / (spectrum[-1] * epsilon))
    )
    return {
        "rank": rank,
        "nullity": dimension - rank,
        "tangent_log_factor": float(tangent_log_factor),
        "normal_log_factors": normal_log_factors.tolist(),
        "full_spectrum_log_bound": full_log_bound,
        "weakest_singular_value_log_bound": weakest_log_bound,
        "full_minus_weakest_log_bound": full_log_bound - weakest_log_bound,
    }
