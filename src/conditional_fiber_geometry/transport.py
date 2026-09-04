"""Numerical primitives for quantitative horizontal fiber transport.

The mathematical transport uses the minimum-norm right inverse of a full-row-
rank observation Jacobian. These helpers expose the exact directional
derivative used in the transport analysis and keep numerical tests independent
of the EIT forward solver.
"""

from __future__ import annotations

from collections.abc import Callable

import numpy as np


def full_row_rank_right_inverse(jacobian: np.ndarray) -> np.ndarray:
    """Return ``B.T @ inv(B @ B.T)`` after verifying full row rank."""
    matrix = np.asarray(jacobian, dtype=float)
    if matrix.ndim != 2:
        raise ValueError("jacobian must be two-dimensional")
    rows, columns = matrix.shape
    if rows < 1 or rows > columns:
        raise ValueError("full-row-rank input requires 1 <= rows <= columns")
    singular = np.linalg.svd(matrix, compute_uv=False)
    tolerance = np.finfo(float).eps * max(matrix.shape) * singular[0]
    if singular[-1] <= tolerance:
        raise ValueError("jacobian is not numerically full row rank")
    gram = matrix @ matrix.T
    return np.linalg.solve(gram, matrix).T


def right_inverse_directional_derivative(
    jacobian: np.ndarray, jacobian_direction: np.ndarray
) -> np.ndarray:
    """Evaluate the exact directional derivative of a full-row-rank inverse.

    For ``A = B^dagger`` and perturbation ``E``, the expression is
    ``-A E A + (I - A B) E.T A.T A``.
    """
    matrix = np.asarray(jacobian, dtype=float)
    direction = np.asarray(jacobian_direction, dtype=float)
    if direction.shape != matrix.shape:
        raise ValueError("jacobian_direction must have the jacobian shape")
    inverse = full_row_rank_right_inverse(matrix)
    projector_complement = np.eye(matrix.shape[1]) - inverse @ matrix
    return (
        -inverse @ direction @ inverse
        + projector_complement @ direction.T @ inverse.T @ inverse
    )


def horizontal_velocity(
    jacobian: np.ndarray, observation_direction: np.ndarray
) -> np.ndarray:
    """Return the minimum-norm velocity lifting an observation direction."""
    direction = np.asarray(observation_direction, dtype=float)
    matrix = np.asarray(jacobian, dtype=float)
    if matrix.ndim != 2:
        raise ValueError("jacobian must be two-dimensional")
    if direction.shape != (matrix.shape[0],):
        raise ValueError("observation_direction has incompatible shape")
    return full_row_rank_right_inverse(matrix) @ direction


def integrate_horizontal_transport_rk4(
    jacobian_fn: Callable[[np.ndarray], np.ndarray],
    initial_point: np.ndarray,
    observation_displacement: np.ndarray,
    *,
    steps: int = 128,
) -> np.ndarray:
    """Integrate the horizontal lift over unit time with classical RK4.

    This helper is not a replacement for the theorem's no-exit hypothesis. The
    caller remains responsible for checking admissibility along the trajectory.
    """
    if steps < 1:
        raise ValueError("steps must be positive")
    point = np.asarray(initial_point, dtype=float).copy()
    displacement = np.asarray(observation_displacement, dtype=float)
    if point.ndim != 1 or displacement.ndim != 1:
        raise ValueError("initial_point and observation_displacement must be vectors")

    def velocity(state: np.ndarray) -> np.ndarray:
        jacobian = np.asarray(jacobian_fn(state), dtype=float)
        if jacobian.ndim != 2 or jacobian.shape[1] != point.size:
            raise ValueError("jacobian_fn returned an incompatible matrix")
        return horizontal_velocity(jacobian, displacement)

    step_size = 1.0 / float(steps)
    for _ in range(steps):
        k1 = velocity(point)
        k2 = velocity(point + 0.5 * step_size * k1)
        k3 = velocity(point + 0.5 * step_size * k2)
        k4 = velocity(point + step_size * k3)
        point += (step_size / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)
    return point
