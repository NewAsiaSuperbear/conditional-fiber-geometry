from __future__ import annotations

import numpy as np
import pytest

from conditional_fiber_geometry.transport import (
    full_row_rank_right_inverse,
    horizontal_velocity,
    integrate_horizontal_transport_rk4,
    right_inverse_directional_derivative,
)


def test_right_inverse_and_scaled_projection_motion_are_exact() -> None:
    scale = 0.23
    jacobian = np.array([[scale, 0.0]])
    inverse = full_row_rank_right_inverse(jacobian)
    direction = np.array([0.017])
    velocity = horizontal_velocity(jacobian, direction)
    assert jacobian @ inverse == pytest.approx(np.eye(1), abs=1.0e-14)
    assert velocity == pytest.approx(np.array([direction[0] / scale, 0.0]))
    assert np.linalg.norm(velocity) == pytest.approx(abs(direction[0]) / scale)


def test_right_inverse_directional_derivative_matches_central_difference() -> None:
    rng = np.random.default_rng(20260904)
    matrix = rng.normal(size=(3, 6))
    direction = rng.normal(size=matrix.shape)
    analytic = right_inverse_directional_derivative(matrix, direction)
    step = 1.0e-6
    numerical = (
        full_row_rank_right_inverse(matrix + step * direction)
        - full_row_rank_right_inverse(matrix - step * direction)
    ) / (2.0 * step)
    assert np.allclose(analytic, numerical, rtol=2.0e-8, atol=2.0e-9)


def test_pseudoinverse_derivative_obeys_two_over_sigma_squared_bound() -> None:
    rng = np.random.default_rng(19)
    matrix = rng.normal(size=(4, 7))
    direction = rng.normal(size=matrix.shape)
    derivative = right_inverse_directional_derivative(matrix, direction)
    sigma_min = np.linalg.svd(matrix, compute_uv=False)[-1]
    upper = 2.0 * np.linalg.norm(direction, ord=2) / sigma_min**2
    assert np.linalg.norm(derivative, ord=2) <= upper * (1.0 + 1.0e-12)


def test_parabola_horizontal_velocity_lifts_observation_exactly() -> None:
    point = np.array([0.2, -0.4])
    jacobian = np.array([[1.0, 2.0 * point[1]]])
    observation_direction = np.array([0.31])
    velocity = horizontal_velocity(jacobian, observation_direction)
    assert jacobian @ velocity == pytest.approx(observation_direction, abs=1.0e-14)
    expected = observation_direction[0] * jacobian[0] / np.dot(jacobian[0], jacobian[0])
    assert velocity == pytest.approx(expected)


def test_critical_model_lift_norm_diverges_at_rank_collapse() -> None:
    observation_direction = np.array([1.0])
    norms = []
    for x in (0.2, 0.1, 0.05):
        jacobian = np.array([[2.0 * x, 0.0]])
        norms.append(np.linalg.norm(horizontal_velocity(jacobian, observation_direction)))
    assert norms == pytest.approx([2.5, 5.0, 10.0])
    with pytest.raises(ValueError, match="not numerically full row rank"):
        horizontal_velocity(np.zeros((1, 2)), observation_direction)


def test_rk4_transport_tracks_nonlinear_parabola_observation_path() -> None:
    initial = np.array([0.2, -0.4])
    displacement = np.array([0.31])

    def observation(point: np.ndarray) -> float:
        return float(point[0] + point[1] ** 2)

    def jacobian(point: np.ndarray) -> np.ndarray:
        return np.array([[1.0, 2.0 * point[1]]])

    transported = integrate_horizontal_transport_rk4(
        jacobian, initial, displacement, steps=64
    )
    assert observation(transported) == pytest.approx(
        observation(initial) + displacement[0], abs=2.0e-12
    )


def test_rk4_transport_validates_input_shapes_and_steps() -> None:
    jacobian = lambda point: np.array([[1.0, 0.0]])
    with pytest.raises(ValueError, match="steps must be positive"):
        integrate_horizontal_transport_rk4(
            jacobian, np.zeros(2), np.ones(1), steps=0
        )
    with pytest.raises(ValueError, match="incompatible matrix"):
        integrate_horizontal_transport_rk4(
            lambda point: np.eye(3), np.zeros(2), np.ones(3), steps=1
        )
