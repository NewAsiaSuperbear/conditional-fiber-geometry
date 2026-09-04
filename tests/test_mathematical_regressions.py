"""Regression examples for assumptions used by the mathematical results.

These tests encode exact counterexamples and analytic consistency checks.  They
guard the software-facing statement of the assumptions; passing them is not a
substitute for a mathematical proof.
"""

from __future__ import annotations

import numpy as np
import pytest

from conditional_fiber_geometry.covering import (
    full_spectrum_linear_tube_log_bound,
)
from conditional_fiber_geometry.transport import (
    horizontal_velocity,
    integrate_horizontal_transport_rk4,
)


def test_componentwise_zero_derivative_does_not_imply_global_lipschitz() -> None:
    """Record the disconnected-domain counterexample to the old W1 argument."""
    # The parameter domain consists of two separated strips.  The data map is
    # constant on a neighborhood of each strip, so its derivative bound on the
    # domain is zero, although the constants on the components differ.
    component_data_values = np.array([0.0, 1.0])
    componentwise_derivative_bound = 0.0
    assert np.ptp(component_data_values) == pytest.approx(1.0)

    # Equal-length sections of the two strips, with densities proportional to
    # 1 + a z and 1 - a z, induce the displayed two-atom conditional law.
    slope = 0.3
    z, z_prime = -0.4, 0.6

    def mass_at_zero(observation: float) -> float:
        return (1.0 + slope * observation) / 2.0

    # For probability measures on {0, 1}, W1 is the difference between their
    # masses at either atom.
    conditional_w1 = abs(mass_at_zero(z) - mass_at_zero(z_prime))
    old_derivative_only_bound = componentwise_derivative_bound * abs(z - z_prime)

    assert conditional_w1 == pytest.approx(slope * abs(z - z_prime) / 2.0)
    assert conditional_w1 > 0.0
    assert old_derivative_only_bound == 0.0


def test_ambient_submersion_does_not_exclude_boundary_tangency() -> None:
    """Record a regular ambient level with a segment and an isolated point."""
    # K is the union of the closed unit disks centered at (0, 0) and (3, 1),
    # and H(x, y) = y.  The level H = 0 cuts the first disk in [-1, 1] x {0}
    # but only touches the second disk at (3, 0).
    ambient_jacobian = np.array([[0.0, 1.0]])
    assert np.linalg.matrix_rank(ambient_jacobian) == 1

    fiber_y = 0.0

    def in_disk(x: float, center: tuple[float, float]) -> bool:
        center_x, center_y = center
        return (x - center_x) ** 2 + (fiber_y - center_y) ** 2 <= 1.0

    for x in np.linspace(-1.0, 1.0, 9):
        assert in_disk(float(x), (0.0, 0.0))

    assert in_disk(3.0, (3.0, 1.0))
    assert not in_disk(3.0 - 1.0e-6, (3.0, 1.0))
    assert not in_disk(3.0 + 1.0e-6, (3.0, 1.0))

    # At the touching point, the boundary tangent is horizontal.  Restricting
    # DH to that tangent has rank zero, so the boundary-submersion condition
    # fails despite full ambient rank.
    boundary_tangent = np.array([1.0, 0.0])
    assert ambient_jacobian @ boundary_tangent == pytest.approx(np.zeros(1))


def test_linear_spectral_tube_has_inverse_singular_value_axes() -> None:
    """Check the exact ellipsoid underlying the full-spectrum tube bound."""
    dimension = 5
    singular_values = np.array([5.0, 2.0, 0.25])
    rank = singular_values.size
    jacobian = np.zeros((rank, dimension))
    jacobian[:, :rank] = np.diag(singular_values)
    delta = 0.04

    # The endpoint on each normal principal axis has residual exactly delta;
    # the remaining d-r coordinates are unconstrained by the linear map.
    for index, singular_value in enumerate(singular_values):
        endpoint = np.zeros(dimension)
        endpoint[index] = delta / singular_value
        assert np.linalg.norm(jacobian @ endpoint) == pytest.approx(delta)

    tangent = np.zeros(dimension)
    tangent[-1] = 0.7
    assert jacobian @ tangent == pytest.approx(np.zeros(rank))

    radius = 0.7
    epsilon = 0.01
    covering_constant = 4.0
    result = full_spectrum_linear_tube_log_bound(
        dimension=dimension,
        radius=radius,
        delta=delta,
        epsilon=epsilon,
        singular_values=singular_values,
        covering_constant=covering_constant,
    )
    expected = (dimension - rank) * np.log1p(
        covering_constant * radius / epsilon
    ) + np.sum(
        np.log1p(
            covering_constant * delta / (singular_values * epsilon)
        )
    )
    assert result["full_spectrum_log_bound"] == pytest.approx(expected)


def test_multirow_horizontal_flow_tracks_the_observation_segment() -> None:
    """Check DH DH^dagger xi = xi and its integrated nonlinear consequence."""
    def observation(point: np.ndarray) -> np.ndarray:
        x, y, z = point
        return np.array([x + y**2, z + 0.5 * x * y])

    def jacobian(point: np.ndarray) -> np.ndarray:
        x, y, _ = point
        return np.array(
            [
                [1.0, 2.0 * y, 0.0],
                [0.5 * y, 0.5 * x, 1.0],
            ]
        )

    initial = np.array([0.2, -0.3, 0.4])
    displacement = np.array([0.07, -0.04])

    for point in (
        initial,
        np.array([-0.1, 0.25, 0.7]),
        np.array([0.6, -0.15, -0.2]),
    ):
        velocity = horizontal_velocity(jacobian(point), displacement)
        assert jacobian(point) @ velocity == pytest.approx(
            displacement, abs=2.0e-15
        )

    transported = integrate_horizontal_transport_rk4(
        jacobian,
        initial,
        displacement,
        steps=128,
    )
    assert observation(transported) == pytest.approx(
        observation(initial) + displacement,
        abs=2.0e-13,
    )
