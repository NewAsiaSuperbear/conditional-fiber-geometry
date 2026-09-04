"""Run deterministic analytic checks for the transport and tube formulas.

This script is a compact reproducibility example, not a new scientific
experiment. It writes no files and does not create an MLflow run.
"""

from __future__ import annotations

import json

import numpy as np

from conditional_fiber_geometry import (
    full_spectrum_linear_tube_log_bound,
    horizontal_velocity,
    integrate_horizontal_transport_rk4,
)


def main() -> None:
    scaled_jacobian = np.array([[0.25, 0.0]])
    scaled_velocity = horizontal_velocity(scaled_jacobian, np.array([0.1]))

    initial = np.array([0.2, -0.4])
    displacement = np.array([0.31])

    def parabola_jacobian(point: np.ndarray) -> np.ndarray:
        return np.array([[1.0, 2.0 * point[1]]])

    transported = integrate_horizontal_transport_rk4(
        parabola_jacobian, initial, displacement, steps=64
    )
    initial_observation = float(initial[0] + initial[1] ** 2)
    final_observation = float(transported[0] + transported[1] ** 2)

    critical_norms = {
        str(x): float(np.linalg.norm(horizontal_velocity(
            np.array([[2.0 * x, 0.0]]), np.array([1.0])
        )))
        for x in (0.2, 0.1, 0.05)
    }

    covering = full_spectrum_linear_tube_log_bound(
        dimension=8,
        radius=0.008,
        delta=0.001,
        epsilon=0.0002,
        singular_values=np.array([1.0, 0.5, 0.2, 0.1, 0.03, 0.005]),
    )

    result = {
        "scaled_projection_velocity": scaled_velocity.tolist(),
        "parabola_observation_residual": final_observation
        - initial_observation
        - displacement[0],
        "critical_lift_norms": critical_norms,
        "covering": covering,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
