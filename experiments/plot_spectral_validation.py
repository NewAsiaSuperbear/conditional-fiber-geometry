"""Regenerate the four-panel conditional-geometry validation figure.

The script reads only the committed CSV tables in
``results/spectral_validation``.  It does not depend on SciPy or on files from
the parent EIT project.  Matplotlib is an optional project dependency; install
it with ``pip install -e '.[figures]'`` before running this script.
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
DEFAULT_DATA_DIR = HERE / "results" / "spectral_validation"
DEFAULT_OUTPUT = DEFAULT_DATA_DIR / "conditional_geometry_validation.pdf"

# Okabe--Ito colors, paired with distinct markers and line styles so that the
# figure remains interpretable when printed in grayscale.
COLORS = ("#0072B2", "#E69F00", "#009E73", "#D55E00", "#CC79A7", "#56B4E9")
MARKERS = ("o", "s", "^", "D", "v", "P")
LINESTYLES = ("-", "--", "-.", ":", (0, (5, 2)), (0, (3, 1, 1, 1)))


def _read_csv(path: Path) -> np.ndarray:
    """Read a named CSV table and preserve scalar tables as one-row arrays."""

    table = np.genfromtxt(path, delimiter=",", names=True, encoding="utf-8")
    return np.atleast_1d(table)


def _average_ranks(values: np.ndarray) -> np.ndarray:
    """Return one-based average ranks, including deterministic tie handling."""

    values = np.asarray(values, dtype=float)
    order = np.argsort(values, kind="mergesort")
    sorted_values = values[order]
    sorted_ranks = np.empty(values.size, dtype=float)
    start = 0
    while start < values.size:
        stop = start + 1
        while stop < values.size and sorted_values[stop] == sorted_values[start]:
            stop += 1
        sorted_ranks[start:stop] = 0.5 * (start + 1 + stop)
        start = stop
    ranks = np.empty(values.size, dtype=float)
    ranks[order] = sorted_ranks
    return ranks


def _spearman(x: np.ndarray, y: np.ndarray) -> float:
    """Compute Spearman's rank correlation using NumPy only."""

    rx = _average_ranks(x)
    ry = _average_ranks(y)
    rx -= rx.mean()
    ry -= ry.mean()
    denominator = np.linalg.norm(rx) * np.linalg.norm(ry)
    if denominator == 0.0:
        raise ValueError("Spearman correlation is undefined for a constant input")
    return float(np.dot(rx, ry) / denominator)


def _configure_matplotlib() -> None:
    try:
        import matplotlib as mpl
    except ImportError as exc:  # pragma: no cover - depends on optional package
        raise SystemExit(
            "Matplotlib is required for this figure. "
            "Install it with: pip install -e '.[figures]'"
        ) from exc

    mpl.rcParams.update(
        {
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
            "font.family": "sans-serif",
            "font.sans-serif": ["DejaVu Sans"],
            "font.size": 9,
            "axes.titlesize": 10,
            "axes.labelsize": 9,
            "legend.fontsize": 8,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
            "axes.linewidth": 0.8,
            "lines.linewidth": 1.5,
            "lines.markersize": 5,
            "figure.dpi": 150,
            "savefig.bbox": "tight",
        }
    )


def make_figure(data_dir: Path, output: Path) -> None:
    """Build the validation figure from the four public CSV tables."""

    _configure_matplotlib()
    import matplotlib.pyplot as plt

    replicated = _read_csv(data_dir / "replicated_fibers.csv")
    calibration = _read_csv(data_dir / "cover_calibration.csv")
    tube = _read_csv(data_dir / "full_spectrum_tube.csv")
    covering = _read_csv(data_dir / "linear_spectral_cover.csv")

    figure, axes = plt.subplots(2, 2, figsize=(10.4, 7.6), constrained_layout=True)
    ax_dimension, ax_calibration, ax_tube, ax_cover = axes.flat

    # (a) Independent continuation from ten held-out polygons.
    ranks = np.unique(replicated["rank"]).astype(int)
    expected_x = np.linspace(float(ranks.min()), float(ranks.max()), 100)
    ax_dimension.plot(
        expected_x,
        8.0 - expected_x,
        color="black",
        linestyle="--",
        label=r"prediction $d-r$",
        zorder=1,
    )
    for index, rank in enumerate(ranks):
        selected = replicated[replicated["rank"] == rank]
        observed = selected["parameter_pca_dimension"]
        ax_dimension.scatter(
            np.full(observed.size, rank),
            observed,
            color=COLORS[index],
            edgecolor="black",
            linewidth=0.35,
            marker=MARKERS[index],
            alpha=0.75,
            label=fr"rank {rank} ($n={observed.size}$)",
            zorder=2,
        )
    ax_dimension.set(
        title="(a) Fiber dimension across held-out polygons",
        xlabel=r"numerical rank $r$",
        ylabel="estimated parameter-space dimension",
        xticks=ranks,
        yticks=np.arange(2, 7),
    )
    ax_dimension.legend(loc="upper right", frameon=False)

    # (b) Bias calibration of the finite-cloud covering estimator.
    for index, dimension in enumerate(
        np.unique(calibration["true_dimension"]).astype(int)
    ):
        selected = calibration[calibration["true_dimension"] == dimension]
        order = np.argsort(selected["point_count"])
        selected = selected[order]
        ax_calibration.errorbar(
            selected["point_count"],
            selected["mean_estimated_slope"],
            yerr=selected["standard_deviation"],
            color=COLORS[index],
            marker=MARKERS[index],
            linestyle=LINESTYLES[index],
            capsize=2.5,
            label=fr"dimension {dimension}",
        )
        ax_calibration.axhline(
            dimension,
            color=COLORS[index],
            linestyle=":",
            linewidth=0.8,
            alpha=0.55,
        )
    ax_calibration.set_xscale("log")
    ax_calibration.set(
        title="(b) Finite-cloud covering calibration",
        xlabel="point count",
        ylabel="estimated log--log slope",
    )
    ax_calibration.legend(loc="upper left", frameon=False, ncols=1)

    # (c) The plotted quantity is explicitly the deviation from the unit
    # linearized prediction.  This avoids the visually opaque +1 axis offset.
    singular_indices = np.unique(tube["singular_index"]).astype(int)
    for index, singular_index in enumerate(singular_indices):
        selected = tube[tube["singular_index"] == singular_index]
        deltas = np.unique(selected["delta"])
        means = []
        half_ranges = []
        for delta in deltas:
            ratios = selected[selected["delta"] == delta][
                "sigma_i_width_over_delta"
            ]
            deviations = ratios - 1.0
            means.append(float(deviations.mean()))
            half_ranges.append(float(0.5 * (deviations.max() - deviations.min())))
        ax_tube.errorbar(
            deltas,
            means,
            yerr=half_ranges,
            color=COLORS[index],
            marker=MARKERS[index],
            linestyle=LINESTYLES[index],
            capsize=2,
            label=fr"$\sigma_{{{singular_index}}}$",
        )
    ax_tube.axhline(0.0, color="black", linestyle="--", linewidth=1.0)
    ax_tube.set_xscale("log")
    ax_tube.ticklabel_format(axis="y", style="sci", scilimits=(-3, -3), useOffset=False)
    ax_tube.set(
        title="(c) Full-spectrum nonlinear tube widths",
        xlabel=r"observation-space radius $\delta$",
        ylabel=r"deviation $\sigma_i w_i/\delta-1$",
    )
    ax_tube.legend(loc="best", frameon=False, ncols=2)

    # (d) Correlations are recomputed directly, without SciPy, across masks at
    # each resolution.  Average ranks handle tied empirical cover counts.
    epsilons = np.unique(covering["epsilon"])
    full_correlations = []
    minimum_correlations = []
    for epsilon in epsilons:
        selected = covering[covering["epsilon"] == epsilon]
        target = selected["log_cover_count"]
        full_correlations.append(
            _spearman(selected["full_spectrum_log_predictor"], target)
        )
        minimum_correlations.append(
            _spearman(selected["sigma_min_only_log_predictor"], target)
        )
    ax_cover.plot(
        epsilons,
        full_correlations,
        color=COLORS[0],
        marker=MARKERS[0],
        linestyle=LINESTYLES[0],
        label="full spectrum",
    )
    ax_cover.plot(
        epsilons,
        minimum_correlations,
        color=COLORS[1],
        marker=MARKERS[1],
        linestyle=LINESTYLES[1],
        label=r"$\sigma_{\min}$ only",
    )
    ax_cover.set_xscale("log")
    ax_cover.set_ylim(0.58, 1.005)
    ax_cover.set(
        title="(d) Linear spectral covering predictor",
        xlabel=r"covering scale $\varepsilon$",
        ylabel="Spearman correlation with cover count",
    )
    ax_cover.legend(loc="lower right", frameon=False)

    for axis in axes.flat:
        axis.grid(True, color="#B8B8B8", linewidth=0.55, alpha=0.45)
        axis.set_axisbelow(True)

    output.parent.mkdir(parents=True, exist_ok=True)
    metadata = {
        "Title": "Conditional Geometry Validation",
        "Author": "Weiyan Wu",
        "Subject": "Numerical validation of conditional-fiber geometry",
        "Keywords": "inverse problems, conditional fibers, covering numbers",
        "Creator": "plot_spectral_validation.py",
        "Producer": "Matplotlib",
        "CreationDate": None,
        "ModDate": None,
    }
    figure.savefig(output, format="pdf", metadata=metadata)
    plt.close(figure)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--data-dir",
        type=Path,
        default=DEFAULT_DATA_DIR,
        help="directory containing the four committed CSV input tables",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="output PDF path",
    )
    arguments = parser.parse_args()
    make_figure(arguments.data_dir, arguments.output)
    resolved_output = arguments.output.resolve()
    try:
        displayed_output = resolved_output.relative_to(HERE.parent)
    except ValueError:
        displayed_output = resolved_output
    print(displayed_output.as_posix())


if __name__ == "__main__":
    main()
