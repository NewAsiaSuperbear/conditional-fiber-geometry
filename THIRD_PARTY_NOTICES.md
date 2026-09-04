# Third-party notices

This file records third-party material, scholarly dependencies, and software
dependencies relevant to the repository. Nothing here grants rights beyond
those provided by the respective copyright holders and licenses.

## KTC2023 v3 reference solver

The following upstream work was used in one numerical interface study:

- Creators: Mikko Räsänen, Petri Kuusela, Jyrki Jauhiainen, Muhammad Arif,
  Kenneth Scheel, Tuomo Savolainen, and Aku Seppänen.
- Title: *Kuopio Tomography Challenge 2023 open electrical impedance
  tomographic dataset (KTC 2023)*.
- Version: v3.
- DOI: [10.5281/zenodo.10986692](https://doi.org/10.5281/zenodo.10986692).
- License: [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/)
  (CC BY 4.0).

The project's CEM derivative-interface study ran the upstream Python reference
solver from the `Codes_Python.zip` archive in a temporary local
directory. The solver was evaluated on an independently specified
four-dimensional smooth conductivity chart. This project computed central
finite differences, compared them with solver Jacobians, and tabulated the
resulting diagnostics. These operations constitute the changes made for this
use.

The resulting author-generated material appears only in:

- `experiments/results/fiber_mechanisms_seed20260903/cem_derivative_sweep.csv`;
- the `cem_derivative_interface` object in
  `experiments/results/fiber_mechanisms_seed20260903/summary.json`; and
- the corresponding numerical summary in `manuscript/main.tex` and the
  compiled `manuscript/main.pdf`.

No KTC2023 source code, measurement data, ground-truth image, finite-element
mesh, or upstream figure is redistributed in this repository. The remaining
included experiment results were computed from synthetic polygonal inputs and
are not copies of the KTC2023 dataset; the underlying population dataset is
not redistributed. The KTC2023 creators retain all applicable rights in their
materials. Neither they nor the University of Eastern Finland endorse this
repository or its conclusions.

## Scholarly references

The manuscript cites external mathematical and scientific results in the
ordinary scholarly manner. In particular, it version-pins the external EIT
and diffusion results on which its conditional corollary depends. The
repository does not reproduce third-party paper text, tables, or figures;
citations do not place the cited works under this repository's licenses.

## Software dependencies

Dependencies are installed from their upstream distributions and are not
vendored in this repository. The principal direct dependencies are:

| Component | Declared version or pin | Use | Upstream license |
| --- | --- | --- | --- |
| [NumPy](https://numpy.org/) | `>=2.2,<3` | Runtime numerical arrays and linear algebra | [BSD-3-Clause](https://github.com/numpy/numpy/blob/main/LICENSE.txt); binary distributions may carry additional bundled-library notices |
| [pytest](https://pytest.org/) | `>=8.4,<9` | Optional test runner | [MIT](https://github.com/pytest-dev/pytest/blob/main/LICENSE) |
| [Matplotlib](https://matplotlib.org/) | `>=3.8,<4` | Optional figure regeneration | [Matplotlib License (PSF-based)](https://matplotlib.org/stable/project/license.html) |
| [setuptools](https://setuptools.pypa.io/) | `>=69` | PEP 517 build backend | [MIT](https://github.com/pypa/setuptools/blob/main/LICENSE) |
| [wheel](https://wheel.readthedocs.io/) | no lower bound declared | Build-system support | [MIT](https://github.com/pypa/wheel/blob/main/LICENSE.txt) |
| [actions/checkout](https://github.com/actions/checkout) | `11d5960a326750d5838078e36cf38b85af677262` (v4) | Continuous-integration checkout | [MIT](https://github.com/actions/checkout/blob/main/LICENSE) |
| [actions/setup-python](https://github.com/actions/setup-python) | `a26af69be951a213d495a4c3e4e4022e16d87065` (v5) | Continuous-integration Python setup | [MIT](https://github.com/actions/setup-python/blob/main/LICENSE) |

The supported direct dependency ranges are authoritative in
`pyproject.toml`. `requirements-release.txt` records the resolved transitive
dependency versions used for the release reproducibility check; it does not
vendor or relicense those distributions.

The manuscript is built with an external LaTeX distribution and the packages
listed in `manuscript/main.tex`. Those tools and packages are not distributed
by this repository and remain under their package-specific upstream licenses.
Users should consult the package metadata supplied by their TeX distribution.

Installed dependency distributions can contain transitive components and
additional notices. Their own bundled license files are authoritative. The
MIT and CC BY 4.0 grants in this repository do not relicense any dependency.
