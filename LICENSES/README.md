# License allocation

This repository uses licenses assigned by file category. A license applies
only to material for which the copyright holder has authority to grant it.

## Software: MIT

The standard MIT License in the repository-root `LICENSE` file applies to the
original software and software-oriented configuration, including:

- `src/` and `tests/`;
- executable source files under `experiments/`;
- `.github/workflows/`;
- `pyproject.toml`, `requirements-release.txt`, `Makefile`, and `.gitignore`; and
- future original software files that do not carry another license notice.

## Research materials: CC BY 4.0

The author's original manuscript, research documentation, figures, and
numerical result artifacts are licensed under the Creative Commons
Attribution 4.0 International license (CC BY 4.0). This category includes:

- `manuscript/`;
- `docs/`;
- author-owned prose and metadata in the repository root;
- author-owned non-executable documentation under `experiments/`; and
- author-owned numerical results under `experiments/results/`.

The CC BY 4.0 license notice and canonical legal-code link are provided in
`CC-BY-4.0.txt`.

## Third-party material

Third-party material remains governed by its own license and attribution
terms and is not relicensed here. Some reported CEM interface measurements
were derived by running the separately obtained KTC2023 v3 reference solver;
the upstream code, data, and mesh are not included. See
`../THIRD_PARTY_NOTICES.md` for attribution and scope details.
