# Conditional Fiber Geometry for Incomplete Inverse Data

This repository studies the geometry of conditional data distributions induced
by incomplete observations of finite-dimensional parameterized inverse
problems. The mathematical results identify ambient regular-level-set
dimension and fiber covering complexity, quantify finite-resolution
uncertainty through the singular spectrum of the observation Jacobian, and
establish conditional-measure stability under explicit transport assumptions.
Numerical electrical impedance tomography (EIT) experiments examine these
mechanisms in a representative discretized setting.

The accompanying paper is available as a
[compiled PDF](manuscript/main.pdf) with its
[LaTeX source](manuscript/main.tex).

## Overview

Let \(V\) be a parameter in a compact subset of \(\mathbb R^d\), let
\(F(V)\in\mathbb R^D\) denote the complete data, and let \(H=P_mF\) be the
observation map associated with a mask \(m\). For an observed value \(z\), the
parameter fiber is

\[
S_{m,z}=E\cap (P_mF)^{-1}(z).
\]

If \(D(P_mF)\) has constant rank \(r\) near a compact fiber, the surrounding
regular level set has dimension \(d-r\). Consequently, the image of the fiber
under the complete-data map has covering-number exponent at most \(d-r\).
This refines a global ambient-dimensional entropy description by using the
geometry of the observed fiber.

For noisy observations, rank alone is insufficient. The local uncertainty in
the measured directions depends on all nonzero singular values of the
observation Jacobian. With anisotropic observation noise, the relevant
spectrum is that of the whitened Jacobian \(\Gamma^{-1/2}DH\).

## Main results

The manuscript proves the following results under the assumptions stated
therein:

1. Regular exact-observation level sets have dimension \(d-r\), and compact
   conditional image supports have covering upper exponent at most \(d-r\).
2. Linear noisy tubes admit a product covering bound that retains every
   nonzero singular value. An explicit quantitative implicit-graph argument
   gives a corresponding local nonlinear bound.
3. The minimum-norm pseudoinverse flow transports nearby fibers with explicit
   displacement, derivative, and fiber-volume distortion estimates.
4. Under boundary submersion, bidirectional no-exit, and density regularity,
   the conditional parameter laws and their complete-data pushforwards vary
   quantitatively in Wasserstein distance.
5. Gaussian convolution converts conditional-law Wasserstein control into
   explicit \(L^1\) bounds for smoothed densities and their gradients.

The detailed status and evidentiary basis of each statement are summarized in
[Claims and evidence](docs/CLAIMS_AND_EVIDENCE.md).

## Mathematical scope

The abstract results require regularity assumptions that are not asserted for
the full EIT polygon class. In particular, the whole-family transport theory
uses:

- full row rank on a common regular observation region;
- transversality of the observation map to the parameter-space boundary;
- a bidirectional no-exit condition for the horizontal flow;
- positive regularity bounds for the parameter density; and
- additional injectivity and tangent noncollapse assumptions when embedded
  image manifolds are considered.

The covering statements are upper bounds. They do not imply that the image
fiber has dimension exactly \(d-r\), because the complete-data map may collapse
tangent directions. Numerical thresholded rank is likewise not identified
with exact differential rank. See [Mathematical scope](docs/MATHEMATICAL_SCOPE.md)
for the full interpretation.

## Relation to conditional diffusion models

The fiber entropy bound can replace the global parameter dimension in the
entropy step of a conditional diffusion argument. The manuscript states this
only as a pointwise conditional corollary of Assumptions 1--3 and Theorem 2 of
Liang--Huang--Chen, arXiv:2501.12982v2. The external theorem's score-error and
distributional hypotheses remain required, and the constants may depend on
the fixed regular mask-observation pair.

The repository therefore does not establish a uniform conditional DDPM
theorem, observation-averaged convergence, conditional-score regularity, or a
new finite-sample diffusion rate.

## Numerical experiments

The EIT study is designed to examine individual geometric predictions rather
than to serve as proof of the analytic statements. Its principal findings are:

- independent local fiber recovery produced PCA dimensions \(6\), \(4\), and
  \(2\) for thresholded ranks \(2\), \(4\), and \(6\), respectively;
- for thresholded rank \(8\), nearby constrained searches returned to an
  isolated local solution; no PCA dimension was assigned to this case;
- re-differentiation along sampled fibers retained the expected thresholded
  rank at all accepted points;
- singular-direction widths followed the predicted \(\delta/\sigma_i\)
  scaling;
- a full-spectrum covering predictor was more informative than a surrogate
  based only on the smallest singular value; and
- whitening improved prediction under anisotropic observation noise.

Committed sanitized tables and figures are located in
[`experiments/results/`](experiments/results/). The limitations of these
experiments, including finite-difference rank, finite-cloud PCA, and mesh
sensitivity, are stated in the manuscript and the reproducibility guide.

## Repository structure

```text
.
├── manuscript/                 LaTeX source, bibliography, and compiled paper
├── src/                        numerical implementations of selected formulas
├── tests/                      unit and mathematical regression tests
├── experiments/                deterministic examples and figure generation
│   └── results/                sanitized numerical results
├── docs/                       scope, claims, revisions, and reproducibility
├── requirements-release.txt   pinned Python release environment
├── CITATION.cff                citation metadata
├── LICENSE                     software license
├── LICENSES/                   license allocation and CC BY 4.0 notice
└── THIRD_PARTY_NOTICES.md      attribution and content-license information
```

## Reproducing the results

Python 3.11 or later is required. A minimal local verification is:

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e ".[test,figures]"
python -m pytest -q
python experiments/run_toy_validation.py
python experiments/plot_spectral_validation.py
```

Compile the manuscript with:

```bash
cd manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The committed results permit regeneration of the public summary figure and
reported tables. A complete FEM rerun is not presently self-contained because
the full source dataset and generator are not distributed here. Exact
environment information and expected outputs are given in
[Reproducibility](docs/REPRODUCIBILITY.md).

## Limitations

The following statements are not claimed:

- global boundary transversality or bidirectional no-exit for the complete EIT
  polygon prior;
- exact differential rank from numerical finite differences;
- a continuum FEM convergence theorem from the reported mesh comparison;
- positive uniform reach of all conditional image manifolds;
- conditional-score regularity;
- a uniform or observation-averaged conditional diffusion rate; or
- a complete finite-sample statistical theory.

Open mathematical and computational questions are listed in
[Future work](docs/FUTURE_WORK.md).

## Citation

Citation metadata are provided in [`CITATION.cff`](CITATION.cff). The
manuscript has not been assigned a journal reference or DOI; none is implied by
this repository release.

## License

Original source code is released under the MIT License. Original manuscript
text, research documentation, and figures are made available under
CC BY 4.0. Third-party material is not relicensed and remains subject to its
respective terms. See [`LICENSE`](LICENSE) and
[`LICENSES/README.md`](LICENSES/README.md) for the license allocation, and
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) for attribution details.
