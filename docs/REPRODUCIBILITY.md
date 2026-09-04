# Reproducibility

This repository supports two forms of verification: self-contained software
and analytic checks, and regeneration of public figures and tables from
committed sanitized numerical results. The complete finite-element EIT
simulation is not included because its source dataset and generator are not
distributed in this release.

## Software requirements

The Python package requires Python 3.11 or later. The public release was
validated with the following environment:

| Component | Version |
|---|---:|
| Python | 3.12.13 |
| NumPy | 2.2.6 |
| Matplotlib | 3.10.3 |
| pytest | 8.4.1 |
| latexmk | 4.83 |
| pdfTeX | 3.141592653-2.6-1.40.25 |
| TeX distribution | TeX Live 2023/Debian |

The package metadata specifies supported dependency ranges. The exact table
above records the environment used for release validation, and
[`requirements-release.txt`](../requirements-release.txt) records the complete
Python dependency snapshot used for byte-level figure verification. Other
versions within the declared ranges may also work, but generated PDF bytes can
differ across Matplotlib or font-library versions even when their scientific
content is unchanged.

## Installation

From the repository root:

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e ".[test,figures]"
```

For the reference release environment, install the pinned Python dependencies
instead:

```bash
python -m pip install -r requirements-release.txt
python -m pip install --no-deps -e .
```

On Windows, activate the virtual environment with the platform-appropriate
command before installing the package.

## Correctness tests

Run the full test suite with:

```bash
python -m pytest -q
```

The tests cover the pseudoinverse derivative, derivative bounds, horizontal
transport, scaled projections, critical rank collapse, and the full-spectrum
covering expression. Mathematical regression tests also record two necessary
cautions:

- a derivative bound on disconnected components is not a global Lipschitz
  bound between those components; and
- ambient submersion alone does not exclude a non-neat, boundary-tangent
  level set.

Passing these tests checks implementations and representative identities. It
does not prove the manuscript's analytic theorems or verify Assumption Q for
the complete EIT parameter class.

## Deterministic analytic examples

Run:

```bash
python experiments/run_toy_validation.py
```

The script writes no files. It reports:

- the exact horizontal velocity for a scaled linear projection;
- the observation residual after Runge--Kutta transport on a parabolic level
  set;
- growth of the horizontal-lift norm near a critical point; and
- a representative full-spectrum logarithmic covering bound.

The script is deterministic and uses no random seed.

## Public numerical results

The directory [`experiments/results/`](../experiments/results/) contains
sanitized outputs from the completed EIT mechanism studies. The public files
contain scientific parameters, metrics, numeric point clouds, and plots; they
do not contain raw experiment-tracking databases or machine-specific artifact
locations.

The principal study used seed `20260904`. Its main parameters were:

| Parameter | Value |
|---|---:|
| Base polygons | 10 |
| Replication points per fiber | 24 |
| Independent full-space starts | 96 |
| Fiber radius | 0.008 |
| Central-difference step | 0.002 |
| Relative numerical-rank threshold | 0.001 |
| Candidate masks | 800 |
| Cover repetitions | 8 |

The earlier direct-fiber and whitening studies use their own parameter files
within the corresponding result directories.

## Regenerating figures and tables

Regenerate the public validation figure and derived tabular summaries from the
committed results with:

```bash
python experiments/plot_spectral_validation.py
```

The script reads only `experiments/results/` and regenerates
`experiments/results/spectral_validation/conditional_geometry_validation.pdf`.
It does not rerun the EIT forward solver. Additional outputs are documented in
[`experiments/README.md`](../experiments/README.md).

To verify the integrity of the committed result files, run:

```bash
cd experiments/results
sha256sum -c SHA256SUMS
```

The checksum of the generated PDF corresponds to the pinned release
environment above. With other supported plotting-library versions, compare the
displayed values and layout rather than expecting byte-identical PDF output.

If `sha256sum` is unavailable, compare the listed SHA-256 values with a local
platform-equivalent utility.

## Building the manuscript

From the repository root, run:

```bash
cd manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The expected output is `manuscript/main.pdf`. The source bibliography is
`manuscript/references.bib`. A successful build should contain resolved
citations and cross-references.

## What is and is not reproducible from this release

The following are self-contained:

- the Python test suite;
- the deterministic analytic examples;
- the mathematical regression cases;
- the figure and table summaries derived from committed sanitized results;
- integrity verification of the committed numerical files; and
- compilation of the manuscript.

The following are not presently self-contained:

- generation of the complete synthetic EIT forward dataset;
- a full finite-element rerun of the mechanism experiments; and
- reproduction of historical experiment-tracking records.

The numerical archive should therefore be interpreted as a documented result
set supporting inspection and summary regeneration, not as a complete
end-to-end FEM workflow.

## Interpretation limits

- Finite-difference rank is a thresholded numerical diagnostic.
- A frozen-Jacobian corrector does not prove a continuum fiber theorem.
- PCA dimension on a finite cloud is an estimator, even when calibrated on
  known-dimensional samples.
- The thresholded rank-\(8\) experiment found an isolated local solution; it
  did not estimate a zero-dimensional PCA cloud or establish global
  uniqueness.
- The mesh comparison covers three discretizations and does not establish a
  continuum FEM convergence rate.
- The numerical results do not verify boundary submersion or bidirectional
  no-exit over the complete polygon population.
