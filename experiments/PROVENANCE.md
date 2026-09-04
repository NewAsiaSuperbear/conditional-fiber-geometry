# Experiment provenance

## Scope

The committed artifacts support the numerical statements in the manuscript.
They record finite-dimensional mechanism studies; they do not establish exact
differential rank, continuum finite-element convergence, global no-exit, or a
uniform conditional diffusion result.

No participant data or other personal data are present. The NPZ files contain
numeric arrays only. The repository does not contain raw MLflow storage,
external solver source code, external meshes, or the complete synthetic
forward dataset.

## Result sets

### Direct fiber mechanisms

Path: `results/fiber_mechanisms_seed20260903/`

- Random seed: `20260903`.
- Population: a project-generated synthetic quadrilateral DtN population.
- Principal settings: parameter dimension 8, contrast 4, central-difference
  step 0.002, relative numerical-rank threshold 0.001, 1,200 candidate masks,
  192 continuation points plus the base point, and fiber radius 0.012.
- Contents: centered finite-difference sweeps, continuation diagnostics,
  parameter/data fiber clouds, nonlinear weakest-direction widths, and a
  public summary of projection, Gaussian-MMSE, whitening, and CEM-interface
  checks.
- Limitation: the complete population dataset is not redistributed. Its
  recorded SHA-256 digest is
  `8cad9f2063f25ac214b3cc93c75f7f9c69558741b064e14e4b8aec6be9ca4eed`.

### Full-spectrum validation

Path: `results/spectral_validation/`

- Random seed: `20260904`.
- Population: the same class of project-generated synthetic quadrilateral DtN
  data.
- Principal settings: 10 held-out base polygons, 24 replication points per
  fiber, 96 independent full-space starts, fiber radius 0.008,
  central-difference step 0.002, relative numerical-rank threshold 0.001, 800
  candidate masks, and 8 covering repetitions.
- Contents: independent fiber clouds, replicated-fiber summaries,
  rank-along-fiber differentiation, all-singular-direction tube widths,
  finite-cloud calibration, linear spectral-cover comparisons, and a
  three-level mesh-sensitivity table.
- Tracking record: MLflow experiment `eit-dtn-fiber-mechanism`, run
  `370ba88fbcb14071a62e0d528895ac3f`, status `FINISHED`. The committed
  `tracked_metrics.json` is a path-free metric export; the raw tracking store
  is intentionally excluded.
- Provenance limitation: Git metadata was unavailable to the original run.
  The recorded source-tree SHA-256 is
  `e372610629c6339f1cef0310a1561a24726100704f34acafde9de6df886c21ba`.

### Whitened mask design

Path: `results/whitened_mask_design_seed20260902/`

- Random seed: `20260902`.
- Design population: 64 training and 64 test Jacobians from the synthetic
  experiment, with 1,000 candidate masks and 200 trials per Jacobian.
- Contents: boolean channel selections for whitened, unweighted, and random
  designs, together with aggregate errors.
- Limitation: this is a finite simulated design comparison, not an optimality
  theorem for physical electrode configurations.

## KTC2023-derived CEM diagnostic

The file
`results/fiber_mechanisms_seed20260903/cem_derivative_sweep.csv` and the
corresponding scalar fields in that result set's `summary.json` are derived
diagnostics from a smooth four-parameter conductivity chart evaluated through
the Kuopio Tomography Challenge 2023 reference complete-electrode-model (CEM)
implementation. The reference record is
[Zenodo 10986692](https://doi.org/10.5281/zenodo.10986692), distributed by its
authors under CC BY 4.0.

The CSV reports original finite-difference and Taylor-residual calculations.
It does not reproduce KTC source code, meshes, voltage data, or figures. Those
upstream materials are not redistributed or relicensed here, and the KTC
authors do not endorse this repository. The diagnostic checks consistency of
one implemented smooth coefficient chart; it does not establish shape
differentiability for moving polygonal interfaces.

No other committed result file contains KTC2023 measurements. In particular,
the fiber clouds and spectral-cover tables use the project-generated synthetic
quadrilateral DtN population.

## Exact run outputs and public-release curation

The scientific values in the following files are retained from completed
runs, apart from the curation described below. CSV line endings were normalized
from CRLF to LF, and redundant terminal blank lines were removed from three
JSON metadata files, for a platform-neutral public release. No fields or
values were changed by these formatting operations.

- all CSV tables, with the line-ending normalization just described;
- all NPZ numeric arrays;
- each `parameters.json` file;
- `results/spectral_validation/tracked_metrics.json`; and
- the files in `results/whitened_mask_design_seed20260902/`.

The two `summary.json` files are curated public summaries. Their scientific
numeric fields are unchanged; internal study labels were replaced by neutral
descriptions and a non-scientific internal tracking label was omitted. The
integrity manifest was regenerated after this curation.

Earlier presentation plots were removed because they duplicated the
manuscript figure and their generating programs were not part of this public
release. The sole committed experiment figure,
`results/spectral_validation/conditional_geometry_validation.pdf`, is rebuilt
from these four unchanged CSV inputs:

1. `replicated_fibers.csv`;
2. `cover_calibration.csv`;
3. `full_spectrum_tube.csv`; and
4. `linear_spectral_cover.csv`.

It is generated by `plot_spectral_validation.py`; no third-party figure is
copied or adapted.

## Commands

Run the public, self-contained computations from the repository root:

```bash
python -m pip install -e ".[test,figures]"
python -m pytest
python experiments/run_toy_validation.py
python experiments/plot_spectral_validation.py
cd experiments/results
sha256sum -c SHA256SUMS
```

The first three result sets cannot be regenerated end to end from this
repository alone because the full synthetic population and original
experiment-generation programs are not bundled. This limitation is explicit;
the committed summaries should not be presented as an independently rerun
benchmark.

## Interpretation constraints

- Every reported rank is a thresholded numerical rank.
- Finite-cloud PCA and covering slopes are diagnostics, not proofs of manifold
  dimension.
- The mesh table is a sensitivity study over three discretizations, not a
  continuum convergence theorem.
- Local continuation does not verify the manuscript's no-exit and boundary
  hypotheses over the full polygon class.
- The whitening and CEM-interface results support implementation choices; they
  are not claimed as new mathematical results.
