# Experiment provenance

## Scope

The committed artifacts support the numerical statements in the manuscript.
They record finite-dimensional mechanism studies; they do not establish exact
differential rank, continuum finite-element convergence, global no-exit, or a
uniform conditional diffusion result.

No participant data or other personal data are present. The NPZ files contain
numeric arrays and, in the learned archive, fixed-width Unicode labels and
hashes; none contains an object array or requires pickle. The repository does
not contain raw MLflow storage, external solver source code, external meshes,
or the complete synthetic forward dataset.

The recorded seed `20260901` identifies generation of the fixed synthetic
population used by the principal local studies; it is not a run seed.
Study-level randomness is separately recorded: `20260902` for whitening,
`20260903` for the direct-fiber study, and `20260904` for the replicated
full-spectrum study. Learned-model seeds and post-hoc analysis seeds are listed
in their own sections below. These roles must not be conflated when citing
reproducibility. Because the population generator and full dataset are not
bundled, the release records but cannot independently replay the `20260901`
population-generation step.
The recorded dataset file digest is
`8cad9f2063f25ac214b3cc93c75f7f9c69558741b064e14e4b8aec6be9ca4eed`,
and its path-independent canonical-array digest is
`493c402b224a0e5f2e5f85e22669b2d2feebfabc386fc467d8319192761c0f26`.

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
- The approximately `297.340` error-amplification factor in this result set is
  from the earlier direct-fiber comparison. It is not another estimate of the
  later near-critical result described below.

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
  three-level mesh-sensitivity table. The added
  `continuation_acceptance.csv` records the selection accounting behind the
  rank-along-fiber summary. The added `cover_scale_diagnostics.csv` and
  `cover_scale_summary.json` expose scale-by-scale correlation and
  finite-cloud saturation.
- The archived novelty-refinement source summary used to curate the acceptance
  table has SHA-256 digest
  `801a3a80c742adf9bfee87c5a405b60d8142772793b631d2826898b60d6b5915`.
- Acceptance accounting: 1,104 of 1,208 attempted starts were accepted. With
  34 base points, these give the 1,138 redifferentiated points. All 104
  rejected starts came from one near-boundary polygon. Within the replicated
  cohort alone, the corresponding counts are 720 accepted of 824 attempts and
  750 redifferentiated points after adding 30 bases. Base-polygon margins are
  retained, but rejected candidate points and their singular values and
  admissibility margins were not retained, so `1,138/1,138` is an
  accepted/base-point statement rather than an unconditional rate.
- The approximately `402.677` near-critical error-amplification factor belongs
  to this later study. It and `297.340` come from independent experiments with
  different selected configurations; they are not repeated estimates for one
  mask pair. The trial-level errors behind `402.677` were not archived, so only
  the committed aggregate can be inspected without rerunning the study.
- Cover-scale accounting: of eight scales, four satisfy the pre-existing
  usable-scale rule `0.1*n < median_cover_count < 0.9*n`. Their mean Spearman
  correlations are `0.990371` for the full-spectrum predictor and `0.853856`
  for the smallest-singular-value surrogate. From finest to coarsest, the
  counts of masks saturated at the 360-point cloud size are
  `21, 13, 6, 4, 2, 1, 0, 0` of 48. These derived tables make saturation
  visible but do not remove the shared-spectrum construction of predictor and
  linear cloud.
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

### Complete-data image-rank audit

Path: `results/image_fiber_rank/`

- Source: 360 previously computed complete-data finite-difference Jacobians,
  120 from each of source population seeds `20260828`, `20260829`, and
  `20260830`. The immutable source-archive digests and audit parameters are in
  `parameters.json`.
- Contents: `full_map_spectra.csv` retains all eight singular values for every
  sample; `summary.json` records the rank counts and spectrum summaries.
- Result: all 360 Jacobians have thresholded numerical rank 8 at relative
  threshold `0.001`. On these samples the rank-difference refinement is
  therefore `8 - r` and is not stricter than the existing parameter-fiber
  exponent.
- Scope: this is a post-hoc, path-free analysis of archived numerical
  Jacobians. It does not establish exact rank, constant rank near a fiber, or
  coverage of every component of a conditional fiber.

### Learned conditional completion

Path: `results/learned_completion/`

- Network seeds: `20260911`, `20260912`, and `20260913` for separately trained
  conditional EDM and deterministic U-Net models. Aggregate uncertainty uses
  crossed network-seed/held-out-polygon resampling with analysis seed
  `20261001` and 10,000 bootstrap samples.
- Evaluation design: 400 held-out polygons, one training-selected mask and 20
  equal-budget control masks sampled from the middle 80% of the candidate score
  ordering, four noise levels, 18 EDM sampling steps, and 16 learned
  conditional samples per case. The evaluation/sampling seed was `20260921`.
- Public artifacts: `per_case_metrics.npz` is the path-free numeric archive;
  `summary.json` is regenerated by `analyze_learned_completion.py`; and
  `learned_completion.pdf` is the optional Matplotlib figure generated from
  the same archive.
- Source integrity: the per-case CSV SHA-256 digests for network seeds
  `20260911`, `20260912`, and `20260913` are respectively
  `770b03dca5fe0647ffae6b36eecc70948235cf5c3d77dfdcffc960e5b0f62ec8`,
  `8c52299b2e80efc69e3216d5609553178873bea2fa3e37ff7d39c2efd3b5a6bf`,
  and `7348b9b19faa079de9fbfb54f013806ffeb5bb20d34df1074176ce145ec774dd`.
  The mask-level source digest is
  `d1d8b87c52841729dd2ae4af4ff472d4de6e5c8964f920a2b495525184b1e139`,
  and the frozen mask configuration digest is
  `708dc60624262b27e75725f6ed417a9ec18bc6e391e7d993769a8c6053a4fc39`.
  The first four hashes are also stored inside the pickle-free NPZ, paired
  with path-free source labels.
- Scope: these are actual learned conditional-completion results under a
  frozen engineering protocol. They do not test Liang--Huang--Chen's DDPM
  chain or score-error assumption, and they do not demonstrate a training or
  sampling benefit caused by `d - r`. The masks share a six-channel budget,
  their training-population mean numerical ranks range from 5.65 to 6.00, and
  rank was not a controlled experimental factor.
- Historical-provenance limitation: these learned runs were not recorded in
  the local public MLflow archive. The release instead preserves declared
  seeds, case coordinates, training-only mask geometry, curated metrics, and
  path-free analysis code; it is not an end-to-end retraining package.
- Protocol definitions: the training-only regularized Gram log-determinant
  formula, 2,000-candidate selection and control-sampling rule, validation-only
  checkpoint rules and selected steps, evaluation settings, and learned metric
  formulas are preserved in
  [`docs/LEARNED_COMPLETION_PROTOCOL.md`](../docs/LEARNED_COMPLETION_PROTOCOL.md).
- Post-hoc curation/reanalysis tracking record: MLflow experiment
  `conditional-fiber-geometry-release-integration`, run
  `623028254fa7415a969b1912449bab07`, status `FINISHED`. This record covers
  public artifact integration and reanalysis only; it is not a runtime record
  for the historical fixed-mask training or evaluation. It records that the
  analysis working tree was based on Git revision
  `783d3837e182a9d462db332cd029c1b97382ce79` and was dirty with the audited
  release changes; it must not be cited as a final-release commit identifier.

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

For historical run outputs retained directly, scientific values are unchanged
apart from the curation described below. CSV line endings were normalized from
CRLF to LF, and redundant terminal blank lines were removed from three JSON
metadata files, for a platform-neutral public release. No fields or values
were changed by these formatting operations.

- the original CSV tables in the direct-fiber, spectral-validation, and
  whitening result sets, with the line-ending normalization just described;
- the original NPZ numeric arrays in the direct-fiber and spectral-validation
  result sets;
- the original `parameters.json` files in those result sets;
- `results/spectral_validation/tracked_metrics.json`; and
- the files in `results/whitened_mask_design_seed20260902/`.

The acceptance table was reconstructed exactly from completed-run aggregate
counts; it cannot recover failure-level quantities that the original run did
not save. `cover_scale_diagnostics.csv` and `cover_scale_summary.json` are
deterministically generated from the retained `linear_spectral_cover.csv` by
`analyze_spectral_cover.py`; unlike `plot_spectral_validation.py`, this analysis
script writes tables. The image-rank tables are deterministic post-hoc
summaries of the archived Jacobian arrays. The learned `per_case_metrics.npz`
is a strict numeric curation of the three completed per-case CSVs: machine
paths, checkpoints, and unused columns are excluded, and loading is supported
with `allow_pickle=False`.

The `summary.json` files in `fiber_mechanisms_seed20260903/` and
`spectral_validation/` are curated public summaries. Their scientific numeric
fields are unchanged; internal study labels were replaced by neutral
descriptions and a non-scientific internal tracking label was omitted. The
image-rank and learned summaries instead have the deterministic post-hoc
origins described above. The integrity manifest was regenerated after this
curation.

Earlier presentation plots were removed because they duplicated the manuscript
figure and their generating programs were not part of this public release. The
committed manuscript validation figure,
`results/spectral_validation/conditional_geometry_validation.pdf`, is rebuilt
from these four unchanged CSV inputs:

1. `replicated_fibers.csv`;
2. `cover_calibration.csv`;
3. `full_spectrum_tube.csv`; and
4. `linear_spectral_cover.csv`.

It is generated by `plot_spectral_validation.py`; no third-party figure is
copied or adapted. The separate learned-completion PDF is generated by
`analyze_learned_completion.py` from its curated public NPZ.

## Commands

Run the public, self-contained computations from the repository root:

```bash
python -m pip install -e ".[test,figures]"
python -m pytest
python experiments/run_toy_validation.py
python experiments/analyze_spectral_cover.py
python experiments/plot_spectral_validation.py
python experiments/analyze_learned_completion.py
cd experiments/results
sha256sum -c SHA256SUMS
```

The original EIT solves, full-map Jacobian population, and learned-model
training cannot be regenerated end to end from this repository alone because
the full synthetic population and original generation/training workflow are
not bundled. The committed validation figure and learned summary can be
regenerated from their public numeric inputs; the historical CSV/NPZ inputs
remain archived outputs. This limitation is explicit, and the archive should
not be presented as an independently rerun benchmark.

## Interpretation constraints

- Every reported rank is a thresholded numerical rank.
- Finite-cloud PCA and covering slopes are diagnostics, not proofs of manifold
  dimension.
- The mesh table is a sensitivity study over three discretizations, not a
  continuum convergence theorem.
- Local continuation does not verify the manuscript's no-exit and boundary
  hypotheses over the full polygon class.
- Rank stability was checked only at accepted and base points; failure-level
  candidate spectra and admissibility margins were not preserved.
- The 360-sample full-map audit is an informative negative result for a
  stricter empirical image-rank exponent, not a global rank theorem.
- Learned conditional EDM performance is engineering evidence, not validation
  of a DDPM convergence rate or of a `d - r` learning advantage.
- The whitening and CEM-interface results support implementation choices; they
  are not claimed as new mathematical results.

The rationale for reusing these outputs and the preregistered protocols for
remaining gaps are in the
[experiment reuse and gap plan](../docs/EXPERIMENT_REUSE_AND_GAP_PLAN.md).
