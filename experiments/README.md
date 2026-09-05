# Numerical experiments

This directory contains compact numerical evidence for the local mechanisms
studied in the manuscript. The experiments are complementary to the
mathematical results: they examine finite-dimensional discretizations and do
not verify the manuscript assumptions over an entire EIT parameter class.

## Contents

| Path | Purpose |
|---|---|
| `run_toy_validation.py` | Deterministic analytic checks of transport and covering formulas. |
| `analyze_image_fiber_rank.py` | Recomputes numerical ranks from the committed complete-map singular spectra; optional private-source arguments recreate the path-free table. |
| `analyze_spectral_cover.py` | Generates per-scale saturation and correlation diagnostics from the committed linear-cover CSV. |
| `plot_spectral_validation.py` | Rebuilds the manuscript's four-panel validation figure from committed CSV tables. |
| `analyze_learned_completion.py` | Recomputes learned-completion statistics from the curated case-level NPZ and, when Matplotlib is installed, rebuilds its figure. |
| `curate_acceptance_summary.py` | One-time path-free acceptance-table curator for the hashed historical source summary. |
| `curate_learned_completion.py` | Validates historical case tables and writes the compact pickle-free public NPZ. |
| `results/fiber_mechanisms_seed20260903/` | Finite-difference, fiber-continuation, local tube, projection, Gaussian-MMSE, whitening, and CEM-interface results. |
| `results/spectral_validation/` | Replicated fiber, rank-along-fiber, acceptance accounting, full-spectrum tube, covering-calibration, near-critical, and mesh-sensitivity results. |
| `results/image_fiber_rank/` | Post-hoc spectra of 360 complete-data Jacobians and the resulting numerical-rank summary. |
| `results/learned_completion/` | Curated case-level conditional EDM/U-Net metrics, reproducible summary, and learned-completion figure. |
| `results/whitened_mask_design_seed20260902/` | Independent comparison of whitened, unweighted, and random mask designs. |
| `PROVENANCE.md` | Origins, attribution boundaries, seeds, curation policy, and data limitations. |
| `results/SHA256SUMS` | Integrity manifest for the committed result artifacts. |

The full synthetic forward dataset and the programs used for the original
large result generation are not included. The committed numeric tables and
arrays permit inspection of the reported diagnostics. The displayed
four-panel figure can be regenerated independently from its four input CSVs;
the plotting program does not regenerate those historical tables.

## Recompute the covering-scale diagnostics

Run:

```bash
python experiments/analyze_spectral_cover.py
```

This reads `linear_spectral_cover.csv` and generates
`cover_scale_diagnostics.csv` and `cover_scale_summary.json`. Of eight scales,
four meet the declared criterion
`0.1 * point_count < median_cover_count < 0.9 * point_count`. Their mean
Spearman correlations are `0.990371` for the full-spectrum predictor and
`0.853856` for the smallest-singular-value surrogate. From finest to coarsest
scale, saturated-mask counts are `21, 13, 6, 4, 2, 1, 0, 0` out of 48. These
diagnostics expose finite-cloud saturation; they do not estimate a continuum
covering dimension.

## Acceptance and image-rank audits

`results/spectral_validation/continuation_acceptance.csv` makes the selection
behind the rank-along-fiber statement explicit. There were 1,104 accepted
starts among 1,208 attempts; 34 base points bring the redifferentiated count to
1,138. All 104 rejected starts came from one near-boundary polygon. The
historical output preserves base-polygon margins but not rejected candidate
points or their singular values and margins, so this is an accepted/base-point
result rather than an unconditional rank-stability rate.

`results/image_fiber_rank/full_map_spectra.csv` contains all eight singular
values for each of 360 previously computed complete-data Jacobians. At the
declared relative threshold, all 360 have numerical rank 8. Consequently the
new image-rank exponent equals `8 - r` on these sampled Jacobians and is not
empirically stricter there. The audit is pointwise and finite-difference based;
it does not establish exact rank or constant rank on complete fibers.

The committed spectrum table is self-contained for the declared numerical
rank summary:

```bash
python experiments/analyze_image_fiber_rank.py
```

Recreating the spectrum or acceptance tables from the parent-study archives
requires the hashed historical sources described in `PROVENANCE.md`; those
large source archives are deliberately not part of this release.

## Learned conditional completion

The learned-study release uses the following stable artifact names:

- `results/learned_completion/per_case_metrics.npz`: path-free numeric tensors
  for three network seeds, 400 held-out polygons, 21 equal-budget masks, and
  four noise levels;
- `results/learned_completion/summary.json`: deterministic aggregate and
  crossed seed--polygon bootstrap results; and
- `results/learned_completion/learned_completion.pdf`: the corresponding
  summary figure.

This is genuine conditional EDM completion evidence, with a deterministic
U-Net comparator. It supports a frozen-protocol engineering comparison and a
test of whether a training-only spectral mask score is associated with held-out
completion difficulty. The 20 random controls were sampled from the middle 80%
of the candidate score ordering rather than uniformly from all six-entry masks.
Across the four noise levels, control-mask mean EDM
missing-entry error divided by selected-mask error was `1.762`--`1.781`; the
Spearman correlation between the training-only score and control-mask EDM error
was `-0.815` to `-0.795`. The crossed bootstrap intervals are retained in
`summary.json`. These are associations within this fixed mask set. They do not
validate the external DDPM convergence theorem, its score-error assumption, or
a benefit from replacing an entropy exponent by `d - r`: all compared masks
have the same six-channel budget, their training-population mean numerical
ranks span only `5.65`--`6.00`, and the study was not designed as a rank
ablation. EDM is also not the DDPM chain in that theorem.

## Rebuild the manuscript figure

Install the optional plotting dependency and run:

```bash
python -m pip install -e ".[figures]"
python experiments/plot_spectral_validation.py
```

The output is:

```text
experiments/results/spectral_validation/conditional_geometry_validation.pdf
```

The plotting program uses NumPy and Matplotlib only. It computes Spearman
correlations internally with average ranks, embeds TrueType fonts in the PDF,
uses redundant color/marker/line encodings, and omits timestamp and local-path
metadata. Panel (c) displays the explicit deviation
`sigma_i * width_i / delta - 1`, rather than relying on an axis offset around
one.

## Rebuild the learned-completion summary

With `per_case_metrics.npz` present, run:

```bash
python experiments/analyze_learned_completion.py
```

The script always writes `summary.json`; it also writes
`learned_completion.pdf` when Matplotlib is available. Statistical calculations
use NumPy, including a crossed network-seed/held-out-polygon bootstrap with
seed `20261001`.

The complete path-free mask-selection rule, validation-only checkpoint rule,
evaluation seeds, and metric formulas are recorded in the
[frozen learned-completion protocol](../docs/LEARNED_COMPLETION_PROTOCOL.md).

## Run the self-contained analytic checks

After installing the package:

```bash
python experiments/run_toy_validation.py
```

These checks are deterministic examples, not scientific experiments and not
proofs of the manuscript's theorems.

## Verify artifact integrity

From the repository root:

```bash
cd experiments/results
sha256sum -c SHA256SUMS
```

See [PROVENANCE.md](PROVENANCE.md) before reusing or interpreting the result
files. Inclusion decisions and protocols for the still-missing nonlinear-tube,
horizontal-flow, coarea, rank-ablation, and noisy-posterior experiments are in
the [experiment reuse and gap plan](../docs/EXPERIMENT_REUSE_AND_GAP_PLAN.md).
