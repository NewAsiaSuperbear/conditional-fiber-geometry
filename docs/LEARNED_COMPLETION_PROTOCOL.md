# Frozen learned-completion protocol

This document records the path-free protocol and metric definitions for the
archived learned-completion study. It is a historical protocol record, not a
claim that the omitted dataset and model checkpoints can be regenerated from
this release alone. The compact per-case archive and its source hashes are
described in [`experiments/PROVENANCE.md`](../experiments/PROVENANCE.md).

## Data and mask selection

- The frozen polygon dataset contained 2,000 training, 200 validation, and 400
  test examples. Mask selection used only the first 80 training examples.
- Each mask contains six distinct upper-triangular measurement entries. For a
  masked Jacobian \(J_M\), the training score was

  \[
  s(M)=\frac1{80}\sum_{q=1}^{80}
  \log\det\!\left(J_{M,q}J_{M,q}^{\mathsf T}
  +10^{-8}a_{M,q}I\right),
  \qquad
  a_{M,q}=\frac{\operatorname{tr}(J_{M,q}J_{M,q}^{\mathsf T})}{6}.
  \]

  We therefore call it the **regularized Gram log-determinant score**. Without
  the ridge, it is twice the log product of the six singular values.
- A NumPy generator with seed `20260904` produced 2,000 candidate masks by
  sampling six entries without replacement. The selected mask maximized
  \(s(M)\). The 20 controls were sampled without replacement from the middle
  80% of candidates after sorting by score; the bottom and top deciles were
  excluded. Thus “random control” below does not mean a uniform draw from all
  six-entry masks.
- The immutable mask-configuration SHA-256 digest is
  `708dc60624262b27e75725f6ed417a9ec18bc6e391e7d993769a8c6053a4fc39`.

## Training and checkpoint selection

- Three conditional EDMs and three deterministic U-Nets used network seeds
  `20260911`, `20260912`, and `20260913`. Every model used the same frozen bank
  of one selected and 20 control masks.
- Checkpoints were selected using the validation split only. For each seed,
  the EDM rule minimized `validation_ema_loss` over checkpoints at steps
  10,000, 20,000, 30,000, 40,000, and 50,000; step 50,000 was selected for all
  three seeds. The U-Net rule minimized `validation_missing_mse` over steps
  2,000, 4,000, 6,000, 8,000, and 10,000; step 10,000 was selected for all
  three seeds. No test quantity entered either rule.

## Frozen evaluation

- Evaluation used all 400 test polygons and normalized observation-noise
  standard deviations \(0\), \(10^{-4}\), \(3\times10^{-4}\), and \(10^{-3}\).
- The evaluation seed was `20260921`. EDM evaluation used 18 sampler steps and
  16 learned conditional samples per polygon, mask, noise level, and network
  seed. These samples are not asserted to be calibrated posterior draws.
- The reported confidence intervals use 10,000 crossed bootstrap replicates
  with seed `20261001`. Network-seed and test-polygon indices are resampled;
  the fixed masks and the already aggregated 16-sample Monte Carlo axis are
  not resampled.

## Metric definitions

Let \(U\) be the set of unobserved matrix entries, \(y_U\) the complete target
restricted to \(U\), and \(X_U^{(b)}\), \(b=1,\ldots,16\), the corresponding
entries of the EDM samples. All norms below are Euclidean/Frobenius norms on
those entries.

- `edm_missing_error` is the relative error of the 16-sample ensemble mean,

  \[
  \frac{\|\bar X_U-y_U\|_2}{\max(\|y_U\|_2,\epsilon_{\rm mach})},
  \qquad \bar X_U=\frac1{16}\sum_{b=1}^{16}X_U^{(b)}.
  \]

- Before the projected metrics are computed, every sample is mapped by the
  fixed affine DtN constraint projector while retaining the noisy observed
  entries. `projected_energy_score` is

  \[
  \frac{
  \frac1{16}\sum_b\|X_U^{(b)}-y_U\|_2
  -\frac1{2\cdot16^2}\sum_{b,b'}
  \|X_U^{(b)}-X_U^{(b')}\|_2}
  {\max(\|y_U\|_2,\epsilon_{\rm mach})},
  \]

  evaluated after that projection.
- `projected_coverage_90` forms the empirical 5th and 95th percentiles of the
  16 projected samples separately at each unobserved matrix entry and reports
  the fraction of target entries inside the resulting intervals.
- Ratios in the manuscript divide the mean over the 20 fixed controls by the
  selected-mask mean. The score/error Spearman coefficient is computed only
  across the 20 controls. Aggregate means cover all three network seeds and
  all 400 test polygons.

## Interpretation boundary

This protocol supplies held-out conditional-completion evidence and a
fixed-control-set association between a training-only spectral score and test
error. It does not test the external DDPM theorem, certify posterior
calibration, isolate numerical rank as a causal factor, or establish a
learning-rate improvement from replacing \(d-r\) by an image-fiber rank.
