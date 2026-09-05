# Experiment reuse audit and gap plan

This document records which completed experiments from the parent research
workspace are incorporated into this public repository, which are deliberately
excluded, and which claims still require new experiments.  The ordering is
mathematical: an experiment is included only when its estimand matches a
stated theorem mechanism or a clearly labelled engineering question.

## Decision summary

| Evidence source | Public-release decision | Reason |
|---|---|---|
| Direct and replicated polygon-fiber studies | Retain and add acceptance accounting | Directly examines local rank/fiber and spectral-tube mechanisms; the added table exposes conditioning on accepted continuations. |
| Three completed full-map Jacobian populations | Add a path-free numerical-rank audit | Tests whether the image-rank refinement is numerically stricter on the available samples.  It is an informative negative result. |
| Three-seed fixed-mask EDM/U-Net study | Add compact case-level data, an independent analysis script, and a figure | Supplies an actual conditional completion endpoint and tests the association between a training-only spectral mask score and learned test performance. |
| Population mask-design study | Use only as provenance/context for the learned study | Its selected mask and training-only score are inputs to the learned comparison; duplicating the much larger parent result set would add little to the current claim set. |
| Contrast-shift robustness study | Do not add to the present manuscript | Useful engineering evidence, but it does not address the audited mathematical gaps and would broaden the application narrative. |
| BPDM and unrelated completion runs | Exclude | Different priors or objectives do not test the fiber results stated here. |
| KTC/CEM full-scale artifacts | Exclude; retain only the already published aggregate derivative diagnostic | Mathematical alignment is weak and third-party redistribution boundaries require special care. |
| Model checkpoints and complete synthetic dataset | Exclude | They are large, unnecessary for checking the reported summaries, and contain provenance or redistribution concerns that are avoided by compact curation. |

The inclusion decision does not turn historical outputs into independently
rerun experiments.  Source hashes, seeds, curation steps, and the limits of
the available runtime provenance are recorded in
[`experiments/PROVENANCE.md`](../experiments/PROVENANCE.md).

## Reused evidence and its exact interpretation

### Continuation acceptance accounting

The public acceptance table separates attempts, accepted points, and base
points.  In the replicated study, 1,104 of 1,208 full-space starts were
accepted; adding 34 base points gives the 1,138 redifferentiated points quoted
in the paper.  All 104 rejected starts occurred for one near-boundary polygon.
The archived run did not retain rejected-point singular values or
admissibility margins, so the table cannot determine whether the rejected
points suffered rank degradation.  Consequently, `1,138/1,138` is explicitly
reported as an accepted/base-point result, not an unconditional stability
rate.

### Full-map numerical-rank audit

For 360 previously computed complete-data Jacobians from three population
seeds, the release recomputes all eight singular values and applies the same
relative threshold used by the other numerical rank diagnostics.  Every
sample has numerical rank eight.  Hence the new rank-difference diagnostic

\[
\operatorname{rank}(DF|_{\ker DH})
=\operatorname{rank}DF-\operatorname{rank}DH
\]

equals (8-r) at these sampled Jacobians and does not produce a stricter
empirical exponent.  This is finite-difference, pointwise evidence only.  It
does not verify exact rank, constant rank on a neighborhood, or a complete
fiber.

### Learned conditional completion

The reused learned study compares one mask selected from training Jacobians
with 20 equal-budget control masks sampled from the middle 80% of the candidate
score ordering.  It uses three independently trained
conditional EDMs, three deterministic U-Nets, 400 held-out polygons, four
noise levels, 18 EDM sampling steps, and 16 learned conditional samples.  A crossed
seed--polygon bootstrap preserves the dependence among masks evaluated on the
same polygon.

This experiment supports two limited engineering statements:

1. an actual conditional EDM completed held-out EIT data under the frozen
   protocol; and
2. among the fixed control masks, a training-only regularized Gram
   log-determinant score was associated with learned completion difficulty.

It does **not** test the external DDPM rate, conditional-score approximation,
or a learning benefit from replacing (d-r) by a smaller exponent.  All
compared masks have the same six-entry budget, but their mean sampled ranks
range from 5.65 to 6.00 and rank was not controlled.  EDM is not the DDPM chain
used by the external theorem.  The exact frozen protocol and metric definitions
are recorded in
[`LEARNED_COMPLETION_PROTOCOL.md`](LEARNED_COMPLETION_PROTOCOL.md).

## Experiments that are still required

The following protocols are preregistered plans, not completed results.  Each
run should be recorded in MLflow with the Git commit, immutable input hashes,
all declared seeds, solver tolerances, and the complete success/failure table.

### P0: nonlinear constrained-tube optimization

**Question.** Does the full singular spectrum predict the width and empirical
cover of a genuinely nonlinear EIT residual tube, beyond a one-dimensional
Taylor check along frozen right-singular vectors?

For each preregistered base polygon and mask, solve for every constrained
direction (q_i), sign, and residual radius

\[
\max_v\; \pm\langle q_i,v-v_0\rangle
\quad\text{subject to}\quad
\|H(v)-H(v_0)\|_{\Gamma^{-1}}\le\delta,
\quad \|v-v_0\|\le R,
\]

together with the polygon admissibility inequalities.  Use multiple starts
that are generated independently of (q_i), and evaluate derivatives at the
optimized points rather than freezing the base Jacobian.

Record feasibility, constraint residual, KKT residual, active constraints,
admissibility margin, start-to-solution variability, optimized/ray width,
and singular-spectrum drift.  Compare empirical nonlinear-tube covers with
the full-spectrum and repeated-σ_min predictors at prespecified, nonsaturated
scales.  A result is interpretable only if optimizer failures and boundary
hits are retained, not discarded.  This is the highest-priority missing
experiment for Section 4.

### P1: EIT horizontal flow and no-exit audit

**Question.** On a declared interior region, how often does the recomputed
pseudoinverse flow remain admissible and how well do its quantitative
identities hold?

Select base polygons before examining trajectory outcomes.  Erode the
admissible set by a declared margin, or analyze each active-constraint stratum
separately; do not treat the corners of the polygon prior as a globally
smooth boundary.  For paired nearby observations, integrate

\[
\dot v=DH(v)^\dagger(z'-z)
\]

with an adaptive solver and a freshly evaluated (DH).  At every accepted
and failed step retain the observation residual, step size, minimum singular
value, all admissibility margins, active stratum, and exit reason.  Run the
reverse trajectory and report cycle error.  Integrate the variational equation
to estimate the fiber Jacobian and compare displacement with
(|z-z'|/s_0).

Primary outcomes are the no-exit fraction with a binomial interval,
forward/reverse residual distributions, normalized displacement, minimum
singular value along each path, and fiber-volume distortion.  This is an
assumption audit on the sampled region, never a proof of global no-exit.

### P2: coarea-law transport

**Question.** Does the transported and reweighted conditional law exhibit the
predicted TV and Wasserstein behavior?

The current rejection-based polygon generator does not provide an evaluable
normalized density in vertex coordinates.  Before this experiment, either
derive that density including the proposal and rejection mechanism, or define
a new interior prior with an explicit positive (C^1) density.  The latter
would be a controlled theorem-mechanism study and must not be described as the
training prior.

Use a validated constrained/manifold sampler for

\[
\nu_z(dv)\propto\rho(v)J_H(v)^{-1}
\,d\mathcal H^{d-r}(v).
\]

Predeclare sampler diagnostics and effective-sample-size thresholds.  Compare
direct target-fiber samples with transported samples before and after coarea
reweighting.  Report density-ratio envelopes, TV with uncertainty, (W_1),
and their dependence on (|z-z'|); include failed or exiting trajectories.
The existing unweighted continuation clouds cannot be relabelled as samples
from this law.

### P3: matched-rank conditional-generation ablation

**Question.** Does residual dimension affect learning once conditioning and
architecture are controlled?

This experiment is needed only if an empirical claim about (d-r), image
rank, score error, sample complexity, or diffusion steps is added.  Train the
same architecture and budget under preregistered rank-2, rank-4, and rank-6
masks, with multiple data and network seeds.  Separate mask rank from the
whitened spectrum through matched-condition or factorial designs.  Report
held-out score error, completion error, calibration, training-set size curves,
and sampling-step curves.  Until then, the present learned study is correctly
limited to equal-budget spectral mask design.

### P4: noisy posterior geometry

After a noisy-posterior theorem is established, test posterior mass inside
whitened residual tubes rather than interpreting a deterministic tube as the
posterior support.  Vary noise covariance and prior metric, and compare
posterior effective covers with the spectrum of
(Gamma^{-1/2}DH\Sigma_V^{1/2}).  This is lower priority because the analytic
object must be specified before a numerical benchmark is meaningful.

## Release boundary

P0--P4 are not release blockers because the corresponding empirical claims
are not made.  The current release may state the abstract theorems, the local
mechanism diagnostics, the negative full-map-rank audit, and the limited
learned-completion evidence.  It may not state that Assumption Q holds for the
full polygon prior, that the hard tube is a noisy posterior, or that intrinsic
rank improves conditional diffusion training.
