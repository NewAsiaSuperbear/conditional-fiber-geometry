# Future Work

The questions in this document are not part of the confirmed claim set.
Concrete protocols, required failure accounting, and the order in which these
experiments should be run are specified in the
[experiment reuse and gap plan](EXPERIMENT_REUSE_AND_GAP_PLAN.md).

## Nonlinear residual-tube validation

The existing singular-direction width calculation moves along frozen right
singular vectors and is therefore primarily a first-order implementation
check. The highest-priority new experiment is a genuinely constrained
nonlinear EIT tube study: optimize width over the residual tube with independent
multiple starts, retain feasibility and KKT diagnostics, re-evaluate spectra at
solutions, and compare empirical covers at prespecified nonsaturated scales.
Optimizer failures and boundary hits must be retained rather than conditioned
away. This experiment is required before treating the nonlinear tube theorem
as independently validated by the EIT numerics.

## Global geometric verification

The whole-family transport theory assumes boundary submersion and
bidirectional no-exit on a compact regular observation region. Establishing
these properties for a useful EIT polygon class requires a canonical global
parameterization, including treatment of cyclic vertex relabeling, and a
quantitative analysis of horizontal trajectories near every admissibility
boundary.

The new acceptance table is useful warning evidence rather than a no-exit
test: all 104 historical continuation rejections came from one near-boundary
polygon, while rejected-point spectra, margins, and exit trajectories were not
saved. A new horizontal-flow audit must retain those quantities at every step,
include reverse transport and cycle error, and treat the polygon prior as a
cornered or stratified region rather than assuming a globally smooth boundary.

A related objective is to identify observation regions on which rank,
singular-value lower bounds, derivative bounds, and fiber chart radii are
uniform. Such a result would convert pointwise covering estimates into
observation-uniform estimates on a set of controlled probability.

## Conditional probability on EIT fibers

The geometric continuation experiments approximate level sets but do not
sample the population conditional distribution. A natural extension is a
constrained or manifold sampler for the coarea law

\[
\nu_z(dv)\propto
\rho(v)J_H(v)^{-1}\,d\mathcal H^{d-r}(v).
\]

Comparing coarea-weighted samples with nullspace continuation and
full-dimensional constrained recovery would distinguish geometric fiber
dimension from the effective dimension and density of the conditional law.
The existing unweighted continuation clouds cannot be retrospectively treated
as coarea-law samples. In particular, the rejection-based polygon generator's
density must first be derived, or a new explicit smooth interior prior must be
declared.

## Image-fiber rank beyond the current sample

The new theorem can sharpen the image covering exponent to

\[
\ell=\operatorname{rank}(DF|_{\ker DH})
=\operatorname{rank}DF-\operatorname{rank}DH
\]

under its constant-rank hypotheses. The available post-hoc audit is an
informative negative result: every one of 360 complete-data finite-difference
Jacobians has thresholded numerical rank 8, so \(\ell=8-r\) and no stricter
exponent appears on those samples. Further numerical searching is worthwhile
only with a prespecified reason to expect image collapse and must audit entire
fiber neighborhoods; pointwise rank alone cannot verify the theorem's
hypothesis.

## Uniform support geometry

The current moving-manifold theorem provides tangent noncollapse, local
metric control, and curvature bounds under explicit assumptions. Curvature
alone does not imply positive reach, because globally distinct portions of an
embedded manifold may approach one another. Future work should introduce a
quantitative separation or inverse-Lipschitz condition for \(F|_{S_z}\) and
determine whether it yields reach bounds uniform in \(z\).

## Statistical theory

Gaussian smoothing gives \(L^1\) stability of conditional densities and their
gradients, but it does not control the score where the smoothed density is
small. A suitable next target is a weighted estimate such as

\[
\int
\|s_t(x,z)-s_t(x,z')\|^2p_t(x\mid z)\,dx
\leq C_t\|z-z'\|^{2\alpha}.
\]

Potential approaches include Tweedie's identity, stability of conditional
posterior means, and fiberwise functional inequalities. If conditional-score
regularity can be established, existing nonparametric conditional-estimation
results may then be used to study finite-sample learning without requiring
repeated observations at identical conditioning values.

## Conditional diffusion theory

The present DDPM statement is a pointwise consequence of a version-pinned
external theorem. A stronger bridge from inverse geometry to conditional
diffusion would require uniform chart radii, higher joint regularity of the
conditional density and observation variable, suitable density lower bounds,
and control of the score error used by the selected diffusion theorem.

Uniform-in-observation and observation-averaged rates remain open. Any future
use of a later formulation of the external theorem should begin with a fresh
assumption-by-assumption comparison rather than an implicit version update.

## Noisy observations

For observations \(Y=H(V)+\xi\), the posterior is no longer supported on an
exact fiber. Under Gaussian noise it has density proportional to

\[
\rho(v)\exp\left[-\frac12
\|H(v)-y\|_{\Gamma^{-1}}^2\right].
\]

Future analysis should relate the concentration, entropy, and observation
regularity of this softened conditional law to the exact-fiber geometry and
the complete singular spectrum of \(\Gamma^{-1/2}DH\).

## Numerical analysis

The reported three-mesh comparison is a sensitivity study, not a continuum
convergence theorem. Further work should quantify FEM discretization error in
the forward map, its parameter derivative, the singular spectrum, and the
resulting fiber geometry. The dependence on electrode models, boundary
coordinate matching, and polygon-interface resolution should be examined
separately.

Additional experiments could also study more base geometries, near-critical
rank transitions, and conditional-law sampling. Such experiments would test
the mechanisms and assumptions; they would not substitute for the corresponding
analytic results.

## Generative-model experiments

The released three-seed conditional EDM/U-Net study now supplies a genuine
held-out completion endpoint for one selected and 20 score-trimmed random
equal-budget controls.
It can support claims about that frozen engineering protocol and about
association with a training-only spectral mask score. Because the masks have
the same six-channel budget, their training-population mean numerical ranks
span only 5.65--6.00, rank was not a controlled factor, and EDM is not the DDPM
chain in the external theorem, the study cannot support a \(d-r\) learning
claim or validate the external convergence rate.

A matched-rank ablation is still needed before making empirical claims about
residual dimension, score error, training-set size, or diffusion-step
complexity. It should compare rank-2, rank-4, and rank-6 masks with common
architectures and budgets, separate rank from whitened conditioning through a
matched or factorial design, and report multiple data and network seeds. Once
a validated conditional reference sampler exists, generated samples should
also be compared with the target coarea law rather than only with completion
errors.
