# Future Work

The questions in this document are not part of the confirmed claim set.

## Global geometric verification

The whole-family transport theory assumes boundary submersion and
bidirectional no-exit on a compact regular observation region. Establishing
these properties for a useful EIT polygon class requires a canonical global
parameterization, including treatment of cyclic vertex relabeling, and a
quantitative analysis of horizontal trajectories near every admissibility
boundary.

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

Once conditional reference samplers are available, diffusion samples may be
compared directly with the target conditional law across masks of different
rank and conditioning. Controlled studies should separate residual dimension
\(d-r\) from stability governed by the whitened singular spectrum, use common
architectures and training budgets, and report uncertainty over independent
seeds. These experiments remain distinct from proving a diffusion convergence
rate.
