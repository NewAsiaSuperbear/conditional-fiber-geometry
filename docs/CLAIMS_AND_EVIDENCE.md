# Claims and Evidence

This document distinguishes proved mathematical statements, numerical
evidence, external conditional consequences, and open problems. Numerical
experiments evaluate mechanisms and implementations; they do not prove the
analytic results.

| Claim | Type | Status | Evidence |
|---|---|---|---|
| Regular level-set dimension and compact image-fiber entropy | Theorem | Proved under local constant-rank and compactness assumptions. The image covering exponent is an upper bound, not necessarily an equality. | Theorem `thm:fiber-entropy`; local fiber experiments are consistent with the predicted dimensions. |
| Random-mask conditional support | Proposition | Proved almost surely in the countable disjoint union of the mask-specific observation spaces. | Proposition `prop:conditional-support`. |
| Random-mask conditional entropy | Corollary | Proved pointwise for regular mask-observation pairs and \(0<\varepsilon\leq 1\). Constants may depend on the pair. | Corollary `cor:random-entropy`. |
| Full-spectrum linear tube | Theorem | Proved by singular-value decomposition and ellipsoid covering. | Theorem `thm:linear-tube`; singular-direction scaling experiment. |
| Noise-whitened tube | Corollary | Proved by applying the linear result to \(\Gamma^{-1/2}J\). | Corollary `cor:whitened`; anisotropic-noise experiment. |
| Quantitative local nonlinear tube | Theorem | Proved under explicit Hessian, radius, and singular-gap assumptions. | Lemma `lem:quantitative-graph` and Theorem `thm:nonlinear-tube`; local nonlinear-width experiment. |
| Uniform exact-fiber covering bound | Corollary | Proved on a compact regular region with uniform derivative and singular-value bounds. | Corollary `cor:uniform-fiber`. |
| Quantitative transport of neat fibers | Theorem | Proved under Assumption Q, including boundary submersion and bidirectional no-exit. | Theorem `thm:transport`; analytic transport tests. |
| Conditional parameter-law transport | Theorem | Proved under Assumption Q using coarea disintegration and density distortion along the horizontal flow. | Theorem `thm:measure-transport`. |
| Conditional complete-data-law stability | Corollary | Proved under Assumption Q with separate bounds for trajectory motion and conditional-mass reweighting. | Corollary `cor:data-law`. |
| Motion and curvature of conditional image manifolds | Theorem | Proved with the additional intrinsic tangent-noncollapse and fiberwise-injectivity assumptions. No positive reach is inferred. | Theorem `thm:moving-manifold`. |
| Gaussian-smoothed conditional density regularity | Proposition | Proved in \(L^1\) for the density and its gradient. No score bound follows without additional control. | Proposition `prop:smoothing`. |
| Conditional DDPM entropy consequence | External conditional corollary | Pointwise in an almost-everywhere fixed regular mask-observation pair, conditional on all hypotheses of Liang--Huang--Chen, arXiv:2501.12982v2, Theorem 2. | Corollary `cor:ddpm`; not an independent or uniform diffusion theorem. |
| Global EIT boundary transversality and no-exit | Open problem | Not claimed. | Discussed in `FUTURE_WORK.md`. |
| Conditional-score regularity and uniform diffusion convergence | Open problem | Not claimed. | Discussed in `FUTURE_WORK.md`. |
| Continuum FEM convergence | Open problem | Not claimed. | The available experiment is a three-mesh sensitivity study only. |

## Interpretation of the numerical evidence

The principal EIT mechanism study reports the following observations:

- all 30 replicated rank-\(2\), rank-\(4\), and rank-\(6\) local fiber clouds
  matched the predicted PCA dimensions \(6\), \(4\), and \(2\);
- all 1,138 accepted continuation points retained the expected thresholded
  full row rank when their finite-difference Jacobians were recomputed;
- in the thresholded rank-\(8\) experiment, 96 nearby starts returned to an
  isolated local solution, with maximum displacement approximately
  \(1.16\times10^{-7}\);
- the 48 normalized singular-direction widths had mean \(0.999961\), consistent
  with first-order \(\delta/\sigma_i\) scaling;
- over 48 linear ellipsoid configurations, the mean usable Spearman
  correlation was \(0.990\) for the full-spectrum predictor and \(0.854\) for
  the smallest-singular-value surrogate; and
- a same-rank near-critical configuration amplified mean linearized parameter
  error by a factor of approximately \(403\) relative to the stable
  configuration.

These quantities are finite-dimensional numerical diagnostics. In particular,
thresholded finite-difference rank is not exact differential rank, finite-cloud
PCA is not a proof of manifold dimension, and the rank-\(8\) result establishes
only an isolated local numerical solution.

## Scope conditions that must remain visible

- Assumption Q includes boundary submersion. Ambient full row rank alone does
  not imply that a fiber intersecting a boundary is a neat manifold.
- Bidirectional no-exit requires the horizontal-flow solution to exist on the
  complete interval, remain in the parameter region, and satisfy the reverse
  transport condition.
- A derivative bound for the complete-data map is used along admissible flow
  paths; it is not treated as a global Lipschitz bound on a disconnected set.
- The conditional entropy inequality is restricted to its stated scale range.
- The DDPM statement is version-pinned, pointwise, and conditional on an
  external theorem. It does not establish the external score assumption.
