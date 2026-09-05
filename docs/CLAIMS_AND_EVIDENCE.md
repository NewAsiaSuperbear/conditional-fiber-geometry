# Claims and Evidence

This document distinguishes proved mathematical statements, numerical
evidence, external conditional consequences, and open problems. Numerical
experiments evaluate mechanisms and implementations; they do not prove the
analytic results.

| Claim | Type | Status | Evidence |
|---|---|---|---|
| Regular level-set dimension and compact image-fiber entropy | Theorem | Proved under local constant-rank and compactness assumptions. The image covering exponent is an upper bound, not necessarily an equality. | Theorem `thm:fiber-entropy`; local fiber experiments are consistent with the predicted dimensions. |
| Image-rank-refined fiber entropy | Corollary | If the rank of the restricted differential of \(F\) on \(\ker DH\) is constant and equal to \(\ell\) on a relative neighborhood of the fiber, the compact image fiber has covering upper exponent at most \(\ell\). Under constant ranks and \(H=PF\), \(\ell=\operatorname{rank}DF-\operatorname{rank}DH\). | Corollary `cor:image-rank-entropy`. The 360-sample EIT audit is a negative empirical result: every sampled \(DF\) has numerical rank 8, so it gives \(\ell=8-r\), not a stricter exponent. |
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
| Conditional DDPM entropy consequence | External conditional corollary | Pointwise in an almost-everywhere fixed regular mask-observation pair for which a positive certified covering exponent is selected, conditional on all hypotheses of Liang--Huang--Chen, arXiv:2501.12982v2, Theorem 2. | Corollary `cor:ddpm`; not an independent or uniform diffusion theorem. |
| Held-out conditional EDM completion and spectral mask association | Engineering evidence | Completed for the frozen three-seed, equal-budget protocol. It shows an actual conditional EDM endpoint and evaluates association between a training-only mask score and held-out performance. | Curated case-level metrics and reproducible analysis in `experiments/results/learned_completion/`. Not evidence for the external DDPM rate, its score hypothesis, or a `d-r` learning advantage. |
| Global EIT boundary transversality and no-exit | Open problem | Not claimed. | Discussed in `FUTURE_WORK.md`. |
| Conditional-score regularity and uniform diffusion convergence | Open problem | Not claimed. | Discussed in `FUTURE_WORK.md`. |
| Continuum FEM convergence | Open problem | Not claimed. | The available experiment is a three-mesh sensitivity study only. |

## Interpretation of the numerical evidence

The principal EIT mechanism study reports the following observations:

- all 30 replicated rank-\(2\), rank-\(4\), and rank-\(6\) local fiber clouds
  matched the predicted PCA dimensions \(6\), \(4\), and \(2\);
- 1,104 of 1,208 attempted continuation starts were accepted; adding 34 base
  points gives the 1,138 redifferentiated points. All 1,138 accepted/base
  points retained the expected thresholded full row rank. All 104 rejected
  starts came from one near-boundary polygon. Its base margins are retained,
  but failure-level candidate points, singular values, and margins were not
  archived;
- in the thresholded rank-\(8\) experiment, 96 nearby starts returned to the
  same numerical solution, with maximum displacement approximately
  \(1.16\times10^{-7}\), which is consistent with local isolation but does not
  establish it;
- the 48 normalized singular-direction widths had mean \(0.999961\), consistent
  with first-order \(\delta/\sigma_i\) scaling;
- over 48 linear ellipsoid configurations and eight scales, four scales met
  the declared criterion \(0.1n<\operatorname{median}N<0.9n\). Their mean
  Spearman correlation was \(0.990371\) for the full-spectrum predictor and
  \(0.853856\) for the smallest-singular-value surrogate. Finest-to-coarsest
  saturated-mask counts were 21, 13, 6, 4, 2, 1, 0, and 0 out of 48;
- a same-rank near-critical configuration in the spectral-validation study
  amplified mean linearized parameter error by a factor of approximately
  \(402.7\) relative to its stable comparator. The approximately \(297.3\)
  amplification in the earlier direct-fiber study is a separate experiment,
  not a second estimate for the same mask pair;
- all 360 audited complete-data Jacobians had thresholded numerical rank 8,
  so the new image-rank formula yields \(8-r\) on those samples and no stricter
  empirical exponent; and
- the learned archive contains conditional EDM and U-Net evaluations for
  three network seeds, 400 held-out polygons, 21 equal-budget masks, and four
  noise levels. Across noise levels, score-trimmed control-mask mean EDM
  missing-entry error was 1.762--1.781 times selected-mask error, and
  control-only Spearman
  score/error association ranged from -0.815 to -0.795. This is an engineering
  endpoint and a fixed-set association, not a test of DDPM theory or
  entropy-controlled sample complexity.

These quantities are finite-dimensional numerical diagnostics. In particular,
thresholded finite-difference rank is not exact differential rank, finite-cloud
PCA is not a proof of manifold dimension, and the rank-\(8\) result supplies
only numerical evidence consistent with local isolation. The continuation rank statement is
conditional on accepted/base points, and the learned comparison does not
isolate rank because all masks have the same six-channel budget, their
training-population mean numerical ranks lie between 5.65 and 6.00, and rank
was not experimentally varied as a controlled factor.

## Scope conditions that must remain visible

- Assumption Q includes boundary submersion. Ambient full row rank alone does
  not imply that a fiber intersecting a boundary is a neat manifold.
- The full inequality-defined polygon admissibility region is naturally
  cornered or stratified and is not globally covered by the smooth-boundary
  formulation of Assumption Q.
- Bidirectional no-exit requires the horizontal-flow solution to exist on the
  complete interval, remain in the parameter region, and satisfy the reverse
  transport condition.
- A derivative bound for the complete-data map is used along admissible flow
  paths; it is not treated as a global Lipschitz bound on a disconnected set.
- The conditional entropy inequality is restricted to its stated scale range.
- The DDPM statement is version-pinned, pointwise, and conditional on an
  external theorem. It does not establish the external score assumption.

The decision to reuse existing outputs and the protocols required before
making stronger empirical claims are documented in the
[experiment reuse and gap plan](EXPERIMENT_REUSE_AND_GAP_PLAN.md).
