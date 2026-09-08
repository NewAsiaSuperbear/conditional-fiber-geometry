# API inventory

Fixed source target: mathlib `71a80585ee495fc24472fd0eaffc89d94e4fd8d6` with Lean `v4.34.0-rc2`.

| Domain | Candidate module / declaration | Local verification | Notes |
|---|---|---|---|
| Euclidean type | `Mathlib.Analysis.InnerProductSpace.PiL2`, `EuclideanSpace` | VERIFIED by fixed-toolchain build | Use instead of the function-space sup norm |
| Compact image | `Mathlib.Topology.Compactness.Compact`, `IsCompact.image` | VERIFIED by fixed-toolchain build | Supports only M00 compactness; the initially guessed `Topology.Sets.Compact` module does not exist |
| Rank-nullity | `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`, `LinearMap.finrank_range_add_finrank_ker` | VERIFIED by fixed-source search and build | Used three times to prove the M01 identity; kernel subtypes are related by an explicit `LinearEquiv` |
| Chain rule | `Mathlib.Analysis.Calculus.FDeriv.Comp`, `HasFDerivAt.comp` | VERIFIED by fixed-toolchain build | Combined with `ContinuousLinearMap.hasFDerivAt` from `FDeriv.Linear` to derive `D(P∘F)=P∘DF` |
| Implicit function | `Mathlib.Analysis.Calculus.Implicit`, `HasStrictFDerivAt.implicitFunction`, `to_implicitFunction`, `eq_implicitFunction` | VERIFIED by fixed-toolchain build | Used to construct a local Lipschitz chart with both chart-to-level and local level-to-chart statements |
| Rank projection | `finrank_le_iff_exists_linearMap`, `LinearMap.exists_leftInverse_of_injective`, `LinearMap.continuous_of_finiteDimensional` | VERIFIED by source inspection and build | Produces an actual continuous output projection from a rank lower bound |
| Covering numbers | `Mathlib.Topology.MetricSpace.CoveringNumbers`, `Metric.IsCover`, `externalCoveringNumber`, `coveringNumber` | VERIFIED by fixed-toolchain build | Radius is `ℝ≥0`, value is `ℕ∞`; internal centers are used only where required |
| Explicit finite-dimensional grid | `Finset.Icc`, `Pi.card_Icc`, `ContinuousLinearEquiv.ofFinrankEq`, `Metric.coveringNumber_subset_le` | VERIFIED by fixed-toolchain build | Gives `(2m+1)^n` centers and transports the internal cover to any finrank-`n` real normed ball with a factor-2 radius loss |
| Finite chart aggregation | `Metric.externalCoveringNumber_mono_set`, finite `iUnion` subadditivity, `Finset.sum_le_sum` | VERIFIED by fixed-toolchain build | Normalizes every local chart to the same requested positive radius and sums its explicit grid count |
| Compact metric cover | `IsCompact.finite_cover_balls`, `Metric.IsCover.coveringNumber_le_encard`, `Set.encard_lt_top_iff` | VERIFIED by fixed-toolchain build | Supplies qualitative finiteness at positive radius, not the Euclidean grid exponent |
| Disintegration | `Measure.condKernel`, `Measure.disintegrate`, `Measure.compProd_apply`, `Kernel.measurable_kernel_prodMk_left` | VERIFIED by source inspection and build | Gives relation-section mass one for `ρ.fst`-a.e. conditioning value |
| Conditional distribution | `ProbabilityTheory.condDistrib`, `compProd_map_condDistrib` | VERIFIED by fixed-toolchain build | The `ae` measure is the actual observation law `μ.map H` |
| Measurable dependent sums | coproduct `MeasurableSpace` on `Sigma`, `IndexedPartition.measurable_piecewise`, countable measurable union | VERIFIED by fixed-toolchain build | Builds a concrete tagged observation and fiber relation for countable varying-dimensional mask families |
| Topological support | `Measure.support_subset_of_isClosed`, `mem_ae_map_iff` | VERIFIED by fixed-toolchain build | Converts fiber mass one into support containment after a continuous pushforward |
| Normed operator ring | `Mathlib.Analysis.Normed.Operator.NormedSpace`, `ContinuousLinearMap.toNormedRing` | VERIFIED by fixed-toolchain build | Required for Neumann-series units on continuous endomorphisms |
| Neumann inverse | `Units.oneSub`, `tsum_geometric_le_of_norm_lt_one`, `ContinuousLinearMap.opNorm_comp_le` | VERIFIED by fixed-toolchain build | Constructs the M19 right inverse and its denominator bound |
| Orthogonal projection | `Submodule.starProjection`, `norm_starProjection_apply_le` | VERIFIED by fixed-toolchain build | Used for compatible affine projection non-expansion |
| Matrix inverse / Schur | `Matrix.invOf_eq_nonsing_inv`, `transpose_nonsing_inv`, `transpose_mul` | VERIFIED by fixed-toolchain build | Supports discrete Schur and posterior-covariance algebra; not PDE assembly |
| Weighted symmetric coordinates | finite subtype sums, `Real.sq_sqrt`, `Finset.sum_comm` | VERIFIED by fixed-toolchain build | Proves exact `√2` upper-triangle/Frobenius isometry and the background-weighted normalization constraint |
| Algebra inversion derivative | `Mathlib.Analysis.Calculus.FDeriv.Mul`, `hasFDerivAt_ringInverse`, `mulLeftRight` | VERIFIED by fixed-toolchain build | Gives `D(A⁻¹)[E] = -A⁻¹EA⁻¹` after the genuine chain rule |
| Hilbert adjoint / Gram inverse | `ContinuousLinearMap.adjoint`, `ContinuousLinearMap.IsInvertible`, `isUnit_iff_bijective` | VERIFIED by fixed-toolchain build | Constructs the surjective Moore–Penrose right inverse and proves its minimum-norm/projection properties |
| Orthogonal complement / operator lower bound | `Submodule.mem_orthogonal`, `ContinuousLinearMap.opNorm_le_bound` | VERIFIED by fixed-toolchain build | Converts `s‖x‖≤‖Bx‖` on `(ker B)ᵮ` into `‖B†‖≤s⁻¹` |
| Matrix Frobenius certificate | `Matrix.toEuclideanLin`, `Matrix.frobenius_norm_mul`, `ContinuousLinearMap.opNorm_le_bound` | VERIFIED by fixed-toolchain build | Converts finite entrywise square sums into operator bounds and feeds the Neumann right-inverse construction |
| One-dimensional FTC/Fubini | `intervalIntegral.integral_eq_sub_of_hasDerivAt`, Bochner integral norm bounds, translation invariance, product integral | VERIFIED by fixed-toolchain build | Supports the one-dimensional Banach-valued kernel translation and finite-coupling smoothing bounds |
| Finite-dimensional FTC/Fubini | `HasFDerivAt.comp_hasDerivAt`, `integrable_prod_iff`, `intervalIntegral_integral_swap`, `integral_sub_right_eq_self` | VERIFIED by fixed-toolchain build | Supports finite-dimensional Fréchet-direction translation and arbitrary finite-coupling smoothing bounds |
| Conditional expectation in L² | `condExpL2`, `lpMeas`, `Submodule.starProjection`, `starProjection_inner_eq_zero` | VERIFIED by fixed-toolchain build | Gives the exact Hilbert Pythagorean decomposition and closest-point risk inequality |
| Atomless finite iid products | `NullSingletonClass`, `Measure.prod_apply`, `Measure.prod_eq`, `Measure.pi_pi_finset`, `ae_all_iff` | VERIFIED by fixed-toolchain build | Proves binary diagonal nullity, exact distinct-coordinate marginals, and almost-sure injectivity of finite iid samples |
| Iid coordinate exchangeability | `measurePreserving_piCongrLeft`, `MeasurableEquiv.piCongrLeft`, `Equiv.piCongrLeft_apply_apply` | VERIFIED by fixed-toolchain build | Identifies project `reindex σ` with the native measurable coordinate equivalence for `σ.symm` and proves the iid product law invariant |
| Compact embedding | `Continuous.isClosedEmbedding`, `isCompact_iff_compactSpace` | VERIFIED by fixed-toolchain build | Establishes the topological embedding step for compact injective restrictions |
| Real powers/logarithms | `Real.rpow_neg`, `Real.log_rpow` | VERIFIED by fixed-toolchain build | Used only for the internal `ε=T^{-c}` entropy substitution |

Web documentation is not treated as proof that an API exists at the fixed commit.
