# Extended formalization build — 2026-09-07

- Project baseline: `77e2203e6d5df42b457823eebe6626f1b1c3ded1`
- mathlib: `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`
- Lean: `v4.34.0-rc2`
- Command: `lake build`
- Result: success, `8928 jobs`
- Production root: `CFG.lean`
- Placeholder scan: no `sorry`, `admit`, declaration-level `axiom`, or declaration-level `opaque` in `CFG/**/*.lean` or `CFG.lean`
- Axiom audit: every audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound`
- `PROOF_STATUS.json`: parsed successfully after the build

New verified layers in this extension include dependent tagged random-mask
conditional support, projected rank charts and the full-rank finite-fiber
branch, sharp normalized-weight distortion, V/U-statistic normalization,
the two-point energy-score counterexample, quantitative M07/M08 arithmetic,
linear-tube reductions, compatible affine projection, algebraic MMSE
covariance, Banach-algebra inverse differentiation, discrete Schur symmetry,
the M19 right-inverse norm certificate and toy instance, compact embedding,
and polynomial-resolution entropy substitution.
The final M20 extension also includes the exact uniform-rank interior mass
`(n-1)/(n+1)` and its `n=16` value `15/17`.

The latest extension additionally includes a common-target-radius global
finite sum and a single-constant inverse-power certificate for degree-`d-r`
image-fiber chart bounds (plus the nonempty-fiber logarithmic entropy form),
an automatic measurable
construction for countable dependent varying-dimensional masks, the exact
`√2` weighted upper-triangle/Frobenius isometry with the safe normalized row
constraint, and finite Frobenius/closed-ball right-inverse certificates.

The theorem/status ledgers explicitly retain the remaining gaps; this build is
not reported as the M04 image-rank-refined entropy formula, transport coupling,
finite-dimensional Gaussian smoothing, Gaussian conditioning, continuous
PDE/shape, or external DDPM result.

The final 8926-job build additionally verifies the exact diagonal-tube product
grid, the Fréchet derivative and norm estimate for the canonical surjective
pseudoinverse, the reciprocal `1/s` bound under a lower singular inequality,
the exact measurable-event total-variation supremum and tanh corollary, the
finite-dimensional non-Gaussian kernel/coupling estimate, the genuine
`condExpL2` Pythagorean risk decomposition, and the atomless binary-product
no-ties theorem.  Every newly audited declaration again reports only
`propext`, `Classical.choice`, and `Quot.sound`.

The 8927-job rerun added the lower-singular-bound derivative corollary
`2‖E‖/s²` and the finite-iid `Measure.pi` bridge: every distinct-coordinate
pair has marginal `μ.prod μ`, and an atomless finite iid sample is almost
surely injective.

The final 8928-job M20 increment proves that the same finite iid product measure
is invariant under every coordinate permutation by identifying the project
`reindex` map with mathlib's measurable `piCongrLeft` equivalence.  The final
measure-level uniform-rank pushforward theorem remains open and is not claimed.
