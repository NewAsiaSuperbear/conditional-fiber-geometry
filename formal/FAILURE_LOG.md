# Failure log

## 2026-09-07 — Initial environment

- Repository clone initially failed inside the restricted sandbox with DNS resolution failure; the authorized network retry succeeded.
- Before setup, the requested Lean `v4.34.0-rc2` toolchain was absent; `lake
  update` installed it successfully alongside existing `v4.28.0` and
  `v4.31.0` toolchains.
- The first `lake update` reached Lean `v4.34.0-rc2` but rejected tuple-valued
  `leanOptions`; this Lake version requires `LeanOption` constructors such as
  `⟨`autoImplicit, false⟩`. The build configuration was corrected without
  changing any mathematical target.
- The first source build showed that `Mathlib.Topology.Sets.Compact` is not a
  module at the fixed mathlib commit. Source search located `IsCompact.image`
  in `Mathlib.Topology.Compactness.Compact`; the import was corrected.
- The first M01 build exposed a deprecated real-number import and an unused
  `simp` argument. Both were corrected under `warningAsError`; the theorem
  statements were unchanged.
- The Euclidean normed-space abbreviation had no canonical measurable-space
  instance. `CFG.eucMeasurableSpace` and `CFG.eucBorelSpace` now explicitly
  select the Borel structure; this also supplies the standard-Borel instance
  used by `condDistrib`.
- The fixed mathlib documentation mentions `Measure.compProd_fst_condKernel`,
  but the compiled API exposes the equality through the `Measure.IsCondKernel`
  instance as `ρ.disintegrate ρ.condKernel`. The implementation uses the
  compiled declaration.
- The first Neumann-certificate attempt imported only the seminormed operator
  ring API. `Units.oneSub` required the genuine `NormedRing` instance, located
  in `Mathlib.Analysis.Normed.Operator.NormedSpace`; importing that fixed module
  made the construction and norm estimate compile.
- The general dependent random-mask interface uses the tagged Sigma observation
  type `Σ m, Euc (q m)` and an arbitrary joint law on `(V,M)`. A subsequent
  countable-mask specialization constructs the tagged map and proves the fiber
  relation measurable, eliminating those interface hypotheses when singleton
  mask sets are measurable.
- Several fixed-version linters (`warningAsError`) rejected otherwise valid
  proofs for unused section variables, redundant tactic sequencing, and
  dependent `Invertible` rewrites. The declarations were restructured; matrix
  Schur symmetry uses the total nonsingular inverse plus a separate theorem
  identifying it with `⅟D` when `D` is invertible.
- No mathematical goal is represented by a placeholder. The major open proof
  layers are the positive-dimensional Euclidean grid/exponent, quantitative
  fixed-point graph, SVD/spectral tube, ODE/coarea/coupling/smoothing chain,
  full constant-rank geometry, Gaussian conditioning/Bayes risk, continuous
  CEM/shape calculus, and the iid exchangeability proof for the min-max interval.

## 2026-09-07 — Extended quantitative pass

- The configured Kimi model alias is `kimi-code/k3-256k`, not the shorter
  `k3-256k`; the first prompt failed before work began, and the corrected
  read-only audit completed successfully. No Kimi output was treated as a
  proof input.
- A sup-norm integer grid was transported to arbitrary finite-dimensional
  normed balls through `ContinuousLinearEquiv.ofFinrankEq`. Because a chart is
  only Lipschitz on its parameter ball, internal centers are required; the
  proof uses `Metric.coveringNumber_subset_le` and explicitly pays the factor
  two instead of applying the chart to external centers.
- The M03 chain now constructs positive-radius ball charts, makes the true
  `F ∘ chart` Lipschitz from a true strict derivative of `F`, selects finitely
  many charts by compactness, normalizes every chart to the same requested
  positive radius, and proves a global finite sum of explicit degree-`d-r`
  grid bounds. A subsequent ceiling-removal argument packages this into one
  positive `C` and finite witnesses `N ≤ C / epsilon^(d-r)`; the nonempty-set
  logarithmic presentation is also proved. The M04 rank refinement remains.
- The M09 algebraic pseudoinverse layer is complete through minimum-norm and
  orthogonal-projection properties. The exact `1/sigma_min` identity and the
  derivative formula for the pseudoinverse family still require a spectral
  lower-bound interface.
- The M14 result currently covers one-dimensional Banach-valued kernels and
  finite couplings. The finite-dimensional directional theorem and Gaussian
  constants remain separate targets; no custom Wasserstein definition was
  introduced.
- The first full build after adding `FrobeniusCertificate` failed only because
  three style linters were promoted to errors (`letI` in a proposition and two
  unnecessary `simpa`s). The proof text was simplified and the complete build
  then succeeded without warnings or theorem-statement changes.

## 2026-09-07 — Delegated model capability checks

- Local `qwen3.5:4b` was tested on a two-lemma M12 corollary.  After roughly 49
  seconds it proposed nonexistent imports and invalid finite-supremum APIs; the
  draft required replacement rather than a small repair.  It is not used for
  this Lean project.
- DeepSeek V4 Flash was called through the configured native `deepseek`
  provider in thinking mode.  The M12 corollary compiled on its first draft;
  the harder M09 lower-singular-bound bridge needed one warning-only cleanup
  and then compiled cleanly.  New routine and medium Lean subtasks therefore
  use the official DeepSeek API first, with Kimi retained as a fallback for
  long-context or stalled work.
- A subsequent Kimi K3 handoff returned HTTP 403 because the rolling five-hour
  usage quota was exhausted.  Work continued through the authorized DeepSeek
  provider; no Kimi result was fabricated or treated as complete.
- Two attempts to call the official DeepSeek endpoint directly from a small
  Codex-owned HTTP client both failed while reading a chunked response
  (`IncompleteRead` / `InvalidChunkLength`, with no authentication error).
  Direct HTTP was therefore abandoned; the native DeepSeek provider in the
  CLI remains the verified channel.
- DeepSeek V4 Pro completed the narrow iid-coordinate-exchangeability bridge
  cleanly using `measurePreserving_piCongrLeft`.  A follow-up request for the
  complete measure-level uniform-rank packaging spent its bounded window on a
  correct but lengthy finite-union plan without producing a file, so it was
  interrupted and no partial production module was retained.  Pro is therefore
  reserved for narrowly scoped API bridges rather than whole analytic layers.
- The M14 status above has advanced: a finite-dimensional Fréchet-derivative
  translation theorem and finite-coupling bound now compile.  The remaining
  analytic targets are the Gaussian constants and Wasserstein infimum wrapper.
