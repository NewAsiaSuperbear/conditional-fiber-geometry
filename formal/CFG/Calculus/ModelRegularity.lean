import CFG.Calculus.ObservedDerivative
import CFG.Basic.Fiber
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Regularity bridges for the genuine observed map

This module connects the regularity hypotheses used in the geometric
theorems to the `HasStrictFDerivAt` inputs consumed by the fiber-chart and
covering constructions.  Every derivative of the observed map is produced
from the actual composition `observed = mask ∘ complete`; no unrelated map,
Jacobian, or certificate field is passed to the geometric side.

## Scope

* `continuous_observed`, `hasStrictFDerivAt_observed`: pointwise bridges
  valid for any `Model`.
* `hasStrictFDerivAt_observed_of_contDiffOn`: the open-domain bridge.  The
  complete map is `C¹` on an *open* set `O` of the ambient parameter space,
  and every point of `O` is a strict differentiability point of the observed
  map with the genuine composite derivative `mask ∘ fderiv complete`.
* `hasStrictFDerivAt_observed_of_contDiff`: the explicit *intermediate*
  scope in which the complete map is globally `C¹`.  This is deliberately a
  separate declaration: it does not claim the cutoff/extension step that a
  general open domain on a bounded region would require, and its name marks
  the stronger global hypothesis.
* `isClosed_fiber_observed`, `isCompact_fiber_observed`,
  `isCompact_imageFiber_observed`: the fiber of the observed map inside a
  compact admissible set `E` is compact (hence relatively closed in `E`),
  and its complete-data image is compact.
-/

namespace CFG.Model

variable {d D q : ℕ} (model : CFG.Model d D q)

/-- The observed map is continuous whenever the complete-data map is. -/
theorem continuous_observed (hcomplete : Continuous model.complete) :
    Continuous model.observed :=
  model.mask.continuous.comp hcomplete

/-- Strict Fréchet derivative bridge: a strict derivative `A` of the
complete map yields the strict derivative `mask ∘ A` of the observed map.
The derivative is genuinely computed from `complete` and `mask`. -/
theorem hasStrictFDerivAt_observed {v : Euc d} {A : Euc d →L[ℝ] Euc D}
    (hcomplete : HasStrictFDerivAt model.complete A v) :
    HasStrictFDerivAt model.observed (model.mask.comp A) v :=
  model.mask.hasStrictFDerivAt.comp v hcomplete

/-- Open-domain bridge: if the complete map is `C¹` on an open set `O`,
then at every point of `O` the observed map has the strict Fréchet
derivative `mask ∘ fderiv complete`. -/
theorem hasStrictFDerivAt_observed_of_contDiffOn {O : Set (Euc d)}
    (hO : IsOpen O) (hcomplete : ContDiffOn ℝ 1 model.complete O)
    {v : Euc d} (hv : v ∈ O) :
    HasStrictFDerivAt model.observed
      (model.mask.comp (fderiv ℝ model.complete v)) v :=
  model.hasStrictFDerivAt_observed
    ((hcomplete.contDiffAt (hO.mem_nhds hv)).hasStrictFDerivAt one_ne_zero)

/-- Intermediate scope with a globally `C¹` complete map: every parameter
point is a strict differentiability point of the observed map.  This does
not subsume the open-domain statement above; it is the explicitly stronger
global hypothesis. -/
theorem hasStrictFDerivAt_observed_of_contDiff
    (hcomplete : ContDiff ℝ 1 model.complete) (v : Euc d) :
    HasStrictFDerivAt model.observed
      (model.mask.comp (fderiv ℝ model.complete v)) v :=
  model.hasStrictFDerivAt_observed
    (hcomplete.contDiffAt.hasStrictFDerivAt one_ne_zero)

/-- The fiber of the observed map inside a closed admissible set is closed. -/
theorem isClosed_fiber_observed {E : Set (Euc d)} (hclosed : IsClosed E)
    (hcomplete : Continuous model.complete) (z : Euc q) :
    IsClosed (CFG.fiber E model.observed z) :=
  CFG.isClosed_fiber hclosed (model.continuous_observed hcomplete)

/-- The fiber of the observed map inside a compact admissible set is
compact. -/
theorem isCompact_fiber_observed {E : Set (Euc d)} (hcompact : IsCompact E)
    (hcomplete : Continuous model.complete) (z : Euc q) :
    IsCompact (CFG.fiber E model.observed z) :=
  CFG.isCompact_fiber hcompact (model.continuous_observed hcomplete)

/-- The complete-data image of an observed fiber inside a compact admissible
set is compact. -/
theorem isCompact_imageFiber_observed {E : Set (Euc d)} (hcompact : IsCompact E)
    (hcomplete : Continuous model.complete) (z : Euc q) :
    IsCompact (CFG.imageFiber E model.complete model.observed z) :=
  CFG.isCompact_imageFiber (model.isCompact_fiber_observed hcompact hcomplete z)
    hcomplete

end CFG.Model
