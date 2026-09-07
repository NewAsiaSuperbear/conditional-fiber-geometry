import CFG.Basic.Model
import CFG.LinearAlgebra.RestrictedRank
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivative of the genuine observed map

This is the pointwise bridge required by M01: the observed derivative is
derived from the actual equality `H = P ∘ F`, rather than supplied as an
unrelated matrix.
-/

namespace CFG.Model

theorem hasFDerivAt_observed {d D q : ℕ} (model : CFG.Model d D q)
    {v : Euc d} {A : Euc d →L[ℝ] Euc D}
    (hcomplete : HasFDerivAt model.complete A v) :
    HasFDerivAt model.observed (model.mask.comp A) v :=
  model.mask.hasFDerivAt.comp v hcomplete

theorem hasFDerivAt_observed_and_rank_identity {d D q : ℕ}
    (model : CFG.Model d D q) {v : Euc d} {A : Euc d →L[ℝ] Euc D}
    (hcomplete : HasFDerivAt model.complete A v) :
    HasFDerivAt model.observed (model.mask.comp A) v ∧
      Module.finrank ℝ
          (LinearMap.range
            (restrictToObservedKer A.toLinearMap model.mask.toLinearMap)) +
        Module.finrank ℝ
          (LinearMap.range (model.mask.toLinearMap.comp A.toLinearMap)) =
        Module.finrank ℝ (LinearMap.range A.toLinearMap) := by
  refine ⟨hasFDerivAt_observed model hcomplete, ?_⟩
  exact finrank_range_restrictToObservedKer_add_finrank_range_comp
    A.toLinearMap model.mask.toLinearMap

end CFG.Model
