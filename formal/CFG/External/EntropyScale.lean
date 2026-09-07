import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial-resolution entropy substitution

This is the internal arithmetic supplied to an external DDPM theorem.  It
does not assume or reproduce that theorem: it only substitutes the genuine
scale `ε = T⁻ᶜ` into a logarithmic covering bound.
-/

namespace CFG.External

/-- The reciprocal of `T⁻ᶜ` has logarithm `c log T`. -/
theorem log_one_div_rpow_neg (T c : ℝ) (hT : 0 < T) :
    Real.log (1 / T ^ (-c)) = c * Real.log T := by
  rw [one_div, Real.rpow_neg hT.le, inv_inv, Real.log_rpow hT]

/-- A bound `log N(ε) ≤ C + k log(1/ε)` becomes the explicit polynomial-scale
bound `C + k c log T` at `ε = T⁻ᶜ`. -/
theorem entropy_bound_at_polynomial_resolution
    (logN : ℝ → ℝ) (C k T c : ℝ) (hT : 0 < T)
    (hbound : ∀ ε > 0, logN ε ≤ C + k * Real.log (1 / ε)) :
    logN (T ^ (-c)) ≤ C + k * c * Real.log T := by
  have hε : 0 < T ^ (-c) := Real.rpow_pos_of_pos hT _
  calc
    logN (T ^ (-c)) ≤ C + k * Real.log (1 / T ^ (-c)) := hbound _ hε
    _ = C + k * c * Real.log T := by
      rw [log_one_div_rpow_neg T c hT]
      ring

end CFG.External
