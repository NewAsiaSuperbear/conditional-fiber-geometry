import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Derivative of an invertible operator family

This is the abstract Banach-algebra layer of M18.  It records the genuine
Fréchet derivative of inversion at a supplied unit and composes it with a
differentiable operator family.
-/

namespace CFG

open ContinuousLinearMap Ring

variable {E R : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]

/-- If `A x` is represented by a unit `u`, the derivative of
`y ↦ (A y)⁻¹` is `E ↦ -u⁻¹ E u⁻¹` composed with the derivative of `A`. -/
theorem hasFDerivAt_ringInverse_comp
    {A : E → R} {A' : E →L[ℝ] R} {x : E}
    (hA : HasFDerivAt A A' x) (u : Rˣ) (hu : (u : R) = A x) :
    HasFDerivAt (fun y => Ring.inverse (A y))
      ((-mulLeftRight ℝ R (↑(u⁻¹) : R) (↑(u⁻¹) : R)).comp A') x := by
  have houter : HasFDerivAt Ring.inverse
      (-mulLeftRight ℝ R (↑(u⁻¹) : R) (↑(u⁻¹) : R)) (A x) := by
    simpa only [← hu] using hasFDerivAt_ringInverse (𝕜 := ℝ) u
  exact houter.comp x hA

end CFG
