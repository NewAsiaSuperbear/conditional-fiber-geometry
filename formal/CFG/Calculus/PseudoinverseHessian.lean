import CFG.Calculus.PseudoinverseDerivative
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The genuine Jacobian/Hessian interface

The operator family is definitionally `fderiv ℝ H`, and the curried Hessian is
its actual Fréchet derivative.  The conclusion is pointwise on an open C²
region; no global two-point Lipschitz bound across a nonconvex region is claimed.
-/

namespace CFG

open scoped InnerProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The curried Hessian is the derivative of the true Jacobian. -/
noncomputable def curriedHessian (H : E → F) (x : E) : E →L[ℝ] (E →L[ℝ] F) :=
  fderiv ℝ (fderiv ℝ H) x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem hasFDerivAt_jacobian_of_contDiffAt_two {H : E → F} {x : E}
    (hH : ContDiffAt ℝ 2 H x) :
    HasFDerivAt (fderiv ℝ H) (curriedHessian H x) x := by
  exact ((hH.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt

/-- A Hessian operator-norm bound gives the certified derivative bound for
the canonical right pseudoinverse of the actual Jacobian. -/
theorem norm_fderiv_pseudoinverse_jacobian_le
    {H : E → F} {x : E} (hH : ContDiffAt ℝ 2 H x)
    (hsurj : Function.Surjective (fderiv ℝ H x)) {s L : ℝ} (hs : 0 < s)
    (hlb : ∀ z ∈ (fderiv ℝ H x).kerᗮ, s * ‖z‖ ≤ ‖fderiv ℝ H x z‖)
    (hHess : ‖curriedHessian H x‖ ≤ L) (v : E) :
    ‖fderiv ℝ (fun y => surjectivePseudoinverse (fderiv ℝ H y)) x v‖ ≤
      (2 * L * (s⁻¹) ^ 2) * ‖v‖ := by
  apply norm_fderiv_surjectivePseudoinverse_apply_le_of_lipschitz
    (hasFDerivAt_jacobian_of_contDiffAt_two hH) hsurj hs hlb
  intro w
  exact ((curriedHessian H x).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right hHess (norm_nonneg w))

/-- The same bound throughout an open C² region, using its genuine Hessian. -/
theorem norm_fderiv_pseudoinverse_jacobian_le_on
    {H : E → F} {O : Set E} (hO : IsOpen O) (hH : ContDiffOn ℝ 2 H O)
    {s L : ℝ} (hs : 0 < s)
    (hsurj : ∀ x ∈ O, Function.Surjective (fderiv ℝ H x))
    (hlb : ∀ x ∈ O, ∀ z ∈ (fderiv ℝ H x).kerᗮ,
      s * ‖z‖ ≤ ‖fderiv ℝ H x z‖)
    (hHess : ∀ x ∈ O, ‖curriedHessian H x‖ ≤ L)
    {x : E} (hx : x ∈ O) (v : E) :
    ‖fderiv ℝ (fun y => surjectivePseudoinverse (fderiv ℝ H y)) x v‖ ≤
      (2 * L * (s⁻¹) ^ 2) * ‖v‖ := by
  exact norm_fderiv_pseudoinverse_jacobian_le
    ((hH x hx).contDiffAt (hO.mem_nhds hx)) (hsurj x hx) hs (hlb x hx) (hHess x hx) v

omit [FiniteDimensional ℝ E] in
/-- Nonempty full-rank instance: the identity Jacobian has zero Hessian. -/
theorem curriedHessian_id (x : E) : curriedHessian (fun y : E => y) x = 0 := by
  change fderiv ℝ (fderiv ℝ (id : E → E)) x = 0
  have h : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun _ => fderiv_id
  rw [h]
  exact fderiv_const_apply _

end CFG
