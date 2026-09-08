import CFG.LinearAlgebra.RightInverseCertificate
import Mathlib.Tactic

/-!
# Exact toy certificate for the numerical-to-analytic bridge

The scalar map `x ↦ 2x` and rational candidate `x ↦ x/2` give a complete M19
certificate with zero approximation error.
-/

namespace CFG.Examples

/-- Scalar multiplication as a continuous real-linear endomorphism. -/
noncomputable def scalarCLM (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.id ℝ ℝ

@[simp]
theorem scalarCLM_apply (a x : ℝ) : scalarCLM a x = a * x := by
  simp [scalarCLM]

theorem scalar_two_comp_half :
    (scalarCLM 2).comp (scalarCLM (1 / 2)) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- The full approximation theorem constructs a true right inverse with norm
at most `1/2` from this rational certificate. -/
theorem exists_scalar_two_rightInverse_norm_le :
    ∃ S : ℝ →L[ℝ] ℝ, (scalarCLM 2).comp S = 1 ∧ ‖S‖ ≤ 1 / 2 := by
  have hq :
      ‖(1 : ℝ →L[ℝ] ℝ) - (scalarCLM 2).comp (scalarCLM (1 / 2))‖ ≤ (0 : ℝ) := by
    rw [scalar_two_comp_half]
    simp
  have he : ‖scalarCLM 2 - scalarCLM 2‖ ≤ (0 : ℝ) := by simp
  obtain ⟨S, hS, hnorm⟩ := CFG.exists_rightInverse_norm_le_of_approx
    (scalarCLM 2) (scalarCLM 2) (scalarCLM (1 / 2)) hq he (by norm_num)
  refine ⟨S, hS, hnorm.trans_eq ?_⟩
  simp [scalarCLM, norm_smul]

end CFG.Examples
