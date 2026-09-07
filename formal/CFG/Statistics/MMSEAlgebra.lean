import CFG.LinearAlgebra.DiscreteSchur

/-!
# Algebraic covariance layer for linear Gaussian MMSE

For a latent-to-observation matrix `B` and invertible noise covariance `Γ`,
this file defines the posterior precision

`I + Bᵀ Γ⁻¹ B`

and its nonsingular inverse.  It proves the exact matrix inverse equations and
symmetry.  No probability space, Gaussian conditioning, or Bayes-risk theorem
is claimed here.
-/

namespace CFG.Statistics

open scoped Matrix

variable {latent obs : Type*}
variable [Fintype latent] [DecidableEq latent] [Fintype obs] [DecidableEq obs]

/-- Precision matrix in the standard linear Gaussian model. -/
noncomputable def posteriorPrecision
    (B : Matrix obs latent ℝ) (Γ : Matrix obs obs ℝ) [Invertible Γ] :
    Matrix latent latent ℝ :=
  1 + Bᵀ * ⅟Γ * B

/-- Algebraic posterior covariance, using mathlib's total nonsingular inverse. -/
noncomputable def posteriorCovariance
    (B : Matrix obs latent ℝ) (Γ : Matrix obs obs ℝ) [Invertible Γ] :
    Matrix latent latent ℝ :=
  (posteriorPrecision B Γ)⁻¹

/-- Under the explicit invertibility condition on the precision, precision
times covariance is the identity. -/
theorem posteriorPrecision_mul_posteriorCovariance
    (B : Matrix obs latent ℝ) (Γ : Matrix obs obs ℝ) [Invertible Γ]
    [Invertible (posteriorPrecision B Γ)] :
    posteriorPrecision B Γ * posteriorCovariance B Γ = 1 := by
  rw [posteriorCovariance, ← Matrix.invOf_eq_nonsing_inv]
  exact mul_invOf_self _

/-- The corresponding right inverse equation. -/
theorem posteriorCovariance_mul_posteriorPrecision
    (B : Matrix obs latent ℝ) (Γ : Matrix obs obs ℝ) [Invertible Γ]
    [Invertible (posteriorPrecision B Γ)] :
    posteriorCovariance B Γ * posteriorPrecision B Γ = 1 := by
  rw [posteriorCovariance, ← Matrix.invOf_eq_nonsing_inv]
  exact invOf_mul_self _

omit [Fintype latent] in
/-- Symmetric noise covariance gives a symmetric posterior precision. -/
theorem posteriorPrecision_isSymm
    (B : Matrix obs latent ℝ) (Γ : Matrix obs obs ℝ) [Invertible Γ]
    (hΓ : Γ.IsSymm) :
    (posteriorPrecision B Γ).IsSymm := by
  have hΓinv : (⅟Γ).IsSymm := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact CFG.isSymm_nonsingInv Γ hΓ
  apply Matrix.isSymm_one.add
  rw [Matrix.IsSymm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hΓinv]
  simp [Matrix.mul_assoc]

/-- Under the same symmetry condition, the algebraic posterior covariance is
symmetric as well. -/
theorem posteriorCovariance_isSymm
    (B : Matrix obs latent ℝ) (Γ : Matrix obs obs ℝ) [Invertible Γ]
    (hΓ : Γ.IsSymm) :
    (posteriorCovariance B Γ).IsSymm := by
  apply CFG.isSymm_nonsingInv
  exact posteriorPrecision_isSymm B Γ hΓ

end CFG.Statistics
