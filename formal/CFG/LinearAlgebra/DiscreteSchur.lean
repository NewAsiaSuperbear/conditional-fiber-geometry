import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Basic.Real.Basic

/-!
# Symmetry of the discrete Schur-complement response

This is the algebraic symmetry part of the finite-dimensional M18 branch.  It
models a symmetric stiffness matrix with boundary-interior block `B` and
invertible symmetric interior block `D`.
-/

namespace CFG

open scoped Matrix

variable {b i : Type*} [Fintype i] [DecidableEq i]

/-- Boundary response obtained by eliminating the interior variables. -/
noncomputable def discreteSchurResponse
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ) :
    Matrix b b ℝ :=
  A - B * D⁻¹ * Bᵀ

/-- The nonsingular inverse operation commutes with symmetry. -/
theorem isSymm_nonsingInv (D : Matrix i i ℝ) (hD : D.IsSymm) :
    D⁻¹.IsSymm := by
  rw [Matrix.IsSymm]
  calc
    D⁻¹ᵀ = (Dᵀ)⁻¹ := Matrix.transpose_nonsing_inv D
    _ = D⁻¹ := by rw [hD]

/-- On an actually invertible block, the total matrix inverse used in the
definition agrees with `⅟D`. -/
theorem discreteSchurResponse_eq_invOf
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ) [Invertible D] :
    discreteSchurResponse A B D = A - B * ⅟D * Bᵀ := by
  simp [discreteSchurResponse, Matrix.invOf_eq_nonsing_inv]

/-- Eliminating a symmetric invertible interior block preserves symmetry of
the boundary response. -/
theorem discreteSchurResponse_isSymm
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ)
    (hA : A.IsSymm) (hD : D.IsSymm) :
    (discreteSchurResponse A B D).IsSymm := by
  apply hA.sub
  rw [Matrix.IsSymm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [show D⁻¹ᵀ = D⁻¹ from isSymm_nonsingInv D hD]
  simp [Matrix.mul_assoc]

end CFG
