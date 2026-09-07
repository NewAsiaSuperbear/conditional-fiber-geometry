import CFG.LinearAlgebra.DiscreteSchur
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positivity and gauge structure of the discrete Schur response

This file records two structural facts used by the discrete M18 branch.

* A positive (semi)definite symmetric block system has a positive
  (semi)definite Schur response after elimination of an invertible positive
  definite interior block.
* Any feasible zero mode of the full block system descends to a zero mode of
  the Schur response.  In particular, a constant gauge of the full system
  gives zero row sums for the response.
-/

namespace CFG

open scoped Matrix

variable {b i : Type*} [Fintype b] [Fintype i] [DecidableEq i]

/-- A positive semidefinite block energy remains positive semidefinite after
eliminating a positive definite, invertible interior block. -/
theorem discreteSchurResponse_posSemidef
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ)
    (hD : D.PosDef) [Invertible D]
    (hBlock : (Matrix.fromBlocks A B Bᵀ D).PosSemidef) :
    (discreteSchurResponse A B D).PosSemidef := by
  have hHerm : (discreteSchurResponse A B D).IsHermitian := by
    simpa [discreteSchurResponse] using
      (Matrix.IsHermitian.fromBlocks₂₂ A B hD.isHermitian).mp hBlock.isHermitian
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm ?_
  intro x
  let y : i → ℝ := -((D⁻¹ * Bᵀ) *ᵥ x)
  have hnonneg := hBlock.dotProduct_mulVec_nonneg (Sum.elim x y)
  rw [Matrix.dotProduct_mulVec] at hnonneg
  have hcomplete :
      (star (Sum.elim x y)) ᵥ* (Matrix.fromBlocks A B Bᵀ D) ⬝ᵥ (Sum.elim x y) =
        (star ((D⁻¹ * Bᵀ) *ᵥ x + y)) ᵥ* D ⬝ᵥ ((D⁻¹ * Bᵀ) *ᵥ x + y) +
          (star x) ᵥ* (A - B * D⁻¹ * Bᵀ) ⬝ᵥ x := by
    simpa using Matrix.schur_complement_eq₂₂ A B x y hD.isHermitian
  rw [hcomplete] at hnonneg
  have hcancel : (D⁻¹ * Bᵀ) *ᵥ x + y = 0 := by
    dsimp [y]
    exact add_neg_cancel ((D⁻¹ * Bᵀ) *ᵥ x)
  rw [hcancel] at hnonneg
  simp only [star_zero, Matrix.zero_vecMul, dotProduct_zero, zero_add,
    ← Matrix.dotProduct_mulVec] at hnonneg
  simpa [discreteSchurResponse] using hnonneg

/-- A positive definite block energy has a positive definite Schur response.

The proof tests the full block quadratic form on the minimizing interior
vector `-D⁻¹ Bᵀ x`.  Its boundary component is nonzero whenever `x` is,
so strict positivity of the block form gives strict positivity of the Schur
quadratic form. -/
theorem discreteSchurResponse_posDef
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ)
    (hD : D.PosDef) [Invertible D]
    (hBlock : (Matrix.fromBlocks A B Bᵀ D).PosDef) :
    (discreteSchurResponse A B D).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (discreteSchurResponse_posSemidef A B D hD hBlock.posSemidef).isHermitian ?_
  intro x hx
  let y : i → ℝ := -((D⁻¹ * Bᵀ) *ᵥ x)
  have hxy : (Sum.elim x y : Sum b i → ℝ) ≠ 0 := by
    intro hzero
    apply hx
    funext j
    have := congr_fun hzero (Sum.inl j)
    simpa using this
  have hpos := hBlock.dotProduct_mulVec_pos hxy
  rw [Matrix.dotProduct_mulVec] at hpos
  have hcomplete :
      (star (Sum.elim x y)) ᵥ* (Matrix.fromBlocks A B Bᵀ D) ⬝ᵥ (Sum.elim x y) =
        (star ((D⁻¹ * Bᵀ) *ᵥ x + y)) ᵥ* D ⬝ᵥ ((D⁻¹ * Bᵀ) *ᵥ x + y) +
          (star x) ᵥ* (A - B * D⁻¹ * Bᵀ) ⬝ᵥ x := by
    simpa using Matrix.schur_complement_eq₂₂ A B x y hD.isHermitian
  rw [hcomplete] at hpos
  have hcancel : (D⁻¹ * Bᵀ) *ᵥ x + y = 0 := by
    dsimp [y]
    exact add_neg_cancel ((D⁻¹ * Bᵀ) *ᵥ x)
  rw [hcancel] at hpos
  simp only [star_zero, Matrix.zero_vecMul, dotProduct_zero, zero_add,
    ← Matrix.dotProduct_mulVec] at hpos
  simpa [discreteSchurResponse] using hpos

/-- Pointwise nonnegativity of the reduced boundary energy. -/
theorem discreteSchurResponse_energy_nonneg
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ)
    (hD : D.PosDef) [Invertible D]
    (hBlock : (Matrix.fromBlocks A B Bᵀ D).PosSemidef) (x : b → ℝ) :
    0 ≤ x ⬝ᵥ (discreteSchurResponse A B D *ᵥ x) := by
  simpa using
    (discreteSchurResponse_posSemidef A B D hD hBlock).dotProduct_mulVec_nonneg x

/-- Pointwise strict positivity of the reduced boundary energy away from the
zero boundary vector. -/
theorem discreteSchurResponse_energy_pos
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ)
    (hD : D.PosDef) [Invertible D]
    (hBlock : (Matrix.fromBlocks A B Bᵀ D).PosDef)
    {x : b → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (discreteSchurResponse A B D *ᵥ x) := by
  simpa using (discreteSchurResponse_posDef A B D hD hBlock).dotProduct_mulVec_pos hx

/-- A feasible zero mode `(x,y)` of the full symmetric block system descends
to a zero mode `x` of the boundary Schur response. -/
theorem discreteSchurResponse_mulVec_eq_zero_of_blockGauge
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ)
    [Invertible D] (x : b → ℝ) (y : i → ℝ)
    (hBoundary : A *ᵥ x + B *ᵥ y = 0)
    (hInterior : Bᵀ *ᵥ x + D *ᵥ y = 0) :
    discreteSchurResponse A B D *ᵥ x = 0 := by
  have hBT : Bᵀ *ᵥ x = -(D *ᵥ y) := eq_neg_of_add_eq_zero_left hInterior
  have hsolve : D⁻¹ *ᵥ (Bᵀ *ᵥ x) = -y := by
    rw [hBT, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  calc
    discreteSchurResponse A B D *ᵥ x =
        A *ᵥ x - (B * D⁻¹ * Bᵀ) *ᵥ x := by
          rw [discreteSchurResponse, Matrix.sub_mulVec]
    _ = A *ᵥ x - B *ᵥ (D⁻¹ *ᵥ (Bᵀ *ᵥ x)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = A *ᵥ x - B *ᵥ (-y) := by rw [hsolve]
    _ = A *ᵥ x + B *ᵥ y := by rw [Matrix.mulVec_neg]; simp
    _ = 0 := hBoundary

/-- If the constant boundary/interior pair is a feasible gauge of the full
block system, the constant boundary vector lies in the kernel of the Schur
response. -/
theorem discreteSchurResponse_const_mem_kernel
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ)
    [Invertible D]
    (hBoundary : A *ᵥ (1 : b → ℝ) + B *ᵥ (1 : i → ℝ) = 0)
    (hInterior : Bᵀ *ᵥ (1 : b → ℝ) + D *ᵥ (1 : i → ℝ) = 0) :
    discreteSchurResponse A B D *ᵥ (1 : b → ℝ) = 0 :=
  discreteSchurResponse_mulVec_eq_zero_of_blockGauge A B D 1 1 hBoundary hInterior

/-- The kernel statement for the constant gauge is exactly the zero-row-sum
property of the Schur response. -/
theorem discreteSchurResponse_rowSum_eq_zero
    (A : Matrix b b ℝ) (B : Matrix b i ℝ) (D : Matrix i i ℝ)
    [Invertible D]
    (hBoundary : A *ᵥ (1 : b → ℝ) + B *ᵥ (1 : i → ℝ) = 0)
    (hInterior : Bᵀ *ᵥ (1 : b → ℝ) + D *ᵥ (1 : i → ℝ) = 0) :
    ∀ r : b, ∑ c : b, discreteSchurResponse A B D r c = 0 := by
  have hker := discreteSchurResponse_const_mem_kernel A B D hBoundary hInterior
  intro r
  have := congr_fun hker r
  simpa [Matrix.mulVec, dotProduct] using this

end CFG
