import Mathlib

/-!
# V- and U-statistic pair-distance normalization

The diagonal terms of a distance kernel vanish.  Consequently a V-statistic
that divides the full ordered-pair sum by `B²` is exactly `(B-1)/B` times the
corresponding U-statistic, which divides the off-diagonal ordered-pair sum by
`B(B-1)`.
-/

namespace CFG.Statistics

open scoped BigOperators

variable {α : Type*}

/-- Ordered-pair sum including the diagonal. -/
noncomputable def fullPairSum (B : ℕ) (x : Fin B → α) (cost : α → α → ℝ) : ℝ :=
  ∑ i, ∑ j, cost (x i) (x j)

/-- Ordered-pair sum with `i = j` removed. -/
noncomputable def offDiagonalPairSum
    (B : ℕ) (x : Fin B → α) (cost : α → α → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, cost (x i) (x j)

/-- Vanishing diagonal terms make the full and off-diagonal pair sums equal. -/
theorem fullPairSum_eq_offDiagonalPairSum
    (B : ℕ) (x : Fin B → α) (cost : α → α → ℝ)
    (hdiag : ∀ a, cost a a = 0) :
    fullPairSum B x cost = offDiagonalPairSum B x cost := by
  unfold fullPairSum offDiagonalPairSum
  apply Finset.sum_congr rfl
  intro i hi
  exact (Finset.sum_erase (Finset.univ : Finset (Fin B))
    (f := fun j => cost (x i) (x j)) (hdiag (x i))).symm

/-- Pair term used by the V-statistic convention. -/
noncomputable def vPairMean (B : ℕ) (x : Fin B → α) (cost : α → α → ℝ) : ℝ :=
  fullPairSum B x cost / (B : ℝ) ^ 2

/-- Pair term used by the U-statistic convention. -/
noncomputable def uPairMean (B : ℕ) (x : Fin B → α) (cost : α → α → ℝ) : ℝ :=
  offDiagonalPairSum B x cost / ((B : ℝ) * ((B : ℝ) - 1))

/-- For `B ≥ 2`, the V-statistic pair penalty is short by the factor
`(B-1)/B` relative to the unbiased U-statistic pair penalty. -/
theorem vPairMean_eq_factor_mul_uPairMean
    (B : ℕ) (hB : 2 ≤ B) (x : Fin B → α) (cost : α → α → ℝ)
    (hdiag : ∀ a, cost a a = 0) :
    vPairMean B x cost = ((B : ℝ) - 1) / B * uPairMean B x cost := by
  have hnpos : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hB)
  have hn : (B : ℝ) ≠ 0 := ne_of_gt hnpos
  have hBreal : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hn1pos : (0 : ℝ) < (B : ℝ) - 1 := by
    linarith
  have hn1 : (B : ℝ) - 1 ≠ 0 := ne_of_gt hn1pos
  rw [vPairMean, uPairMean, fullPairSum_eq_offDiagonalPairSum B x cost hdiag]
  field_simp [hn, hn1]

/-- Multiplying the pair penalty by `1/2` preserves the same bias factor,
as used in the empirical energy score. -/
theorem half_vPairMean_eq_factor_mul_half_uPairMean
    (B : ℕ) (hB : 2 ≤ B) (x : Fin B → α) (cost : α → α → ℝ)
    (hdiag : ∀ a, cost a a = 0) :
    (1 / 2 : ℝ) * vPairMean B x cost =
      ((B : ℝ) - 1) / B * ((1 / 2 : ℝ) * uPairMean B x cost) := by
  rw [vPairMean_eq_factor_mul_uPairMean B hB x cost hdiag]
  ring

end CFG.Statistics
