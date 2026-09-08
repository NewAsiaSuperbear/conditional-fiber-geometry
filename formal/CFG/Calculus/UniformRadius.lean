import Mathlib

/-!
# A division-safe uniform radius

M08 chooses a common local radius from an extension radius, a singular-value
lower bound, and a Hessian bound.  The zero-Hessian branch is definitionally
separate, so no proof silently relies on real division by zero.
-/

namespace CFG

/-- Common radius, with an explicit `L = 0` branch. -/
noncomputable def uniformRadius (ρ s L : ℝ) : ℝ :=
  if L = 0 then ρ / 2 else min (ρ / 2) (s / (16 * L))

theorem uniformRadius_of_eq_zero (ρ s : ℝ) : uniformRadius ρ s 0 = ρ / 2 := by
  simp [uniformRadius]

/-- Positivity of all genuine scale inputs implies positivity of the selected
common radius. -/
theorem uniformRadius_pos
    {ρ s L : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hL : 0 ≤ L) :
    0 < uniformRadius ρ s L := by
  by_cases hzero : L = 0
  · simp [uniformRadius, hzero, hρ]
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hzero)
    simp [uniformRadius, hzero, hρ, hs, hLpos]

/-- The common radius never exceeds half the extension radius. -/
theorem uniformRadius_le_half (ρ s L : ℝ) : uniformRadius ρ s L ≤ ρ / 2 := by
  by_cases hzero : L = 0
  · simp [uniformRadius, hzero]
  · simp [uniformRadius, hzero]

/-- The selected radius satisfies the small-Hessian product bound in both the
zero and positive branches. -/
theorem mul_uniformRadius_le
    {ρ s L : ℝ} (hs : 0 ≤ s) (hL : 0 ≤ L) :
    L * uniformRadius ρ s L ≤ s / 16 := by
  by_cases hzero : L = 0
  · subst L
    simp only [zero_mul]
    exact div_nonneg hs (by norm_num)
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hzero)
    have hRle : uniformRadius ρ s L ≤ s / (16 * L) := by
      simp [uniformRadius, hzero]
    calc
      L * uniformRadius ρ s L ≤ L * (s / (16 * L)) :=
        mul_le_mul_of_nonneg_left hRle hL
      _ = s / 16 := by
        field_simp [ne_of_gt hLpos]

end CFG
