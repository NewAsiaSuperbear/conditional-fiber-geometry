import Mathlib.Tactic

/-!
# A normalization counterexample for the two-point energy score

For truth equally likely to be `1` or `2`, and a forecast assigning probability
`q` to `2`, the unnormalized expected energy score is minimized at `q = 1/2`.
After dividing each realized score by the truth norm, the expected score is
instead uniquely minimized at `q = 1/3`.
-/

namespace CFG.Statistics

/-- Expected two-point energy score before truth-dependent normalization. -/
noncomputable def twoPointExpectedEnergy (q : ℝ) : ℝ :=
  (1 / 2 : ℝ) * q ^ 2 + (1 / 2 : ℝ) * (1 - q) ^ 2

/-- Expected two-point energy score after division by `|y|`, for truths `1`
and `2` occurring with equal probability. -/
noncomputable def twoPointNormalizedExpectedEnergy (q : ℝ) : ℝ :=
  (1 / 2 : ℝ) * q ^ 2 + (1 / 4 : ℝ) * (1 - q) ^ 2

theorem twoPointExpectedEnergy_eq_square (q : ℝ) :
    twoPointExpectedEnergy q = (q - 1 / 2) ^ 2 + 1 / 4 := by
  simp [twoPointExpectedEnergy]
  ring

theorem twoPointNormalizedExpectedEnergy_eq_square (q : ℝ) :
    twoPointNormalizedExpectedEnergy q =
      (3 / 4 : ℝ) * (q - 1 / 3) ^ 2 + 1 / 6 := by
  simp [twoPointNormalizedExpectedEnergy]
  ring

/-- The proper, unnormalized score is minimized at the true mass `1/2`. -/
theorem twoPointExpectedEnergy_minimized_at_half (q : ℝ) :
    twoPointExpectedEnergy (1 / 2) ≤ twoPointExpectedEnergy q := by
  rw [twoPointExpectedEnergy_eq_square, twoPointExpectedEnergy_eq_square]
  nlinarith [sq_nonneg (q - 1 / 2)]

theorem twoPointExpectedEnergy_eq_at_half_iff (q : ℝ) :
    twoPointExpectedEnergy q = twoPointExpectedEnergy (1 / 2) ↔ q = 1 / 2 := by
  rw [twoPointExpectedEnergy_eq_square, twoPointExpectedEnergy_eq_square]
  constructor
  · intro h
    nlinarith [sq_nonneg (q - 1 / 2)]
  · rintro rfl
    simp

/-- Truth-dependent normalization changes the unique optimizer to `1/3`. -/
theorem twoPointNormalizedExpectedEnergy_minimized_at_third (q : ℝ) :
    twoPointNormalizedExpectedEnergy (1 / 3) ≤
      twoPointNormalizedExpectedEnergy q := by
  rw [twoPointNormalizedExpectedEnergy_eq_square,
    twoPointNormalizedExpectedEnergy_eq_square]
  nlinarith [sq_nonneg (q - 1 / 3)]

theorem twoPointNormalizedExpectedEnergy_eq_at_third_iff (q : ℝ) :
    twoPointNormalizedExpectedEnergy q =
        twoPointNormalizedExpectedEnergy (1 / 3) ↔ q = 1 / 3 := by
  rw [twoPointNormalizedExpectedEnergy_eq_square,
    twoPointNormalizedExpectedEnergy_eq_square]
  constructor
  · intro h
    nlinarith [sq_nonneg (q - 1 / 3)]
  · rintro rfl
    simp

/-- The normalized expected score is strictly smaller at the biased forecast
`q=1/3` than at the true forecast `q=1/2`. -/
theorem normalizedEnergy_third_lt_half :
    twoPointNormalizedExpectedEnergy (1 / 3) <
      twoPointNormalizedExpectedEnergy (1 / 2) := by
  norm_num [twoPointNormalizedExpectedEnergy]

end CFG.Statistics
