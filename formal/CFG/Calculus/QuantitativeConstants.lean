import Mathlib

/-!
# Arithmetic constants for the quantitative implicit graph

These lemmas isolate the four numerical inequalities used by the contraction
argument in work package M07.  Keeping them independent of the later analytic
construction makes every denominator and strict-positivity obligation explicit.
-/

namespace CFG.QuantitativeGraph

/-- The controlled parameter cylinder fits in the radius `17 R / 16` ball. -/
theorem radius_square_lt (R : ℝ) (hR : 0 < R) :
    (R / 8) ^ 2 + R ^ 2 < (17 * R / 16) ^ 2 := by
  nlinarith [sq_pos_of_pos hR]

/-- The universal contraction factor used in the paper is strictly below one. -/
theorem contraction_factor_lt_one : (17 : ℝ) / 256 < 1 := by
  norm_num

/-- The proposed contraction maps the closed `R/8` ball strictly into itself. -/
theorem contraction_maps_ball (R : ℝ) (hR : 0 < R) :
    R / 32 + ((17 : ℝ) / 256) * (R / 8) < R / 8 := by
  nlinarith

/-- The inverse-stability ratio obtained from `L R ≤ s/16` has the advertised
`17/239` bound. -/
theorem inverse_stability_ratio_le
    (L R s : ℝ) (hs : 0 < s)
    (hsmall : L * R ≤ s / 16) :
    (17 * L * R / 16) / (s - 17 * L * R / 16) ≤ (17 : ℝ) / 239 := by
  have hnum : 17 * L * R / 16 ≤ 17 * s / 256 := by
    nlinarith
  have hden : 239 * s / 256 ≤ s - 17 * L * R / 16 := by
    nlinarith
  have hden_pos : 0 < s - 17 * L * R / 16 := by
    nlinarith
  rw [div_le_iff₀ hden_pos]
  nlinarith

end CFG.QuantitativeGraph
