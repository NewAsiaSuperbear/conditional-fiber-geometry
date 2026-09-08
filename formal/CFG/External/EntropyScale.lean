import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial-resolution entropy substitution

This is the internal arithmetic supplied to an external DDPM theorem.  It
does not assume or reproduce that theorem: it only substitutes the genuine
scale `ε = T⁻ᶜ` into a logarithmic covering bound.
-/

namespace CFG.External

/-- The reciprocal of `T⁻ᶜ` has logarithm `c log T`. -/
theorem log_one_div_rpow_neg (T c : ℝ) (hT : 0 < T) :
    Real.log (1 / T ^ (-c)) = c * Real.log T := by
  rw [one_div, Real.rpow_neg hT.le, inv_inv, Real.log_rpow hT]

/-- A bound `log N(ε) ≤ C + k log(1/ε)` becomes the explicit polynomial-scale
bound `C + k c log T` at `ε = T⁻ᶜ`. -/
theorem entropy_bound_at_polynomial_resolution
    (logN : ℝ → ℝ) (C k T c : ℝ) (hT : 0 < T)
    (hbound : ∀ ε > 0, logN ε ≤ C + k * Real.log (1 / ε)) :
    logN (T ^ (-c)) ≤ C + k * c * Real.log T := by
  have hε : 0 < T ^ (-c) := Real.rpow_pos_of_pos hT _
  calc
    logN (T ^ (-c)) ≤ C + k * Real.log (1 / T ^ (-c)) := hbound _ hε
    _ = C + k * c * Real.log T := by
      rw [log_one_div_rpow_neg T c hT]
      ring

/-- Local entropy bounds suffice when the polynomial radius belongs to their domain.
No sign condition on `c` or lower bound `1 ≤ T` is needed here. -/
theorem entropy_bound_at_polynomial_resolution_local
    (logN : ℝ → ℝ) (C k T c ε₀ : ℝ) (hT : 0 < T)
    (_hε₀ : 0 < ε₀) (hscale : T ^ (-c) ≤ ε₀)
    (hbound : ∀ ε, 0 < ε → ε ≤ ε₀ → logN ε ≤ C + k * Real.log (1 / ε)) :
    logN (T ^ (-c)) ≤ C + k * c * Real.log T := by
  calc
    logN (T ^ (-c)) ≤ C + k * Real.log (1 / T ^ (-c)) :=
      hbound _ (Real.rpow_pos_of_pos hT _) hscale
    _ = C + k * c * Real.log T := by
      rw [log_one_div_rpow_neg T c hT]
      ring

/-- The usual unit-radius entropy interface, valid for `T ≥ 1` and `c ≥ 0`. -/
theorem entropy_bound_at_polynomial_resolution_unit
    (logN : ℝ → ℝ) (C k T c : ℝ) (hT : 1 ≤ T) (hc : 0 ≤ c)
    (hbound : ∀ ε, 0 < ε → ε ≤ 1 → logN ε ≤ C + k * Real.log (1 / ε)) :
    logN (T ^ (-c)) ≤ C + k * c * Real.log T := by
  exact entropy_bound_at_polynomial_resolution_local logN C k T c 1
    (lt_of_lt_of_le zero_lt_one hT) zero_lt_one
    (Real.rpow_le_one_of_one_le_of_nonpos hT (neg_nonpos.mpr hc)) hbound

/-- A sufficient real-valued step threshold for a general positive local radius. -/
theorem polynomial_resolution_le_of_threshold
    (T c ε₀ : ℝ) (hε₀ : 0 < ε₀) (hc : 0 < c)
    (hT : max 1 (ε₀ ^ (-1 / c)) ≤ T) : T ^ (-c) ≤ ε₀ := by
  have hbase : 0 < ε₀ ^ (-1 / c) := Real.rpow_pos_of_pos hε₀ _
  calc
    T ^ (-c) ≤ (ε₀ ^ (-1 / c)) ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos hbase (le_trans (le_max_right _ _) hT)
        (neg_nonpos.mpr hc.le)
    _ = ε₀ := by
      rw [← Real.rpow_mul hε₀.le]
      have hexp : (-1 / c) * (-c) = (1 : ℝ) := by field_simp
      rw [hexp, Real.rpow_one]

/-- A sufficiently large natural step count satisfies the local radius condition. -/
theorem exists_nat_polynomial_resolution_threshold
    (c ε₀ : ℝ) (hε₀ : 0 < ε₀) (hc : 0 < c) :
    ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → 0 < (T : ℝ) ∧ (T : ℝ) ^ (-c) ≤ ε₀ := by
  obtain ⟨T₀, hT₀⟩ := exists_nat_ge (max 1 (ε₀ ^ (-1 / c)))
  refine ⟨T₀, fun T hT => ?_⟩
  have hthreshold : max 1 (ε₀ ^ (-1 / c)) ≤ (T : ℝ) :=
    le_trans hT₀ (Nat.cast_le.mpr hT)
  exact ⟨lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hthreshold),
    polynomial_resolution_le_of_threshold T c ε₀ hε₀ hc hthreshold⟩

/-- A zero logarithmic covering function satisfies the local unit-radius hypothesis. -/
theorem zero_entropy_local (ε : ℝ) (hε : 0 < ε) (hsmall : ε ≤ 1) :
    0 ≤ Real.log (1 / ε) := by
  exact Real.log_nonneg ((one_le_div hε).mpr hsmall)

/-- Requiring the same positive-dimensional bound at every radius is too strong. -/
theorem zero_entropy_not_global : ¬ (∀ ε > (0 : ℝ), 0 ≤ Real.log (1 / ε)) := by
  intro h
  have hneg : Real.log (1 / (2 : ℝ)) < 0 := Real.log_neg (by norm_num) (by norm_num)
  exact (not_le_of_gt hneg) (h 2 (by norm_num))

end CFG.External
