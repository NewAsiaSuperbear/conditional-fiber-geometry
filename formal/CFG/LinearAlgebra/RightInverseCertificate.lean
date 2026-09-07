import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Checkable approximate-right-inverse certificates

This is the exact analytic skeleton used to turn a rational or interval
matrix certificate into a true surjectivity statement.  No numerical rank
predicate appears in the result.
-/

namespace CFG

/-- Error propagation from an approximate operator and a candidate right
inverse to the true operator. -/
theorem norm_id_sub_comp_le_of_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B Bhat : E →L[ℝ] F) (R : F →L[ℝ] E) {q e : ℝ}
    (hq : ‖(1 : F →L[ℝ] F) - Bhat.comp R‖ ≤ q)
    (he : ‖B - Bhat‖ ≤ e) :
    ‖(1 : F →L[ℝ] F) - B.comp R‖ ≤ q + e * ‖R‖ := by
  have hid :
      (1 : F →L[ℝ] F) - B.comp R =
        ((1 : F →L[ℝ] F) - Bhat.comp R) + (Bhat - B).comp R := by
    ext x
    simp
  rw [hid]
  calc
    ‖((1 : F →L[ℝ] F) - Bhat.comp R) + (Bhat - B).comp R‖ ≤
        ‖(1 : F →L[ℝ] F) - Bhat.comp R‖ + ‖(Bhat - B).comp R‖ :=
      norm_add_le _ _
    _ ≤ q + e * ‖R‖ := by
      apply add_le_add hq
      refine (ContinuousLinearMap.opNorm_comp_le (Bhat - B) R).trans ?_
      have hdiff : ‖Bhat - B‖ ≤ e := by simpa [norm_sub_rev] using he
      exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg R)

/-- If `B R` is within operator norm one of the identity, a genuine continuous
right inverse of `B` is constructed by the Neumann-series unit. -/
theorem exists_rightInverse_of_norm_id_sub_comp_lt_one
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]
    (B : E →L[ℝ] F) (R : F →L[ℝ] E)
    (h : ‖(1 : F →L[ℝ] F) - B.comp R‖ < 1) :
    ∃ S : F →L[ℝ] E, B.comp S = 1 := by
  let t : F →L[ℝ] F := (1 : F →L[ℝ] F) - B.comp R
  have ht : ‖t‖ < 1 := by simpa [t] using h
  let u : (F →L[ℝ] F)ˣ := Units.oneSub t ht
  let S : F →L[ℝ] E := R.comp (↑u⁻¹ : F →L[ℝ] F)
  refine ⟨S, ?_⟩
  have hu : (↑u : F →L[ℝ] F) = B.comp R := by
    simp [u, t]
  have hinv : (↑u : F →L[ℝ] F) * (↑u⁻¹ : F →L[ℝ] F) = 1 :=
    Units.val_inv u
  rw [hu, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] at hinv
  simpa [S] using hinv

/-- The Neumann construction also gives the quantitative norm bound for the
resulting right inverse. -/
theorem exists_rightInverse_norm_le_of_norm_id_sub_comp_lt_one
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]
    (B : E →L[ℝ] F) (R : F →L[ℝ] E)
    (h : ‖(1 : F →L[ℝ] F) - B.comp R‖ < 1) :
    ∃ S : F →L[ℝ] E, B.comp S = 1 ∧
      ‖S‖ ≤ ‖R‖ / (1 - ‖(1 : F →L[ℝ] F) - B.comp R‖) := by
  let t : F →L[ℝ] F := (1 : F →L[ℝ] F) - B.comp R
  have ht : ‖t‖ < 1 := by simpa [t] using h
  let u : (F →L[ℝ] F)ˣ := Units.oneSub t ht
  let S : F →L[ℝ] E := R.comp (↑u⁻¹ : F →L[ℝ] F)
  have hu : (↑u : F →L[ℝ] F) = B.comp R := by
    simp [u, t]
  have hinv : (↑u : F →L[ℝ] F) * (↑u⁻¹ : F →L[ℝ] F) = 1 :=
    Units.val_inv u
  rw [hu, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] at hinv
  refine ⟨S, by simpa [S] using hinv, ?_⟩
  have hgeom : ‖(↑u⁻¹ : F →L[ℝ] F)‖ ≤ (1 - ‖t‖)⁻¹ := by
    change ‖∑' n : ℕ, t ^ n‖ ≤ (1 - ‖t‖)⁻¹
    simpa using tsum_geometric_le_of_norm_lt_one t ht
  calc
    ‖S‖ ≤ ‖R‖ * ‖(↑u⁻¹ : F →L[ℝ] F)‖ := by
      simpa [S] using ContinuousLinearMap.opNorm_comp_le R (↑u⁻¹ : F →L[ℝ] F)
    _ ≤ ‖R‖ * (1 - ‖t‖)⁻¹ :=
      mul_le_mul_of_nonneg_left hgeom (norm_nonneg R)
    _ = ‖R‖ / (1 - ‖(1 : F →L[ℝ] F) - B.comp R‖) := by
      simp [t, div_eq_mul_inv]

/-- Full interval/rational certificate interface: approximation error plus a
strict Neumann margin constructs a right inverse for the true operator. -/
theorem exists_rightInverse_of_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]
    (B Bhat : E →L[ℝ] F) (R : F →L[ℝ] E) {q e : ℝ}
    (hq : ‖(1 : F →L[ℝ] F) - Bhat.comp R‖ ≤ q)
    (he : ‖B - Bhat‖ ≤ e)
    (hmargin : q + e * ‖R‖ < 1) :
    ∃ S : F →L[ℝ] E, B.comp S = 1 := by
  apply exists_rightInverse_of_norm_id_sub_comp_lt_one B R
  exact (norm_id_sub_comp_le_of_approx B Bhat R hq he).trans_lt hmargin

/-- Quantitative form of the full approximation certificate, with the exact
denominator required by M19. -/
theorem exists_rightInverse_norm_le_of_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]
    (B Bhat : E →L[ℝ] F) (R : F →L[ℝ] E) {q e : ℝ}
    (hq : ‖(1 : F →L[ℝ] F) - Bhat.comp R‖ ≤ q)
    (he : ‖B - Bhat‖ ≤ e)
    (hmargin : q + e * ‖R‖ < 1) :
    ∃ S : F →L[ℝ] E, B.comp S = 1 ∧ ‖S‖ ≤ ‖R‖ / (1 - q - e * ‖R‖) := by
  let err : ℝ := q + e * ‖R‖
  have hactual : ‖(1 : F →L[ℝ] F) - B.comp R‖ ≤ err := by
    simpa [err] using norm_id_sub_comp_le_of_approx B Bhat R hq he
  have hactual_lt : ‖(1 : F →L[ℝ] F) - B.comp R‖ < 1 :=
    hactual.trans_lt (by simpa [err] using hmargin)
  obtain ⟨S, hS, hSnorm⟩ :=
    exists_rightInverse_norm_le_of_norm_id_sub_comp_lt_one B R hactual_lt
  refine ⟨S, hS, hSnorm.trans ?_⟩
  have herrden : 0 < 1 - err := by simpa [err] using sub_pos.mpr hmargin
  have hden : 1 - err ≤ 1 - ‖(1 : F →L[ℝ] F) - B.comp R‖ := by linarith
  have hinv :
      1 / (1 - ‖(1 : F →L[ℝ] F) - B.comp R‖) ≤ 1 / (1 - err) :=
    one_div_le_one_div_of_le herrden hden
  calc
    ‖R‖ / (1 - ‖(1 : F →L[ℝ] F) - B.comp R‖) ≤ ‖R‖ / (1 - err) := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (norm_nonneg R)
    _ = ‖R‖ / (1 - q - e * ‖R‖) := by
      congr 1
      dsimp [err]
      ring

/-- The same certificate proves surjectivity of the true operator. -/
theorem surjective_of_approx_rightInverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]
    (B Bhat : E →L[ℝ] F) (R : F →L[ℝ] E) {q e : ℝ}
    (hq : ‖(1 : F →L[ℝ] F) - Bhat.comp R‖ ≤ q)
    (he : ‖B - Bhat‖ ≤ e)
    (hmargin : q + e * ‖R‖ < 1) : Function.Surjective B := by
  obtain ⟨S, hS⟩ := exists_rightInverse_of_approx B Bhat R hq he hmargin
  intro y
  refine ⟨S y, ?_⟩
  have hy := congrArg (fun T : F →L[ℝ] F => T y) hS
  simpa using hy

end CFG
