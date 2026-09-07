import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Bounds for normalized multiplicative weights

The main result is the sharp elementary estimate used to control total
variation after normalization.  It is stated first with a generic distortion
factor `M ≥ 1`; an exponential/tanh specialization follows.
-/

open MeasureTheory Filter

namespace CFG.Analysis

/-- The sharp secant bound for a scalar lying between `1 / M` and `M`. -/
theorem abs_sub_one_le_ratio_mul_add
    {M t : ℝ} (hM : 1 ≤ M) (hlower : 1 / M ≤ t) (hupper : t ≤ M) :
    |t - 1| ≤ ((M - 1) / (M + 1)) * (t + 1) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hden : 0 < M + 1 := by linarith
  have hMt : 1 ≤ M * t := by
    have h := (div_le_iff₀ hMpos).mp hlower
    nlinarith
  have hright : t - 1 ≤ ((M - 1) / (M + 1)) * (t + 1) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hleft : 1 - t ≤ ((M - 1) / (M + 1)) * (t + 1) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- If a probability density integrates to one and is bounded between
`1 / M` and `M`, its half `L¹` distance from one is at most
`(M - 1) / (M + 1)`. -/
theorem half_integral_abs_sub_one_le_ratio
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} {M : ℝ}
    (hf : Integrable f η) (hnorm : ∫ x, f x ∂η = 1)
    (hM : 1 ≤ M)
    (hbounds : ∀ᵐ x ∂η, 1 / M ≤ f x ∧ f x ≤ M) :
    (1 / 2 : ℝ) * ∫ x, |f x - 1| ∂η ≤ (M - 1) / (M + 1) := by
  let c : ℝ := (M - 1) / (M + 1)
  have hc : 0 ≤ c := by
    exact div_nonneg (sub_nonneg.mpr hM) (by linarith)
  have hsub : Integrable (fun x => f x - 1) η := hf.sub (integrable_const 1)
  have habs : Integrable (fun x => |f x - 1|) η := hsub.abs
  have hsum : Integrable (fun x => f x + 1) η := hf.add (integrable_const 1)
  have hrhs : Integrable (fun x => c * (f x + 1)) η := hsum.const_mul c
  have hpoint : ∀ᵐ x ∂η, |f x - 1| ≤ c * (f x + 1) := by
    filter_upwards [hbounds] with x hx
    exact abs_sub_one_le_ratio_mul_add hM hx.1 hx.2
  have hint : (∫ x, |f x - 1| ∂η) ≤ ∫ x, c * (f x + 1) ∂η :=
    integral_mono_ae habs hrhs hpoint
  have hrhs_eq : (∫ x, c * (f x + 1) ∂η) = 2 * c := by
    rw [integral_const_mul, integral_add hf (integrable_const 1), hnorm]
    simp
    ring
  calc
    (1 / 2 : ℝ) * ∫ x, |f x - 1| ∂η ≤ (1 / 2 : ℝ) * (2 * c) :=
      mul_le_mul_of_nonneg_left (hint.trans_eq hrhs_eq) (by norm_num)
    _ = (M - 1) / (M + 1) := by simp [c]

/-- The exponential ratio appearing above is exactly a hyperbolic tangent. -/
theorem exp_ratio_eq_tanh_half (a : ℝ) :
    (Real.exp a - 1) / (Real.exp a + 1) = Real.tanh (a / 2) := by
  rw [Real.tanh_eq]
  have hne : Real.exp (a / 2) ≠ 0 := Real.exp_ne_zero _
  rw [Real.exp_neg]
  have hhalf : Real.exp a = Real.exp (a / 2) * Real.exp (a / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hhalf]
  field_simp

/-- Exponential multiplicative distortion gives the standard sharp
`tanh (a/2)` half-`L¹` bound. -/
theorem half_integral_abs_sub_one_le_tanh
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} {a : ℝ}
    (hf : Integrable f η) (hnorm : ∫ x, f x ∂η = 1)
    (ha : 0 ≤ a)
    (hbounds : ∀ᵐ x ∂η, Real.exp (-a) ≤ f x ∧ f x ≤ Real.exp a) :
    (1 / 2 : ℝ) * ∫ x, |f x - 1| ∂η ≤ Real.tanh (a / 2) := by
  have hM : 1 ≤ Real.exp a := by simpa using Real.exp_le_exp.mpr ha
  have hexpneg : Real.exp (-a) = 1 / Real.exp a := by
    rw [Real.exp_neg]
    simp [div_eq_mul_inv]
  rw [← exp_ratio_eq_tanh_half a]
  apply half_integral_abs_sub_one_le_ratio η hf hnorm hM
  filter_upwards [hbounds] with x hx
  rwa [← hexpneg]

end CFG.Analysis
