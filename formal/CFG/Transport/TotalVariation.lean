import CFG.Analysis.NormalizedWeights
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Event total-variation bounds from an `L¹` density estimate

This file proves the event formulation of the standard total-variation
estimate.  If `f` is a normalized density with respect to `η`, then the
deviation of its mass on every measurable event is at most half the `L¹`
distance from the constant density one.

We state the result directly in terms of measurable-event probabilities,
rather than introducing a new quantity and calling it a Wasserstein metric.
-/

open MeasureTheory

namespace CFG.Transport

/-- A normalized integrable function has zero total signed deviation from the
constant function one. -/
theorem integral_sub_one_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} (hf : Integrable f η) (hnorm : ∫ x, f x ∂η = 1) :
    ∫ x, (f x - 1) ∂η = 0 := by
  rw [integral_sub hf (integrable_const 1), hnorm]
  simp

/-- The absolute normalized-density deviation on any measurable event is at
most half of its global `L¹` deviation.  This is the analytic core of the
event characterization of total variation. -/
theorem abs_setIntegral_sub_one_le_half_integral
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} (hf : Integrable f η) (hnorm : ∫ x, f x ∂η = 1)
    {s : Set Ω} (hs : MeasurableSet s) :
    |∫ x in s, (f x - 1) ∂η| ≤
      (1 / 2 : ℝ) * ∫ x, |f x - 1| ∂η := by
  let g : Ω → ℝ := fun x => f x - 1
  have hg : Integrable g η := hf.sub (integrable_const 1)
  have hzero : ∫ x, g x ∂η = 0 := integral_sub_one_eq_zero η hf hnorm
  have hsplit :
      (∫ x in s, |g x| ∂η) + (∫ x in sᶜ, |g x| ∂η) = ∫ x, |g x| ∂η :=
    integral_add_compl hs hg.abs
  have hs_bound : |∫ x in s, g x ∂η| ≤ ∫ x in s, |g x| ∂η :=
    abs_integral_le_integral_abs
  have hcomp_eq : (∫ x in sᶜ, g x ∂η) = -(∫ x in s, g x ∂η) := by
    have h := integral_add_compl hs hg
    rw [hzero] at h
    linarith
  have hcomp_bound : |∫ x in s, g x ∂η| ≤ ∫ x in sᶜ, |g x| ∂η := by
    have h : |∫ x in sᶜ, g x ∂η| ≤ ∫ x in sᶜ, |g x| ∂η :=
      abs_integral_le_integral_abs
    rwa [hcomp_eq, abs_neg] at h
  change |∫ x in s, g x ∂η| ≤ (1 / 2 : ℝ) * ∫ x, |g x| ∂η
  linarith

/-- On a measurable set, the real mass of the measure with nonnegative
integrable density `f` is the set integral of `f`. -/
theorem withDensity_ofReal_real_apply
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω)
    {f : Ω → ℝ} (hf : Integrable f η) (hf_nonneg : 0 ≤ᵐ[η] f)
    {s : Set Ω} (hs : MeasurableSet s) :
    (η.withDensity fun x => ENNReal.ofReal (f x)).real s = ∫ x in s, f x ∂η := by
  rw [measureReal_def, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_restrict_of_ae hf_nonneg)]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae hf_nonneg))

/-- A nonnegative density with integral one defines a probability measure.
This theorem is deliberately non-instance-valued: callers can install the
result locally when they need probability-measure typeclass inference. -/
theorem isProbabilityMeasure_withDensity_ofReal
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω)
    {f : Ω → ℝ} (hf : Integrable f η) (hf_nonneg : 0 ≤ᵐ[η] f)
    (hnorm : ∫ x, f x ∂η = 1) :
    IsProbabilityMeasure (η.withDensity fun x => ENNReal.ofReal (f x)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf hf_nonneg, hnorm]
  simp

/-- If `f` is a normalized nonnegative density, its probability on every
measurable event differs from the reference probability by at most half its
global `L¹` distance from one. -/
theorem abs_withDensity_event_sub_le_half_integral
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} (hf : Integrable f η) (hf_nonneg : 0 ≤ᵐ[η] f)
    (hnorm : ∫ x, f x ∂η = 1) {s : Set Ω} (hs : MeasurableSet s) :
    |(η.withDensity fun x => ENNReal.ofReal (f x)).real s - η.real s| ≤
      (1 / 2 : ℝ) * ∫ x, |f x - 1| ∂η := by
  rw [withDensity_ofReal_real_apply η hf hf_nonneg hs]
  rw [← setIntegral_one_eq_measureReal, ← integral_sub hf.integrableOn (integrable_const 1)]
  exact abs_setIntegral_sub_one_le_half_integral η hf hnorm hs

/-- The preceding event bound combined with a multiplicative distortion
`1 / M ≤ f ≤ M`. -/
theorem abs_withDensity_event_sub_le_ratio
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} {M : ℝ}
    (hf : Integrable f η) (hf_nonneg : 0 ≤ᵐ[η] f)
    (hnorm : ∫ x, f x ∂η = 1) (hM : 1 ≤ M)
    (hbounds : ∀ᵐ x ∂η, 1 / M ≤ f x ∧ f x ≤ M)
    {s : Set Ω} (hs : MeasurableSet s) :
    |(η.withDensity fun x => ENNReal.ofReal (f x)).real s - η.real s| ≤
      (M - 1) / (M + 1) := by
  exact (abs_withDensity_event_sub_le_half_integral η hf hf_nonneg hnorm hs).trans
    (CFG.Analysis.half_integral_abs_sub_one_le_ratio η hf hnorm hM hbounds)

/-- Exponential multiplicative distortion yields the sharp hyperbolic-tangent
event bound. -/
theorem abs_withDensity_event_sub_le_tanh
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} {a : ℝ}
    (hf : Integrable f η) (hf_nonneg : 0 ≤ᵐ[η] f)
    (hnorm : ∫ x, f x ∂η = 1) (ha : 0 ≤ a)
    (hbounds : ∀ᵐ x ∂η, Real.exp (-a) ≤ f x ∧ f x ≤ Real.exp a)
    {s : Set Ω} (hs : MeasurableSet s) :
    |(η.withDensity fun x => ENNReal.ofReal (f x)).real s - η.real s| ≤
      Real.tanh (a / 2) := by
  exact (abs_withDensity_event_sub_le_half_integral η hf hf_nonneg hnorm hs).trans
    (CFG.Analysis.half_integral_abs_sub_one_le_tanh η hf hnorm ha hbounds)

/-- The event deviation attained on `{x | 1 ≤ f x}` equals half the `L¹`
deviation.  Measurability of `f` is explicit because `Integrable f η` only
supplies an almost-everywhere measurable representative. -/
theorem abs_withDensity_event_sub_attains_half_integral
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f η) (hf_nonneg : 0 ≤ᵐ[η] f)
    (hnorm : ∫ x, f x ∂η = 1) :
    |(η.withDensity fun x => ENNReal.ofReal (f x)).real {x | 1 ≤ f x} -
        η.real {x | 1 ≤ f x}| =
      (1 / 2 : ℝ) * ∫ x, |f x - 1| ∂η := by
  let g : Ω → ℝ := fun x => f x - 1
  have hg : Integrable g η := hf.sub (integrable_const 1)
  have hzero : ∫ x, g x ∂η = 0 := integral_sub_one_eq_zero η hf hnorm
  have hs₀ : MeasurableSet {x | 1 ≤ f x} := measurableSet_le measurable_const hfm
  have hsplit_g :
      (∫ x in {x | 1 ≤ f x}, g x ∂η) + ∫ x in {x | 1 ≤ f x}ᶜ, g x ∂η = 0 := by
    rw [integral_add_compl hs₀ hg, hzero]
  have hsplit_abs :
      (∫ x in {x | 1 ≤ f x}, |g x| ∂η) + ∫ x in {x | 1 ≤ f x}ᶜ, |g x| ∂η =
        ∫ x, |g x| ∂η :=
    integral_add_compl hs₀ hg.abs
  have hpos :
      ∫ x in {x | 1 ≤ f x}, |g x| ∂η = ∫ x in {x | 1 ≤ f x}, g x ∂η :=
    setIntegral_congr_fun hs₀ (fun x hx => abs_of_nonneg (sub_nonneg.mpr hx))
  have hneg :
      ∫ x in {x | 1 ≤ f x}ᶜ, |g x| ∂η = -(∫ x in {x | 1 ≤ f x}ᶜ, g x ∂η) := by
    have h :
        ∫ x in {x | 1 ≤ f x}ᶜ, |g x| ∂η = ∫ x in {x | 1 ≤ f x}ᶜ, -(g x) ∂η := by
      apply setIntegral_congr_fun hs₀.compl
      intro x hx
      rw [Set.mem_compl_iff] at hx
      exact abs_of_neg (sub_neg.mpr (not_le.mp hx))
    rw [h, integral_neg]
  have hattain :
      ∫ x in {x | 1 ≤ f x}, g x ∂η = (1 / 2 : ℝ) * ∫ x, |g x| ∂η := by
    linarith
  have hnonneg : 0 ≤ ∫ x in {x | 1 ≤ f x}, g x ∂η :=
    setIntegral_nonneg hs₀ (fun x hx => sub_nonneg.mpr hx)
  rw [withDensity_ofReal_real_apply η hf hf_nonneg hs₀,
    ← setIntegral_one_eq_measureReal, ← integral_sub hf.integrableOn (integrable_const 1)]
  change |∫ x in {x | 1 ≤ f x}, g x ∂η| = _
  rw [abs_of_nonneg hnonneg, hattain]

/-- Half the `L¹` deviation of a normalized nonnegative measurable density
from one equals the supremum of its measurable-event deviations against the
reference probability.  The preceding theorem supplies an attaining event. -/
theorem half_integral_abs_sub_one_eq_iSup_event_abs
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f η) (hf_nonneg : 0 ≤ᵐ[η] f)
    (hnorm : ∫ x, f x ∂η = 1) :
    (1 / 2 : ℝ) * ∫ x, |f x - 1| ∂η =
      ⨆ s : {s : Set Ω // MeasurableSet s},
        |(η.withDensity fun x => ENNReal.ofReal (f x)).real s - η.real s| := by
  have : IsProbabilityMeasure (η.withDensity fun x => ENNReal.ofReal (f x)) :=
    isProbabilityMeasure_withDensity_ofReal η hf hf_nonneg hnorm
  have hbdd : BddAbove (Set.range fun s : {s : Set Ω // MeasurableSet s} =>
      |(η.withDensity fun x => ENNReal.ofReal (f x)).real s - η.real s|) := by
    refine ⟨1, ?_⟩
    rintro - ⟨s, rfl⟩
    have hη0 : 0 ≤ η.real s := measureReal_nonneg
    have hη1 : η.real s ≤ 1 := measureReal_le_one
    have hμ0 : 0 ≤ (η.withDensity fun x => ENNReal.ofReal (f x)).real s :=
      measureReal_nonneg
    have hμ1 : (η.withDensity fun x => ENNReal.ofReal (f x)).real s ≤ 1 :=
      measureReal_le_one
    rw [abs_le]
    constructor <;> linarith
  apply le_antisymm
  · rw [← abs_withDensity_event_sub_attains_half_integral η hfm hf hf_nonneg hnorm]
    exact le_ciSup hbdd ⟨{x | 1 ≤ f x}, measurableSet_le measurable_const hfm⟩
  · exact ciSup_le fun s =>
      abs_withDensity_event_sub_le_half_integral η hf hf_nonneg hnorm s.2

/-- The measurable-event total-variation supremum inherits the sharp
hyperbolic-tangent bound for a uniformly log-bounded density. -/
theorem iSup_event_abs_le_tanh
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsProbabilityMeasure η]
    {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f η) (hf_nonneg : 0 ≤ᵐ[η] f)
    (hnorm : ∫ x, f x ∂η = 1) {a : ℝ} (ha : 0 ≤ a)
    (hbounds : ∀ᵐ x ∂η, Real.exp (-a) ≤ f x ∧ f x ≤ Real.exp a) :
    (⨆ s : {s : Set Ω // MeasurableSet s},
      |(η.withDensity fun x => ENNReal.ofReal (f x)).real s - η.real s|) ≤
      Real.tanh (a / 2) := by
  rw [← half_integral_abs_sub_one_eq_iSup_event_abs η hfm hf hf_nonneg hnorm]
  exact CFG.Analysis.half_integral_abs_sub_one_le_tanh η hf hnorm ha hbounds

end CFG.Transport
