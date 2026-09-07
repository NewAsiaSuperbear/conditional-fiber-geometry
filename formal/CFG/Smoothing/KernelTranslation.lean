import Mathlib

open MeasureTheory Set
open scoped Interval

namespace CFG.Smoothing

section OneDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fundamental-theorem-of-calculus representation of a translated one-dimensional kernel.

The derivative is evaluated along the unit-speed affine parameterization of the segment from
`x` to `x - h`.  Continuity of `K'` is a convenient concrete sufficient condition for the
interval-integrability needed by the FTC. -/
theorem kernel_sub_eq_intervalIntegral [CompleteSpace E] {K K' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt K (K' x) x) (hK' : Continuous K') (x h : ℝ) :
    K (x - h) - K x = ∫ t in (0 : ℝ)..1, (-h) • K' (x - t * h) := by
  have hpath : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ ↦ K (x - s * h)) ((-h) • K' (x - t * h)) t := by
    intro t
    have haff : HasDerivAt (fun s : ℝ ↦ x - s * h) (-h) t := by
      exact (hasDerivAt_mul_const h).const_sub x
    have hc := (hderiv (x - t * h)).scomp t haff
    change HasDerivAt (fun s : ℝ ↦ K (x - s * h)) ((-h) • K' (x - t * h)) t at hc
    exact hc
  have hint : IntervalIntegrable (fun t : ℝ ↦ (-h) • K' (x - t * h)) volume 0 1 :=
    ((hK'.comp
      (continuous_const.sub (continuous_id.mul_const h))).const_smul (-h)).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ ↦ hpath t) hint
  simpa using hFTC.symm

/-- Pointwise domination of a translated kernel difference by the integral of its derivative
along the joining segment. -/
theorem norm_kernel_sub_le_intervalIntegral_norm [CompleteSpace E] {K K' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt K (K' x) x) (hK' : Continuous K') (x h : ℝ) :
    ‖K (x - h) - K x‖ ≤ ∫ t in (0 : ℝ)..1, ‖(-h) • K' (x - t * h)‖ := by
  rw [kernel_sub_eq_intervalIntegral hderiv hK' x h]
  exact intervalIntegral.norm_integral_le_integral_norm zero_le_one

/-- The two-variable derivative majorant used in the Tonelli/Fubini step is integrable. -/
private theorem integrable_segmentDerivative {K' : ℝ → E} (hK'int : Integrable K')
    (hK' : Continuous K') (h : ℝ) :
    Integrable (Function.uncurry fun t x : ℝ ↦ ‖(-h) • K' (x - t * h)‖)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
  have hcont : Continuous (fun p : ℝ × ℝ ↦ ‖(-h) • K' (p.2 - p.1 * h)‖) :=
    ((hK'.comp (continuous_snd.sub (continuous_fst.mul_const h))).const_smul (-h)).norm
  change Integrable (fun p : ℝ × ℝ ↦ ‖(-h) • K' (p.2 - p.1 * h)‖)
    ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume)
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  constructor
  · filter_upwards with t
    simpa only [norm_smul, Real.norm_eq_abs, abs_neg] using
      (hK'int.comp_sub_right (t * h)).norm.const_mul |h|
  · have heq : (fun t : ℝ ↦ ∫ x : ℝ, ‖‖(-h) • K' (x - t * h)‖‖) =
        fun _ : ℝ ↦ ∫ x : ℝ, ‖(-h) • K' x‖ := by
      funext t
      simpa only [norm_norm] using
        (integral_sub_right_eq_self (fun x : ℝ ↦ ‖(-h) • K' x‖) (t * h))
    rw [heq]
    exact integrableOn_const (s := uIoc (0 : ℝ) 1) (by simp)

/-- One-dimensional `W^{1,1}` translation estimate.

This is the non-Gaussian kernel layer required by M14: the conclusion is derived from a genuine
global derivative and its `L¹` integrability, not postulated as a stability assumption. -/
theorem integral_norm_kernel_sub_le [CompleteSpace E] {K K' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt K (K' x) x) (hK' : Continuous K')
    (hK'int : Integrable K') (h : ℝ) :
    (∫ x : ℝ, ‖K (x - h) - K x‖) ≤ |h| * ∫ x : ℝ, ‖K' x‖ := by
  have hprod := integrable_segmentDerivative hK'int hK' h
  have hmajorant : Integrable
      (fun x : ℝ ↦ ∫ t in (0 : ℝ)..1, ‖(-h) • K' (x - t * h)‖) := by
    simpa only [Function.uncurry_apply_pair, intervalIntegral.integral_of_le zero_le_one,
      uIoc_of_le zero_le_one] using hprod.integral_prod_right
  have hKcont : Continuous K := continuous_iff_continuousAt.2 fun x ↦ (hderiv x).continuousAt
  have hlhs : Integrable (fun x : ℝ ↦ ‖K (x - h) - K x‖) :=
    hmajorant.mono' ((hKcont.comp (continuous_id.sub continuous_const)).sub hKcont).norm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        simpa only [Real.norm_eq_abs, abs_norm,
          abs_of_nonneg (intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ norm_nonneg _)] using
          norm_kernel_sub_le_intervalIntegral_norm hderiv hK' x h)
  calc
    (∫ x : ℝ, ‖K (x - h) - K x‖)
        ≤ ∫ x : ℝ, ∫ t in (0 : ℝ)..1, ‖(-h) • K' (x - t * h)‖ := by
          apply integral_mono
          · exact hlhs
          · exact hmajorant
          · exact fun x ↦ norm_kernel_sub_le_intervalIntegral_norm hderiv hK' x h
    _ = ∫ t in (0 : ℝ)..1, ∫ x : ℝ, ‖(-h) • K' (x - t * h)‖ := by
          exact (intervalIntegral_integral_swap hprod).symm
    _ = ∫ t in (0 : ℝ)..1, |h| * ∫ x : ℝ, ‖K' x‖ := by
          apply intervalIntegral.integral_congr
          intro t _
          change (∫ x : ℝ, ‖(-h) • K' (x - t * h)‖) = _
          rw [integral_sub_right_eq_self (fun x : ℝ ↦ ‖(-h) • K' x‖) (t * h)]
          simp only [norm_smul, Real.norm_eq_abs, abs_neg, integral_const_mul]
    _ = |h| * ∫ x : ℝ, ‖K' x‖ := by simp

end OneDimensional

section CouplingBridge

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The analytic bridge behind the coupling argument: averaging a jointly integrable family
cannot increase its `L¹` norm.  No marginal or optimal-transport structure is needed for this
Tonelli/Fubini step. -/
theorem integral_norm_integral_le_integral_integral_norm (γ : Measure Ω) [SFinite γ]
    {f : Ω → ℝ → E}
    (hf : Integrable (Function.uncurry f) (γ.prod volume)) :
    (∫ x : ℝ, ‖∫ ω : Ω, f ω x ∂γ‖) ≤ ∫ ω : Ω, ∫ x : ℝ, ‖f ω x‖ ∂volume ∂γ := by
  have hleft : Integrable (fun x : ℝ ↦ ‖∫ ω : Ω, f ω x ∂γ‖) :=
    hf.integral_prod_right.norm
  have hright : Integrable (fun x : ℝ ↦ ∫ ω : Ω, ‖f ω x‖ ∂γ) :=
    hf.norm.integral_prod_right
  calc
    (∫ x : ℝ, ‖∫ ω : Ω, f ω x ∂γ‖)
        ≤ ∫ x : ℝ, ∫ ω : Ω, ‖f ω x‖ ∂γ := by
          apply integral_mono hleft hright
          intro x
          exact norm_integral_le_integral_norm _
    _ = ∫ ω : Ω, ∫ x : ℝ, ‖f ω x‖ ∂volume ∂γ :=
      (integral_integral_swap hf.norm).symm

/-- A coupling-style consequence of the preceding bridge.  The pointwise transportation cost
bound is integrated here; it is not assumed as an `L¹` bound on the averaged mixture. -/
theorem integral_norm_integral_le_of_pointwise_l1_bound (γ : Measure Ω) [SFinite γ]
    {f : Ω → ℝ → E} {cost : Ω → ℝ} {C : ℝ}
    (hf : Integrable (Function.uncurry f) (γ.prod volume))
    (hcost : Integrable cost γ)
    (hpoint : ∀ ω, (∫ x : ℝ, ‖f ω x‖) ≤ C * cost ω) :
    (∫ x : ℝ, ‖∫ ω : Ω, f ω x ∂γ‖) ≤ C * ∫ ω : Ω, cost ω ∂γ := by
  calc
    (∫ x : ℝ, ‖∫ ω : Ω, f ω x ∂γ‖)
        ≤ ∫ ω : Ω, ∫ x : ℝ, ‖f ω x‖ ∂volume ∂γ :=
      integral_norm_integral_le_integral_integral_norm γ hf
    _ ≤ ∫ ω : Ω, C * cost ω ∂γ := by
      apply integral_mono hf.norm.integral_prod_left (hcost.const_mul C)
      exact fun ω ↦ hpoint ω
    _ = C * ∫ ω : Ω, cost ω ∂γ := integral_const_mul C cost

/-- One-dimensional non-Gaussian smoothing bound over an arbitrary coupling measure.

The measure `γ` may later be instantiated by any coupling of two laws.  Joint integrability of the
kernel-difference integrand is stated explicitly, while its pointwise translation estimate is
proved from `K'`.  The right-hand side is the expected coupling cost, hence taking an infimum over
couplings yields the usual Wasserstein consequence once that interface is connected. -/
theorem integral_norm_coupledKernelDifference_le
    [CompleteSpace E] (γ : Measure (ℝ × ℝ)) [SFinite γ] {K K' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt K (K' x) x) (hK' : Continuous K')
    (hK'int : Integrable K') (α : ℝ)
    (hjoint : Integrable
      (Function.uncurry fun (p : ℝ × ℝ) (x : ℝ) ↦
        K (x - α * p.1) - K (x - α * p.2))
      (γ.prod volume))
    (hcost : Integrable (fun p : ℝ × ℝ ↦ |p.1 - p.2|) γ) :
    (∫ x : ℝ, ‖∫ p : ℝ × ℝ,
        (K (x - α * p.1) - K (x - α * p.2)) ∂γ‖) ≤
      (∫ x : ℝ, ‖K' x‖) * (|α| * ∫ p : ℝ × ℝ, |p.1 - p.2| ∂γ) := by
  let C : ℝ := ∫ x : ℝ, ‖K' x‖
  let cost : ℝ × ℝ → ℝ := fun p ↦ |α| * |p.1 - p.2|
  have hcost' : Integrable cost γ := hcost.const_mul |α|
  have hpoint (p : ℝ × ℝ) :
      (∫ x : ℝ, ‖K (x - α * p.1) - K (x - α * p.2)‖) ≤ C * cost p := by
    let shift : ℝ := α * p.1
    let step : ℝ := α * (p.2 - p.1)
    have heq :
        (∫ x : ℝ, ‖K (x - α * p.1) - K (x - α * p.2)‖) =
          ∫ u : ℝ, ‖K (u - step) - K u‖ := by
      rw [← integral_sub_right_eq_self (fun u : ℝ ↦ ‖K (u - step) - K u‖) shift]
      apply integral_congr_ae
      filter_upwards with x
      change ‖K (x - α * p.1) - K (x - α * p.2)‖ =
        ‖K ((x - shift) - step) - K (x - shift)‖
      rw [norm_sub_rev]
      congr 2
      congr 1
      simp only [shift, step]
      ring
    rw [heq]
    calc
      (∫ u : ℝ, ‖K (u - step) - K u‖) ≤ |step| * C :=
        integral_norm_kernel_sub_le hderiv hK' hK'int step
      _ = C * cost p := by
        simp only [step, cost, abs_mul, abs_sub_comm]
        ring
  have hbridge := integral_norm_integral_le_of_pointwise_l1_bound γ hjoint hcost' hpoint
  simpa only [C, cost, integral_const_mul, mul_assoc] using hbridge

omit [NormedSpace ℝ E] in
/-- For a finite coupling, integrability of the kernel itself proves (rather than assumes) joint
integrability of the two translated copies appearing in the coupling argument. -/
private theorem integrable_coupledKernelDifference
    (γ : Measure (ℝ × ℝ)) [SFinite γ] [IsFiniteMeasure γ] {K : ℝ → E}
    (hK : Continuous K) (hKint : Integrable K) (α : ℝ) :
    Integrable
      (Function.uncurry fun (p : ℝ × ℝ) (x : ℝ) ↦
        K (x - α * p.1) - K (x - α * p.2))
      (γ.prod volume) := by
  let f : (ℝ × ℝ) × ℝ → E := fun p ↦
    K (p.2 - α * p.1.1) - K (p.2 - α * p.1.2)
  have hfcont : Continuous f := by
    apply Continuous.sub
    · exact hK.comp (continuous_snd.sub (continuous_const.mul continuous_fst.fst))
    · exact hK.comp (continuous_snd.sub (continuous_const.mul continuous_fst.snd))
  change Integrable f (γ.prod volume)
  rw [integrable_prod_iff hfcont.aestronglyMeasurable]
  constructor
  · filter_upwards with p
    exact (hKint.comp_sub_right (α * p.1)).sub (hKint.comp_sub_right (α * p.2))
  · have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ ∫ x : ℝ, ‖f (p, x)‖) γ :=
      hfcont.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    have hconst : Integrable (fun _ : ℝ × ℝ ↦ 2 * ∫ x : ℝ, ‖K x‖) γ := integrable_const _
    refine hconst.mono' hmeas ?_
    filter_upwards with p
    have h₁ := (hKint.comp_sub_right (α * p.1)).norm
    have h₂ := (hKint.comp_sub_right (α * p.2)).norm
    have hsum : Integrable (fun x : ℝ ↦ ‖K (x - α * p.1)‖ + ‖K (x - α * p.2)‖) :=
      h₁.add h₂
    have hdiff : Integrable (fun x : ℝ ↦ ‖f (p, x)‖) :=
      ((hKint.comp_sub_right (α * p.1)).sub
        (hKint.comp_sub_right (α * p.2))).norm
    have hbound : (∫ x : ℝ, ‖f (p, x)‖) ≤ 2 * ∫ x : ℝ, ‖K x‖ := by
      calc
        (∫ x : ℝ, ‖f (p, x)‖)
            ≤ ∫ x : ℝ, (‖K (x - α * p.1)‖ + ‖K (x - α * p.2)‖) := by
              apply integral_mono hdiff hsum
              intro x
              exact norm_sub_le _ _
        _ = 2 * ∫ x : ℝ, ‖K x‖ := by
          rw [integral_add h₁ h₂,
            integral_sub_right_eq_self (fun x : ℝ ↦ ‖K x‖) (α * p.1),
            integral_sub_right_eq_self (fun x : ℝ ↦ ‖K x‖) (α * p.2)]
          ring
    have hnonneg : 0 ≤ ∫ x : ℝ, ‖f (p, x)‖ := integral_nonneg fun _ ↦ norm_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (mul_nonneg (by positivity) (integral_nonneg fun _ ↦ norm_nonneg _))] using hbound

/-- Fully integrability-closed one-dimensional coupling estimate for an integrable kernel.

Compared with `integral_norm_coupledKernelDifference_le`, this version assumes that `γ` is finite
(as every probability coupling is) and proves the joint-integrability premise from `K ∈ L¹`. -/
theorem integral_norm_coupledKernelDifference_le_of_integrable
    [CompleteSpace E] (γ : Measure (ℝ × ℝ)) [SFinite γ] [IsFiniteMeasure γ]
    {K K' : ℝ → E} (hKint : Integrable K)
    (hderiv : ∀ x, HasDerivAt K (K' x) x) (hK' : Continuous K')
    (hK'int : Integrable K') (α : ℝ)
    (hcost : Integrable (fun p : ℝ × ℝ ↦ |p.1 - p.2|) γ) :
    (∫ x : ℝ, ‖∫ p : ℝ × ℝ,
        (K (x - α * p.1) - K (x - α * p.2)) ∂γ‖) ≤
      (∫ x : ℝ, ‖K' x‖) * (|α| * ∫ p : ℝ × ℝ, |p.1 - p.2| ∂γ) := by
  have hK : Continuous K := continuous_iff_continuousAt.2 fun x ↦ (hderiv x).continuousAt
  exact integral_norm_coupledKernelDifference_le γ hderiv hK' hK'int α
    (integrable_coupledKernelDifference γ hK hKint α) hcost

end CouplingBridge

end CFG.Smoothing
