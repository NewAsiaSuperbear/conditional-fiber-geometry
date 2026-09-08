import CFG.Smoothing.KernelTranslation

open MeasureTheory Set
open scoped Interval

namespace CFG.Smoothing

section FiniteDimensional

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise domination of a translated finite-dimensional kernel difference by the integral of
its directional derivative along the joining segment.

This is the `ι → ℝ` analogue of `norm_kernel_sub_le_intervalIntegral_norm`, obtained by applying
the one-dimensional result to the unit-speed affine parameterization `t ↦ x - t • h`.  The
derivative is the Fréchet derivative `K'` applied to the direction `h`. -/
theorem norm_kernel_sub_le_intervalIntegral_norm_fderiv [CompleteSpace E]
    {K : (ι → ℝ) → E} {K' : (ι → ℝ) → (ι → ℝ) →L[ℝ] E}
    (hderiv : ∀ x, HasFDerivAt K (K' x) x) (hK' : Continuous K') (x h : ι → ℝ) :
    ‖K (x - h) - K x‖ ≤ ∫ t in (0 : ℝ)..1, ‖(K' (x - t • h)) h‖ := by
  have hpath : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ ↦ K (x - s • h)) (-(K' (x - t • h) h)) t := by
    intro t
    have haff : HasDerivAt (fun s : ℝ ↦ x - s • h) (-h) t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_sub x
    have hc := (hderiv (x - t • h)).comp_hasDerivAt t haff
    have happ : (K' (x - t • h)) (-h) = -(K' (x - t • h) h) := by simp
    rw [happ] at hc
    exact hc
  have hcont : Continuous fun t : ℝ ↦ -(K' (x - t • h) h) :=
    ((hK'.comp (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply
      continuous_const).neg
  have h1d := norm_kernel_sub_le_intervalIntegral_norm (E := E)
    (K := fun s : ℝ ↦ K (x - s • h)) (K' := fun s : ℝ ↦ -(K' (x - s • h) h)) hpath hcont 0 (-1)
  simpa using h1d

/-- The two-variable derivative majorant used in the Tonelli/Fubini step is integrable. -/
private theorem integrable_segmentDerivApply {K' : (ι → ℝ) → (ι → ℝ) →L[ℝ] E}
    (hK'int : Integrable K') (hK' : Continuous K') (h : ι → ℝ) :
    Integrable (Function.uncurry fun (t : ℝ) (x : ι → ℝ) ↦ ‖(K' (x - t • h)) h‖)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
  have hcont : Continuous (fun p : ℝ × (ι → ℝ) ↦ ‖(K' (p.2 - p.1 • h)) h‖) :=
    ((hK'.comp (continuous_snd.sub (continuous_fst.smul continuous_const))).clm_apply
      continuous_const).norm
  change Integrable (fun p : ℝ × (ι → ℝ) ↦ ‖(K' (p.2 - p.1 • h)) h‖)
    ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume)
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  constructor
  · filter_upwards with t
    refine ((hK'int.comp_sub_right (t • h)).norm.const_mul ‖h‖).mono' ?_ ?_
    · exact ((hK'.comp (continuous_id.sub continuous_const)).clm_apply
        continuous_const).norm.aestronglyMeasurable
    · filter_upwards with x
      simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      show ‖(K' (x - t • h)) h‖ ≤ ‖h‖ * ‖K' (x - t • h)‖
      rw [mul_comm]
      exact ContinuousLinearMap.le_opNorm (K' (x - t • h)) h
  · have heq : (fun t : ℝ ↦ ∫ x : ι → ℝ, ‖‖(K' (x - t • h)) h‖‖) =
        fun _ : ℝ ↦ ∫ x : ι → ℝ, ‖(K' x) h‖ := by
      funext t
      simpa only [norm_norm] using
        (integral_sub_right_eq_self (fun x : ι → ℝ ↦ ‖(K' x) h‖) (t • h))
    rw [heq]
    exact integrableOn_const (s := uIoc (0 : ℝ) 1) (by simp)

/-- Finite-dimensional `W^{1,1}` translation estimate, the `ι → ℝ` analogue of
`integral_norm_kernel_sub_le`.

The conclusion is derived from a genuine global Fréchet derivative and its `L¹` integrability via
the one-dimensional FTC along the segment, Tonelli/Fubini, and translation invariance of Lebesgue
measure on `ι → ℝ`; it is not postulated as a stability assumption.  This is the kernel layer of
M14 needed before instantiating the `D`-dimensional Gaussian. -/
theorem integral_norm_kernel_sub_le_fderiv [CompleteSpace E]
    {K : (ι → ℝ) → E} {K' : (ι → ℝ) → (ι → ℝ) →L[ℝ] E}
    (hderiv : ∀ x, HasFDerivAt K (K' x) x) (hK' : Continuous K')
    (hK'int : Integrable K') (h : ι → ℝ) :
    (∫ x : ι → ℝ, ‖K (x - h) - K x‖) ≤ ‖h‖ * ∫ x : ι → ℝ, ‖K' x‖ := by
  have hprod := integrable_segmentDerivApply hK'int hK' h
  have hmajorant : Integrable
      (fun x : ι → ℝ ↦ ∫ t in (0 : ℝ)..1, ‖(K' (x - t • h)) h‖) := by
    simpa only [Function.uncurry_apply_pair, intervalIntegral.integral_of_le zero_le_one,
      uIoc_of_le zero_le_one] using hprod.integral_prod_right
  have hKcont : Continuous K := continuous_iff_continuousAt.2 fun x ↦ (hderiv x).continuousAt
  have hlhs : Integrable (fun x : ι → ℝ ↦ ‖K (x - h) - K x‖) :=
    hmajorant.mono'
      ((hKcont.comp (continuous_id.sub continuous_const)).sub hKcont).norm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        simpa only [Real.norm_eq_abs, abs_norm,
          abs_of_nonneg (intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ norm_nonneg _)]
          using norm_kernel_sub_le_intervalIntegral_norm_fderiv hderiv hK' x h)
  have hinner : Integrable (fun x : ι → ℝ ↦ ‖(K' x) h‖) := by
    refine (hK'int.norm.const_mul ‖h‖).mono'
      (hK'.clm_apply continuous_const).norm.aestronglyMeasurable ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    show ‖(K' x) h‖ ≤ ‖h‖ * ‖K' x‖
    rw [mul_comm]
    exact ContinuousLinearMap.le_opNorm (K' x) h
  calc
    (∫ x : ι → ℝ, ‖K (x - h) - K x‖)
        ≤ ∫ x : ι → ℝ, ∫ t in (0 : ℝ)..1, ‖(K' (x - t • h)) h‖ := by
          apply integral_mono hlhs hmajorant
          exact fun x ↦ norm_kernel_sub_le_intervalIntegral_norm_fderiv hderiv hK' x h
    _ = ∫ t in (0 : ℝ)..1, ∫ x : ι → ℝ, ‖(K' (x - t • h)) h‖ := by
          exact (intervalIntegral_integral_swap hprod).symm
    _ = ∫ t in (0 : ℝ)..1, ∫ x : ι → ℝ, ‖(K' x) h‖ := by
          apply intervalIntegral.integral_congr
          intro t _
          exact integral_sub_right_eq_self (fun x : ι → ℝ ↦ ‖(K' x) h‖) (t • h)
    _ = ∫ x : ι → ℝ, ‖(K' x) h‖ := by simp
    _ ≤ ∫ x : ι → ℝ, ‖h‖ * ‖K' x‖ := by
          apply integral_mono hinner (hK'int.norm.const_mul ‖h‖)
          intro x
          show ‖(K' x) h‖ ≤ ‖h‖ * ‖K' x‖
          rw [mul_comm]
          exact ContinuousLinearMap.le_opNorm (K' x) h
    _ = ‖h‖ * ∫ x : ι → ℝ, ‖K' x‖ := integral_const_mul ‖h‖ _

/-- The spec's formulation of M14 with a uniform derivative bound: if the `L¹` norm of the
derivative is at most `c`, every translation `h` moves the kernel by at most `c * ‖h‖` in `L¹`. -/
theorem integral_norm_kernel_sub_le_fderiv_of_bound [CompleteSpace E]
    {K : (ι → ℝ) → E} {K' : (ι → ℝ) → (ι → ℝ) →L[ℝ] E}
    (hderiv : ∀ x, HasFDerivAt K (K' x) x) (hK' : Continuous K')
    (hK'int : Integrable K') {c : ℝ} (hc : (∫ x : ι → ℝ, ‖K' x‖) ≤ c) (h : ι → ℝ) :
    (∫ x : ι → ℝ, ‖K (x - h) - K x‖) ≤ c * ‖h‖ := by
  calc
    (∫ x : ι → ℝ, ‖K (x - h) - K x‖) ≤ ‖h‖ * ∫ x : ι → ℝ, ‖K' x‖ :=
      integral_norm_kernel_sub_le_fderiv hderiv hK' hK'int h
    _ ≤ ‖h‖ * c := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ = c * ‖h‖ := mul_comm _ _

end FiniteDimensional

section CouplingBridgeGeneral

variable {Ω αm : Type*} [MeasurableSpace Ω] [MeasurableSpace αm]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The analytic bridge behind the coupling argument, with the second variable ranging over an
arbitrary `SFinite` measure space rather than `ℝ` with Lebesgue measure: averaging a jointly
integrable family cannot increase its `L¹` norm.  This generalizes
`integral_norm_integral_le_integral_integral_norm`. -/
theorem integral_norm_integral_le_integral_integral_norm_sfinite (γ : Measure Ω) [SFinite γ]
    {ν : Measure αm} [SFinite ν] {f : Ω → αm → E}
    (hf : Integrable (Function.uncurry f) (γ.prod ν)) :
    (∫ x : αm, ‖∫ ω : Ω, f ω x ∂γ‖ ∂ν) ≤ ∫ ω : Ω, ∫ x : αm, ‖f ω x‖ ∂ν ∂γ := by
  have hleft : Integrable (fun x : αm ↦ ‖∫ ω : Ω, f ω x ∂γ‖) ν :=
    hf.integral_prod_right.norm
  have hright : Integrable (fun x : αm ↦ ∫ ω : Ω, ‖f ω x‖ ∂γ) ν :=
    hf.norm.integral_prod_right
  calc
    (∫ x : αm, ‖∫ ω : Ω, f ω x ∂γ‖ ∂ν)
        ≤ ∫ x : αm, ∫ ω : Ω, ‖f ω x‖ ∂γ ∂ν := by
          apply integral_mono hleft hright
          intro x
          exact norm_integral_le_integral_norm _
    _ = ∫ ω : Ω, ∫ x : αm, ‖f ω x‖ ∂ν ∂γ :=
      (integral_integral_swap hf.norm).symm

/-- A coupling-style consequence of the preceding bridge over an arbitrary `SFinite` second
factor.  The pointwise transportation cost bound is integrated here; it is not assumed as an `L¹`
bound on the averaged mixture. -/
theorem integral_norm_integral_le_of_pointwise_l1_bound_sfinite (γ : Measure Ω) [SFinite γ]
    {ν : Measure αm} [SFinite ν] {f : Ω → αm → E} {cost : Ω → ℝ} {C : ℝ}
    (hf : Integrable (Function.uncurry f) (γ.prod ν))
    (hcost : Integrable cost γ)
    (hpoint : ∀ ω, (∫ x : αm, ‖f ω x‖ ∂ν) ≤ C * cost ω) :
    (∫ x : αm, ‖∫ ω : Ω, f ω x ∂γ‖ ∂ν) ≤ C * ∫ ω : Ω, cost ω ∂γ := by
  calc
    (∫ x : αm, ‖∫ ω : Ω, f ω x ∂γ‖ ∂ν)
        ≤ ∫ ω : Ω, ∫ x : αm, ‖f ω x‖ ∂ν ∂γ :=
      integral_norm_integral_le_integral_integral_norm_sfinite γ hf
    _ ≤ ∫ ω : Ω, C * cost ω ∂γ := by
      apply integral_mono hf.norm.integral_prod_left (hcost.const_mul C)
      exact fun ω ↦ hpoint ω
    _ = C * ∫ ω : Ω, cost ω ∂γ := integral_const_mul C cost

end CouplingBridgeGeneral

section FiniteDimensionalCoupling

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- For a finite coupling, integrability of the kernel itself proves (rather than assumes) joint
integrability of the two translated copies appearing in the finite-dimensional coupling
argument. -/
private theorem integrable_coupledKernelDifference_fderiv
    (γ : Measure ((ι → ℝ) × (ι → ℝ))) [SFinite γ] [IsFiniteMeasure γ] {K : (ι → ℝ) → E}
    (hK : Continuous K) (hKint : Integrable K) (α : ℝ) :
    Integrable
      (Function.uncurry fun (p : (ι → ℝ) × (ι → ℝ)) (x : ι → ℝ) ↦
        K (x - α • p.1) - K (x - α • p.2))
      (γ.prod volume) := by
  let f : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) → E := fun p ↦
    K (p.2 - α • p.1.1) - K (p.2 - α • p.1.2)
  have hfcont : Continuous f := by
    apply Continuous.sub
    · exact hK.comp (continuous_snd.sub (continuous_fst.fst.const_smul α))
    · exact hK.comp (continuous_snd.sub (continuous_fst.snd.const_smul α))
  change Integrable f (γ.prod volume)
  rw [integrable_prod_iff hfcont.aestronglyMeasurable]
  constructor
  · filter_upwards with p
    exact (hKint.comp_sub_right (α • p.1)).sub (hKint.comp_sub_right (α • p.2))
  · have hmeas : AEStronglyMeasurable (fun p : (ι → ℝ) × (ι → ℝ) ↦ ∫ x : ι → ℝ, ‖f (p, x)‖) γ :=
      hfcont.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    have hconst : Integrable (fun _ : (ι → ℝ) × (ι → ℝ) ↦ 2 * ∫ x : ι → ℝ, ‖K x‖) γ :=
      integrable_const _
    refine hconst.mono' hmeas ?_
    filter_upwards with p
    have h₁ := (hKint.comp_sub_right (α • p.1)).norm
    have h₂ := (hKint.comp_sub_right (α • p.2)).norm
    have hsum : Integrable (fun x : ι → ℝ ↦ ‖K (x - α • p.1)‖ + ‖K (x - α • p.2)‖) :=
      h₁.add h₂
    have hdiff : Integrable (fun x : ι → ℝ ↦ ‖f (p, x)‖) :=
      ((hKint.comp_sub_right (α • p.1)).sub
        (hKint.comp_sub_right (α • p.2))).norm
    have hbound : (∫ x : ι → ℝ, ‖f (p, x)‖) ≤ 2 * ∫ x : ι → ℝ, ‖K x‖ := by
      calc
        (∫ x : ι → ℝ, ‖f (p, x)‖)
            ≤ ∫ x : ι → ℝ, (‖K (x - α • p.1)‖ + ‖K (x - α • p.2)‖) := by
              apply integral_mono hdiff hsum
              intro x
              exact norm_sub_le _ _
        _ = 2 * ∫ x : ι → ℝ, ‖K x‖ := by
          rw [integral_add h₁ h₂,
            integral_sub_right_eq_self (fun x : ι → ℝ ↦ ‖K x‖) (α • p.1),
            integral_sub_right_eq_self (fun x : ι → ℝ ↦ ‖K x‖) (α • p.2)]
          ring
    have hnonneg : 0 ≤ ∫ x : ι → ℝ, ‖f (p, x)‖ := integral_nonneg fun _ ↦ norm_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (mul_nonneg (by positivity) (integral_nonneg fun _ ↦ norm_nonneg _))]
      using hbound

/-- Finite-dimensional non-Gaussian smoothing bound over an arbitrary coupling measure.

The measure `γ` may later be instantiated by any coupling of two laws on `ι → ℝ`.  Joint
integrability of the kernel-difference integrand is proved from `K ∈ L¹` and finiteness of `γ`;
the pointwise translation estimate is proved from `K'` via `integral_norm_kernel_sub_le_fderiv`.
The right-hand side is the expected coupling cost (Wasserstein direction `‖p.1 - p.2‖`), hence
taking an infimum over couplings yields the usual Wasserstein consequence once that interface is
connected.  No case split on `α` is needed: for `α = 0` both sides vanish by the same proof. -/
theorem integral_norm_coupledKernelDifference_le_fderiv
    [CompleteSpace E] (γ : Measure ((ι → ℝ) × (ι → ℝ))) [SFinite γ] [IsFiniteMeasure γ]
    {K : (ι → ℝ) → E} {K' : (ι → ℝ) → (ι → ℝ) →L[ℝ] E} (hKint : Integrable K)
    (hderiv : ∀ x, HasFDerivAt K (K' x) x) (hK' : Continuous K')
    (hK'int : Integrable K') (α : ℝ)
    (hcost : Integrable (fun p : (ι → ℝ) × (ι → ℝ) ↦ ‖p.1 - p.2‖) γ) :
    (∫ x : ι → ℝ, ‖∫ p : (ι → ℝ) × (ι → ℝ),
        (K (x - α • p.1) - K (x - α • p.2)) ∂γ‖) ≤
      (∫ x : ι → ℝ, ‖K' x‖) * (|α| * ∫ p : (ι → ℝ) × (ι → ℝ), ‖p.1 - p.2‖ ∂γ) := by
  let C : ℝ := ∫ x : ι → ℝ, ‖K' x‖
  let cost : (ι → ℝ) × (ι → ℝ) → ℝ := fun p ↦ |α| * ‖p.1 - p.2‖
  have hcost' : Integrable cost γ := hcost.const_mul |α|
  have hpoint (p : (ι → ℝ) × (ι → ℝ)) :
      (∫ x : ι → ℝ, ‖K (x - α • p.1) - K (x - α • p.2)‖) ≤ C * cost p := by
    let shift : ι → ℝ := α • p.1
    let step : ι → ℝ := α • (p.2 - p.1)
    have heq :
        (∫ x : ι → ℝ, ‖K (x - α • p.1) - K (x - α • p.2)‖) =
          ∫ u : ι → ℝ, ‖K (u - step) - K u‖ := by
      rw [← integral_sub_right_eq_self (fun u : ι → ℝ ↦ ‖K (u - step) - K u‖) shift]
      apply integral_congr_ae
      filter_upwards with x
      change ‖K (x - α • p.1) - K (x - α • p.2)‖ =
        ‖K ((x - shift) - step) - K (x - shift)‖
      rw [norm_sub_rev]
      congr 2
      congr 1
      simp only [shift, step, smul_sub]
      module
    rw [heq]
    calc
      (∫ u : ι → ℝ, ‖K (u - step) - K u‖) ≤ ‖step‖ * C :=
        integral_norm_kernel_sub_le_fderiv hderiv hK' hK'int step
      _ = C * cost p := by
        simp only [step, cost, norm_smul, Real.norm_eq_abs, norm_sub_rev]
        ring
  have hjoint : Integrable
      (Function.uncurry fun (p : (ι → ℝ) × (ι → ℝ)) (x : ι → ℝ) ↦
        K (x - α • p.1) - K (x - α • p.2))
      (γ.prod volume) :=
    integrable_coupledKernelDifference_fderiv γ
      (continuous_iff_continuousAt.2 fun x ↦ (hderiv x).continuousAt) hKint α
  have hbridge := integral_norm_integral_le_of_pointwise_l1_bound_sfinite γ hjoint hcost' hpoint
  simpa only [C, cost, integral_const_mul, mul_assoc] using hbridge

end FiniteDimensionalCoupling

end CFG.Smoothing
