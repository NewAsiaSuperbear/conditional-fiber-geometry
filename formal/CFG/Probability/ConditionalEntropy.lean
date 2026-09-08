import CFG.Covering.ImageFiberAtlas
import CFG.Calculus.ModelRegularity
import CFG.Calculus.RankProjection
import CFG.Probability.ConditionalSupport

/-!
# Model-facing covering certificates and conditional support covering

This module closes the loop between the quantitative image-fiber covering
theory and the conditional-support theory, for the *genuine* observed map
of a `Model`:

* `Model.exists_observedImageFiber_coveringNumber_polynomial_certificate`:
  the polynomial covering certificate stated directly for a `Model`.  The
  level map is definitionally `model.observed = mask ∘ complete`, and the
  strict derivative is the genuine composite `mask ∘ B` obtained from a
  strict derivative `B` of `model.complete`.  The caller supplies no
  unrelated level map or Jacobian.
* `Model.exists_observedImageFiber_log_covering_certificate`: the
  logarithmic form, for a nonempty observed fiber.
* `Model.finite_fiber_observed_of_fullRank` and
  `Model.finite_imageFiber_observed_of_fullRank`: the `r = d` (full-rank)
  branch, in which the fiber and its image are finite sets.
* `Probability.ae_isProbabilityMeasure_condDistrib`,
  `Probability.ae_condDistrib_nonempty_fiber`: under a true probability
  prior, the conditional parameter law given the observation is almost
  surely a probability measure, and (when the prior is concentrated on `E`)
  the observed fiber is almost surely nonempty.
* `Probability.ae_condDistrib_support_polynomial_covering`: the observed
  law almost surely satisfies all three conclusions simultaneously —
  probability kernel, nonempty fiber, and a polynomial covering bound for
  the topological support of the pushed conditional law.

## Quantifier and measurability caveats (per the audit plan)

* The constant `C₀` in the almost-sure covering conclusion is a *pointwise*
  (per-observation) constant.  No measurable selection of `C₀` is claimed,
  and the pointwise bound cannot be integrated against the observed law
  without an additional uniform or measurable-envelope hypothesis.
* "Almost every" is with respect to the observed law `μ.map model.observed`,
  never with respect to Lebesgue measure on the observation space.
* A nonempty fiber conclusion is only drawn almost surely under the observed
  law. No pointwise guarantee is made on its exceptional null set, and no
  claim is made for priors not concentrated on `E`. A singleton can have zero
  mass even inside the support of a continuous observation law.
-/

open MeasureTheory Set

open scoped ENNReal NNReal

namespace CFG.Model

variable {d D q r : ℕ} (model : CFG.Model d D q)

/-- Polynomial covering certificate for the genuine observed image fiber.
The level map is `model.observed` itself, the strict derivative of the
level map is computed from `complete` and `mask`, and the rank lower bound
concerns the actual composite derivative `mask ∘ B`. -/
theorem exists_observedImageFiber_coveringNumber_polynomial_certificate
    {E : Set (Euc d)} (hcompact : IsCompact E)
    (hcomplete : Continuous model.complete) {z : Euc q}
    (B : Euc d → Euc d →L[ℝ] Euc D)
    (hstrict : ∀ v ∈ CFG.fiber E model.observed z,
      HasStrictFDerivAt model.complete (B v) v)
    (hrank : ∀ v ∈ CFG.fiber E model.observed z,
      r ≤ Module.finrank ℝ (model.mask.comp (B v)).range) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ≥0, ε ≠ 0 → (ε : ℝ) ≤ 1 →
      ∃ N : ℕ,
        Metric.externalCoveringNumber ε
            (CFG.imageFiber E model.complete model.observed z) ≤ (N : ℕ∞) ∧
          (N : ℝ) * (ε : ℝ) ^ (d - r) ≤ C₀ :=
  CFG.exists_imageFiber_coveringNumber_polynomial_certificate hcompact
    (model.continuous_observed hcomplete) (fun v => model.mask.comp (B v)) B
    (fun v hv => model.hasStrictFDerivAt_observed (hstrict v hv)) hstrict hrank

/-- Logarithmic entropy form of the observed image-fiber certificate, for a
nonempty observed fiber. -/
theorem exists_observedImageFiber_log_covering_certificate
    {E : Set (Euc d)} (hcompact : IsCompact E)
    (hcomplete : Continuous model.complete) {z : Euc q}
    (B : Euc d → Euc d →L[ℝ] Euc D)
    (hstrict : ∀ v ∈ CFG.fiber E model.observed z,
      HasStrictFDerivAt model.complete (B v) v)
    (hrank : ∀ v ∈ CFG.fiber E model.observed z,
      r ≤ Module.finrank ℝ (model.mask.comp (B v)).range)
    (hnonempty : (CFG.fiber E model.observed z).Nonempty) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ≥0, ε ≠ 0 → (ε : ℝ) ≤ 1 →
      ∃ N : ℕ,
        Metric.externalCoveringNumber ε
            (CFG.imageFiber E model.complete model.observed z) ≤ (N : ℕ∞) ∧
          0 < N ∧
          Real.log (N : ℝ) ≤ Real.log C₀ +
            ((d - r : ℕ) : ℝ) * Real.log (1 / (ε : ℝ)) :=
  CFG.exists_imageFiber_log_covering_certificate hcompact
    (model.continuous_observed hcomplete) (fun v => model.mask.comp (B v)) B
    (fun v hv => model.hasStrictFDerivAt_observed (hstrict v hv)) hstrict hrank
    hnonempty

/-- Full-rank branch: if the genuine observed derivative has rank at least
`d` at every fiber point, the observed fiber is a finite set. -/
theorem finite_fiber_observed_of_fullRank
    {E : Set (Euc d)} (hcompact : IsCompact E)
    (hcomplete : Continuous model.complete) {z : Euc q}
    (B : Euc d → Euc d →L[ℝ] Euc D)
    (hstrict : ∀ v ∈ CFG.fiber E model.observed z,
      HasStrictFDerivAt model.complete (B v) v)
    (hfull : ∀ v ∈ CFG.fiber E model.observed z,
      d ≤ Module.finrank ℝ (model.mask.comp (B v)).range) :
    (CFG.fiber E model.observed z).Finite :=
  CFG.finite_fiber_of_fullRank_strictFDeriv hcompact
    (model.continuous_observed hcomplete) (fun v => model.mask.comp (B v))
    (fun v hv => model.hasStrictFDerivAt_observed (hstrict v hv)) hfull

/-- In the full-rank branch the observed image fiber is finite as well. -/
theorem finite_imageFiber_observed_of_fullRank
    {E : Set (Euc d)} (hcompact : IsCompact E)
    (hcomplete : Continuous model.complete) {z : Euc q}
    (B : Euc d → Euc d →L[ℝ] Euc D)
    (hstrict : ∀ v ∈ CFG.fiber E model.observed z,
      HasStrictFDerivAt model.complete (B v) v)
    (hfull : ∀ v ∈ CFG.fiber E model.observed z,
      d ≤ Module.finrank ℝ (model.mask.comp (B v)).range) :
    (CFG.imageFiber E model.complete model.observed z).Finite :=
  (model.finite_fiber_observed_of_fullRank hcompact hcomplete B hstrict hfull).image
    model.complete

end CFG.Model

namespace CFG.Probability

/-- Under a true probability prior, the conditional parameter law given a
continuous observation is almost surely (in the observed law) a probability
measure. -/
theorem ae_isProbabilityMeasure_condDistrib
    {d q : ℕ} (μ : Measure (CFG.Euc d)) [IsProbabilityMeasure μ]
    (H : CFG.Euc d → CFG.Euc q) (hH : Continuous H) :
    ∀ᵐ z ∂μ.map H,
      IsProbabilityMeasure (ProbabilityTheory.condDistrib id H μ z) := by
  have h := ae_condDistrib_relation_section_eq_one μ H id
    hH.measurable.aemeasurable measurable_id.aemeasurable
    MeasurableSet.univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
  filter_upwards [h] with z hz
  refine { measure_univ := ?_ }
  exact hz

/-- If the prior is concentrated on a measurable admissible set `E`, then
for almost every observation the observed fiber inside `E` is nonempty:
the conditional law assigns it mass one, so it cannot be empty. -/
theorem ae_condDistrib_nonempty_fiber
    {d q : ℕ} (μ : Measure (CFG.Euc d)) [IsFiniteMeasure μ]
    (E : Set (CFG.Euc d)) (hE : MeasurableSet E)
    (H : CFG.Euc d → CFG.Euc q) (hH : Continuous H) (hμE : μ Eᶜ = 0) :
    ∀ᵐ z ∂μ.map H, (CFG.fiber E H z).Nonempty := by
  have hfiber := ae_condDistrib_fiber_measure_eq_one μ E hE H hH hμE
  filter_upwards [hfiber] with z hz
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne, measure_empty] at hz
  exact zero_ne_one hz

/-- The observed law almost surely satisfies the full conditional
support-covering package: the conditional parameter law is a probability
measure, the observed fiber is nonempty, and the topological support of the
pushed conditional law admits a polynomial covering certificate with the
genuine exponent `d - r`.  The constant `C₀` is pointwise in the
observation; no measurable selection or integrability is asserted. -/
theorem ae_condDistrib_support_polynomial_covering
    {d D q r : ℕ} (model : CFG.Model d D q)
    (μ : Measure (CFG.Euc d)) [IsProbabilityMeasure μ]
    {E : Set (CFG.Euc d)} (hcompact : IsCompact E) (hμE : μ Eᶜ = 0)
    (hcomplete : Continuous model.complete)
    (B : CFG.Euc d → CFG.Euc d →L[ℝ] CFG.Euc D)
    (hstrict : ∀ v ∈ E, HasStrictFDerivAt model.complete (B v) v)
    (hrank : ∀ v ∈ E, r ≤ Module.finrank ℝ (model.mask.comp (B v)).range) :
    ∀ᵐ z ∂μ.map model.observed,
      IsProbabilityMeasure (ProbabilityTheory.condDistrib id model.observed μ z) ∧
        (CFG.fiber E model.observed z).Nonempty ∧
        ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ≥0, ε ≠ 0 → (ε : ℝ) ≤ 1 →
          ∃ N : ℕ,
            Metric.externalCoveringNumber ε
                (Measure.map model.complete
                  (ProbabilityTheory.condDistrib id model.observed μ z)).support ≤
              (N : ℕ∞) ∧
            (N : ℝ) * (ε : ℝ) ^ (d - r) ≤ C₀ := by
  have hobs : Continuous model.observed := model.continuous_observed hcomplete
  have hprob := ae_isProbabilityMeasure_condDistrib μ model.observed hobs
  have hfiber :=
    ae_condDistrib_nonempty_fiber μ E hcompact.measurableSet model.observed hobs hμE
  have hsupp := ae_support_map_condDistrib_subset_imageFiber μ E hcompact
    model.complete hcomplete model.observed hobs hμE
  filter_upwards [hprob, hfiber, hsupp] with z hzprob hzfiber hzsupp
  refine ⟨hzprob, hzfiber, ?_⟩
  obtain ⟨C₀, hC₀, hbound⟩ :=
    model.exists_observedImageFiber_coveringNumber_polynomial_certificate
      hcompact hcomplete B
      (fun v hv => hstrict v hv.1) (fun v hv => hrank v hv.1)
  refine ⟨C₀, hC₀, fun ε hε hεone => ?_⟩
  obtain ⟨N, hcover, hN⟩ := hbound ε hε hεone
  exact ⟨N, (Metric.externalCoveringNumber_mono_set hzsupp).trans hcover, hN⟩

end CFG.Probability

/-!
## A concrete non-vacuous instance

The identity model on the unit closed ball: `complete = id`, `mask = id`.
At the observation `z = 0` the fiber is `{0} ∩ closedBall 0 1`, genuinely
nonempty, and the observed derivative has full rank `d`.  This instance
exercises the polynomial certificate, the finite full-rank branch, and —
with the Dirac prior at `0` — the almost-sure conditional support covering,
at the single point of the observed law.
-/

namespace CFG.Model

/-- The identity model: complete data and mask are both the identity. -/
noncomputable def identityModel (d : ℕ) : CFG.Model d d d where
  complete := id
  mask := ContinuousLinearMap.id ℝ (Euc d)

/-- The identity model has full-rank observed derivative everywhere. -/
theorem identityModel_observed_rank {d : ℕ} :
    Module.finrank ℝ
        ((identityModel d).mask.comp
          (ContinuousLinearMap.id ℝ (Euc d))).range = d := by
  have htop : ((identityModel d).mask.comp
      (ContinuousLinearMap.id ℝ (Euc d))).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨y, rfl⟩
  rw [htop, finrank_top, finrank_euclideanSpace_fin]

/-- Non-vacuity instance of the polynomial covering certificate: the
identity model on the unit closed ball at the observation `0`, with the
full-rank exponent `d - d = 0`. -/
theorem identityModel_covering_polynomial_certificate (d : ℕ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ≥0, ε ≠ 0 → (ε : ℝ) ≤ 1 →
      ∃ N : ℕ,
        Metric.externalCoveringNumber ε
            (CFG.imageFiber (Metric.closedBall 0 1) (identityModel d).complete
              (identityModel d).observed (0 : Euc d)) ≤ (N : ℕ∞) ∧
          (N : ℝ) * (ε : ℝ) ^ (d - d) ≤ C₀ := by
  apply (identityModel d).exists_observedImageFiber_coveringNumber_polynomial_certificate
    (isCompact_closedBall 0 1) continuous_id (fun _ => ContinuousLinearMap.id ℝ (Euc d))
  · intro v _
    exact hasStrictFDerivAt_id v
  · intro _ _
    exact (identityModel_observed_rank (d := d)).symm.le

/-- Non-vacuity instance of the full-rank finite branch: the identity model
fiber at `0` is finite (it is the singleton `{0}` inside the ball). -/
theorem identityModel_finite_fiber (d : ℕ) :
    (CFG.fiber (Metric.closedBall 0 1) (identityModel d).observed
      (0 : Euc d)).Finite :=
  (identityModel d).finite_fiber_observed_of_fullRank (isCompact_closedBall 0 1)
    continuous_id (fun _ => ContinuousLinearMap.id ℝ (Euc d))
    (fun v _ => hasStrictFDerivAt_id v)
    (fun _ _ => (identityModel_observed_rank (d := d)).symm.le)

end CFG.Model

namespace CFG.Probability

/-- End-to-end instance of the almost-sure conditional support covering:
the Dirac prior at the center of the unit ball for the identity model.  At
the single point of the observed law, the conditional law is a probability
measure, the fiber is nonempty, and its pushed support admits a polynomial
covering certificate. -/
theorem identityModel_condDistrib_support_polynomial_covering_dirac (d : ℕ) :
    IsProbabilityMeasure (ProbabilityTheory.condDistrib id
        (CFG.Model.identityModel d).observed (Measure.dirac 0) 0) ∧
      (CFG.fiber (Metric.closedBall 0 1) (CFG.Model.identityModel d).observed
        (0 : CFG.Euc d)).Nonempty ∧
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ≥0, ε ≠ 0 → (ε : ℝ) ≤ 1 →
        ∃ N : ℕ,
          Metric.externalCoveringNumber ε
              (Measure.map (CFG.Model.identityModel d).complete
                (ProbabilityTheory.condDistrib id
                  (CFG.Model.identityModel d).observed
                  (Measure.dirac 0) 0)).support ≤ (N : ℕ∞) ∧
            (N : ℝ) * (ε : ℝ) ^ (d - d) ≤ C₀ := by
  have h0mem : (0 : CFG.Euc d) ∈ Metric.closedBall 0 1 :=
    Metric.mem_closedBall_self zero_le_one
  have hE : (Measure.dirac (0 : CFG.Euc d)) (Metric.closedBall 0 1)ᶜ = 0 := by
    rw [Measure.dirac_apply]
    simp [Set.mem_compl_iff, h0mem]
  have h := ae_condDistrib_support_polynomial_covering (CFG.Model.identityModel d)
    (Measure.dirac (0 : CFG.Euc d)) (isCompact_closedBall 0 1) hE continuous_id
    (fun _ => ContinuousLinearMap.id ℝ (CFG.Euc d))
    (fun v _ => hasStrictFDerivAt_id v)
    (fun _ _ => (CFG.Model.identityModel_observed_rank (d := d)).symm.le)
  have hmap : (Measure.dirac (0 : CFG.Euc d)).map
      (CFG.Model.identityModel d).observed =
        Measure.dirac ((CFG.Model.identityModel d).observed 0) :=
    Measure.map_dirac' continuous_id.measurable _
  rw [hmap, ae_dirac_eq, Filter.eventually_pure] at h
  exact h

end CFG.Probability
