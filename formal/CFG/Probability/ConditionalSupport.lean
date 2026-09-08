import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Measure.Support
import CFG.Basic.Fiber

/-!
# Conditional kernels inherit almost-sure relations

If a joint measure is concentrated on a measurable relation, then its
conditional kernel is almost surely concentrated on the corresponding
sections of that relation.  This is the measure-theoretic core of the
conditional-fiber support statement.
-/

open MeasureTheory Set Filter MeasurableSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace CFG.Probability

variable {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]

/-- A Markov kernel assigns mass one to a fixed measurable set whenever the
integral of the mass of its complement vanishes. -/
theorem ae_kernel_measure_eq_one_of_lintegral_compl_eq_zero
    (ν : Measure Z) (κ : ProbabilityTheory.Kernel Z V)
    [ProbabilityTheory.IsMarkovKernel κ]
    {A : Set V} (hA : MeasurableSet A)
    (hzero : ∫⁻ z, κ z Aᶜ ∂ν = 0) :
    ∀ᵐ z ∂ν, κ z A = 1 := by
  have hcompl : (fun z => κ z Aᶜ) =ᵐ[ν] 0 :=
    (lintegral_eq_zero_iff (κ.measurable_coe hA.compl)).mp hzero
  filter_upwards [hcompl] with z hz
  have hz' : κ z Aᶜ = 0 := by simpa using hz
  exact (prob_compl_eq_zero_iff hA).mp hz'

/-- If a measure-kernel product is concentrated on a measurable relation,
then almost every kernel measure is concentrated on its relation section. -/
theorem ae_kernel_section_measure_eq_one
    (ν : Measure Z) [SFinite ν] (κ : ProbabilityTheory.Kernel Z V)
    [ProbabilityTheory.IsMarkovKernel κ]
    {R : Set (Z × V)} (hR : MeasurableSet R)
    (hconcentrated : (ν ⊗ₘ κ) Rᶜ = 0) :
    ∀ᵐ z ∂ν, κ z {v | (z, v) ∈ R} = 1 := by
  have hzero : ∫⁻ z, κ z {v | (z, v) ∈ Rᶜ} ∂ν = 0 := by
    rw [Measure.compProd_apply hR.compl] at hconcentrated
    have hsections :
        (fun z => κ z {v | (z, v) ∈ Rᶜ}) =
          fun z => κ z (Prod.mk z ⁻¹' Rᶜ) := by
      funext z
      congr 1
    rw [hsections]
    exact hconcentrated
  have hcompl :
      (fun z => κ z {v | (z, v) ∈ Rᶜ}) =ᵐ[ν] 0 :=
    (lintegral_eq_zero_iff
      (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hR.compl)).mp hzero
  filter_upwards [hcompl] with z hz
  have hsection : MeasurableSet {v | (z, v) ∈ R} := measurable_prodMk_left hR
  have hsection_compl : {v | (z, v) ∈ Rᶜ} = {v | (z, v) ∈ R}ᶜ := by
    ext v
    simp
  have hz' : κ z {v | (z, v) ∈ R}ᶜ = 0 := by
    rw [← hsection_compl]
    simpa using hz
  exact (prob_compl_eq_zero_iff hsection).mp hz'

variable [StandardBorelSpace V] [Nonempty V]

/-- A finite joint measure concentrated on a measurable relation has a
conditional kernel concentrated almost surely on the corresponding fibers. -/
theorem ae_condKernel_section_measure_eq_one
    (ρ : Measure (Z × V)) [IsFiniteMeasure ρ]
    {R : Set (Z × V)} (hR : MeasurableSet R)
    (hconcentrated : ρ Rᶜ = 0) :
    ∀ᵐ z ∂ρ.fst, ρ.condKernel z {v | (z, v) ∈ R} = 1 := by
  apply ae_kernel_section_measure_eq_one ρ.fst ρ.condKernel hR
  rwa [ρ.disintegrate ρ.condKernel]

/-- A regular conditional distribution inherits every measurable relation
which holds almost surely for the conditioned and output random variables. -/
theorem ae_condDistrib_relation_section_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Z) (Y : Ω → V)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {R : Set (Z × V)} (hR : MeasurableSet R)
    (hrel : ∀ᵐ ω ∂μ, (X ω, Y ω) ∈ R) :
    ∀ᵐ z ∂μ.map X,
      ProbabilityTheory.condDistrib Y X μ z {v | (z, v) ∈ R} = 1 := by
  apply ae_kernel_section_measure_eq_one (μ.map X)
    (ProbabilityTheory.condDistrib Y X μ) hR
  rw [ProbabilityTheory.compProd_map_condDistrib hX hY]
  rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) hR.compl]
  exact mem_ae_iff.mp hrel

/-- The regular conditional law of a Euclidean parameter given a continuous
observation is almost surely concentrated on the corresponding level set. -/
theorem ae_condDistrib_levelSet_measure_eq_one
    {d q : ℕ} (μ : Measure (CFG.Euc d)) [IsFiniteMeasure μ]
    (H : CFG.Euc d → CFG.Euc q) (hH : Continuous H) :
    ∀ᵐ z ∂μ.map H,
      ProbabilityTheory.condDistrib id H μ z {v | H v = z} = 1 := by
  let R : Set (CFG.Euc q × CFG.Euc d) := {p | H p.2 = p.1}
  have hR : MeasurableSet R :=
    (isClosed_eq (hH.comp continuous_snd) continuous_fst).measurableSet
  have hconcentrated :
      ((μ.map H) ⊗ₘ ProbabilityTheory.condDistrib id H μ) Rᶜ = 0 := by
    rw [ProbabilityTheory.compProd_map_condDistrib hH.measurable.aemeasurable
      measurable_id.aemeasurable]
    rw [Measure.map_apply (hH.measurable.prodMk measurable_id) hR.compl]
    simp [R]
  simpa [R] using
    (ae_kernel_section_measure_eq_one (μ.map H)
      (ProbabilityTheory.condDistrib id H μ) hR hconcentrated)

/-- If the prior is concentrated on an admissible measurable set `E`, then
the regular conditional law is almost surely concentrated on the restricted
fiber `E ∩ H ⁻¹' {z}`. -/
theorem ae_condDistrib_fiber_measure_eq_one
    {d q : ℕ} (μ : Measure (CFG.Euc d)) [IsFiniteMeasure μ]
    (E : Set (CFG.Euc d)) (hE : MeasurableSet E)
    (H : CFG.Euc d → CFG.Euc q) (hH : Continuous H)
    (hμE : μ Eᶜ = 0) :
    ∀ᵐ z ∂μ.map H,
      ProbabilityTheory.condDistrib id H μ z (CFG.fiber E H z) = 1 := by
  let R : Set (CFG.Euc q × CFG.Euc d) := {p | p.2 ∈ E ∧ H p.2 = p.1}
  have hR : MeasurableSet R := by
    exact (hE.preimage measurable_snd).inter
      (isClosed_eq (hH.comp continuous_snd) continuous_fst).measurableSet
  have hconcentrated :
      ((μ.map H) ⊗ₘ ProbabilityTheory.condDistrib id H μ) Rᶜ = 0 := by
    rw [ProbabilityTheory.compProd_map_condDistrib hH.measurable.aemeasurable
      measurable_id.aemeasurable]
    rw [Measure.map_apply (hH.measurable.prodMk measurable_id) hR.compl]
    simpa [R] using hμE
  have hsections :=
    ae_kernel_section_measure_eq_one (μ.map H)
      (ProbabilityTheory.condDistrib id H μ) hR hconcentrated
  filter_upwards [hsections] with z hz
  have heq : CFG.fiber E H z = {v | (z, v) ∈ R} := by
    ext v
    simp [R, CFG.fiber]
  rw [heq]
  exact hz

/-- Under compactness and continuity, pushing the conditional parameter law
through `F` gives a measure whose topological support is contained in the
closed image fiber. -/
theorem ae_support_map_condDistrib_subset_imageFiber
    {d D q : ℕ} (μ : Measure (CFG.Euc d)) [IsFiniteMeasure μ]
    (E : Set (CFG.Euc d)) (hE : IsCompact E)
    (F : CFG.Euc d → CFG.Euc D) (hF : Continuous F)
    (H : CFG.Euc d → CFG.Euc q) (hH : Continuous H)
    (hμE : μ Eᶜ = 0) :
    ∀ᵐ z ∂μ.map H,
      (Measure.map F (ProbabilityTheory.condDistrib id H μ z)).support ⊆
        CFG.imageFiber E F H z := by
  have hfiber := ae_condDistrib_fiber_measure_eq_one μ E hE.measurableSet H hH hμE
  filter_upwards [hfiber] with z hz
  have hcompactFiber : IsCompact (CFG.fiber E H z) :=
    CFG.isCompact_fiber hE hH
  have hclosedImage : IsClosed (CFG.imageFiber E F H z) :=
    (CFG.isCompact_imageFiber hcompactFiber hF).isClosed
  apply Measure.support_subset_of_isClosed hclosedImage
  rw [mem_ae_map_iff hF.measurable.aemeasurable hclosedImage.measurableSet]
  have hfiberMeasurable : MeasurableSet (CFG.fiber E H z) :=
    hcompactFiber.isClosed.measurableSet
  have hfiberAE : CFG.fiber E H z ∈
      ae (ProbabilityTheory.condDistrib id H μ z) :=
    (mem_ae_iff_prob_eq_one hfiberMeasurable).2 hz
  refine Filter.mem_of_superset hfiberAE ?_
  intro v hv
  exact ⟨v, hv, rfl⟩

/-- Random-mask fiber concentration for a common Euclidean observation
dimension.  The law `μ` is an arbitrary joint law of parameter and mask, so
the result makes no independence assumption.  Measurability of the tagged
relation is exposed explicitly. -/
theorem ae_condDistrib_randomMask_fiber_measure_eq_one
    {M : Type*} [MeasurableSpace M]
    {d q : ℕ} (μ : Measure (CFG.Euc d × M)) [IsFiniteMeasure μ]
    (E : M → Set (CFG.Euc d)) (H : M → CFG.Euc d → CFG.Euc q)
    (T : CFG.Euc d × M → M × CFG.Euc q)
    (hT : AEMeasurable T μ)
    (hT_def : ∀ᵐ p ∂μ, T p = (p.2, H p.2 p.1))
    (hR : MeasurableSet
      {p : (M × CFG.Euc q) × CFG.Euc d |
        p.2 ∈ E p.1.1 ∧ H p.1.1 p.2 = p.1.2})
    (hμE : ∀ᵐ p ∂μ, p.1 ∈ E p.2) :
    ∀ᵐ mz ∂μ.map T,
      ProbabilityTheory.condDistrib Prod.fst T μ mz
        (CFG.fiber (E mz.1) (H mz.1) mz.2) = 1 := by
  let R : Set ((M × CFG.Euc q) × CFG.Euc d) :=
    {p | p.2 ∈ E p.1.1 ∧ H p.1.1 p.2 = p.1.2}
  have hrel : ∀ᵐ p ∂μ, (T p, p.1) ∈ R := by
    filter_upwards [hT_def, hμE] with p hTp hpE
    simp [R, hTp, hpE]
  have hsections := ae_condDistrib_relation_section_eq_one μ T Prod.fst
    hT measurable_fst.aemeasurable hR hrel
  filter_upwards [hsections] with mz hmz
  have heq : CFG.fiber (E mz.1) (H mz.1) mz.2 = {v | (mz, v) ∈ R} := by
    ext v
    simp [CFG.fiber, R]
  rw [heq]
  exact hmz

/-- In the same dependent random-mask setting, compact admissible sets and a
continuous complete-data map turn conditional concentration into topological
support containment for almost every tagged observation. -/
theorem ae_support_map_condDistrib_randomMask_subset_imageFiber
    {M : Type*} [MeasurableSpace M]
    {d D q : ℕ} (μ : Measure (CFG.Euc d × M)) [IsFiniteMeasure μ]
    (E : M → Set (CFG.Euc d)) (hE : ∀ m, IsCompact (E m))
    (F : CFG.Euc d → CFG.Euc D) (hF : Continuous F)
    (H : M → CFG.Euc d → CFG.Euc q) (hH : ∀ m, Continuous (H m))
    (T : CFG.Euc d × M → M × CFG.Euc q)
    (hT : AEMeasurable T μ)
    (hT_def : ∀ᵐ p ∂μ, T p = (p.2, H p.2 p.1))
    (hR : MeasurableSet
      {p : (M × CFG.Euc q) × CFG.Euc d |
        p.2 ∈ E p.1.1 ∧ H p.1.1 p.2 = p.1.2})
    (hμE : ∀ᵐ p ∂μ, p.1 ∈ E p.2) :
    ∀ᵐ mz ∂μ.map T,
      (Measure.map F (ProbabilityTheory.condDistrib Prod.fst T μ mz)).support ⊆
        CFG.imageFiber (E mz.1) F (H mz.1) mz.2 := by
  have hfiber := ae_condDistrib_randomMask_fiber_measure_eq_one
    μ E H T hT hT_def hR hμE
  filter_upwards [hfiber] with mz hmz
  have hcompactFiber : IsCompact (CFG.fiber (E mz.1) (H mz.1) mz.2) :=
    CFG.isCompact_fiber (hE mz.1) (hH mz.1)
  have hclosedImage : IsClosed (CFG.imageFiber (E mz.1) F (H mz.1) mz.2) :=
    (CFG.isCompact_imageFiber hcompactFiber hF).isClosed
  apply Measure.support_subset_of_isClosed hclosedImage
  rw [mem_ae_map_iff hF.measurable.aemeasurable hclosedImage.measurableSet]
  have hfiberMeasurable : MeasurableSet (CFG.fiber (E mz.1) (H mz.1) mz.2) :=
    hcompactFiber.isClosed.measurableSet
  have hfiberAE : CFG.fiber (E mz.1) (H mz.1) mz.2 ∈
      ae (ProbabilityTheory.condDistrib Prod.fst T μ mz) :=
    (mem_ae_iff_prob_eq_one hfiberMeasurable).2 hmz
  refine Filter.mem_of_superset hfiberAE ?_
  intro v hv
  exact ⟨v, hv, rfl⟩

/-- The dependent tagged-observation version: mask `m` may have its own
dimension `q m`, and the conditioning variable lives in the measurable sigma
type `Σ m, Euc (q m)`.  The joint parameter-mask law is still arbitrary. -/
theorem ae_condDistrib_dependentRandomMask_fiber_measure_eq_one
    {M : Type*} [MeasurableSpace M] (q : M → ℕ)
    {d : ℕ} (μ : Measure (CFG.Euc d × M)) [IsFiniteMeasure μ]
    (E : M → Set (CFG.Euc d)) (H : (m : M) → CFG.Euc d → CFG.Euc (q m))
    (T : CFG.Euc d × M → Σ m, CFG.Euc (q m))
    (hT : AEMeasurable T μ)
    (hT_def : ∀ᵐ p ∂μ, T p = ⟨p.2, H p.2 p.1⟩)
    (hR : MeasurableSet
      {p : (Σ m, CFG.Euc (q m)) × CFG.Euc d |
        p.2 ∈ E p.1.1 ∧ H p.1.1 p.2 = p.1.2})
    (hμE : ∀ᵐ p ∂μ, p.1 ∈ E p.2) :
    ∀ᵐ mz ∂μ.map T,
      ProbabilityTheory.condDistrib Prod.fst T μ mz
        (CFG.fiber (E mz.1) (H mz.1) mz.2) = 1 := by
  let R : Set ((Σ m, CFG.Euc (q m)) × CFG.Euc d) :=
    {p | p.2 ∈ E p.1.1 ∧ H p.1.1 p.2 = p.1.2}
  have hrel : ∀ᵐ p ∂μ, (T p, p.1) ∈ R := by
    filter_upwards [hT_def, hμE] with p hTp hpE
    simp [R, hTp, hpE]
  have hsections := ae_condDistrib_relation_section_eq_one μ T Prod.fst
    hT measurable_fst.aemeasurable hR hrel
  filter_upwards [hsections] with mz hmz
  have heq : CFG.fiber (E mz.1) (H mz.1) mz.2 = {v | (mz, v) ∈ R} := by
    ext v
    simp [CFG.fiber, R]
  rw [heq]
  exact hmz

/-- Pushing the dependent random-mask conditional law through a continuous
complete-data map gives the corresponding almost-sure image-fiber support
containment. -/
theorem ae_support_map_condDistrib_dependentRandomMask_subset_imageFiber
    {M : Type*} [MeasurableSpace M] (q : M → ℕ)
    {d D : ℕ} (μ : Measure (CFG.Euc d × M)) [IsFiniteMeasure μ]
    (E : M → Set (CFG.Euc d)) (hE : ∀ m, IsCompact (E m))
    (F : CFG.Euc d → CFG.Euc D) (hF : Continuous F)
    (H : (m : M) → CFG.Euc d → CFG.Euc (q m)) (hH : ∀ m, Continuous (H m))
    (T : CFG.Euc d × M → Σ m, CFG.Euc (q m))
    (hT : AEMeasurable T μ)
    (hT_def : ∀ᵐ p ∂μ, T p = ⟨p.2, H p.2 p.1⟩)
    (hR : MeasurableSet
      {p : (Σ m, CFG.Euc (q m)) × CFG.Euc d |
        p.2 ∈ E p.1.1 ∧ H p.1.1 p.2 = p.1.2})
    (hμE : ∀ᵐ p ∂μ, p.1 ∈ E p.2) :
    ∀ᵐ mz ∂μ.map T,
      (Measure.map F (ProbabilityTheory.condDistrib Prod.fst T μ mz)).support ⊆
        CFG.imageFiber (E mz.1) F (H mz.1) mz.2 := by
  have hfiber := ae_condDistrib_dependentRandomMask_fiber_measure_eq_one
    q μ E H T hT hT_def hR hμE
  filter_upwards [hfiber] with mz hmz
  have hcompactFiber : IsCompact (CFG.fiber (E mz.1) (H mz.1) mz.2) :=
    CFG.isCompact_fiber (hE mz.1) (hH mz.1)
  have hclosedImage : IsClosed (CFG.imageFiber (E mz.1) F (H mz.1) mz.2) :=
    (CFG.isCompact_imageFiber hcompactFiber hF).isClosed
  apply Measure.support_subset_of_isClosed hclosedImage
  rw [mem_ae_map_iff hF.measurable.aemeasurable hclosedImage.measurableSet]
  have hfiberMeasurable : MeasurableSet (CFG.fiber (E mz.1) (H mz.1) mz.2) :=
    hcompactFiber.isClosed.measurableSet
  have hfiberAE : CFG.fiber (E mz.1) (H mz.1) mz.2 ∈
      ae (ProbabilityTheory.condDistrib Prod.fst T μ mz) :=
    (mem_ae_iff_prob_eq_one hfiberMeasurable).2 hmz
  refine Filter.mem_of_superset hfiberAE ?_
  intro v hv
  exact ⟨v, hv, rfl⟩

end CFG.Probability
