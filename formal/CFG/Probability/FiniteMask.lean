import Mathlib.MeasureTheory.Function.Piecewise
import CFG.Probability.ConditionalSupport

/-!
# Finite and countable dependent mask families

Concrete tagged observations for a countable family of masks.  The measurable
space on the dependent sum is Mathlib's coproduct measurable space.
-/

open MeasureTheory Set Filter MeasurableSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace CFG.Probability

variable {M : Type*} (q : M → ℕ)

/-- Each summand injection into Mathlib's measurable coproduct is measurable. -/
theorem measurable_sigmaMk (m : M) :
    Measurable (@Sigma.mk M (fun m => CFG.Euc (q m)) m) := by
  apply Measurable.of_comap_le
  refine le_trans (MeasurableSpace.comap_mono ?_) MeasurableSpace.comap_map_le
  exact iInf_le (fun i =>
    (inferInstance : MeasurableSpace (CFG.Euc (q i))).map
      (@Sigma.mk M (fun m => CFG.Euc (q m)) i)) m

/-- A function out of a measurable coproduct is measurable when all of its
restrictions to the summands are measurable. -/
theorem measurable_sigma_elim {Y : Type*} [MeasurableSpace Y]
    (f : (Σ m, CFG.Euc (q m)) → Y)
    (hf : ∀ m, Measurable (f ∘ @Sigma.mk M (fun m => CFG.Euc (q m)) m)) :
    Measurable f := by
  apply Measurable.of_comap_le
  change _ ≤ ⨅ m, (inferInstance : MeasurableSpace (CFG.Euc (q m))).map
    (@Sigma.mk M (fun m => CFG.Euc (q m)) m)
  rw [le_iInf_iff]
  intro m
  rw [← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
  exact (hf m).comap_le

/-- The range of every summand injection is measurable when the index type is
countable. -/
theorem measurableSet_range_sigmaMk [Countable M] (m : M) :
    MeasurableSet (range (@Sigma.mk M (fun m => CFG.Euc (q m)) m)) := by
  change MeasurableSet[⨅ i,
    (inferInstance : MeasurableSpace (CFG.Euc (q i))).map
      (@Sigma.mk M (fun m => CFG.Euc (q m)) i)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  change MeasurableSet
    ((@Sigma.mk M (fun m => CFG.Euc (q m)) i) ⁻¹'
      range (@Sigma.mk M (fun m => CFG.Euc (q m)) m))
  by_cases h : i = m
  · subst i
    have heq :
        ((@Sigma.mk M (fun m => CFG.Euc (q m)) m) ⁻¹'
          range (@Sigma.mk M (fun m => CFG.Euc (q m)) m)) = Set.univ := by
      ext z
      simp only [mem_preimage, mem_range, mem_univ, iff_true]
      exact ⟨z, rfl⟩
    rw [heq]
    exact MeasurableSet.univ
  · have heq :
        ((@Sigma.mk M (fun m => CFG.Euc (q m)) i) ⁻¹'
          range (@Sigma.mk M (fun m => CFG.Euc (q m)) m)) = ∅ := by
      ext z
      simp only [mem_preimage, mem_range, mem_empty_iff_false, iff_false]
      rintro ⟨w, hw⟩
      exact h (congrArg Sigma.fst hw).symm
    rw [heq]
    exact MeasurableSet.empty

/-- Extract the value from one chosen summand, returning zero on the other
summands. -/
noncomputable def sigmaValue (m : M) :
    (Σ i, CFG.Euc (q i)) → CFG.Euc (q m) := by
  classical
  exact fun z => if h : z.1 = m then
    (congrArg (fun j => CFG.Euc (q j)) h).mp z.2 else 0

@[simp]
theorem sigmaValue_mk (m : M) (z : CFG.Euc (q m)) :
    sigmaValue q m ⟨m, z⟩ = z := by
  simp [sigmaValue]

/-- The chosen-summand extractor is measurable. -/
theorem measurable_sigmaValue (m : M) : Measurable (sigmaValue q m) := by
  apply measurable_sigma_elim q
  intro i
  classical
  by_cases h : i = m
  · have hc : Measurable (fun z : CFG.Euc (q i) =>
        (congrArg (fun j => CFG.Euc (q j)) h).mp z) :=
      Measurable.eq_mp (fun j => CFG.Euc (q j)) h measurable_id
    simpa [sigmaValue, Function.comp_def, h] using hc
  · simp [sigmaValue, Function.comp_def, h]

/-- The fibers of the mask projection form an indexed partition. -/
def maskPartition {d : ℕ} :
    IndexedPartition (fun m : M => {p : CFG.Euc d × M | p.2 = m}) where
  eq_of_mem := by
    intro p i j hi hj
    exact hi.symm.trans hj
  some m := (0, m)
  some_mem m := rfl
  index p := p.2
  mem_index p := rfl

/-- The actual tagged observation, retaining the mask and placing its
observation in the corresponding dependent summand. -/
def taggedObservation {d : ℕ} (H : (m : M) → CFG.Euc d → CFG.Euc (q m)) :
    CFG.Euc d × M → Σ m, CFG.Euc (q m) :=
  fun p => ⟨p.2, H p.2 p.1⟩

/-- For a countable measurable mask type with measurable singletons,
componentwise measurable observations assemble to a measurable tagged map. -/
theorem measurable_taggedObservation [Countable M] [MeasurableSpace M]
    [MeasurableSingletonClass M] {d : ℕ}
    (H : (m : M) → CFG.Euc d → CFG.Euc (q m))
    (hH : ∀ m, Measurable (H m)) :
    Measurable (taggedObservation q H) := by
  let P := maskPartition (M := M) (d := d)
  let f : M → CFG.Euc d × M → Σ m, CFG.Euc (q m) :=
    fun m p => ⟨m, H m p.1⟩
  have hpiece : Measurable (P.piecewise f) := by
    apply P.measurable_piecewise
    · intro m
      exact (measurableSet_singleton m).preimage measurable_snd
    · intro m
      exact (measurable_sigmaMk q m).comp ((hH m).comp measurable_fst)
  convert hpiece using 1
  funext p
  simp [P, f, maskPartition, taggedObservation, IndexedPartition.piecewise_apply]

/-- The relation whose section at a tagged observation is the corresponding
restricted fiber. -/
def taggedFiberRelation {d : ℕ}
    (E : M → Set (CFG.Euc d))
    (H : (m : M) → CFG.Euc d → CFG.Euc (q m)) :
    Set ((Σ m, CFG.Euc (q m)) × CFG.Euc d) :=
  {p | p.2 ∈ E p.1.1 ∧ H p.1.1 p.2 = p.1.2}

/-- For a countable mask family, measurable admissible sets and
componentwise measurable observations make the concrete tagged fiber
relation measurable automatically. -/
theorem measurableSet_taggedFiberRelation [Countable M] {d : ℕ}
    (E : M → Set (CFG.Euc d)) (hE : ∀ m, MeasurableSet (E m))
    (H : (m : M) → CFG.Euc d → CFG.Euc (q m))
    (hH : ∀ m, Measurable (H m)) :
    MeasurableSet (taggedFiberRelation q E H) := by
  let Rm : M → Set ((Σ m, CFG.Euc (q m)) × CFG.Euc d) := fun m =>
    {p | p.1 ∈ range (@Sigma.mk M (fun i => CFG.Euc (q i)) m) ∧
      p.2 ∈ E m ∧ H m p.2 = sigmaValue q m p.1}
  have hRm : ∀ m, MeasurableSet (Rm m) := by
    intro m
    exact ((measurableSet_range_sigmaMk q m).preimage measurable_fst).inter
      (((hE m).preimage measurable_snd).inter
        (((hH m).comp measurable_snd).eq
          ((measurable_sigmaValue q m).comp measurable_fst)).setOf)
  rw [show taggedFiberRelation q E H = ⋃ m, Rm m by
    ext p
    constructor
    · intro hp
      refine mem_iUnion.2 ⟨p.1.1, ?_⟩
      rcases p with ⟨⟨m, z⟩, v⟩
      simpa [taggedFiberRelation, Rm] using hp
    · intro hp
      rcases mem_iUnion.1 hp with ⟨m, hm⟩
      rcases p with ⟨⟨i, z⟩, v⟩
      have him : i = m := by
        rcases hm.1 with ⟨w, hw⟩
        exact (congrArg Sigma.fst hw).symm
      subst i
      simpa [taggedFiberRelation, Rm] using hm]
  exact MeasurableSet.iUnion hRm

/-- Conditional concentration for the actual tagged observation of a
countable family of possibly dependent masks.  Unlike the general interface
theorem, this statement has no separate tagged-map or relation-measurability
hypotheses. -/
theorem ae_condDistrib_countableDependentRandomMask_fiber_measure_eq_one
    [Countable M] [MeasurableSpace M] [MeasurableSingletonClass M]
    {d : ℕ} (μ : Measure (CFG.Euc d × M)) [IsFiniteMeasure μ]
    (E : M → Set (CFG.Euc d)) (hE : ∀ m, MeasurableSet (E m))
    (H : (m : M) → CFG.Euc d → CFG.Euc (q m))
    (hH : ∀ m, Measurable (H m))
    (hμE : ∀ᵐ p ∂μ, p.1 ∈ E p.2) :
    ∀ᵐ mz ∂μ.map (taggedObservation q H),
      ProbabilityTheory.condDistrib Prod.fst (taggedObservation q H) μ mz
        (CFG.fiber (E mz.1) (H mz.1) mz.2) = 1 := by
  apply ae_condDistrib_dependentRandomMask_fiber_measure_eq_one q μ E H
    (taggedObservation q H)
    (measurable_taggedObservation q H hH).aemeasurable
    (Filter.Eventually.of_forall fun _ => rfl)
    (measurableSet_taggedFiberRelation q E hE H hH)
    hμE

/-- Pushing the preceding conditional law through a continuous complete-data
map gives image-fiber support containment.  The joint parameter-mask law is
arbitrary; in particular, this theorem assumes no independence. -/
theorem ae_support_map_condDistrib_countableDependentRandomMask_subset_imageFiber
    [Countable M] [MeasurableSpace M] [MeasurableSingletonClass M]
    {d D : ℕ} (μ : Measure (CFG.Euc d × M)) [IsFiniteMeasure μ]
    (E : M → Set (CFG.Euc d)) (hE : ∀ m, IsCompact (E m))
    (F : CFG.Euc d → CFG.Euc D) (hF : Continuous F)
    (H : (m : M) → CFG.Euc d → CFG.Euc (q m))
    (hH : ∀ m, Continuous (H m))
    (hμE : ∀ᵐ p ∂μ, p.1 ∈ E p.2) :
    ∀ᵐ mz ∂μ.map (taggedObservation q H),
      (Measure.map F
        (ProbabilityTheory.condDistrib Prod.fst (taggedObservation q H) μ mz)).support ⊆
        CFG.imageFiber (E mz.1) F (H mz.1) mz.2 := by
  apply ae_support_map_condDistrib_dependentRandomMask_subset_imageFiber q μ E hE F hF H hH
    (taggedObservation q H)
    (measurable_taggedObservation q H fun m => (hH m).measurable).aemeasurable
    (Filter.Eventually.of_forall fun _ => rfl)
    (measurableSet_taggedFiberRelation q E (fun m => (hE m).measurableSet) H
      fun m => (hH m).measurable)
    hμE

end CFG.Probability
