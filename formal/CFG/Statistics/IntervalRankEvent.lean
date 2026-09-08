import CFG.Statistics.ContinuousRank
import CFG.Statistics.RankInterval

namespace CFG.Statistics

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

def withinSampleExtrema {n : ℕ} (x : Fin (n + 1) → ℝ) : Prop :=
  (∃ i : Fin (n + 1), i ≠ 0 ∧ x i ≤ x 0) ∧
    (∃ j : Fin (n + 1), j ≠ 0 ∧ x 0 ≤ x j)

def truthInteriorRank (n : ℕ) (x : Fin (n + 1) → ℝ) : Prop :=
  0 < rankNat x 0 ∧ rankNat x 0 < n

theorem withinSampleExtrema_iff_truthInteriorRank
    {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) :
    withinSampleExtrema x ↔ truthInteriorRank n x := by
  let s : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun i => x i < x 0)
  have h0 : (0 : Fin (n + 1)) ∉ s := by
    simp [s]
  have hcard : s.card = rankNat x 0 := rfl
  constructor
  · rintro ⟨⟨i, hi0, hle⟩, ⟨j, hj0, hge⟩⟩
    have hil : x i < x 0 := lt_of_le_of_ne hle
      (Ne.symm (hx.ne (Ne.symm hi0)))
    have hjl : x 0 < x j := lt_of_le_of_ne hge (hx.ne (Ne.symm hj0))
    constructor
    · rw [← hcard]
      exact Finset.card_pos.mpr ⟨i, by simp [s, hil]⟩
    · rw [← hcard]
      have hsub : s ⊂ Finset.univ.erase j := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro q hq
          have hq' : x q < x 0 := by simpa [s] using hq
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
          intro hqj
          subst q
          exact (not_lt_of_ge hge) hq'
        · intro heq
          have hjmem : j ∈ s := by
            have hz : (0 : Fin (n + 1)) ∈ Finset.univ.erase j :=
              Finset.mem_erase.mpr ⟨Ne.symm hj0, Finset.mem_univ _⟩
            have hz' : (0 : Fin (n + 1)) ∈ s := heq.symm ▸ hz
            exact False.elim (h0 hz')
          have : j ∈ s := hjmem
          have hthis : x j < x 0 := by simpa [s] using this
          exact (not_lt_of_ge hge) hthis
      have hc : s.card < (Finset.univ.erase j).card := Finset.card_lt_card hsub
      simpa using hc
  · rintro ⟨hrpos, hrlt⟩
    have hi : ∃ i, i ≠ (0 : Fin (n + 1)) ∧ x i < x 0 := by
      rw [← hcard] at hrpos
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hrpos
      have hi' : x i < x 0 := by simpa [s] using hi
      refine ⟨i, ?_, hi'⟩
      intro hi0
      subst i
      exact (lt_irrefl _) hi'
    have hj : ∃ j, j ≠ (0 : Fin (n + 1)) ∧ x 0 < x j := by
      by_contra hn
      push Not at hn
      have hsub : Finset.univ.erase 0 ⊆ s := by
        intro j hj
        have hj0 : j ≠ (0 : Fin (n + 1)) := (Finset.mem_erase.mp hj).1
        have hne : x 0 ≠ x j := hx.ne (Ne.symm hj0)
        have hlt : x j < x 0 := lt_of_le_of_ne (hn j hj0) (Ne.symm hne)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      have hc : (Finset.univ.erase (0 : Fin (n + 1))).card ≤ s.card :=
        Finset.card_le_card hsub
      rw [hcard] at hc
      simp at hc
      omega
    obtain ⟨i, hi0, hil⟩ := hi
    obtain ⟨j, hj0, hjl⟩ := hj
    exact ⟨⟨i, hi0, hil.le⟩, ⟨j, hj0, hjl.le⟩⟩

theorem truthRank_mem_interiorRank_iff
    {n : ℕ} {x : Fin (n + 1) → ℝ} :
    truthRank n x ∈ Set.range (interiorRank n) ↔
      truthInteriorRank n x := by
  constructor
  · rintro ⟨j, hj⟩
    constructor
    · have hjv := congrArg Fin.val hj
      simp [truthRank_val, interiorRank] at hjv
      omega
    · have hjv := congrArg Fin.val hj
      simp [truthRank_val, interiorRank] at hjv
      omega
  · rintro ⟨hpos, hlt⟩
    let j : Fin (n - 1) := ⟨rankNat x 0 - 1, by omega⟩
    refine ⟨j, ?_⟩
    apply Fin.ext
    simp [j, truthRank_val, interiorRank]
    omega

theorem continuous_withinSampleExtrema_probability
    (n : ℕ) (ν : Measure (Fin (n + 1) → ℝ)) [IsProbabilityMeasure ν]
    (hNoTies : NoTiesAE ν)
    (hRank : Measurable (fun x : Fin (n + 1) → ℝ => coordinateRank x 0))
    (hUniform : ν.map (fun x : Fin (n + 1) → ℝ => coordinateRank x 0) =
      (PMF.uniformOfFintype (Fin (Fintype.card (Fin (n + 1))))).toMeasure) :
    ν {x | withinSampleExtrema x} =
      ((n - 1 : ℕ) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) := by
  classical
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    (Fin.castOrderIso (Fintype.card_fin (n + 1))).toEquiv
  have he : Measurable e := measurable_of_finite e
  have htruth : Measurable (fun x : Fin (n + 1) → ℝ => truthRank n x) := by
    exact he.comp hRank
  have hunifTruth : ν.map (truthRank n) =
      (PMF.uniformOfFintype (Fin (n + 1))).toMeasure := by
    calc
      ν.map (truthRank n) =
          (ν.map (fun x : Fin (n + 1) → ℝ => coordinateRank x 0)).map e := by
        rw [Measure.map_map he hRank]
        congr 1
      _ = ((PMF.uniformOfFintype
          (Fin (Fintype.card (Fin (n + 1))))).map e).toMeasure := by
        rw [hUniform, PMF.toMeasure_map e _ he]
      _ = (PMF.uniformOfFintype (Fin (n + 1))).toMeasure := by
        rw [uniformOfFintype_map_of_bijective e e.bijective]
  have hevent :
      {x : Fin (n + 1) → ℝ | withinSampleExtrema x} =ᵐ[ν]
        {x | truthRank n x ∈ Set.range (interiorRank n)} := by
    filter_upwards [hNoTies] with x hx
    rw [withinSampleExtrema_iff_truthInteriorRank hx,
      truthRank_mem_interiorRank_iff]
  calc
    ν {x | withinSampleExtrema x} =
        ν {x | truthRank n x ∈ Set.range (interiorRank n)} :=
      measure_congr hevent
    _ = (ν.map (truthRank n)) (Set.range (interiorRank n)) := by
      have hs : MeasurableSet (Set.range (interiorRank n)) :=
        (Set.finite_range (interiorRank n)).measurableSet
      rw [Measure.map_apply htruth hs]
      rfl
    _ = (PMF.uniformOfFintype (Fin (n + 1))).toOuterMeasure
        (Set.range (interiorRank n)) := by
      rw [hunifTruth, PMF.toMeasure_apply_eq_toOuterMeasure]
    _ = ((n - 1 : ℕ) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) :=
      uniformRank_interior_probability n

theorem iidPi_real_withinSampleExtrema_probability
    (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    (Measure.pi (fun _ : Fin (n + 1) => μ))
        {x | withinSampleExtrema x} =
      ((n - 1 : ℕ) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) := by
  apply continuous_withinSampleExtrema_probability n
    (Measure.pi (fun _ : Fin (n + 1) => μ))
    (iidPi_ae_injective μ)
    (measurable_coordinateRank_of_measurableSet_lt
      (ι := Fin (n + 1)) (α := ℝ)
      ((isOpen_lt continuous_fst continuous_snd).measurableSet) 0)
    (iidPi_real_continuousRank_uniform μ 0)

theorem iidPi_real_withinSampleExtrema_sixteen_probability
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    (Measure.pi (fun _ : Fin 17 => μ))
        {x | withinSampleExtrema x} = (15 : ℝ≥0∞) / 17 := by
  simpa using iidPi_real_withinSampleExtrema_probability 16 μ

end
end CFG.Statistics
