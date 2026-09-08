import CFG.Statistics.ExchangeableRank
import CFG.Statistics.IIDExchangeable

/-!
# Continuous rank interface (general probability measures)

This file deliberately keeps the law on `ι → α` as a genuine `Measure`.
It does not turn a continuous law into a PMF.  The finite-valued rank map is
the only object converted to a finite distribution.

The exchangeability and a.e. no-ties hypotheses are pushed through a finite
partition/counting argument for measures, yielding a uniform finite-valued
rank law.  Real-valued iid specialization is included at the end.
-/

namespace CFG.Statistics

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

variable {ι α : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [LinearOrder α]
  [MeasurableSpace α]

/- The law-level versions of the hypotheses in `ExchangeableRank`. -/

def ExchangeableMeasure (ν : Measure (ι → α)) : Prop :=
  ∀ σ : Equiv.Perm ι, ν.map (reindex σ) = ν

def NoTiesAE (ν : Measure (ι → α)) : Prop :=
  ∀ᵐ x ∂ν, Function.Injective x

def RankMeasurable (i : ι) : Prop :=
  Measurable (fun x : ι → α => coordinateRank x i)

omit [Nonempty ι] in
theorem exchangeableMeasure_map_coordinateRank_eq
    {ν : Measure (ι → α)} (hν : ExchangeableMeasure ν)
    {i j : ι} (hri : RankMeasurable (α := α) i)
    (hσ : Measurable (reindex (α := α) (Equiv.swap i j))) :
    ν.map (fun x => coordinateRank x i) =
      ν.map (fun x => coordinateRank x j) := by
  classical
  let σ : Equiv.Perm ι := Equiv.swap i j
  calc
    ν.map (fun x => coordinateRank x i) =
        (ν.map (reindex σ)).map (fun x => coordinateRank x i) := by
      rw [hν σ]
    _ = ν.map ((fun x => coordinateRank x i) ∘ reindex σ) := by
      exact Measure.map_map hri hσ
    _ = ν.map (fun x => coordinateRank x j) := by
      congr 1
      funext x
      change coordinateRank (reindex σ x) i = coordinateRank x j
      rw [coordinateRank_reindex]
      exact congrArg (coordinateRank x) (Equiv.swap_apply_left i j)

omit [Nonempty ι] [DecidableEq ι] [MeasurableSpace α] in
theorem coordinateRank_bijective_of_injective {x : ι → α}
    (hx : Function.Injective x) :
    Function.Bijective (coordinateRank x) := by
  exact (Fintype.bijective_iff_injective_and_card (coordinateRank x)).2
    ⟨coordinateRank_injective hx, by simp⟩

omit [Nonempty ι] [DecidableEq ι] in
theorem ae_coordinateRank_surjective (ν : Measure (ι → α))
    (hNoTies : NoTiesAE ν) :
    ∀ᵐ x ∂ν, Function.Surjective (coordinateRank x) := by
  filter_upwards [hNoTies] with x hx
  exact (coordinateRank_bijective_of_injective hx).2

omit [Nonempty ι] in
theorem ae_rank_indicator_sum_eq_one
    (ν : Measure (ι → α)) (hNoTies : NoTiesAE ν)
    (k : Fin (Fintype.card ι)) :
    (fun x : ι → α => ∑ i, if coordinateRank x i = k then (1 : ℝ≥0∞) else 0)
      =ᵐ[ν] (fun _ => 1) := by
  filter_upwards [hNoTies] with x hx
  obtain ⟨j, hj⟩ := (coordinateRank_bijective_of_injective hx).2 k
  have hi : ∀ i : ι, coordinateRank x i = k ↔ i = j := by
    intro i
    constructor
    · intro hik
      apply coordinateRank_injective hx
      exact hik.trans hj.symm
    · intro hij
      rw [hij]
      exact hj
  simp_rw [hi]
  simp

omit [Nonempty ι] in
theorem rank_event_mass_sum_eq_one
    (ν : Measure (ι → α)) [IsProbabilityMeasure ν]
    (hNoTies : NoTiesAE ν)
    (hRank : ∀ i : ι, Measurable (fun x : ι → α => coordinateRank x i))
    (k : Fin (Fintype.card ι)) :
    ∑ i, ν {x : ι → α | coordinateRank x i = k} = 1 := by
  classical
  have hA : ∀ i : ι, MeasurableSet {x : ι → α | coordinateRank x i = k} := by
    intro i
    exact (measurableSet_singleton k).preimage (hRank i)
  have hterm : ∀ i : ι,
      Measurable (fun x : ι → α =>
        if coordinateRank x i = k then (1 : ℝ≥0∞) else 0) := by
    intro i
    exact Measurable.ite (hA i) measurable_const measurable_const
  have hmass : ∀ i : ι,
      (∫⁻ x : ι → α, if coordinateRank x i = k then (1 : ℝ≥0∞) else 0 ∂ν) =
        ν {x : ι → α | coordinateRank x i = k} := by
    intro i
    have heq : (fun x : ι → α =>
        if coordinateRank x i = k then (1 : ℝ≥0∞) else 0) =
        Set.indicator {x : ι → α | coordinateRank x i = k} 1 := by
      funext x
      by_cases hx : coordinateRank x i = k <;> simp [Set.indicator, hx]
    rw [heq, lintegral_indicator_one (hA i)]
  calc
    ∑ i, ν {x : ι → α | coordinateRank x i = k} =
        ∑ i, ∫⁻ x : ι → α,
          if coordinateRank x i = k then (1 : ℝ≥0∞) else 0 ∂ν := by
      exact Finset.sum_congr rfl (fun i _ => (hmass i).symm)
    _ = ∫⁻ x : ι → α, ∑ i,
          if coordinateRank x i = k then (1 : ℝ≥0∞) else 0 ∂ν := by
      symm
      exact lintegral_finsetSum (Finset.univ : Finset ι)
        (fun i _ => hterm i)
    _ = ∫⁻ _ : ι → α, 1 ∂ν :=
      lintegral_congr_ae (ae_rank_indicator_sum_eq_one ν hNoTies k)
    _ = 1 := by simp

omit [Nonempty ι] in
theorem exchangeableMeasure_rank_event_eq
    {ν : Measure (ι → α)} (hν : ExchangeableMeasure ν)
    {i j : ι} (k : Fin (Fintype.card ι))
    (hRank : ∀ q : ι, Measurable (fun x : ι → α => coordinateRank x q))
    (hσ : Measurable (reindex (α := α) (Equiv.swap i j))) :
    ν {x : ι → α | coordinateRank x i = k} =
      ν {x : ι → α | coordinateRank x j = k} := by
  have hm := exchangeableMeasure_map_coordinateRank_eq hν (hRank i) hσ
  calc
    ν {x : ι → α | coordinateRank x i = k} =
        (ν.map (fun x => coordinateRank x i)) {k} := by
      rw [Measure.map_apply (hRank i) (measurableSet_singleton k)]
      rfl
    _ = (ν.map (fun x => coordinateRank x j)) {k} := by rw [hm]
    _ = ν {x : ι → α | coordinateRank x j = k} := by
      rw [Measure.map_apply (hRank j) (measurableSet_singleton k)]
      rfl

theorem continuousRank_event_mass_eq_inv_card
    (ν : Measure (ι → α)) [IsProbabilityMeasure ν]
    (hν : ExchangeableMeasure ν) (hNoTies : NoTiesAE ν)
    (truth : ι)
    (hRank : ∀ q : ι, Measurable (fun x : ι → α => coordinateRank x q))
    (hReindex : ∀ σ : Equiv.Perm ι,
      Measurable (reindex (α := α) σ))
    (k : Fin (Fintype.card ι)) :
    ν {x : ι → α | coordinateRank x truth = k} =
      1 / (Fintype.card ι : ℝ≥0∞) := by
  classical
  have hsum := rank_event_mass_sum_eq_one ν hNoTies hRank k
  have heq : (∑ i, ν {x : ι → α | coordinateRank x i = k}) =
      (Fintype.card ι : ℝ≥0∞) *
        ν {x : ι → α | coordinateRank x truth = k} := by
    calc
      ∑ i, ν {x : ι → α | coordinateRank x i = k} =
          ∑ i, ν {x : ι → α | coordinateRank x truth = k} := by
        apply Finset.sum_congr rfl
        intro i hi
        exact exchangeableMeasure_rank_event_eq hν k hRank (hReindex (Equiv.swap i truth))
      _ = (Fintype.card ι : ℝ≥0∞) *
          ν {x : ι → α | coordinateRank x truth = k} := by
        simp
  have hmul : (Fintype.card ι : ℝ≥0∞) *
      ν {x : ι → α | coordinateRank x truth = k} = 1 := by
    rw [← heq, hsum]
  apply (ENNReal.eq_div_iff
    (by positivity)
    (by simp)).2
  exact hmul

theorem continuousRank_uniform
    (ν : Measure (ι → α)) [IsProbabilityMeasure ν]
    (hν : ExchangeableMeasure ν) (hNoTies : NoTiesAE ν)
    (truth : ι)
    (hRank : ∀ q : ι, Measurable (fun x : ι → α => coordinateRank x q))
    (hReindex : ∀ σ : Equiv.Perm ι,
      Measurable (reindex (α := α) σ)) :
    ν.map (fun x => coordinateRank x truth) =
      (PMF.uniformOfFintype (Fin (Fintype.card ι))).toMeasure := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (hRank truth) (measurableSet_singleton k)]
  have hset : (fun x : ι → α => coordinateRank x truth) ⁻¹' ({k} : Set _ ) =
      {x : ι → α | coordinateRank x truth = k} := by
    ext x
    rfl
  rw [hset]
  rw [continuousRank_event_mass_eq_inv_card ν hν hNoTies truth hRank hReindex k]
  simp [PMF.uniformOfFintype_apply]

omit [Nonempty ι] [DecidableEq ι] in
theorem measurable_rankNat_of_measurableSet_lt
    (hLt : MeasurableSet {p : α × α | p.1 < p.2}) (i : ι) :
    Measurable (fun x : ι → α => rankNat x i) := by
  classical
  have hterm : ∀ j : ι,
      Measurable (fun x : ι → α => if x j < x i then 1 else 0) := by
    intro j
    apply Measurable.ite
    · change MeasurableSet
        ((fun x : ι → α => (x j, x i)) ⁻¹' {p : α × α | p.1 < p.2})
      exact hLt.preimage ((measurable_pi_apply j).prodMk (measurable_pi_apply i))
    · fun_prop
    · fun_prop
  have hs := Finset.measurable_fun_sum (s := (Finset.univ : Finset ι))
      (fun j _ => hterm j)
  have heq : (fun x : ι → α => rankNat x i) =
      (fun x => ∑ j, if x j < x i then 1 else 0) := by
    funext x
    unfold rankNat
    exact Finset.card_filter (fun j => x j < x i) Finset.univ
  rw [heq]
  exact hs

omit [DecidableEq ι] in
theorem measurable_coordinateRank_of_measurableSet_lt
    (hLt : MeasurableSet {p : α × α | p.1 < p.2}) (i : ι) :
    Measurable (fun x : ι → α => coordinateRank x i) := by
  let f : ℕ → Fin (Fintype.card ι) := fun n =>
    if h : n < Fintype.card ι then ⟨n, h⟩ else ⟨0, Fintype.card_pos⟩
  have hf : Measurable f := measurable_of_countable f
  have hr := measurable_rankNat_of_measurableSet_lt hLt i
  have hcomp : Measurable (f ∘ fun x : ι → α => rankNat x i) :=
    hf.comp hr
  have heq : f ∘ (fun x : ι → α => rankNat x i) =
      (fun x : ι → α => coordinateRank x i) := by
    funext x
    apply Fin.ext
    rw [coordinateRank_val]
    simp only [Function.comp_apply, f]
    rw [dite_eq_left (rankNat_lt_card x i)]
  rw [← heq]
  exact hcomp

/-! IID laws satisfy the law-level exchangeability condition.  The map
measurability is supplied explicitly because arbitrary measurable spaces do
not make comparison-based rank maps measurable automatically. -/
omit [Nonempty ι] [DecidableEq ι] [LinearOrder α] in
theorem iidPi_exchangeableMeasure
    (μ : Measure α) [IsProbabilityMeasure μ] :
    ExchangeableMeasure (Measure.pi fun _ : ι => μ) := by
  classical
  intro σ
  exact iidPi_reindex_eq μ σ

omit [Nonempty ι] [DecidableEq ι] [LinearOrder α] in
theorem iidPi_noTiesAE
    [MeasurableEq α] (μ : Measure α) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    NoTiesAE (Measure.pi fun _ : ι => μ) :=
  iidPi_ae_injective μ

theorem iidPi_continuousRank_uniform
    (μ : Measure α) [IsProbabilityMeasure μ] [MeasurableEq α]
    [NullSingletonClass μ]
    (hLt : MeasurableSet {p : α × α | p.1 < p.2})
    (truth : ι) :
    (Measure.pi (fun _ : ι => μ)).map
        (fun x => coordinateRank x truth) =
      (PMF.uniformOfFintype (Fin (Fintype.card ι))).toMeasure := by
  let hRank : ∀ q : ι, Measurable (fun x : ι → α => coordinateRank x q) :=
    fun q => measurable_coordinateRank_of_measurableSet_lt hLt q
  have hReindex : ∀ σ : Equiv.Perm ι,
      Measurable (reindex (α := α) σ) := by
    intro σ
    let e : (ι → α) ≃ᵐ (ι → α) :=
      MeasurableEquiv.piCongrLeft (fun _ : ι => α) σ.symm
    have he : ⇑e = reindex σ := by
      ext x i
      dsimp [e]
      rw [MeasurableEquiv.coe_piCongrLeft]
      change (Equiv.piCongrLeft (fun _ : ι => α) σ.symm x) i = x (σ i)
      conv_lhs => rw [← Equiv.symm_apply_apply σ i]
      rw [Equiv.piCongrLeft_apply_apply]
    rw [← he]
    exact e.measurable
  exact continuousRank_uniform (Measure.pi (fun _ : ι => μ))
    (iidPi_exchangeableMeasure μ) (iidPi_noTiesAE μ) truth hRank hReindex

theorem iidPi_real_continuousRank_uniform
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (truth : ι) :
    (Measure.pi (fun _ : ι => μ)).map
        (fun x => coordinateRank x truth) =
      (PMF.uniformOfFintype (Fin (Fintype.card ι))).toMeasure := by
  apply iidPi_continuousRank_uniform μ
    ((isOpen_lt continuous_fst continuous_snd).measurableSet) truth

end
end CFG.Statistics
