import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Finite-cover algebra

These results use mathlib's genuine metric covering certificates and covering
numbers. In particular, `Metric.externalCoveringNumber` has external centers,
radius in `ℝ≥0`, and value in `ℕ∞`.
-/

namespace CFG

open Set
open scoped ENNReal NNReal

namespace Covering

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
variable {ε K : ℝ≥0} {s t C D : Set X} {f : X → Y}

theorem externalCoveringNumber_union_le :
    Metric.externalCoveringNumber ε (s ∪ t) ≤
      Metric.externalCoveringNumber ε s + Metric.externalCoveringNumber ε t := by
  simp only [Metric.externalCoveringNumber]
  apply ENat.le_iInf₂_add_iInf₂
  intro C hCs D hDt
  exact (Metric.IsCover.externalCoveringNumber_le_encard (hCs.union hDt)).trans
    (Set.encard_union_le C D)

/-- External covering numbers are subadditive over a genuinely finite family. -/
theorem externalCoveringNumber_biUnion_finset_le
    {ι : Type*} (I : Finset ι) (S : ι → Set X) :
    Metric.externalCoveringNumber ε (⋃ i ∈ I, S i) ≤
      ∑ i ∈ I, Metric.externalCoveringNumber ε (S i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      rw [Finset.sum_insert ha]
      calc
        Metric.externalCoveringNumber ε (⋃ i ∈ insert a I, S i) =
            Metric.externalCoveringNumber ε (S a ∪ ⋃ i ∈ I, S i) := by
              congr 1
              simp
        _ ≤ Metric.externalCoveringNumber ε (S a) +
              Metric.externalCoveringNumber ε (⋃ i ∈ I, S i) :=
            externalCoveringNumber_union_le
        _ ≤ Metric.externalCoveringNumber ε (S a) +
              ∑ i ∈ I, Metric.externalCoveringNumber ε (S i) :=
            add_le_add_right ih _

theorem isCover_image_lipschitzOn (hcover : Metric.IsCover ε s C) (hcenters : C ⊆ s)
    (hf : LipschitzOnWith K f s) : Metric.IsCover (K * ε) (f '' s) (f '' C) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc, hdist⟩ := hcover hx
  refine ⟨f c, ⟨c, hc, rfl⟩, ?_⟩
  dsimp at hdist ⊢
  grw [hf hx (hcenters hc), hdist]

theorem externalCoveringNumber_image_le_coveringNumber
    (hf : LipschitzOnWith K f s) :
    Metric.externalCoveringNumber (K * ε) (f '' s) ≤ Metric.coveringNumber ε s := by
  simp only [Metric.coveringNumber, le_iInf_iff]
  intro C hCs hcover
  exact (Metric.IsCover.externalCoveringNumber_le_encard
      (isCover_image_lipschitzOn hcover hCs hf)).trans
    (Set.encard_image_le f C)

theorem coveringNumber_image_le_coveringNumber
    (hf : LipschitzOnWith K f s) :
    Metric.coveringNumber (K * ε) (f '' s) ≤ Metric.coveringNumber ε s := by
  simp only [Metric.coveringNumber, le_iInf_iff]
  intro C hCs hcover
  exact (Metric.IsCover.coveringNumber_le_encard (Set.image_mono hCs)
      (isCover_image_lipschitzOn hcover hCs hf)).trans (Set.encard_image_le f C)

/-- A finite union of images of a common-Lipschitz family is covered by the
sum of the covering numbers of its parameter domains. -/
theorem externalCoveringNumber_biUnion_image_le
    {ι : Type*} (I : Finset ι) (U : ι → Set X) (ψ : ι → X → Y)
    (hψ : ∀ i ∈ I, LipschitzOnWith K (ψ i) (U i)) :
    Metric.externalCoveringNumber (K * ε) (⋃ i ∈ I, ψ i '' U i) ≤
      ∑ i ∈ I, Metric.coveringNumber ε (U i) := by
  calc
    Metric.externalCoveringNumber (K * ε) (⋃ i ∈ I, ψ i '' U i) ≤
        ∑ i ∈ I, Metric.externalCoveringNumber (K * ε) (ψ i '' U i) :=
      externalCoveringNumber_biUnion_finset_le I (fun i => ψ i '' U i)
    _ ≤ ∑ i ∈ I, Metric.coveringNumber ε (U i) := by
      exact Finset.sum_le_sum fun i hi =>
        externalCoveringNumber_image_le_coveringNumber (hψ i hi)

section Compact

variable {Z : Type*} [PseudoMetricSpace Z] {A : Set Z}

/-- Every compact set has a finite internal cover at each positive radius, so
its covering number is not `⊤`. -/
theorem coveringNumber_ne_top_of_isCompact
    (hA : IsCompact A) {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.coveringNumber ε A ≠ ⊤ := by
  have hεpos : (0 : ℝ) < ε := by exact_mod_cast (pos_iff_ne_zero.mpr hε)
  obtain ⟨t, htA, htfin, htcover⟩ := hA.finite_cover_balls hεpos
  have hcover : Metric.IsCover ε A t := by
    intro x hx
    have hxcover := htcover hx
    simp only [Set.mem_iUnion] at hxcover
    obtain ⟨c, hc, hball⟩ := hxcover
    refine ⟨c, hc, ?_⟩
    simpa [edist_dist] using le_of_lt hball
  have hle := hcover.coveringNumber_le_encard htA
  intro htop
  rw [htop] at hle
  exact (not_le_of_gt (Set.encard_lt_top_iff.mpr htfin)) hle

end Compact

end Covering

end CFG
