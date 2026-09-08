import CFG.Statistics.ProductNoTies
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory

namespace CFG.Statistics

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

theorem iidPairMarginal (μ : Measure α) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j) :
    (Measure.pi fun _ : ι ↦ μ).map (fun x : ι → α ↦ (x i, x j)) = μ.prod μ := by
  classical
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.map_apply (by fun_prop) (hs.prod ht)]
  let f : ι → Set α := fun k ↦ if k = i then s else if k = j then t else Set.univ
  have hpre :
      (fun x : ι → α ↦ (x i, x j)) ⁻¹' (s ×ˢ t) =
        ((({i, j} : Finset ι) : Set ι).pi f) := by
    ext x
    simp [f, Ne.symm hij]
  rw [hpre, Measure.pi_pi_finset]
  simp [f, hij, Ne.symm hij]

variable [MeasurableEq α]

theorem iidPi_ae_ne (μ : Measure α) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (i j : ι) (hij : i ≠ j) :
    ∀ᵐ x ∂(Measure.pi fun _ : ι ↦ μ), x i ≠ x j := by
  rw [ae_iff]
  have hset :
      {x : ι → α | ¬x i ≠ x j} =
        (fun x : ι → α ↦ (x i, x j)) ⁻¹' {p : α × α | p.1 = p.2} := by
    ext x
    simp
  rw [hset, ← Measure.map_apply (by fun_prop) (measurableSet_prod_diagonal (α := α)),
    iidPairMarginal μ i j hij]
  exact prod_diagonal_eq_zero μ

theorem iidPi_ae_injective (μ : Measure α) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∀ᵐ x ∂(Measure.pi fun _ : ι ↦ μ), Function.Injective x := by
  classical
  have hpairs :
      ∀ᵐ x ∂(Measure.pi fun _ : ι ↦ μ),
        ∀ p : ι × ι, p.1 ≠ p.2 → x p.1 ≠ x p.2 := by
    rw [ae_all_iff]
    intro p
    by_cases hp : p.1 ≠ p.2
    · filter_upwards [iidPi_ae_ne μ p.1 p.2 hp] with x hx
      exact fun _ ↦ hx
    · exact Filter.Eventually.of_forall fun _ h ↦ (hp h).elim
  filter_upwards [hpairs] with x hx
  intro i j heq
  by_contra hij
  exact hx (i, j) hij heq

end CFG.Statistics
