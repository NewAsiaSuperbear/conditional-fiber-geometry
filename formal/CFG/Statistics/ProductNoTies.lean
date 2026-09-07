import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

namespace CFG.Statistics

/-- The diagonal `{p : α × α | p.1 = p.2}` is measurable. -/
theorem measurableSet_prod_diagonal {α : Type*} [MeasurableSpace α] [MeasurableEq α] :
    MeasurableSet {p : α × α | p.1 = p.2} :=
  measurableSet_eq_fun measurable_fst measurable_snd

/-- For an atomless probability measure, the product measure of the diagonal
is zero. -/
theorem prod_diagonal_eq_zero {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    (μ : Measure α) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    (μ.prod μ) {p : α × α | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_prod_diagonal (α := α))]
  have hpre : ∀ x : α, Prod.mk x ⁻¹' {p : α × α | p.1 = p.2} = {x} := by
    intro x
    ext y
    simp [Set.mem_singleton_iff, eq_comm]
  simp_rw [hpre, measure_singleton]
  simp

/-- Consequently, `μ.prod μ`-almost every pair has distinct components. -/
theorem ae_prod_fst_ne_snd {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    (μ : Measure α) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ p ∂(μ.prod μ), p.1 ≠ p.2 := by
  rw [ae_iff]
  have hset : {p : α × α | ¬p.1 ≠ p.2} = {p : α × α | p.1 = p.2} := by
    ext p
    simp
  rw [hset]
  exact prod_diagonal_eq_zero μ

end CFG.Statistics
