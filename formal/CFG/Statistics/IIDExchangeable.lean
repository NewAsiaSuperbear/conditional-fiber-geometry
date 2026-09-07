import CFG.Statistics.ExchangeableRank
import CFG.Statistics.IIDNoTies

open MeasureTheory
open scoped ENNReal BigOperators

namespace CFG.Statistics

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

/-- Permuting the coordinates of an iid product measure leaves the measure
unchanged: pushing the product measure `Measure.pi (fun _ : ι => μ)` forward
along `reindex σ` returns the same product measure. -/
theorem iidPi_reindex_eq (μ : Measure α) [IsProbabilityMeasure μ]
    (σ : Equiv.Perm ι) :
    (Measure.pi fun _ : ι => μ).map (reindex σ) = Measure.pi fun _ : ι => μ := by
  classical
  let e : (ι → α) ≃ᵐ (ι → α) := MeasurableEquiv.piCongrLeft (fun _ : ι => α) σ.symm
  have hmp : MeasurePreserving e (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) := by
    simpa using measurePreserving_piCongrLeft (α := fun _ : ι => α)
      (μ := fun _ : ι => μ) σ.symm
  have hcoe : ⇑e = reindex σ := by
    ext x i
    dsimp [e]
    rw [MeasurableEquiv.coe_piCongrLeft]
    change (Equiv.piCongrLeft (fun _ : ι => α) σ.symm x) i = x (σ i)
    conv_lhs => rw [← Equiv.symm_apply_apply σ i]
    rw [Equiv.piCongrLeft_apply_apply]
  rw [← hcoe]
  exact hmp.map_eq

end CFG.Statistics
