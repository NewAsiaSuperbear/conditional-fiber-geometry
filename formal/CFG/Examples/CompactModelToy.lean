import CFG.Covering.ImageFiberAtlas
import CFG.Basic.Model
import Mathlib.Tactic

namespace CFG.Examples

open CFG Set

noncomputable def toyCompleteCLM : Euc 3 →L[ℝ] Euc 2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun i : Fin 2 =>
      ContinuousLinearMap.proj (Fin.castLE (show 2 ≤ 3 by decide) i)) :
        (Fin 3 → ℝ) →L[ℝ] (Fin 2 → ℝ)).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap)

noncomputable def toyComplete : Euc 3 → Euc 2 := toyCompleteCLM

noncomputable def toyMask : Euc 2 →L[ℝ] Euc 1 :=
  (EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun _ : Fin 1 =>
      ContinuousLinearMap.proj (0 : Fin 2)) :
        (Fin 2 → ℝ) →L[ℝ] (Fin 1 → ℝ)).comp
      (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap)

noncomputable def toyObserved : Euc 3 → Euc 1 :=
  fun v => toyMask (toyComplete v)

noncomputable def toyModel : Model 3 2 1 :=
  ⟨toyComplete, toyMask⟩

def toyE : Set (Euc 3) := Metric.closedBall 0 1

theorem toyE_compact : IsCompact toyE :=
  isCompact_closedBall 0 1

theorem toyComplete_continuous : Continuous toyComplete :=
  toyCompleteCLM.continuous

theorem toyObserved_eq : toyModel.observed = toyObserved := by
  funext v
  rfl

noncomputable def toyDerivative : Euc 3 →L[ℝ] Euc 1 :=
  toyMask.comp toyCompleteCLM

noncomputable def toyE0 : Euc 3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => if i = 0 then 1 else 0)

theorem toyDerivative_e0_ne_zero : toyDerivative toyE0 ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Euc 1 => v 0) h
  simp [toyDerivative, toyE0, toyMask, toyCompleteCLM,
    ContinuousLinearMap.comp_apply] at h0

theorem toyDerivative_rank_one :
    1 ≤ Module.finrank ℝ (toyDerivative : Euc 3 →ₗ[ℝ] Euc 1).range := by
  apply (Submodule.one_le_finrank_iff).2
  intro hrange
  apply toyDerivative_e0_ne_zero
  have hv : toyDerivative toyE0 ∈
      (toyDerivative : Euc 3 →ₗ[ℝ] Euc 1).range := ⟨toyE0, rfl⟩
  rw [hrange] at hv
  exact (Submodule.mem_bot ℝ).mp hv

theorem toy_zero_mem_fiber :
    (0 : Euc 3) ∈ fiber toyE toyObserved (0 : Euc 1) := by
  constructor
  · exact Metric.mem_closedBall'.mpr (by simp)
  · simp [toyObserved, toyMask, toyComplete, toyCompleteCLM]
    ext i
    simp

theorem toy_polynomial_cover_certificate :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : NNReal, ε ≠ 0 → (ε : ℝ) ≤ 1 →
      ∃ N : ℕ,
        Metric.externalCoveringNumber ε
            (imageFiber toyE toyComplete toyObserved (0 : Euc 1)) ≤ (N : ℕ∞) ∧
        (N : ℝ) * (ε : ℝ) ^ (3 - 1) ≤ C₀ := by
  apply exists_imageFiber_coveringNumber_polynomial_certificate
    (E := toyE) (F := toyComplete) (H := toyObserved)
    (z := (0 : Euc 1)) toyE_compact
    (toyMask.continuous.comp toyComplete_continuous)
    (fun _ => toyDerivative) (fun _ => toyCompleteCLM)
  · intro v hv
    exact toyDerivative.hasStrictFDerivAt
  · intro v hv
    exact toyCompleteCLM.hasStrictFDerivAt
  · intro v hv
    exact toyDerivative_rank_one

end CFG.Examples
