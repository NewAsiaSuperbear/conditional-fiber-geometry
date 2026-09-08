import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-!
# Exact coverage in the uniform-rank model

For `n` generated samples plus one exchangeable truth there are `n+1` rank
positions.  This file formalizes the finite uniform-rank calculation: the
positions strictly between the two extremes have probability
`(n-1)/(n+1)`.  The probabilistic bridge from iid continuous samples to a
uniform, tie-free rank is intentionally not assumed here.
-/

namespace CFG.Statistics

open scoped ENNReal

/-- Embed the `n-1` interior rank positions into all `n+1` positions by
shifting them past the minimum. -/
def interiorRank (n : ℕ) (j : Fin (n - 1)) : Fin (n + 1) :=
  ⟨j.1 + 1, by omega⟩

theorem interiorRank_injective (n : ℕ) : Function.Injective (interiorRank n) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp [interiorRank] at this
  omega

/-- Under the uniform law on the `n+1` possible ranks, the truth rank is
strictly between the sample minimum and maximum with mass `(n-1)/(n+1)`. -/
theorem uniformRank_interior_probability (n : ℕ) :
    (PMF.uniformOfFintype (Fin (n + 1))).toOuterMeasure
        (Set.range (interiorRank n)) =
      ((n - 1 : ℕ) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have hcard : Fintype.card (Set.range (interiorRank n)) = n - 1 := by
    calc
      Fintype.card (Set.range (interiorRank n)) = Fintype.card (Fin (n - 1)) :=
        (Fintype.card_congr (Equiv.ofInjective (interiorRank n)
          (interiorRank_injective n))).symm
      _ = n - 1 := Fintype.card_fin _
  rw [hcard, Fintype.card_fin]

/-- For sixteen generated samples the extremal interval ceiling is exactly
`15/17` in the uniform-rank model. -/
theorem uniformRank_sixteen_probability :
    (PMF.uniformOfFintype (Fin 17)).toOuterMeasure
        (Set.range (interiorRank 16)) = (15 : ℝ≥0∞) / 17 := by
  simpa using uniformRank_interior_probability 16

end CFG.Statistics
