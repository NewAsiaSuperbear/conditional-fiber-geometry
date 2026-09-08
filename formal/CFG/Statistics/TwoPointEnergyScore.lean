import CFG.Statistics.NormalizedEnergyScore
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-!
# A genuine two-point PMF bridge for the normalized energy score

The polynomial formulas in `NormalizedEnergyScore` are connected here to an
actual finite probability mass function.  The forecast puts mass `q` on `2`
and `1-q` on `1`; the two independent forecast draws are represented by the
finite double sum in `energyScore`.
-/

namespace CFG.Statistics

open scoped BigOperators

noncomputable def twoPointValue : Bool → ℝ
  | false => 1
  | true => 2

noncomputable def energyScore (p : PMF Bool) (y : ℝ) : ℝ :=
  (∑ x, (p x).toReal * |twoPointValue x - y|) -
    (1 / 2 : ℝ) * ∑ x, ∑ x', (p x).toReal * (p x').toReal *
      |twoPointValue x - twoPointValue x'|

noncomputable def normalizedEnergyScore (p : PMF Bool) (y : ℝ) : ℝ :=
  energyScore p y / |y|

def twoPointForecast (q : NNReal) (hq : q ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b then (q : ENNReal) else (1 - q : ENNReal)) (by
    simp [hq])

noncomputable def fairTruth : PMF Bool :=
  PMF.uniformOfFintype Bool

noncomputable def truthExpected (t : PMF Bool) (f : ℝ → ℝ) : ℝ :=
  ∑ y, (t y).toReal * f (twoPointValue y)

noncomputable def iidPair (p : PMF Bool) : PMF (Bool × Bool) :=
  p.bind (fun x => p.map (fun x' => (x, x')))

theorem iidPair_apply (p : PMF Bool) (x x' : Bool) :
    iidPair p (x, x') = p x * p x' := by
  cases x <;> cases x' <;> simp [iidPair, PMF.bind_apply, PMF.map_apply]

theorem energyScore_eq_iidPair_expectation (p : PMF Bool) (y : ℝ) :
    energyScore p y =
      (∑ x, (p x).toReal * |twoPointValue x - y|) -
        (1 / 2 : ℝ) *
          ∑ z : Bool × Bool, (iidPair p z).toReal *
            |twoPointValue z.1 - twoPointValue z.2| := by
  unfold energyScore
  congr 2
  rw [Fintype.sum_prod_type]
  simp_rw [iidPair_apply, ENNReal.toReal_mul]

theorem truthExpected_fairTruth (f : ℝ → ℝ) :
    truthExpected fairTruth f = (1 / 2 : ℝ) * f 1 + (1 / 2 : ℝ) * f 2 := by
  simp [truthExpected, fairTruth, twoPointValue]
  ring

theorem energyScore_twoPointForecast_at_one (q : NNReal) (hq : q ≤ 1) :
    energyScore (twoPointForecast q hq) 1 = q.toReal ^ 2 := by
  simp [energyScore, twoPointForecast, twoPointValue]
  have hsub : (1 - (q : ENNReal)).toReal = 1 - q.toReal := by
    rw [ENNReal.toReal_sub_of_le]
    · simp
    · exact_mod_cast hq
    · simp
  rw [hsub]
  norm_num
  ring

theorem energyScore_twoPointForecast_at_two (q : NNReal) (hq : q ≤ 1) :
    energyScore (twoPointForecast q hq) 2 = (1 - q.toReal) ^ 2 := by
  simp [energyScore, twoPointForecast, twoPointValue]
  have hsub : (1 - (q : ENNReal)).toReal = 1 - q.toReal := by
    rw [ENNReal.toReal_sub_of_le]
    · simp
    · exact_mod_cast hq
    · simp
  rw [hsub]
  norm_num
  ring

theorem normalizedEnergyScore_twoPointForecast_at_one (q : NNReal) (hq : q ≤ 1) :
    normalizedEnergyScore (twoPointForecast q hq) 1 = q.toReal ^ 2 := by
  rw [normalizedEnergyScore, energyScore_twoPointForecast_at_one q hq]
  norm_num

theorem normalizedEnergyScore_twoPointForecast_at_two (q : NNReal) (hq : q ≤ 1) :
    normalizedEnergyScore (twoPointForecast q hq) 2 =
      (1 / 2 : ℝ) * (1 - q.toReal) ^ 2 := by
  rw [normalizedEnergyScore, energyScore_twoPointForecast_at_two q hq]
  norm_num
  ring

theorem normalizedExpectedEnergy_twoPointForecast (q : NNReal) (hq : q ≤ 1) :
    (1 / 2 : ℝ) * normalizedEnergyScore (twoPointForecast q hq) 1 +
      (1 / 2 : ℝ) * normalizedEnergyScore (twoPointForecast q hq) 2 =
      twoPointNormalizedExpectedEnergy q.toReal := by
  rw [normalizedEnergyScore_twoPointForecast_at_one q hq,
    normalizedEnergyScore_twoPointForecast_at_two q hq]
  simp [twoPointNormalizedExpectedEnergy]
  ring

theorem expectedEnergy_twoPointForecast (q : NNReal) (hq : q ≤ 1) :
    (1 / 2 : ℝ) * energyScore (twoPointForecast q hq) 1 +
      (1 / 2 : ℝ) * energyScore (twoPointForecast q hq) 2 =
      twoPointExpectedEnergy q.toReal := by
  rw [energyScore_twoPointForecast_at_one q hq,
    energyScore_twoPointForecast_at_two q hq]
  simp [twoPointExpectedEnergy]

theorem normalizedExpectedEnergy_twoPointForecast_fairTruth
    (q : NNReal) (hq : q ≤ 1) :
    truthExpected fairTruth
        (normalizedEnergyScore (twoPointForecast q hq)) =
      twoPointNormalizedExpectedEnergy q.toReal := by
  rw [truthExpected_fairTruth,
    normalizedExpectedEnergy_twoPointForecast q hq]

theorem expectedEnergy_twoPointForecast_fairTruth
    (q : NNReal) (hq : q ≤ 1) :
    truthExpected fairTruth (energyScore (twoPointForecast q hq)) =
      twoPointExpectedEnergy q.toReal := by
  rw [truthExpected_fairTruth, expectedEnergy_twoPointForecast q hq]

theorem normalizedExpectedEnergy_twoPointForecast_third_lt_half :
    truthExpected fairTruth
        (normalizedEnergyScore (twoPointForecast (1 / 3 : NNReal) (by norm_num [div_le_iff₀]))) <
      truthExpected fairTruth
        (normalizedEnergyScore (twoPointForecast (1 / 2 : NNReal) (by norm_num [div_le_iff₀]))) := by
  rw [normalizedExpectedEnergy_twoPointForecast_fairTruth,
    normalizedExpectedEnergy_twoPointForecast_fairTruth]
  norm_num at *
  exact normalizedEnergy_third_lt_half

theorem normalizedExpectedEnergy_twoPointForecast_minimized_at_third
    (q : NNReal) (hq : q ≤ 1) :
    truthExpected fairTruth
        (normalizedEnergyScore (twoPointForecast (1 / 3 : NNReal) (by norm_num [div_le_iff₀]))) ≤
      truthExpected fairTruth (normalizedEnergyScore (twoPointForecast q hq)) := by
  rw [normalizedExpectedEnergy_twoPointForecast_fairTruth,
    normalizedExpectedEnergy_twoPointForecast_fairTruth]
  exact twoPointNormalizedExpectedEnergy_minimized_at_third q.toReal

end CFG.Statistics
