import Mathlib

/-!
# Concrete scope examples and counterexamples

These small real-coordinate models guard the intended scope of the abstract
fiber statements.  In particular, a parameter fiber can have an invisible
direction even when its image forgets another direction, and zero-dimensional
nonempty fibers must be distinguished from empty fibers.
-/

namespace CFG.Examples

/-- First-coordinate observation on the plane. -/
def firstObservation (p : ℝ × ℝ) : ℝ := p.1

theorem hasFDerivAt_firstObservation (p : ℝ × ℝ) :
    HasFDerivAt firstObservation (ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  change HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p
  exact hasFDerivAt_fst

theorem firstObservation_level (z : ℝ) :
    {p : ℝ × ℝ | firstObservation p = z} = Set.range (fun y : ℝ => (z, y)) := by
  ext p
  constructor
  · intro hp
    refine ⟨p.2, ?_⟩
    apply Prod.ext
    · exact hp.symm
    · rfl
  · rintro ⟨y, rfl⟩
    rfl

theorem firstObservation_level_infinite (z : ℝ) :
    Set.Infinite {p : ℝ × ℝ | firstObservation p = z} := by
  rw [firstObservation_level]
  exact Set.infinite_range_of_injective fun _ _ h => congrArg Prod.snd h

/-- Radial squared observation on the plane. -/
def radiusSq (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- Exact first-order expansion, exposing the linear derivative term and the
quadratic remainder without any asymptotic shorthand. -/
theorem radiusSq_increment (p h : ℝ × ℝ) :
    radiusSq (p + h) - radiusSq p =
      2 * p.1 * h.1 + 2 * p.2 * h.2 + radiusSq h := by
  simp [radiusSq]
  ring

/-- A three-parameter complete map that drops the third coordinate. -/
def completeDropThird (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ := (p.1, p.2.1)

/-- Observing the first complete-data coordinate. -/
def observedFirst (p : ℝ × (ℝ × ℝ)) : ℝ := (completeDropThird p).1

theorem observedFirst_eq (p : ℝ × (ℝ × ℝ)) : observedFirst p = p.1 := rfl

/-- The parameter fiber has two free coordinates. -/
theorem observedFirst_level (z : ℝ) :
    {p : ℝ × (ℝ × ℝ) | observedFirst p = z} =
      Set.range (fun yz : ℝ × ℝ => (z, yz)) := by
  ext p
  constructor
  · intro hp
    refine ⟨p.2, ?_⟩
    apply Prod.ext
    · exact hp.symm
    · rfl
  · rintro ⟨yz, rfl⟩
    rfl

/-- Its complete-data image fiber has only one free coordinate. -/
theorem completeDropThird_level_image (z : ℝ) :
    completeDropThird '' {p : ℝ × (ℝ × ℝ) | observedFirst p = z} =
      Set.range (fun y : ℝ => (z, y)) := by
  ext w
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2.1, ?_⟩
    apply Prod.ext
    · exact hp.symm
    · rfl
  · rintro ⟨y, rfl⟩
    exact ⟨(z, (y, 0)), rfl, rfl⟩

/-- A genuine empty real fiber. -/
theorem negative_radiusSq_level_empty :
    {p : ℝ × ℝ | radiusSq p = -1} = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  change radiusSq p = -1 at h
  unfold radiusSq at h
  nlinarith [sq_nonneg p.1, sq_nonneg p.2]

/-- A nonempty zero-dimensional fiber, kept separate from the empty case. -/
theorem square_zero_level_singleton :
    {x : ℝ | x ^ 2 = 0} = {0} := by
  ext x
  simp

end CFG.Examples
