import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Core model objects

This module fixes the Euclidean-space convention used by the formalization and
defines an observed map as the actual composition of a continuous linear mask
with the complete-data map.
-/

namespace CFG

/-- The finite-dimensional real Euclidean space used throughout the project. -/
abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Euclidean spaces carry their canonical Borel measurable structure. -/
noncomputable instance eucMeasurableSpace (n : ℕ) : MeasurableSpace (Euc n) :=
  borel (Euc n)

/-- The measurable structure chosen above is definitionally the Borel one. -/
instance eucBorelSpace (n : ℕ) : BorelSpace (Euc n) :=
  ⟨rfl⟩

/-- A complete-data map together with the genuine linear observation mask. -/
structure Model (d D q : ℕ) where
  complete : Euc d → Euc D
  mask : Euc D →L[ℝ] Euc q

namespace Model

/-- The observed map is definitionally the mask composed with complete data. -/
def observed {d D q : ℕ} (model : Model d D q) : Euc d → Euc q :=
  fun v => model.mask (model.complete v)

@[simp]
theorem observed_apply {d D q : ℕ} (model : Model d D q) (v : Euc d) :
    model.observed v = model.mask (model.complete v) :=
  rfl

end Model

end CFG
