import CFG.Basic.Model
import Mathlib.Topology.Compactness.Compact

/-!
# Parameter and image fibers
-/

namespace CFG

/-- The parameter fiber inside an admissible set. -/
def fiber {d q : ℕ} (E : Set (Euc d)) (H : Euc d → Euc q) (z : Euc q) :
    Set (Euc d) :=
  E ∩ H ⁻¹' {z}

/-- The image fiber under a complete-data map. -/
def imageFiber {d D q : ℕ} (E : Set (Euc d)) (F : Euc d → Euc D)
    (H : Euc d → Euc q) (z : Euc q) : Set (Euc D) :=
  F '' fiber E H z

theorem mem_fiber_iff {d q : ℕ} {E : Set (Euc d)} {H : Euc d → Euc q}
    {z : Euc q} {v : Euc d} : v ∈ fiber E H z ↔ v ∈ E ∧ H v = z := by
  rfl

theorem fiber_disjoint {d q : ℕ} {E : Set (Euc d)} {H : Euc d → Euc q}
    {z z' : Euc q} (hne : z ≠ z') : Disjoint (fiber E H z) (fiber E H z') := by
  rw [Set.disjoint_left]
  intro v hv hv'
  exact hne (hv.2.symm.trans hv'.2)

theorem isClosed_fiber {d q : ℕ} {E : Set (Euc d)} {H : Euc d → Euc q}
    {z : Euc q} (hclosed : IsClosed E) (hcontinuous : Continuous H) :
    IsClosed (fiber E H z) :=
  hclosed.inter (isClosed_singleton.preimage hcontinuous)

theorem isCompact_fiber {d q : ℕ} {E : Set (Euc d)} {H : Euc d → Euc q}
    {z : Euc q} (hcompact : IsCompact E) (hcontinuous : Continuous H) :
    IsCompact (fiber E H z) :=
  hcompact.inter_right (isClosed_singleton.preimage hcontinuous)

theorem isCompact_imageFiber {d D q : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q} (hcompact : IsCompact (fiber E H z))
    (hcontinuous : Continuous F) : IsCompact (imageFiber E F H z) :=
  hcompact.image hcontinuous

end CFG
