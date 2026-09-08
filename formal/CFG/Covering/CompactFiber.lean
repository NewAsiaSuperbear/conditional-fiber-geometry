import CFG.Basic.Fiber
import CFG.Covering.FiniteCover

/-!
# Finite covers of compact image fibers

This closes the qualitative compactness-to-finite-cover bridge.  It is not a
replacement for the quantitative `ε^{-(d-r)}` exponent still requiring the
explicit Euclidean grid.
-/

namespace CFG.Covering

open scoped NNReal

/-- A compact admissible set and continuous forward/observation maps give a
finite internal cover of every image fiber at every positive radius. -/
theorem coveringNumber_imageFiber_ne_top
    {d D q : ℕ} {E : Set (CFG.Euc d)} {F : CFG.Euc d → CFG.Euc D}
    {H : CFG.Euc d → CFG.Euc q} {z : CFG.Euc q}
    (hE : IsCompact E) (hF : Continuous F) (hH : Continuous H)
    {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.coveringNumber ε (CFG.imageFiber E F H z) ≠ ⊤ := by
  apply coveringNumber_ne_top_of_isCompact
  · exact CFG.isCompact_imageFiber (CFG.isCompact_fiber hE hH) hF
  · exact hε

end CFG.Covering
