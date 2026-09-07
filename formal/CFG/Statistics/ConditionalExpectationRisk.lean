import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.L2Space

/-! # M17 (narrowed): Pythagorean risk decomposition and minimality of `condExpL2`

Hilbert-space layer only: `f : Lp ℝ 2 μ`, `g` in the `lpMeas` subspace. -/

noncomputable section

open MeasureTheory Submodule

namespace CFG.Statistics

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} [Fact (m ≤ m0)]

/-- The value of `condExpL2` coerced to `Lp` is the orthogonal projection onto
the `lpMeas` submodule. -/
theorem coe_condExpL2 (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
    ((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ) =
      (lpMeas ℝ ℝ m 2 μ).starProjection f :=
  rfl

/-- **Pythagorean risk decomposition**: for `f : Lp ℝ 2 μ` and `g` in the
`lpMeas` subspace, the squared risk around `g` splits into the squared residual
around the conditional expectation plus the squared within-subspace distance. -/
theorem sq_norm_sub_eq_sq_sub_condExpL2_add (hm : m ≤ m0) (f : Lp ℝ 2 μ)
    (g : lpMeas ℝ ℝ m 2 μ) :
    ‖f - (g : Lp ℝ 2 μ)‖ ^ 2 =
      ‖f - ((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ)‖ ^ 2 +
        ‖((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ) - (g : Lp ℝ 2 μ)‖ ^ 2 := by
  have hPfeq : ((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ)
      = (lpMeas ℝ ℝ m 2 μ).starProjection f :=
    coe_condExpL2 hm f
  have hmem : (lpMeas ℝ ℝ m 2 μ).starProjection f - (g : Lp ℝ 2 μ) ∈
      lpMeas ℝ ℝ m 2 μ :=
    (lpMeas ℝ ℝ m 2 μ).sub_mem (starProjection_apply_mem _ f) g.2
  have hinner : inner ℝ (f - ((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ))
      (((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ) - (g : Lp ℝ 2 μ)) = 0 := by
    rw [hPfeq]
    exact starProjection_inner_eq_zero f _ hmem
  have hsum : (f - ((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ)) +
        (((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ) - (g : Lp ℝ 2 μ)) =
      f - (g : Lp ℝ 2 μ) := by abel
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real hinner
  rw [hsum, ← pow_two, ← pow_two, ← pow_two] at h
  exact h

/-- **Minimality**: the conditional expectation `condExpL2 f` is a closest point
of the `lpMeas` subspace to `f` in norm. -/
theorem norm_sub_condExpL2_le (hm : m ≤ m0) (f : Lp ℝ 2 μ) (g : lpMeas ℝ ℝ m 2 μ) :
    ‖f - ((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ)‖ ≤
      ‖f - (g : Lp ℝ 2 μ)‖ := by
  have hdecomp := sq_norm_sub_eq_sq_sub_condExpL2_add hm f g
  have hsq : ‖f - ((condExpL2 ℝ ℝ hm f : lpMeas ℝ ℝ m 2 μ) : Lp ℝ 2 μ)‖ ^ 2 ≤
      ‖f - (g : Lp ℝ 2 μ)‖ ^ 2 := by
    rw [hdecomp]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h

end CFG.Statistics
