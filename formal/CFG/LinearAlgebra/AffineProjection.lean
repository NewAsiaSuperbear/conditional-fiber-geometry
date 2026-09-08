import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Compatible affine orthogonal projection

This module proves the M16 non-expansion statement in the natural affine
coordinate form `a + S`.  The compatibility hypothesis is exactly
`x⋆ - a ∈ S`; without it, projection toward the constraint need not improve
distance to the chosen truth.
-/

namespace CFG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal projection onto the affine set `a + S`. -/
noncomputable def affineProjection (a : E) (S : Submodule ℝ E)
    [S.HasOrthogonalProjection] (x : E) : E :=
  a + S.starProjection (x - a)

/-- The affine projection really belongs to `a + S`. -/
theorem affineProjection_sub_mem (a : E) (S : Submodule ℝ E)
    [S.HasOrthogonalProjection] (x : E) :
    affineProjection a S x - a ∈ S := by
  simpa [affineProjection] using S.starProjection_apply_mem (x - a)

/-- Every compatible point is fixed by the affine projection. -/
theorem affineProjection_eq_self
    (a : E) (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    {x : E} (hx : x - a ∈ S) :
    affineProjection a S x = x := by
  rw [affineProjection, S.starProjection_eq_self_iff.mpr hx]
  abel

/-- Projecting onto a compatible affine constraint cannot increase error to
any truth point in that constraint. -/
theorem norm_affineProjection_sub_le
    (a : E) (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (x xstar : E) (hxstar : xstar - a ∈ S) :
    ‖affineProjection a S x - xstar‖ ≤ ‖x - xstar‖ := by
  have hfixed : S.starProjection (xstar - a) = xstar - a :=
    S.starProjection_eq_self_iff.mpr hxstar
  have heq : affineProjection a S x - xstar =
      S.starProjection ((x - a) - (xstar - a)) := by
    calc
      affineProjection a S x - xstar =
          S.starProjection (x - a) - (xstar - a) := by
        rw [affineProjection]
        abel
      _ = S.starProjection (x - a) - S.starProjection (xstar - a) := by rw [hfixed]
      _ = S.starProjection ((x - a) - (xstar - a)) :=
        (S.starProjection.map_sub (x - a) (xstar - a)).symm
  calc
    ‖affineProjection a S x - xstar‖ =
        ‖S.starProjection ((x - a) - (xstar - a))‖ := congrArg norm heq
    _ ≤ ‖(x - a) - (xstar - a)‖ := S.norm_starProjection_apply_le _
    _ = ‖x - xstar‖ := by
      congr 1
      abel

end CFG
