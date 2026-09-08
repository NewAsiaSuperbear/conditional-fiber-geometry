import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Real.Basic

/-!
# Rank of a map along the kernel of an observed composition

For linear maps `A : E → F` and `P : F → G`, this module proves the exact
finite-dimensional identity

`rank (A|ker(P ∘ A)) + rank (P ∘ A) = rank A`.

It is a linear-algebra statement only; it does not assert differentiability,
local constant rank, a fiber chart, or any covering theorem.
-/

namespace CFG

open Module

section

variable {E F G : Type*}
variable [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
variable [Module ℝ E] [Module ℝ F] [Module ℝ G]

theorem ker_le_ker_comp (A : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] G) :
    LinearMap.ker A ≤ LinearMap.ker (P.comp A) := by
  intro x hx
  simp only [LinearMap.mem_ker] at hx ⊢
  simp [hx]

/-- `A` restricted to vectors invisible to the observed composition `P ∘ A`. -/
def restrictToObservedKer (A : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] G) :
    LinearMap.ker (P.comp A) →ₗ[ℝ] F :=
  A.domRestrict (LinearMap.ker (P.comp A))

/-- Restricting `A` to `ker (P ∘ A)` does not change its own kernel. -/
def kerRestrictToObservedKerEquiv (A : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] G) :
    LinearMap.ker (restrictToObservedKer A P) ≃ₗ[ℝ] LinearMap.ker A where
  toFun x := ⟨x.1.1, by
    simpa [restrictToObservedKer] using x.2⟩
  invFun x := ⟨⟨x.1, ker_le_ker_comp A P x.2⟩, by
    simp [restrictToObservedKer]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [FiniteDimensional ℝ E]

theorem finrank_range_restrictToObservedKer_add_finrank_range_comp
    (A : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] G) :
    finrank ℝ (LinearMap.range (restrictToObservedKer A P)) +
        finrank ℝ (LinearMap.range (P.comp A)) =
      finrank ℝ (LinearMap.range A) := by
  have hA := A.finrank_range_add_finrank_ker
  have hPA := (P.comp A).finrank_range_add_finrank_ker
  have hRestrict := (restrictToObservedKer A P).finrank_range_add_finrank_ker
  have hKer := (kerRestrictToObservedKerEquiv A P).finrank_eq
  omega

theorem finrank_range_comp_le_finrank_range (A : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] G) :
    finrank ℝ (LinearMap.range (P.comp A)) ≤ finrank ℝ (LinearMap.range A) := by
  have h := finrank_range_restrictToObservedKer_add_finrank_range_comp A P
  omega

theorem finrank_range_restrictToObservedKer_eq_sub (A : E →ₗ[ℝ] F)
    (P : F →ₗ[ℝ] G) :
    finrank ℝ (LinearMap.range (restrictToObservedKer A P)) =
      finrank ℝ (LinearMap.range A) - finrank ℝ (LinearMap.range (P.comp A)) := by
  have h := finrank_range_restrictToObservedKer_add_finrank_range_comp A P
  omega

end

end CFG
