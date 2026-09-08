import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The pseudoinverse of a surjective finite-dimensional operator

For a surjective continuous linear map `B : E →L[ℝ] F`, this module
constructs the canonical right inverse

`B† (B B†)⁻¹`.

The inverse is `ContinuousLinearMap.inverse`; the hypotheses below prove that
the Gram operator `B B†` is genuinely invertible, so its junk-value branch is
never used.  We also record positivity, strict positivity, the right-inverse
identity, orthogonality to `ker B`, and idempotence of the induced projection.
-/

namespace CFG

open scoped InnerProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The output-space Gram operator `B B†`. -/
noncomputable def surjectiveGram (B : E →L[ℝ] F) : F →L[ℝ] F :=
  B.comp B.adjoint

/-- The canonical right inverse `B† (B B†)⁻¹` of a surjective operator. -/
noncomputable def surjectivePseudoinverse (B : E →L[ℝ] F) : F →L[ℝ] E :=
  B.adjoint.comp (surjectiveGram B).inverse

/-- Surjectivity of `B` forces injectivity of its adjoint. -/
theorem adjoint_injective_of_surjective (B : E →L[ℝ] F)
    (hB : Function.Surjective B) : Function.Injective B.adjoint := by
  rw [← B.adjoint.coe_coe, ← LinearMap.ker_eq_bot]
  rw [← B.orthogonal_range, LinearMap.range_eq_top.mpr hB]
  simp

/-- For surjective `B`, the output-space Gram operator has trivial kernel. -/
theorem surjectiveGram_ker_eq_bot (B : E →L[ℝ] F)
    (hB : Function.Surjective B) : (surjectiveGram B).ker = ⊥ := by
  rw [surjectiveGram, B.ker_self_comp_adjoint]
  exact LinearMap.ker_eq_bot.mpr (adjoint_injective_of_surjective B hB)

/-- For surjective `B`, the output-space Gram operator is bijective. -/
theorem surjectiveGram_bijective (B : E →L[ℝ] F)
    (hB : Function.Surjective B) : Function.Bijective (surjectiveGram B) := by
  have hinj : Function.Injective (surjectiveGram B) :=
    LinearMap.ker_eq_bot.mp (surjectiveGram_ker_eq_bot B hB)
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

/-- For surjective `B`, the output-space Gram operator is continuously invertible. -/
theorem surjectiveGram_isInvertible (B : E →L[ℝ] F)
    (hB : Function.Surjective B) : (surjectiveGram B).IsInvertible := by
  let e : F ≃L[ℝ] F := ContinuousLinearEquiv.ofBijective (surjectiveGram B)
    (surjectiveGram_ker_eq_bot B hB)
    (LinearMap.range_eq_top.mpr (surjectiveGram_bijective B hB).surjective)
  exact ⟨e, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- The output-space Gram operator is positive semidefinite. -/
theorem surjectiveGram_isPositive (B : E →L[ℝ] F) :
    (surjectiveGram B).IsPositive := by
  simpa [surjectiveGram] using ContinuousLinearMap.isPositive_self_comp_adjoint B

/-- For surjective `B`, the output-space Gram operator is strictly positive. -/
theorem surjectiveGram_inner_pos (B : E →L[ℝ] F)
    (hB : Function.Surjective B) {y : F} (hy : y ≠ 0) :
    0 < inner ℝ y (surjectiveGram B y) := by
  have hadj : B.adjoint y ≠ 0 := by
    intro h
    apply hy
    apply adjoint_injective_of_surjective B hB
    simpa using h
  rw [surjectiveGram, ContinuousLinearMap.comp_apply, ← B.adjoint_inner_left]
  exact real_inner_self_pos.mpr hadj

/-- The inverse selected for the Gram operator is a true right inverse. -/
theorem surjectiveGram_comp_inverse (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    (surjectiveGram B).comp (surjectiveGram B).inverse = ContinuousLinearMap.id ℝ F :=
  (surjectiveGram_isInvertible B hB).self_comp_inverse

/-- The canonical pseudoinverse is a genuine right inverse of `B`. -/
theorem comp_surjectivePseudoinverse (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    B.comp (surjectivePseudoinverse B) = ContinuousLinearMap.id ℝ F := by
  rw [surjectivePseudoinverse, ← ContinuousLinearMap.comp_assoc]
  exact surjectiveGram_comp_inverse B hB

/-- Pointwise form of the right-inverse identity. -/
@[simp]
theorem apply_surjectivePseudoinverse (B : E →L[ℝ] F)
    (hB : Function.Surjective B) (y : F) :
    B (surjectivePseudoinverse B y) = y := by
  have h := congrArg (fun T : F →L[ℝ] F ↦ T y) (comp_surjectivePseudoinverse B hB)
  simpa using h

/-- The canonical pseudoinverse takes values orthogonal to `ker B`. -/
theorem inner_surjectivePseudoinverse_eq_zero_of_mem_ker
    (B : E →L[ℝ] F) (y : F) {z : E} (hz : z ∈ B.ker) :
    inner ℝ z (surjectivePseudoinverse B y) = 0 := by
  rw [surjectivePseudoinverse, ContinuousLinearMap.comp_apply,
    B.adjoint_inner_right]
  have hBz : B z = 0 := hz
  rw [hBz, inner_zero_left]

/-- Subtracting the canonical lift from any other lift leaves an element of
`ker B`. -/
theorem sub_surjectivePseudoinverse_mem_ker (B : E →L[ℝ] F)
    (hB : Function.Surjective B) {x : E} {y : F} (hxy : B x = y) :
    x - surjectivePseudoinverse B y ∈ B.ker := by
  change B (x - surjectivePseudoinverse B y) = 0
  rw [map_sub, hxy, apply_surjectivePseudoinverse B hB, sub_self]

/-- The canonical lift has least norm among all solutions of `B x = y`. -/
theorem norm_surjectivePseudoinverse_le_of_image_eq (B : E →L[ℝ] F)
    (hB : Function.Surjective B) {x : E} {y : F} (hxy : B x = y) :
    ‖surjectivePseudoinverse B y‖ ≤ ‖x‖ := by
  let z : E := x - surjectivePseudoinverse B y
  have hz : z ∈ B.ker := by
    simpa [z] using sub_surjectivePseudoinverse_mem_ker B hB hxy
  have hort : inner ℝ (surjectivePseudoinverse B y) z = 0 := by
    rw [real_inner_comm]
    exact inner_surjectivePseudoinverse_eq_zero_of_mem_ker B y hz
  have hpyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_real
      (x := surjectivePseudoinverse B y) (y := z) hort
  have hsum : surjectivePseudoinverse B y + z = x := by
    simp [z]
  rw [hsum] at hpyth
  nlinarith [sq_nonneg ‖surjectivePseudoinverse B y‖, sq_nonneg ‖z‖,
    norm_nonneg (surjectivePseudoinverse B y), norm_nonneg x]

/-- `B† (B B†)⁻¹ B` is idempotent when `B` is surjective. -/
theorem surjectivePseudoinverse_comp_idempotent (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    ((surjectivePseudoinverse B).comp B).comp
        ((surjectivePseudoinverse B).comp B) =
      (surjectivePseudoinverse B).comp B := by
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  rw [apply_surjectivePseudoinverse B hB]

/-- `B† (B B†)⁻¹ B` is symmetric: it is the orthogonal projection onto
the complement of `ker B`. -/
theorem surjectivePseudoinverse_comp_isSymmetric (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    ((surjectivePseudoinverse B).comp B).IsSymmetric := by
  intro x y
  let P : E →L[ℝ] E := (surjectivePseudoinverse B).comp B
  have hxker : x - P x ∈ B.ker := by
    simpa [P] using sub_surjectivePseudoinverse_mem_ker B hB (x := x) (y := B x) rfl
  have hyker : y - P y ∈ B.ker := by
    simpa [P] using sub_surjectivePseudoinverse_mem_ker B hB (x := y) (y := B y) rfl
  have hxy0 : inner ℝ (P x) (y - P y) = 0 := by
    rw [real_inner_comm]
    simpa [P] using
      inner_surjectivePseudoinverse_eq_zero_of_mem_ker B (B x) hyker
  have hyx0 : inner ℝ (x - P x) (P y) = 0 := by
    simpa [P] using
      inner_surjectivePseudoinverse_eq_zero_of_mem_ker B (B y) hxker
  change inner ℝ (P x) y = inner ℝ x (P y)
  calc
    inner ℝ (P x) y = inner ℝ (P x) (P y + (y - P y)) := by
      congr 2
      abel
    _ = inner ℝ (P x) (P y) := by rw [inner_add_right, hxy0, add_zero]
    _ = inner ℝ (P x + (x - P x)) (P y) := by
      rw [inner_add_left, hyx0, add_zero]
    _ = inner ℝ x (P y) := by
      congr 2
      abel

/-- Self-adjoint form of the orthogonal-projection statement. -/
theorem surjectivePseudoinverse_comp_isSelfAdjoint (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    IsSelfAdjoint ((surjectivePseudoinverse B).comp B) :=
  (surjectivePseudoinverse_comp_isSymmetric B hB).isSelfAdjoint

/-- The orthogonal projection `B† (B B†)⁻¹ B` is a contraction. -/
theorem norm_surjectivePseudoinverse_comp_le_one (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    ‖(surjectivePseudoinverse B).comp B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, ContinuousLinearMap.comp_apply] using
    norm_surjectivePseudoinverse_le_of_image_eq B hB (x := x) (y := B x) rfl

/-- Elementary operator-norm bound inherited from the defining composition. -/
theorem norm_surjectivePseudoinverse_le (B : E →L[ℝ] F) :
    ‖surjectivePseudoinverse B‖ ≤ ‖B‖ * ‖(surjectiveGram B).inverse‖ := by
  calc
    ‖surjectivePseudoinverse B‖ ≤
        ‖B.adjoint‖ * ‖(surjectiveGram B).inverse‖ := by
      simpa [surjectivePseudoinverse] using
        ContinuousLinearMap.opNorm_comp_le B.adjoint (surjectiveGram B).inverse
    _ = ‖B‖ * ‖(surjectiveGram B).inverse‖ := by
      rw [LinearIsometryEquiv.norm_map]

/-- The canonical right inverse takes values in the orthogonal complement of
`ker B`.  This orthogonality follows directly from its adjoint construction and
does not itself require surjectivity. -/
theorem surjectivePseudoinverse_mem_ker_orthogonal (B : E →L[ℝ] F) (y : F) :
    surjectivePseudoinverse B y ∈ (B.ker)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  exact inner_surjectivePseudoinverse_eq_zero_of_mem_ker B y hz

/-- A singular-value-style lower bound on the orthogonal complement of the
kernel yields the reciprocal operator-norm bound for the canonical right
inverse. -/
theorem norm_surjectivePseudoinverse_le_inv_of_lower_bound (B : E →L[ℝ] F)
    (hB : Function.Surjective B) {s : ℝ} (hs : 0 < s)
    (hlb : ∀ x ∈ (B.ker)ᗮ, s * ‖x‖ ≤ ‖B x‖) :
    ‖surjectivePseudoinverse B‖ ≤ s⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (le_of_lt hs))
  intro y
  have hy0 : s * ‖surjectivePseudoinverse B y‖ ≤ ‖y‖ := by
    have h1 :
        s * ‖surjectivePseudoinverse B y‖ ≤ ‖B (surjectivePseudoinverse B y)‖ :=
      hlb (surjectivePseudoinverse B y) (surjectivePseudoinverse_mem_ker_orthogonal B y)
    rw [apply_surjectivePseudoinverse B hB y] at h1
    exact h1
  calc
    ‖surjectivePseudoinverse B y‖ =
        s⁻¹ * (s * ‖surjectivePseudoinverse B y‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    _ ≤ s⁻¹ * ‖y‖ :=
      mul_le_mul_of_nonneg_left hy0 (inv_nonneg.mpr (le_of_lt hs))

end CFG
