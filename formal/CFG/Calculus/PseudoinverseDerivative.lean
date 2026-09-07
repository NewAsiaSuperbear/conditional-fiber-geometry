import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.Positive
import CFG.LinearAlgebra.SurjectivePseudoinverse
import CFG.Calculus.InverseFamily

/-!
# Differentiation of the surjective pseudoinverse

For a differentiable family of surjective finite-dimensional real Hilbert
space operators, this file differentiates the adjoint, Gram operator, Gram
inverse, and canonical right pseudoinverse `B† (B B†)⁻¹`.
-/

namespace CFG

open ContinuousLinearMap
open scoped InnerProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Over `ℝ`, taking the adjoint is a continuous linear map. -/
noncomputable def adjointCLM : (E →L[ℝ] F) →L[ℝ] F →L[ℝ] E where
  toFun := ContinuousLinearMap.adjoint
  map_add' := fun A B => map_add _ A B
  map_smul' := fun r A => by
    show (r • A)† = r • A†
    rw [map_smulₛₗ]
    simp
  cont := ContinuousLinearMap.adjoint.continuous

@[simp]
lemma adjointCLM_apply (A : E →L[ℝ] F) : adjointCLM A = A† := rfl

/-- Chain rule for a differentiable family followed by the real-linear
adjoint map. -/
theorem HasFDerivAt.adjoint_clm
    {Bf : X → E →L[ℝ] F} {Bf' : X →L[ℝ] (E →L[ℝ] F)} {x : X}
    (hB : HasFDerivAt Bf Bf' x) :
    HasFDerivAt (fun y => (Bf y)†) (adjointCLM.comp Bf') x := by
  show HasFDerivAt (adjointCLM ∘ Bf) (adjointCLM ∘SL Bf') x
  exact adjointCLM.hasFDerivAt.comp x hB

/-- Derivative of the Gram family `y ↦ Bf y ∘L (Bf y)†`. -/
theorem hasFDerivAt_surjectiveGram
    {Bf : X → E →L[ℝ] F} {Bf' : X →L[ℝ] (E →L[ℝ] F)} {x : X}
    (hB : HasFDerivAt Bf Bf' x) :
    HasFDerivAt (fun y => surjectiveGram (Bf y))
      ((compL ℝ F E F (Bf x)).comp (adjointCLM.comp Bf') +
        ((compL ℝ F E F).flip ((Bf x)†)).comp Bf') x := by
  simpa only [surjectiveGram] using hB.clm_comp (HasFDerivAt.adjoint_clm hB)

/-- Derivative of the Gram-inverse family through the genuine unit supplied by
surjectivity. -/
theorem hasFDerivAt_gram_inverse
    {Bf : X → E →L[ℝ] F} {Bf' : X →L[ℝ] (E →L[ℝ] F)} {x : X}
    (hB : HasFDerivAt Bf Bf' x) (hsurj : Function.Surjective (Bf x)) :
    HasFDerivAt (fun y => (surjectiveGram (Bf y)).inverse)
      ((-(mulLeftRight ℝ (F →L[ℝ] F)
            (surjectiveGram (Bf x)).inverse (surjectiveGram (Bf x)).inverse)).comp
        ((compL ℝ F E F (Bf x)).comp (adjointCLM.comp Bf') +
          ((compL ℝ F E F).flip ((Bf x)†)).comp Bf')) x := by
  obtain ⟨e, he⟩ := surjectiveGram_isInvertible (Bf x) hsurj
  set u : (F →L[ℝ] F)ˣ := (ContinuousLinearEquiv.unitsEquiv ℝ F).symm e with hu
  have hucoe : (u : F →L[ℝ] F) = surjectiveGram (Bf x) := by
    rw [hu]
    exact he.symm ▸ rfl
  have huinv : ((u⁻¹ : (F →L[ℝ] F)ˣ) : F →L[ℝ] F) =
      (surjectiveGram (Bf x)).inverse := by
    rw [← Ring.inverse_unit u, hucoe, ContinuousLinearMap.ringInverse_eq_inverse]
  rw [show (fun y => (surjectiveGram (Bf y)).inverse) =
        fun y => Ring.inverse (surjectiveGram (Bf y)) from by
      rw [ContinuousLinearMap.ringInverse_eq_inverse]]
  have h := hasFDerivAt_ringInverse_comp (hasFDerivAt_surjectiveGram hB) u hucoe
  rwa [huinv] at h

/-- The canonical pseudoinverse of a differentiable surjective family is
Fréchet differentiable.  The displayed derivative is the direct
product/inverse-rule expression. -/
theorem hasFDerivAt_surjectivePseudoinverse
    {Bf : X → E →L[ℝ] F} {Bf' : X →L[ℝ] (E →L[ℝ] F)} {x : X}
    (hB : HasFDerivAt Bf Bf' x) (hsurj : Function.Surjective (Bf x)) :
    HasFDerivAt (fun y => surjectivePseudoinverse (Bf y))
      ((compL ℝ F F E ((Bf x)†)).comp
          ((-(mulLeftRight ℝ (F →L[ℝ] F) (surjectiveGram (Bf x)).inverse
              (surjectiveGram (Bf x)).inverse)).comp
            ((compL ℝ F E F (Bf x)).comp (adjointCLM.comp Bf') +
              ((compL ℝ F E F).flip ((Bf x)†)).comp Bf')) +
        ((compL ℝ F F E).flip (surjectiveGram (Bf x)).inverse).comp
          (adjointCLM.comp Bf')) x := by
  simpa only [surjectivePseudoinverse] using
    (HasFDerivAt.adjoint_clm hB).clm_comp (hasFDerivAt_gram_inverse hB hsurj)

/-- The inverse of a surjective Gram operator is self-adjoint. -/
theorem adjoint_gram_inverse (B : E →L[ℝ] F) (hB : Function.Surjective B) :
    (surjectiveGram B).inverse† = (surjectiveGram B).inverse := by
  have h1 := surjectiveGram_comp_inverse B hB
  have hG : (surjectiveGram B)† = surjectiveGram B := by
    have h := (surjectiveGram_isPositive B).isSelfAdjoint
    rw [← star_eq_adjoint]
    exact h
  have h2 : (surjectiveGram B).inverse† ∘L surjectiveGram B = .id ℝ F := by
    have := congrArg ContinuousLinearMap.adjoint h1
    rwa [adjoint_comp, hG, adjoint_id] at this
  calc
    (surjectiveGram B).inverse† =
        (surjectiveGram B).inverse† ∘L .id ℝ F := (comp_id _).symm
    _ = (surjectiveGram B).inverse† ∘L
          (surjectiveGram B ∘L (surjectiveGram B).inverse) := by rw [h1]
    _ = ((surjectiveGram B).inverse† ∘L surjectiveGram B) ∘L
          (surjectiveGram B).inverse := comp_assoc _ _ _
    _ = (surjectiveGram B).inverse := by rw [h2, id_comp]

/-- Applied to a direction `v`, the derivative of the pseudoinverse family is
`-A (Bf' v) A + (I - A B) (Bf' v)† A† A`, the closed form
`DA[B][E] = -A E A + (I - AB) E* A* A`. -/
theorem fderiv_surjectivePseudoinverse_apply
    {Bf : X → E →L[ℝ] F} {Bf' : X →L[ℝ] (E →L[ℝ] F)} {x : X}
    (hB : HasFDerivAt Bf Bf' x) (hsurj : Function.Surjective (Bf x)) (v : X) :
    fderiv ℝ (fun y => surjectivePseudoinverse (Bf y)) x v =
      -((surjectivePseudoinverse (Bf x)).comp
          ((Bf' v).comp (surjectivePseudoinverse (Bf x)))) +
        (ContinuousLinearMap.id ℝ E -
          (surjectivePseudoinverse (Bf x)).comp (Bf x)).comp
          ((Bf' v)†.comp ((surjectivePseudoinverse (Bf x))†.comp
            (surjectivePseudoinverse (Bf x)))) := by
  have hder := (hasFDerivAt_surjectivePseudoinverse hB hsurj).fderiv
  rw [hder]
  simp only [ContinuousLinearMap.comp_apply, add_apply, neg_apply, compL_apply,
    ContinuousLinearMap.flip_apply, mulLeftRight_apply, adjointCLM_apply]
  have hAc : surjectivePseudoinverse (Bf x) =
      (Bf x)† ∘L (surjectiveGram (Bf x)).inverse := rfl
  have hGiG :
      (surjectiveGram (Bf x)).inverse ∘L ((Bf x) ∘L (Bf x)†) = .id ℝ F :=
    (surjectiveGram_isInvertible (Bf x) hsurj).inverse_comp_self
  have hAadj :
      (surjectivePseudoinverse (Bf x))† ∘L surjectivePseudoinverse (Bf x) =
        (surjectiveGram (Bf x)).inverse := by
    rw [hAc, adjoint_comp, adjoint_adjoint, adjoint_gram_inverse _ hsurj]
    rw [ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc (Bf x) ((Bf x)†)
        (surjectiveGram (Bf x)).inverse,
      ← ContinuousLinearMap.comp_assoc (surjectiveGram (Bf x)).inverse
        ((Bf x) ∘L ((Bf x)†)) (surjectiveGram (Bf x)).inverse,
      hGiG, id_comp]
  rw [mul_def]
  rw [mul_def]
  rw [comp_add, add_comp]
  rw [neg_add, comp_add, comp_neg, comp_neg]
  have e1 :
      (Bf x)† ∘L (((surjectiveGram (Bf x)).inverse ∘L
          ((Bf x) ∘L ((Bf' v)†))) ∘L (surjectiveGram (Bf x)).inverse) =
        (surjectivePseudoinverse (Bf x) ∘L Bf x) ∘L
          ((Bf' v)† ∘L (surjectiveGram (Bf x)).inverse) := by
    rw [hAc]
    simp only [ContinuousLinearMap.comp_assoc]
  have e2 :
      (Bf x)† ∘L (((surjectiveGram (Bf x)).inverse ∘L
          ((Bf' v) ∘L ((Bf x)†))) ∘L (surjectiveGram (Bf x)).inverse) =
        surjectivePseudoinverse (Bf x) ∘L
          ((Bf' v) ∘L surjectivePseudoinverse (Bf x)) := by
    rw [hAc]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [e1, e2, hAadj, sub_comp, id_comp]
  abel

/-- `I - A B` is the orthogonal projection onto `ker B`, hence a contraction. -/
theorem norm_one_sub_surjectivePseudoinverse_comp_le_one (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    ‖ContinuousLinearMap.id ℝ E - (surjectivePseudoinverse B).comp B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, one_mul]
  have hz : x - surjectivePseudoinverse B (B x) ∈ B.ker :=
    sub_surjectivePseudoinverse_mem_ker B hB (x := x) (y := B x) rfl
  have hort : inner ℝ (surjectivePseudoinverse B (B x))
      (x - surjectivePseudoinverse B (B x)) = 0 := by
    rw [real_inner_comm]
    exact inner_surjectivePseudoinverse_eq_zero_of_mem_ker B (B x) hz
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real
    (x := surjectivePseudoinverse B (B x))
    (y := x - surjectivePseudoinverse B (B x)) hort
  have hsum :
      surjectivePseudoinverse B (B x) + (x - surjectivePseudoinverse B (B x)) = x := by
    abel
  rw [hsum] at hpyth
  have hsq : ‖x - surjectivePseudoinverse B (B x)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖surjectivePseudoinverse B (B x)‖]
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h

/-- The derivative obeys `‖DA[B][E]‖ ≤ 2 ‖E‖ ‖A‖²`; the factor two comes from
the two terms in the closed derivative formula. -/
theorem norm_fderiv_surjectivePseudoinverse_apply_le
    {Bf : X → E →L[ℝ] F} {Bf' : X →L[ℝ] (E →L[ℝ] F)} {x : X}
    (hB : HasFDerivAt Bf Bf' x) (hsurj : Function.Surjective (Bf x)) (v : X) :
    ‖fderiv ℝ (fun y => surjectivePseudoinverse (Bf y)) x v‖ ≤
      2 * ‖Bf' v‖ * ‖surjectivePseudoinverse (Bf x)‖ ^ 2 := by
  rw [fderiv_surjectivePseudoinverse_apply hB hsurj v]
  set A := surjectivePseudoinverse (Bf x) with hAdef
  have hV' : ‖(Bf' v)†‖ = ‖Bf' v‖ := LinearIsometryEquiv.norm_map _ _
  have hA' : ‖A†‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
  have hP : ‖ContinuousLinearMap.id ℝ E - A ∘L Bf x‖ ≤ 1 :=
    norm_one_sub_surjectivePseudoinverse_comp_le_one _ hsurj
  have h1 : ‖A ∘L ((Bf' v) ∘L A)‖ ≤ ‖A‖ * ‖Bf' v‖ * ‖A‖ :=
    calc
      ‖A ∘L ((Bf' v) ∘L A)‖ ≤ ‖A‖ * ‖(Bf' v) ∘L A‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ * (‖Bf' v‖ * ‖A‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = ‖A‖ * ‖Bf' v‖ * ‖A‖ := (mul_assoc _ _ _).symm
  have hQ : ‖(Bf' v)† ∘L (A† ∘L A)‖ ≤ ‖Bf' v‖ * (‖A‖ * ‖A‖) :=
    calc
      ‖(Bf' v)† ∘L (A† ∘L A)‖ ≤ ‖(Bf' v)†‖ * ‖A† ∘L A‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(Bf' v)†‖ * (‖A†‖ * ‖A‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = ‖Bf' v‖ * (‖A‖ * ‖A‖) := by rw [hV', hA']
  have h2 :
      ‖(ContinuousLinearMap.id ℝ E - A ∘L Bf x) ∘L
          ((Bf' v)† ∘L (A† ∘L A))‖ ≤ 1 * (‖Bf' v‖ * (‖A‖ * ‖A‖)) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hP hQ (norm_nonneg _) zero_le_one)
  calc
    ‖-(A ∘L ((Bf' v) ∘L A)) +
        (ContinuousLinearMap.id ℝ E - A ∘L Bf x) ∘L
          ((Bf' v)† ∘L (A† ∘L A))‖ ≤
        ‖-(A ∘L ((Bf' v) ∘L A))‖ +
          ‖(ContinuousLinearMap.id ℝ E - A ∘L Bf x) ∘L
            ((Bf' v)† ∘L (A† ∘L A))‖ := norm_add_le _ _
    _ = ‖A ∘L ((Bf' v) ∘L A)‖ +
          ‖(ContinuousLinearMap.id ℝ E - A ∘L Bf x) ∘L
            ((Bf' v)† ∘L (A† ∘L A))‖ := by rw [norm_neg]
    _ ≤ ‖A‖ * ‖Bf' v‖ * ‖A‖ + 1 * (‖Bf' v‖ * (‖A‖ * ‖A‖)) := add_le_add h1 h2
    _ = 2 * ‖Bf' v‖ * ‖A‖ ^ 2 := by ring

/-- If `Bf x` has lower singular bound `s` on the orthogonal complement
of its kernel, the pseudoinverse derivative obeys the explicit
`2 ‖Bf' v‖ s⁻²` estimate. -/
theorem norm_fderiv_surjectivePseudoinverse_apply_le_of_lower_bound
    {Bf : X → E →L[ℝ] F} {BfPrime : X →L[ℝ] (E →L[ℝ] F)} {x : X}
    (hB : HasFDerivAt Bf BfPrime x) (hsurj : Function.Surjective (Bf x))
    {s : ℝ} (hs : 0 < s)
    (hlb : ∀ z ∈ (Bf x).kerᗮ, s * ‖z‖ ≤ ‖Bf x z‖) (v : X) :
    ‖fderiv ℝ (fun y => surjectivePseudoinverse (Bf y)) x v‖ ≤
      2 * ‖BfPrime v‖ * (s⁻¹) ^ 2 := by
  have hder := norm_fderiv_surjectivePseudoinverse_apply_le hB hsurj v
  have hA := norm_surjectivePseudoinverse_le_inv_of_lower_bound (Bf x) hsurj hs hlb
  have hA2 : ‖surjectivePseudoinverse (Bf x)‖ ^ 2 ≤ (s⁻¹) ^ 2 := by
    gcongr
  have hc : 0 ≤ 2 * ‖BfPrime v‖ := mul_nonneg (by norm_num) (norm_nonneg _)
  have h2le : 2 * ‖BfPrime v‖ * ‖surjectivePseudoinverse (Bf x)‖ ^ 2 ≤
      2 * ‖BfPrime v‖ * (s⁻¹) ^ 2 :=
    mul_le_mul_of_nonneg_left hA2 hc
  exact hder.trans h2le

/-- If the derivative of the operator family has pointwise Lipschitz bound
`L`, the pseudoinverse derivative has constant `2 L s⁻²`.  No separate
nonnegativity hypothesis on `L` is needed: it is already forced wherever the
pointwise bound is nontrivial. -/
theorem norm_fderiv_surjectivePseudoinverse_apply_le_of_lipschitz
    {Bf : X → E →L[ℝ] F} {BfPrime : X →L[ℝ] (E →L[ℝ] F)} {x : X}
    (hB : HasFDerivAt Bf BfPrime x) (hsurj : Function.Surjective (Bf x))
    {s : ℝ} (hs : 0 < s)
    (hlb : ∀ z ∈ (Bf x).kerᗮ, s * ‖z‖ ≤ ‖Bf x z‖)
    {L : ℝ} (hLip : ∀ v, ‖BfPrime v‖ ≤ L * ‖v‖) (v : X) :
    ‖fderiv ℝ (fun y => surjectivePseudoinverse (Bf y)) x v‖ ≤
      (2 * L * (s⁻¹) ^ 2) * ‖v‖ := by
  calc
    ‖fderiv ℝ (fun y => surjectivePseudoinverse (Bf y)) x v‖ ≤
        2 * ‖BfPrime v‖ * (s⁻¹) ^ 2 :=
      norm_fderiv_surjectivePseudoinverse_apply_le_of_lower_bound hB hsurj hs hlb v
    _ ≤ 2 * (L * ‖v‖) * (s⁻¹) ^ 2 := by
      gcongr
      exact hLip v
    _ = (2 * L * (s⁻¹) ^ 2) * ‖v‖ := by ring

end CFG
