import Mathlib

/-!
# Weighted upper-triangular flattening

For a real symmetric `n × n` matrix, the upper triangle is flattened with
weight `1` on the diagonal and weight `√2` off the diagonal.  The resulting
Euclidean norm is exactly the Frobenius norm.  All sums below are literal
finite sums over `Fin n`.

The second part records the physical constraint after entrywise
normalization.  Division by a zero background entry is explicitly defined to
be zero, and recovering the original row-sum constraint therefore requires
the stated compatibility hypothesis that the corresponding unnormalized
entry was already zero.
-/

namespace CFG

open scoped BigOperators

/-- Indices in the upper triangle, including the diagonal. -/
abbrev UpperTriangleIndex (n : ℕ) :=
  {p : Fin n × Fin n // p.1 ≤ p.2}

/-- Upper-triangular flattening with off-diagonal entries multiplied by `√2`. -/
noncomputable def weightedUpperFlatten {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    UpperTriangleIndex n → ℝ :=
  fun p => if p.1.1 = p.1.2 then A p.1.1 p.1.2 else Real.sqrt 2 * A p.1.1 p.1.2

/-- The squared Euclidean norm of a finite real coordinate vector. -/
def euclideanSq {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

/-- The squared Frobenius norm, written as an exact finite double sum. -/
def frobeniusSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Euclidean norm associated with `euclideanSq`. -/
noncomputable def euclideanNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (euclideanSq x)

/-- Frobenius norm associated with the exact entrywise square sum. -/
noncomputable def frobeniusNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (frobeniusSq A)

private def upperContribution {n : ℕ} (f : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  if i = j then f i j else if i < j then 2 * f i j else 0

private theorem sum_upperTriangle_eq_sum_upperContribution {n : ℕ}
    (f : Fin n → Fin n → ℝ) :
    (∑ p : UpperTriangleIndex n,
        if p.1.1 = p.1.2 then f p.1.1 p.1.2 else 2 * f p.1.1 p.1.2) =
      ∑ i, ∑ j, upperContribution f i j := by
  classical
  have hsub :
      (∑ p : UpperTriangleIndex n,
          if p.1.1 = p.1.2 then f p.1.1 p.1.2 else 2 * f p.1.1 p.1.2) =
        ∑ p : Fin n × Fin n,
          if p.1 ≤ p.2 then
            (if p.1 = p.2 then f p.1 p.2 else 2 * f p.1 p.2)
          else 0 := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_subtype_eq_sum_filter]
    congr 1
    ext p
    simp
  rw [hsub, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [upperContribution]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hij, hij.ne, hij.le]
  · simp
  · have hnle : ¬i ≤ j := not_le.mpr hji
    have hne : i ≠ j := ne_of_gt hji
    simp [hne, hnle, hji.not_gt]

private theorem sum_upperContribution_eq_full {n : ℕ}
    (f : Fin n → Fin n → ℝ) (hsymm : ∀ i j, f j i = f i j) :
    (∑ i, ∑ j, upperContribution f i j) = ∑ i, ∑ j, f i j := by
  classical
  have hpair (i j : Fin n) :
      upperContribution f i j + upperContribution f j i = f i j + f j i := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [upperContribution, hij, hij.ne, hij.ne', hij.not_gt]
      rw [hsymm i j]
      ring
    · simp [upperContribution]
    · simp [upperContribution, hji, hji.ne, hji.ne', hji.not_gt]
      rw [hsymm i j]
      ring
  have hswapUpper :
      (∑ i, ∑ j, upperContribution f j i) =
        ∑ i, ∑ j, upperContribution f i j := by
    rw [Finset.sum_comm]
  have hswapFull :
      (∑ i, ∑ j, f j i) = ∑ i, ∑ j, f i j := by
    rw [Finset.sum_comm]
  have htwice :
      (∑ i, ∑ j, upperContribution f i j) +
          (∑ i, ∑ j, upperContribution f i j) =
        (∑ i, ∑ j, f i j) + (∑ i, ∑ j, f i j) := by
    calc
      (∑ i, ∑ j, upperContribution f i j) +
          (∑ i, ∑ j, upperContribution f i j) =
          (∑ i, ∑ j, upperContribution f i j) +
            (∑ i, ∑ j, upperContribution f j i) := by rw [hswapUpper]
      _ = ∑ i, ∑ j,
          (upperContribution f i j + upperContribution f j i) := by
            simp_rw [Finset.sum_add_distrib]
      _ = ∑ i, ∑ j, (f i j + f j i) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hpair i j
      _ = (∑ i, ∑ j, f i j) + (∑ i, ∑ j, f j i) := by
            simp_rw [Finset.sum_add_distrib]
      _ = (∑ i, ∑ j, f i j) + (∑ i, ∑ j, f i j) := by rw [hswapFull]
  linarith

/-- Squared isometry identity for the `√2`-weighted upper-triangle flattening.
The symmetry hypothesis is essential: it identifies the omitted lower
triangle with the retained upper triangle. -/
theorem euclideanSq_weightedUpperFlatten_eq_frobeniusSq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    euclideanSq (weightedUpperFlatten A) = frobeniusSq A := by
  classical
  let f : Fin n → Fin n → ℝ := fun i j => (A i j) ^ 2
  have hfsymm : ∀ i j, f j i = f i j := by
    intro i j
    simp only [f]
    rw [hA.apply]
  calc
    euclideanSq (weightedUpperFlatten A) =
        ∑ p : UpperTriangleIndex n,
          if p.1.1 = p.1.2 then f p.1.1 p.1.2 else 2 * f p.1.1 p.1.2 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.1.1 = p.1.2
      · simp [weightedUpperFlatten, f, hp]
      · simp only [weightedUpperFlatten, f, hp, ↓reduceIte]
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ = ∑ i, ∑ j, f i j :=
      (sum_upperTriangle_eq_sum_upperContribution f).trans
        (sum_upperContribution_eq_full f hfsymm)
    _ = frobeniusSq A := rfl

/-- Norm-level formulation: weighted upper-triangle flattening is an exact
Frobenius isometry on symmetric matrices. -/
theorem euclideanNorm_weightedUpperFlatten_eq_frobeniusNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    euclideanNorm (weightedUpperFlatten A) = frobeniusNorm A := by
  simp only [euclideanNorm, frobeniusNorm,
    euclideanSq_weightedUpperFlatten_eq_frobeniusSq A hA]

/-- Safe entrywise normalization: a zero background entry produces zero
instead of invoking division by zero implicitly. -/
noncomputable def entrywiseNormalize {n : ℕ}
    (background A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if background i j = 0 then 0 else A i j / background i j

/-- Away from zero background entries, weighted de-normalization recovers the
original entry. -/
theorem background_mul_entrywiseNormalize {n : ℕ}
    (background A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hbackground : background i j ≠ 0) :
    background i j * entrywiseNormalize background A i j = A i j := by
  simp only [entrywiseNormalize, hbackground, ↓reduceIte]
  field_simp

/-- Under the explicit zero-entry compatibility condition, safe normalized
coordinates satisfy `background ⊙ Y = A` entrywise. -/
theorem background_mul_entrywiseNormalize_eq {n : ℕ}
    (background A : Matrix (Fin n) (Fin n) ℝ)
    (hzero : ∀ i j, background i j = 0 → A i j = 0) (i j : Fin n) :
    background i j * entrywiseNormalize background A i j = A i j := by
  by_cases hbackground : background i j = 0
  · simp [entrywiseNormalize, hbackground, hzero i j hbackground]
  · exact background_mul_entrywiseNormalize background A i j hbackground

/-- If the unnormalized matrix has zero row sums, then its safely normalized
coordinates obey the physically correct *background-weighted* row-sum
constraint.  The zero-entry compatibility hypothesis is precisely what is
needed by the chosen zero-division convention. -/
theorem weighted_rowSum_entrywiseNormalize_eq_zero {n : ℕ}
    (background A : Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 0)
    (hzero : ∀ i j, background i j = 0 → A i j = 0) (i : Fin n) :
    ∑ j, background i j * entrywiseNormalize background A i j = 0 := by
  calc
    (∑ j, background i j * entrywiseNormalize background A i j) =
        ∑ j, A i j := by
      apply Finset.sum_congr rfl
      intro j _
      exact background_mul_entrywiseNormalize_eq background A hzero i j
    _ = 0 := hrow i

end CFG
