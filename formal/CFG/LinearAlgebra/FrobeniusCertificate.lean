import CFG.LinearAlgebra.RightInverseCertificate
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Frobenius certificates for finite real matrices

This file connects a finite, entrywise sum-of-squares calculation to the
operator-norm hypotheses in `CFG.LinearAlgebra.RightInverseCertificate`.
It also propagates a certificate at one derivative to every derivative in a
closed ball when an explicit Lipschitz remainder estimate is available.
-/

namespace CFG

noncomputable section

open Matrix

/-- The continuous linear map between Euclidean spaces represented by a real
matrix.  This definition also works for rectangular matrices. -/
def matrixEuclideanCLM {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (Matrix.toEuclideanLin (m := m) (n := n) (𝕜 := ℝ)).trans
    LinearMap.toContinuousLinearMap A

@[simp]
theorem matrixEuclideanCLM_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    matrixEuclideanCLM A x =
      (EuclideanSpace.equiv m ℝ).symm (A *ᵥ (EuclideanSpace.equiv n ℝ) x) :=
  rfl

/-- The squared Frobenius norm, deliberately exposed as a finite sum.  For
rational matrices this expression is a rational number and can therefore be
checked exactly after coercion to `ℝ`. -/
def matrixFrobeniusSq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

theorem matrixFrobeniusSq_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : 0 ≤ matrixFrobeniusSq A := by
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (A i j)

/-- The Euclidean operator norm of a real matrix is bounded by the square
root of its finite entrywise sum of squares. -/
theorem norm_matrixEuclideanCLM_le_sqrt_frobeniusSq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) :
    ‖matrixEuclideanCLM A‖ ≤ Real.sqrt (matrixFrobeniusSq A) := by
  classical
  let := Matrix.frobeniusNormedAddCommGroup (m := m) (n := n) (α := ℝ)
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
  change ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ ≤
    Real.sqrt (matrixFrobeniusSq A) * ‖x‖
  have hmul := Matrix.frobenius_norm_mul A
    (Matrix.replicateCol (Fin 1) (WithLp.ofLp x))
  rw [← Matrix.replicateCol_mulVec] at hmul
  simpa [matrixFrobeniusSq, Matrix.frobenius_norm_def, EuclideanSpace.norm_eq,
    Real.sqrt_eq_rpow] using hmul

/-- A purely algebraic squared bound implies the desired operator-norm
bound.  The side condition `0 ≤ c` is intended to be discharged by exact
rational arithmetic. -/
theorem norm_matrixEuclideanCLM_le_of_frobeniusSq_le_sq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hA : matrixFrobeniusSq A ≤ c ^ 2) :
    ‖matrixEuclideanCLM A‖ ≤ c := by
  refine (norm_matrixEuclideanCLM_le_sqrt_frobeniusSq A).trans ?_
  rw [← Real.sqrt_sq hc]
  exact Real.sqrt_le_sqrt hA

@[simp]
theorem matrixEuclideanCLM_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    matrixEuclideanCLM (0 : Matrix m n ℝ) = 0 := by
  simp [matrixEuclideanCLM]

@[simp]
theorem matrixEuclideanCLM_sub {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix m n ℝ) :
    matrixEuclideanCLM (A - B) = matrixEuclideanCLM A - matrixEuclideanCLM B := by
  simp [matrixEuclideanCLM]

@[simp]
theorem matrixEuclideanCLM_one {n : Type*} [Fintype n] [DecidableEq n] :
    matrixEuclideanCLM (1 : Matrix n n ℝ) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply (EuclideanSpace.equiv n ℝ).injective
  change (1 : Matrix n n ℝ) *ᵥ WithLp.ofLp x = WithLp.ofLp x
  exact Matrix.one_mulVec _

@[simp]
theorem matrixEuclideanCLM_mul
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    matrixEuclideanCLM (A * B) = (matrixEuclideanCLM A).comp (matrixEuclideanCLM B) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (EuclideanSpace.equiv l ℝ).injective
  change (A * B) *ᵥ WithLp.ofLp x = A *ᵥ (B *ᵥ WithLp.ofLp x)
  exact (Matrix.mulVec_mulVec (WithLp.ofLp x) A B).symm

/-- A fully finite matrix certificate.  All three analytic norm estimates
(residual, approximation, and candidate inverse) are derived from entrywise
sums of squares. -/
theorem exists_rightInverse_of_matrix_frobenius_certificate
    {m n : Type*} [Fintype m] [Fintype n] [Nonempty m]
    [DecidableEq m] [DecidableEq n]
    (B Bhat : Matrix m n ℝ) (R : Matrix n m ℝ)
    {q e r : ℝ} (hq0 : 0 ≤ q) (he0 : 0 ≤ e) (hr0 : 0 ≤ r)
    (hres : matrixFrobeniusSq (1 - Bhat * R) ≤ q ^ 2)
    (happrox : matrixFrobeniusSq (B - Bhat) ≤ e ^ 2)
    (hR : matrixFrobeniusSq R ≤ r ^ 2)
    (hmargin : q + e * r < 1) :
    ∃ S : EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ n,
      (matrixEuclideanCLM B).comp S = 1 := by
  have hq :
      ‖(1 : EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m) -
          (matrixEuclideanCLM Bhat).comp (matrixEuclideanCLM R)‖ ≤ q := by
    rw [← matrixEuclideanCLM_one, ← matrixEuclideanCLM_mul,
      ← matrixEuclideanCLM_sub]
    exact norm_matrixEuclideanCLM_le_of_frobeniusSq_le_sq _ hq0 hres
  have he : ‖matrixEuclideanCLM B - matrixEuclideanCLM Bhat‖ ≤ e := by
    rw [← matrixEuclideanCLM_sub]
    exact norm_matrixEuclideanCLM_le_of_frobeniusSq_le_sq _ he0 happrox
  have hRnorm : ‖matrixEuclideanCLM R‖ ≤ r :=
    norm_matrixEuclideanCLM_le_of_frobeniusSq_le_sq _ hr0 hR
  apply exists_rightInverse_of_approx
    (matrixEuclideanCLM B) (matrixEuclideanCLM Bhat) (matrixEuclideanCLM R) hq he
  calc
    q + e * ‖matrixEuclideanCLM R‖ ≤ q + e * r := by
      simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hRnorm he0) q
    _ < 1 := hmargin

/-- A Lipschitz estimate for a family of candidate derivatives turns a
pointwise approximation at `x₀` into a uniform approximation on a closed
ball. -/
theorem norm_sub_reference_le_on_closedBall
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : E → E →L[ℝ] F) (Bhat : E →L[ℝ] F)
    (x₀ : E) {L ρ e : ℝ} (hL : 0 ≤ L)
    (hcenter : ‖D x₀ - Bhat‖ ≤ e)
    (hLip : ∀ x ∈ Metric.closedBall x₀ ρ,
      ‖D x - D x₀‖ ≤ L * ‖x - x₀‖) :
    ∀ x ∈ Metric.closedBall x₀ ρ, ‖D x - Bhat‖ ≤ e + L * ρ := by
  intro x hx
  have hdist : ‖x - x₀‖ ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  calc
    ‖D x - Bhat‖ ≤ ‖D x - D x₀‖ + ‖D x₀ - Bhat‖ := by
      rw [show D x - Bhat = (D x - D x₀) + (D x₀ - Bhat) by abel]
      exact norm_add_le _ _
    _ ≤ L * ‖x - x₀‖ + e := add_le_add (hLip x hx) hcenter
    _ ≤ L * ρ + e := by
      simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hdist hL) e
    _ = e + L * ρ := add_comm _ _

/-- Uniform quantitative right-inverse certificates on a closed ball.  The
only variation hypothesis is the explicit Lipschitz derivative error. -/
theorem exists_rightInverse_on_closedBall_of_lipschitz_error
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]
    (D : E → E →L[ℝ] F) (Bhat : E →L[ℝ] F) (R : F →L[ℝ] E)
    (x₀ : E) {L ρ q e : ℝ} (hL : 0 ≤ L)
    (hq : ‖(1 : F →L[ℝ] F) - Bhat.comp R‖ ≤ q)
    (hcenter : ‖D x₀ - Bhat‖ ≤ e)
    (hLip : ∀ x ∈ Metric.closedBall x₀ ρ,
      ‖D x - D x₀‖ ≤ L * ‖x - x₀‖)
    (hmargin : q + (e + L * ρ) * ‖R‖ < 1) :
    ∀ x ∈ Metric.closedBall x₀ ρ,
      ∃ S : F →L[ℝ] E, (D x).comp S = 1 ∧
        ‖S‖ ≤ ‖R‖ / (1 - q - (e + L * ρ) * ‖R‖) := by
  intro x hx
  apply exists_rightInverse_norm_le_of_approx (D x) Bhat R hq
    (norm_sub_reference_le_on_closedBall D Bhat x₀ hL hcenter hLip x hx) hmargin

/-- Specialization of the closed-ball result to the actual Fréchet
derivative.  Differentiability is returned alongside the certificate so the
statement cannot certify a merely default value of `fderiv`. -/
theorem exists_rightInverse_fderiv_on_closedBall
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]
    (f : E → F) (Bhat : E →L[ℝ] F) (R : F →L[ℝ] E)
    (x₀ : E) {L ρ q e : ℝ} (hL : 0 ≤ L)
    (hdiff : ∀ x ∈ Metric.closedBall x₀ ρ, DifferentiableAt ℝ f x)
    (hq : ‖(1 : F →L[ℝ] F) - Bhat.comp R‖ ≤ q)
    (hcenter : ‖fderiv ℝ f x₀ - Bhat‖ ≤ e)
    (hLip : ∀ x ∈ Metric.closedBall x₀ ρ,
      ‖fderiv ℝ f x - fderiv ℝ f x₀‖ ≤ L * ‖x - x₀‖)
    (hmargin : q + (e + L * ρ) * ‖R‖ < 1) :
    ∀ x ∈ Metric.closedBall x₀ ρ,
      DifferentiableAt ℝ f x ∧
      ∃ S : F →L[ℝ] E, (fderiv ℝ f x).comp S = 1 ∧
        ‖S‖ ≤ ‖R‖ / (1 - q - (e + L * ρ) * ‖R‖) := by
  intro x hx
  refine ⟨hdiff x hx, ?_⟩
  exact exists_rightInverse_on_closedBall_of_lipschitz_error
    (fun y ↦ fderiv ℝ f y) Bhat R x₀ hL hq hcenter hLip hmargin x hx

end

end CFG
