import CFG.Covering.FiniteCover
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Pi.Interval

namespace CFG

open Set
open scoped ENNReal NNReal

namespace Covering

/-- Integer multi-indices in the symmetric coordinate box `[-m,m]^n`. -/
def integerBox (n m : ℕ) : Finset (Fin n → ℤ) :=
  Finset.Icc (fun _ => -(m : ℤ)) (fun _ => (m : ℤ))

/-- A coordinate grid with mesh `ε`, represented in the ambient real function
space equipped with its sup norm. -/
def boxGrid (n m : ℕ) (ε : ℝ≥0) : Set (Fin n → ℝ) :=
  (fun z i => (ε : ℝ) * (z i : ℝ)) '' (integerBox n m : Set (Fin n → ℤ))

/-- The closed coordinate box of radius `R`. -/
def supNormBox (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, |x i| ≤ R}

@[simp]
theorem card_integerBox (n m : ℕ) :
    (integerBox n m).card = (2 * m + 1) ^ n := by
  rw [integerBox, Pi.card_Icc]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [show (m : ℤ) + 1 - -(m : ℤ) = ((2 * m + 1 : ℕ) : ℤ) by omega]
  exact Int.toNat_natCast _

/-- The explicit grid has at most `(2m+1)^n` centers.  This statement is in
`ℕ∞`, exactly the codomain used by mathlib's covering numbers. -/
theorem encard_boxGrid_le (n m : ℕ) (ε : ℝ≥0) :
    (boxGrid n m ε).encard ≤ ((2 * m + 1) ^ n : ℕ) := by
  calc
    (boxGrid n m ε).encard ≤ (integerBox n m : Set (Fin n → ℤ)).encard :=
      Set.encard_image_le _ _
    _ = ((2 * m + 1) ^ n : ℕ) := by
      simp

/-- At positive mesh size the parametrization has no collisions, so the upper
bound on the number of centers is exact. -/
theorem encard_boxGrid_eq {n m : ℕ} {ε : ℝ≥0} (hε : ε ≠ 0) :
    (boxGrid n m ε).encard = ((2 * m + 1) ^ n : ℕ) := by
  have hεreal : (ε : ℝ) ≠ 0 := by exact_mod_cast hε
  have hinj : Function.Injective (fun z : Fin n → ℤ =>
      fun i => (ε : ℝ) * (z i : ℝ)) := by
    intro z w hzw
    funext i
    have hcast : (z i : ℝ) = (w i : ℝ) :=
      mul_left_cancel₀ hεreal (congrFun hzw i)
    exact_mod_cast hcast
  rw [boxGrid, (hinj.injOn.encard_image)]
  simp

/-- Flooring each coordinate selects an index in the symmetric integer box. -/
private theorem floorIndex_mem_integerBox
    {n m : ℕ} {ε : ℝ≥0} (hε : ε ≠ 0) {x : Fin n → ℝ}
    (hx : x ∈ supNormBox n ((m : ℝ) * ε)) :
    (fun i => ⌊x i / (ε : ℝ)⌋) ∈ integerBox n m := by
  have hεposNN : 0 < ε := pos_iff_ne_zero.mpr hε
  have hεpos : 0 < (ε : ℝ) := by exact_mod_cast hεposNN
  rw [integerBox, Finset.mem_Icc]
  constructor
  · intro i
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hεpos).2
    simpa [neg_mul] using
      (abs_le.mp (hx i)).1
  · intro i
    have hquot : x i / (ε : ℝ) ≤ (m : ℝ) := by
      apply (div_le_iff₀ hεpos).2
      simpa [mul_comm] using (abs_le.mp (hx i)).2
    have := Int.floor_le_floor hquot
    simpa using this

theorem boxGrid_subset_supNormBox (n m : ℕ) (ε : ℝ≥0) :
    boxGrid n m ε ⊆ supNormBox n ((m : ℝ) * ε) := by
  rintro _ ⟨z, hz, rfl⟩ i
  have hz' : z ∈ integerBox n m := hz
  rw [integerBox, Finset.mem_Icc] at hz'
  have hlow : (-(m : ℤ) : ℝ) ≤ (z i : ℝ) := by exact_mod_cast hz'.1 i
  have hupp : (z i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hz'.2 i
  have habs : |(z i : ℝ)| ≤ (m : ℝ) := abs_le.mpr ⟨by simpa using hlow, hupp⟩
  rw [abs_mul, abs_of_nonneg ε.coe_nonneg]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left habs ε.coe_nonneg

/-- Every point of the radius-`mε` coordinate box is within sup-norm distance
`ε` of the explicit integer grid. -/
theorem isCover_supNormBox_boxGrid
    {n m : ℕ} {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.IsCover ε (supNormBox n ((m : ℝ) * ε)) (boxGrid n m ε) := by
  intro x hx
  let z : Fin n → ℤ := fun i => ⌊x i / (ε : ℝ)⌋
  let c : Fin n → ℝ := fun i => (ε : ℝ) * (z i : ℝ)
  refine ⟨c, ?_, ?_⟩
  · exact ⟨z, floorIndex_mem_integerBox hε hx, rfl⟩
  · change edist x c ≤ ε
    rw [edist_dist]
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_pi_le_iff ε.coe_nonneg]
    intro i
    rw [Real.dist_eq]
    have hεposNN : 0 < ε := pos_iff_ne_zero.mpr hε
    have hεpos : 0 < (ε : ℝ) := by exact_mod_cast hεposNN
    have hlo : 0 ≤ x i - (ε : ℝ) * (z i : ℝ) := by
      rw [sub_nonneg]
      calc
        (ε : ℝ) * (z i : ℝ) ≤ (ε : ℝ) * (x i / (ε : ℝ)) := by
          gcongr
          exact Int.floor_le _
        _ = x i := by field_simp
    have hhi : x i - (ε : ℝ) * (z i : ℝ) ≤ (ε : ℝ) := by
      have hfract : x i / (ε : ℝ) < (z i : ℝ) + 1 := Int.lt_floor_add_one _
      have hmul := mul_lt_mul_of_pos_left hfract hεpos
      rw [mul_add, mul_one] at hmul
      have hcancel : (ε : ℝ) * (x i / (ε : ℝ)) = x i := by field_simp
      linarith
    simpa [c, abs_of_nonneg hlo] using hhi

/-- Explicit polynomial upper bound for the external covering number of a
coordinate box. -/
theorem externalCoveringNumber_supNormBox_le
    {n m : ℕ} {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.externalCoveringNumber ε (supNormBox n ((m : ℝ) * ε)) ≤
      ((2 * m + 1) ^ n : ℕ) := by
  exact (Metric.IsCover.externalCoveringNumber_le_encard
    (isCover_supNormBox_boxGrid hε)).trans (encard_boxGrid_le n m ε)

/-- For an exactly mesh-aligned box the same grid is internal, hence it also
bounds mathlib's internal covering number. -/
theorem coveringNumber_supNormBox_le
    {n m : ℕ} {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.coveringNumber ε (supNormBox n ((m : ℝ) * ε)) ≤
      ((2 * m + 1) ^ n : ℕ) := by
  exact (Metric.IsCover.coveringNumber_le_encard
    (boxGrid_subset_supNormBox n m ε) (isCover_supNormBox_boxGrid hε)).trans
      (encard_boxGrid_le n m ε)

/-- Number of mesh intervals needed from the origin to radius `R`. -/
noncomputable def gridSteps (R ε : ℝ≥0) : ℕ :=
  ⌈(R : ℝ) / (ε : ℝ)⌉₊

theorem gridSteps_lt_div_add_one (R ε : ℝ≥0) :
    (gridSteps R ε : ℝ) < (R : ℝ) / (ε : ℝ) + 1 := by
  exact Nat.ceil_lt_add_one (div_nonneg R.coe_nonneg ε.coe_nonneg)

/-- A ceiling-free real-valued estimate for the cardinality polynomial. -/
theorem gridCard_real_le_polynomial (n : ℕ) (R ε : ℝ≥0) :
    (((2 * gridSteps R ε + 1) ^ n : ℕ) : ℝ) ≤
      (2 * ((R : ℝ) / (ε : ℝ)) + 3) ^ n := by
  rw [Nat.cast_pow]
  gcongr
  have hs := gridSteps_lt_div_add_one R ε
  push_cast
  linarith

theorem radius_le_gridSteps_mul
    (R : ℝ≥0) {ε : ℝ≥0} (hε : ε ≠ 0) :
    (R : ℝ) ≤ (gridSteps R ε : ℝ) * (ε : ℝ) := by
  have hεposNN : 0 < ε := pos_iff_ne_zero.mpr hε
  have hεpos : 0 < (ε : ℝ) := by exact_mod_cast hεposNN
  have hceil : (R : ℝ) / (ε : ℝ) ≤ (gridSteps R ε : ℝ) := by
    exact Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hceil hεpos.le
  rw [div_mul_cancel₀ _ hεpos.ne'] at hmul
  simpa [mul_comm] using hmul

/-- The same explicit grid covers a coordinate box of an arbitrary radius,
after choosing the number of steps by a ceiling. -/
theorem isCover_supNormBox_gridSteps
    {n : ℕ} (R : ℝ≥0) {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.IsCover ε (supNormBox n R) (boxGrid n (gridSteps R ε) ε) := by
  apply (isCover_supNormBox_boxGrid (n := n) (m := gridSteps R ε) hε).anti
  intro x hx i
  exact (hx i).trans (radius_le_gridSteps_mul R hε)

/-- Scale-ready covering-number bound.  Its right-hand side is an explicit
degree-`n` polynomial in the ceiling of `R / ε`. -/
theorem externalCoveringNumber_supNormBox_le_gridSteps
    {n : ℕ} (R : ℝ≥0) {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.externalCoveringNumber ε (supNormBox n R) ≤
      ((2 * gridSteps R ε + 1) ^ n : ℕ) := by
  exact (Metric.IsCover.externalCoveringNumber_le_encard
    (isCover_supNormBox_gridSteps (n := n) R hε)).trans
      (encard_boxGrid_le n (gridSteps R ε) ε)

theorem closedBall_zero_subset_supNormBox (n : ℕ) (R : ℝ≥0) :
    Metric.closedBall (0 : Fin n → ℝ) R ⊆ supNormBox n R := by
  intro x hx i
  rw [Metric.mem_closedBall] at hx
  have hi := (dist_pi_le_iff R.coe_nonneg).mp hx i
  simpa [Real.dist_eq] using hi

/-- In particular, the closed ball in the finite-dimensional sup-norm model
has the same explicit polynomial external covering bound. -/
theorem externalCoveringNumber_closedBall_zero_le_gridSteps
    {n : ℕ} (R : ℝ≥0) {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.externalCoveringNumber ε
        (Metric.closedBall (0 : Fin n → ℝ) R) ≤
      ((2 * gridSteps R ε + 1) ^ n : ℕ) := by
  exact (Metric.externalCoveringNumber_mono_set
    (closedBall_zero_subset_supNormBox n R)).trans
      (externalCoveringNumber_supNormBox_le_gridSteps (n := n) R hε)

end Covering

end CFG
