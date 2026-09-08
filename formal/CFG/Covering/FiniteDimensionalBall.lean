import CFG.Covering.BoxGrid
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Quantitative covers of balls in arbitrary finite-dimensional normed spaces

The explicit grid lives in the sup-norm coordinate model.  A continuous
linear equivalence transports it to any finite-dimensional real normed space.
The resulting constants retain the norms of the chosen coordinate map and its
inverse; the important exponent is the true finrank of the space.
-/

namespace CFG.Covering

open Set
open scoped ENNReal NNReal

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- A globally Lipschitz map transports an external cover; unlike the
`LipschitzOnWith` version, its centers need not belong to the covered set. -/
theorem isCover_image_lipschitzWith
    {s C : Set X} {f : X → Y} {K ε : ℝ≥0}
    (hcover : Metric.IsCover ε s C) (hf : LipschitzWith K f) :
    Metric.IsCover (K * ε) (f '' s) (f '' C) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc, hdist⟩ := hcover hx
  refine ⟨f c, ⟨c, hc, rfl⟩, ?_⟩
  dsimp at hdist ⊢
  grw [hf x c, hdist]

/-- A chosen coordinate equivalence sends the radius-`R` ball into the
sup-norm coordinate box of radius `‖e‖ R`. -/
theorem image_closedBall_subset_supNormBox
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (e : V ≃L[ℝ] (Fin n → ℝ)) (R : ℝ≥0) :
    e '' Metric.closedBall (0 : V) R ⊆
      supNormBox n ((‖e.toContinuousLinearMap‖₊ * R : ℝ≥0) : ℝ) := by
  rintro y ⟨x, hx, rfl⟩ i
  rw [Metric.mem_closedBall] at hx
  have hxnorm : ‖x‖ ≤ (R : ℝ) := by simpa [dist_zero_right] using hx
  have hexnorm : ‖e x‖ ≤ (‖e.toContinuousLinearMap‖₊ * R : ℝ≥0) := by
    calc
      ‖e x‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x‖ :=
        e.toContinuousLinearMap.le_opNorm x
      _ ≤ ‖e.toContinuousLinearMap‖ * (R : ℝ) := by gcongr
      _ = (‖e.toContinuousLinearMap‖₊ * R : ℝ≥0) := by simp
  have hdist : dist (e x) 0 ≤
      ((‖e.toContinuousLinearMap‖₊ * R : ℝ≥0) : ℝ) := by
    simpa [dist_zero_right] using hexnorm
  have hi := (dist_pi_le_iff (show 0 ≤
      ((‖e.toContinuousLinearMap‖₊ * R : ℝ≥0) : ℝ) by positivity)).mp hdist i
  simpa [Real.dist_eq] using hi

/-- Every finite-dimensional real normed ball has an explicit polynomial
cover after choosing linear coordinates.  The cover radius pays the inverse
coordinate Lipschitz constant; the center count has degree exactly `n`.

This theorem constructs the coordinate equivalence from `finrank V = n`, so
no covering certificate is assumed. -/
theorem exists_externalCoveringNumber_closedBall_le_gridSteps_of_finrank_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ}
    (hn : Module.finrank ℝ V = n) (R : ℝ≥0) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ e : V ≃L[ℝ] (Fin n → ℝ),
      Metric.externalCoveringNumber (‖e.symm.toContinuousLinearMap‖₊ * ε)
          (Metric.closedBall (0 : V) R) ≤
        ((2 * gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε + 1) ^ n : ℕ) := by
  let e : V ≃L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (Module.finrank_fin_fun ℝ).symm)
  refine ⟨e, ?_⟩
  let C : Set (Fin n → ℝ) :=
    boxGrid n (gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε) ε
  have hcoverBox : Metric.IsCover ε
      (supNormBox n (((‖e.toContinuousLinearMap‖₊ * R : ℝ≥0) : ℝ))) C :=
    isCover_supNormBox_gridSteps (n := n) (‖e.toContinuousLinearMap‖₊ * R) hε
  have hcoverImage : Metric.IsCover (‖e.symm.toContinuousLinearMap‖₊ * ε)
      (e.symm '' supNormBox n
        (((‖e.toContinuousLinearMap‖₊ * R : ℝ≥0) : ℝ)))
      (e.symm '' C) :=
    isCover_image_lipschitzWith hcoverBox
      e.symm.toContinuousLinearMap.lipschitzWith
  have hballSubset : Metric.closedBall (0 : V) R ⊆
      e.symm '' supNormBox n
        (((‖e.toContinuousLinearMap‖₊ * R : ℝ≥0) : ℝ)) := by
    intro x hx
    refine ⟨e x, image_closedBall_subset_supNormBox e R ⟨x, hx, rfl⟩, ?_⟩
    exact e.symm_apply_apply x
  have hcoverBall : Metric.IsCover (‖e.symm.toContinuousLinearMap‖₊ * ε)
      (Metric.closedBall (0 : V) R) (e.symm '' C) :=
    hcoverImage.anti hballSubset
  calc
    Metric.externalCoveringNumber (‖e.symm.toContinuousLinearMap‖₊ * ε)
        (Metric.closedBall (0 : V) R) ≤ (e.symm '' C).encard :=
      hcoverBall.externalCoveringNumber_le_encard
    _ ≤ C.encard := Set.encard_image_le _ _
    _ ≤ ((2 * gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε + 1) ^ n : ℕ) :=
      encard_boxGrid_le n
        (gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε) ε

/-- Internal-center version for an open ball.  The factor `2` is the honest
price paid when restricting an internal cover of the enclosing coordinate box
to an internal cover of the ball.  Consequently these centers may safely be
inserted into a map that is only Lipschitz on the ball. -/
theorem exists_coveringNumber_ball_le_gridSteps_of_finrank_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ}
    (hn : Module.finrank ℝ V = n) (R : ℝ≥0) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ e : V ≃L[ℝ] (Fin n → ℝ),
      Metric.coveringNumber
          (2 * (‖e.symm.toContinuousLinearMap‖₊ * ε))
          (Metric.ball (0 : V) R) ≤
        ((2 * gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε + 1) ^ n : ℕ) := by
  let e : V ≃L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (Module.finrank_fin_fun ℝ).symm)
  refine ⟨e, ?_⟩
  let S : Set (Fin n → ℝ) :=
    supNormBox n
      ((gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε : ℝ) * (ε : ℝ))
  have hballSubset : Metric.ball (0 : V) R ⊆ e.symm '' S := by
    intro x hx
    have hxclosed : x ∈ Metric.closedBall (0 : V) R :=
      Metric.ball_subset_closedBall hx
    have hcoord := image_closedBall_subset_supNormBox e R ⟨x, hxclosed, rfl⟩
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    intro i
    exact (hcoord i).trans
      (radius_le_gridSteps_mul (‖e.toContinuousLinearMap‖₊ * R) hε)
  have himage : Metric.coveringNumber
      (‖e.symm.toContinuousLinearMap‖₊ * ε) (e.symm '' S) ≤
      Metric.coveringNumber ε S := by
    exact coveringNumber_image_le_coveringNumber
      e.symm.toContinuousLinearMap.lipschitzWith.lipschitzOnWith
  calc
    Metric.coveringNumber
        (2 * (‖e.symm.toContinuousLinearMap‖₊ * ε))
        (Metric.ball (0 : V) R) ≤
        Metric.coveringNumber
          ((2 * (‖e.symm.toContinuousLinearMap‖₊ * ε)) / 2)
          (e.symm '' S) := Metric.coveringNumber_subset_le hballSubset
    _ = Metric.coveringNumber
          (‖e.symm.toContinuousLinearMap‖₊ * ε) (e.symm '' S) := by
      congr 2
      simp
    _ ≤ Metric.coveringNumber ε S := himage
    _ ≤ ((2 * gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε + 1) ^ n : ℕ) := by
      exact coveringNumber_supNormBox_le
        (n := n) (m := gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε) hε

/-- The internal ball-cover bound with a caller-specified coordinate
equivalence.  This form lets later theorems choose their mesh as a function of
the desired target radius while retaining the same coordinates. -/
theorem coveringNumber_ball_le_gridSteps_with_coordinates
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (e : V ≃L[ℝ] (Fin n → ℝ))
    (R : ℝ≥0) {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.coveringNumber
        (2 * (‖e.symm.toContinuousLinearMap‖₊ * ε))
        (Metric.ball (0 : V) R) ≤
      ((2 * gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε + 1) ^ n : ℕ) := by
  let S : Set (Fin n → ℝ) :=
    supNormBox n
      ((gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε : ℝ) * (ε : ℝ))
  have hballSubset : Metric.ball (0 : V) R ⊆ e.symm '' S := by
    intro x hx
    have hxclosed : x ∈ Metric.closedBall (0 : V) R :=
      Metric.ball_subset_closedBall hx
    have hcoord := image_closedBall_subset_supNormBox e R ⟨x, hxclosed, rfl⟩
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    intro i
    exact (hcoord i).trans
      (radius_le_gridSteps_mul (‖e.toContinuousLinearMap‖₊ * R) hε)
  have himage : Metric.coveringNumber
      (‖e.symm.toContinuousLinearMap‖₊ * ε) (e.symm '' S) ≤
      Metric.coveringNumber ε S := by
    exact coveringNumber_image_le_coveringNumber
      e.symm.toContinuousLinearMap.lipschitzWith.lipschitzOnWith
  calc
    Metric.coveringNumber
        (2 * (‖e.symm.toContinuousLinearMap‖₊ * ε))
        (Metric.ball (0 : V) R) ≤
        Metric.coveringNumber
          ((2 * (‖e.symm.toContinuousLinearMap‖₊ * ε)) / 2)
          (e.symm '' S) := Metric.coveringNumber_subset_le hballSubset
    _ = Metric.coveringNumber
          (‖e.symm.toContinuousLinearMap‖₊ * ε) (e.symm '' S) := by
      congr 2
      simp
    _ ≤ Metric.coveringNumber ε S := himage
    _ ≤ ((2 * gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε + 1) ^ n : ℕ) := by
      exact coveringNumber_supNormBox_le
        (n := n) (m := gridSteps (‖e.toContinuousLinearMap‖₊ * R) ε) hε

end CFG.Covering
