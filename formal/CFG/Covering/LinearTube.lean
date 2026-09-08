import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Elementary linear-tube reductions

These are the coordinate-free reductions at the start of M06.  They do not
claim the later singular-value grid bound, but they verify the residual
diameter estimate and the exact algebra used by a fixed whitening operator.
-/

namespace CFG.LinearTube

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Two points in the same radius-`δ` residual tube differ by at most `2δ`
after applying the linear observation. -/
theorem norm_map_sub_le_two_mul
    (J : E →L[ℝ] F) (x x₀ : E) (z : F) (δ : ℝ)
    (hx : ‖J x - z‖ ≤ δ) (hx₀ : ‖J x₀ - z‖ ≤ δ) :
    ‖J (x - x₀)‖ ≤ 2 * δ := by
  rw [map_sub]
  have hid : J x - J x₀ = (J x - z) - (J x₀ - z) := by abel
  rw [hid]
  calc
    ‖(J x - z) - (J x₀ - z)‖ ≤ ‖J x - z‖ + ‖J x₀ - z‖ := norm_sub_le _ _
    _ ≤ δ + δ := add_le_add hx hx₀
    _ = 2 * δ := by ring

omit [NormedSpace ℝ E] in
/-- Points in a radius-`R` parameter ball differ by at most `2R`. -/
theorem norm_sub_le_two_mul
    (x x₀ : E) (R : ℝ) (hx : ‖x‖ ≤ R) (hx₀ : ‖x₀‖ ≤ R) :
    ‖x - x₀‖ ≤ 2 * R := by
  calc
    ‖x - x₀‖ ≤ ‖x‖ + ‖x₀‖ := norm_sub_le _ _
    _ ≤ R + R := add_le_add hx hx₀
    _ = 2 * R := by ring

/-- Applying a fixed whitening operator to a residual is exactly the residual
of the composed observation map with whitened target. -/
theorem whitened_residual_eq
    (J : E →L[ℝ] F) (W : F →L[ℝ] G) (x : E) (z : F) :
    W (J x - z) = (W.comp J) x - W z := by simp

/-- Hence the two descriptions of a fixed-whitening tube are equivalent. -/
theorem mem_whitened_tube_iff
    (J : E →L[ℝ] F) (W : F →L[ℝ] G) (x : E) (z : F) (δ : ℝ) :
    ‖W (J x - z)‖ ≤ δ ↔ ‖(W.comp J) x - W z‖ ≤ δ := by
  rw [whitened_residual_eq]

/-! ### Explicit diagonal spectral coordinates

The following intermediate model deliberately uses the sup norm on finite
coordinate functions.  It is the coordinate box to which the Euclidean
spectral frame will later be transported; it is not confused with `CFG.Euc`.
-/

/-- The explicit diagonal observation in spectral coordinates,
`J(a,b)ᵢ = σᵢ aᵢ`.  The second factor is the kernel coordinate block. -/
noncomputable def diagonalObservationCLM {r k : ℕ} (σ : Fin r → ℝ) :
    ((Fin r → ℝ) × (Fin k → ℝ)) →L[ℝ] (Fin r → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i => σ i * x.1 i
      map_add' := by
        intro x y
        ext i
        simp [mul_add]
      map_smul' := by
        intro c x
        ext i
        simp [mul_left_comm] }

@[simp]
theorem diagonalObservationCLM_apply {r k : ℕ} (σ : Fin r → ℝ)
    (x : (Fin r → ℝ) × (Fin k → ℝ)) (i : Fin r) :
    diagonalObservationCLM σ x i = σ i * x.1 i := rfl

/-- A bounded diagonal residual tube in the spectral coordinate model. -/
def diagonalTube {r k : ℕ} (σ : Fin r → ℝ) (z : Fin r → ℝ)
    (R δ : ℝ) : Set ((Fin r → ℝ) × (Fin k → ℝ)) :=
  {x | ‖x‖ ≤ R ∧ ‖diagonalObservationCLM σ x - z‖ ≤ δ}

/-- The coordinate box centered at an anchor in the live coordinates.  The
kernel coordinates retain the original radius-`R` absolute bounds. -/
def diagonalCoordinateBox {r k : ℕ} (σ : Fin r → ℝ)
    (x₀ : (Fin r → ℝ) × (Fin k → ℝ)) (R δ : ℝ) :
    Set ((Fin r → ℝ) × (Fin k → ℝ)) :=
  {x | (∀ i, |x.1 i - x₀.1 i| ≤ 2 * δ / σ i) ∧
    ∀ j, |x.2 j| ≤ R}

/-- An anchored diagonal tube lies in the explicit spectral coordinate box.
Thus the live-coordinate interval length is `4δ/σᵢ`, and the kernel-coordinate
interval length is `2R`.  Positivity of each retained singular value is the
only spectral assumption. -/
theorem diagonalTube_subset_coordinateBox {r k : ℕ}
    (σ : Fin r → ℝ) (hσ : ∀ i, 0 < σ i) (z : Fin r → ℝ)
    (R δ : ℝ) (x₀ : (Fin r → ℝ) × (Fin k → ℝ))
    (hx₀ : x₀ ∈ diagonalTube σ z R δ) :
    diagonalTube σ z R δ ⊆ diagonalCoordinateBox σ x₀ R δ := by
  intro x hx
  constructor
  · intro i
    have hmap := norm_map_sub_le_two_mul (diagonalObservationCLM σ) x x₀ z δ
      hx.2 hx₀.2
    have hcoord :
        |diagonalObservationCLM σ (x - x₀) i| ≤
          ‖diagonalObservationCLM σ (x - x₀)‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (diagonalObservationCLM σ (x - x₀)) i
    have hmul : σ i * |x.1 i - x₀.1 i| ≤ 2 * δ := by
      calc
        σ i * |x.1 i - x₀.1 i| =
            |diagonalObservationCLM σ (x - x₀) i| := by
          simp [abs_mul, abs_of_pos (hσ i)]
        _ ≤ ‖diagonalObservationCLM σ (x - x₀)‖ := hcoord
        _ ≤ 2 * δ := hmap
    exact (le_div_iff₀ (hσ i)).2 (by simpa [mul_comm] using hmul)
  · intro j
    have hsnd : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
    have hcoord : |x.2 j| ≤ ‖x.2‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x.2 j
    exact hcoord.trans (hsnd.trans hx.1)

end CFG.LinearTube
