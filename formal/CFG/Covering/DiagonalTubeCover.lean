import CFG.Covering.LinearTube
import CFG.Covering.BoxGrid

/-!
# Explicit finite covers for diagonal linear tubes

`CFG.LinearTube.diagonalTube_subset_coordinateBox` places any anchored
diagonal spectral tube inside an explicit coordinate box.  Here an
anisotropic integer grid covers its live coordinates and the symmetric grid
from `CFG.Covering.BoxGrid` covers its kernel coordinates.  This gives the
genuine product bound

`∏ i, (2 * ⌈(2δ/σᵢ)/ε⌉₊ + 1) * (2 * ⌈R/ε⌉₊ + 1)^k`.
-/

namespace CFG.Covering

open Set
open scoped ENNReal NNReal

variable {r k : ℕ}

/-- Per-coordinate integer box `∏ᵢ [-mᵢ, mᵢ]`. -/
def anisoIntegerBox (m : Fin r → ℕ) : Finset (Fin r → ℤ) :=
  Finset.Icc (fun i => -(m i : ℤ)) (fun i => (m i : ℤ))

/-- An anisotropic coordinate grid of mesh `ε` around center `c`. -/
def anisoGrid (c : Fin r → ℝ) (m : Fin r → ℕ) (ε : ℝ≥0) : Set (Fin r → ℝ) :=
  (fun z i => c i + (ε : ℝ) * (z i : ℝ)) '' (anisoIntegerBox m : Set (Fin r → ℤ))

/-- The anisotropic coordinate box with per-coordinate half-widths `w`. -/
def anisoBox (c : Fin r → ℝ) (w : Fin r → ℝ) : Set (Fin r → ℝ) :=
  {a | ∀ i, |a i - c i| ≤ w i}

@[simp]
theorem card_anisoIntegerBox (m : Fin r → ℕ) :
    (anisoIntegerBox m).card = ∏ i, (2 * m i + 1) := by
  rw [anisoIntegerBox, Pi.card_Icc]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Int.card_Icc]
  rw [show (m i : ℤ) + 1 - -(m i : ℤ) = ((2 * m i + 1 : ℕ) : ℤ) by omega]
  exact Int.toNat_natCast _

/-- The anisotropic grid has at most `∏ᵢ (2mᵢ+1)` centers. -/
theorem encard_anisoGrid_le (c : Fin r → ℝ) (m : Fin r → ℕ) (ε : ℝ≥0) :
    (anisoGrid c m ε).encard ≤ ((∏ i, (2 * m i + 1)) : ℕ) := by
  calc
    (anisoGrid c m ε).encard ≤ (anisoIntegerBox m : Set (Fin r → ℤ)).encard :=
      Set.encard_image_le _ _
    _ = ((∏ i, (2 * m i + 1)) : ℕ) := by simp

/-- Flooring each shifted coordinate selects an index in the anisotropic
integer box. -/
private theorem floorIndex_mem_anisoIntegerBox
    (c : Fin r → ℝ) (m : Fin r → ℕ) {ε : ℝ≥0} (hε : ε ≠ 0)
    {a : Fin r → ℝ} (ha : a ∈ anisoBox c (fun i => (m i : ℝ) * (ε : ℝ))) :
    (fun i => ⌊(a i - c i) / (ε : ℝ)⌋) ∈ anisoIntegerBox m := by
  have hεpos : 0 < (ε : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hε)
  rw [anisoIntegerBox, Finset.mem_Icc]
  constructor
  · intro i
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hεpos).2
    have h1 := (abs_le.mp (ha i)).1
    push_cast
    simpa [neg_mul] using h1
  · intro i
    have hquot : (a i - c i) / (ε : ℝ) ≤ (m i : ℝ) := by
      apply (div_le_iff₀ hεpos).2
      have h2 := (abs_le.mp (ha i)).2
      simpa [mul_comm] using h2
    have := Int.floor_le_floor hquot
    simpa using this

/-- Every point of the anisotropic box of half-widths `mᵢ·ε` is within
sup-norm distance `ε` of the anisotropic grid. -/
theorem isCover_anisoBox_anisoGrid
    (c : Fin r → ℝ) (m : Fin r → ℕ) {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.IsCover ε (anisoBox c (fun i => (m i : ℝ) * (ε : ℝ)))
      (anisoGrid c m ε) := by
  have hεpos : 0 < (ε : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hε)
  intro a ha
  refine ⟨fun i => c i + (ε : ℝ) * (⌊(a i - c i) / (ε : ℝ)⌋ : ℝ), ?_, ?_⟩
  · exact ⟨fun i => ⌊(a i - c i) / (ε : ℝ)⌋,
      floorIndex_mem_anisoIntegerBox c m hε ha, rfl⟩
  · change edist a _ ≤ ε
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_pi_le_iff ε.coe_nonneg]
    intro i
    rw [Real.dist_eq]
    have hsub : a i - (c i + (ε : ℝ) * (⌊(a i - c i) / (ε : ℝ)⌋ : ℝ)) =
        (a i - c i) - (ε : ℝ) * (⌊(a i - c i) / (ε : ℝ)⌋ : ℝ) := by ring
    rw [hsub]
    have hlo : 0 ≤ (a i - c i) - (ε : ℝ) * (⌊(a i - c i) / (ε : ℝ)⌋ : ℝ) := by
      rw [sub_nonneg]
      calc
        (ε : ℝ) * (⌊(a i - c i) / (ε : ℝ)⌋ : ℝ) ≤
            (ε : ℝ) * ((a i - c i) / (ε : ℝ)) := by
          gcongr
          exact Int.floor_le _
        _ = a i - c i := by field_simp
    have hhi : (a i - c i) - (ε : ℝ) * (⌊(a i - c i) / (ε : ℝ)⌋ : ℝ) ≤
        (ε : ℝ) := by
      have hfract : (a i - c i) / (ε : ℝ) <
          (⌊(a i - c i) / (ε : ℝ)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hmul := mul_lt_mul_of_pos_left hfract hεpos
      rw [mul_add, mul_one] at hmul
      have hcancel : (ε : ℝ) * ((a i - c i) / (ε : ℝ)) = a i - c i := by
        field_simp
      linarith
    rw [abs_of_nonneg hlo]
    exact hhi

/-- The anisotropic grid covers arbitrary nonnegative half-widths after
choosing per-coordinate step counts by ceilings. -/
theorem isCover_anisoBox_gridSteps
    (c : Fin r → ℝ) (w : Fin r → ℝ≥0) {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.IsCover ε (anisoBox c (fun i => (w i : ℝ)))
      (anisoGrid c (fun i => gridSteps (w i) ε) ε) :=
  (isCover_anisoBox_anisoGrid c (fun i => gridSteps (w i) ε) hε).anti
    (fun _ ha i => (ha i).trans (radius_le_gridSteps_mul (w i) hε))

/-- Scale-ready anisotropic center count. -/
theorem encard_anisoGrid_gridSteps_le (c : Fin r → ℝ) (w : Fin r → ℝ≥0)
    (ε : ℝ≥0) :
    (anisoGrid c (fun i => gridSteps (w i) ε) ε).encard ≤
      ((∏ i, (2 * gridSteps (w i) ε + 1)) : ℕ) :=
  encard_anisoGrid_le _ _ _

/-- A product of `ε`-covers is an `ε`-cover of the product set because product
edistance is the maximum of the factor edistances. -/
theorem isCover_prod {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {s₁ C₁ : Set X} {s₂ C₂ : Set Y} {ε : ℝ≥0}
    (h₁ : Metric.IsCover ε s₁ C₁) (h₂ : Metric.IsCover ε s₂ C₂) :
    Metric.IsCover ε (s₁ ×ˢ s₂) (C₁ ×ˢ C₂) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨c₁, hc₁, hd₁⟩ := h₁ hx
  obtain ⟨c₂, hc₂, hd₂⟩ := h₂ hy
  refine ⟨(c₁, c₂), ⟨hc₁, hc₂⟩, ?_⟩
  show edist (x, y) (c₁, c₂) ≤ (ε : ℝ≥0∞)
  rw [Prod.edist_eq]
  exact max_le hd₁ hd₂

/-- Live-coordinate half-widths `2δ/σᵢ` of the diagonal coordinate box. -/
noncomputable def liveHalfWidths {r : ℕ} (σ : Fin r → ℝ) (hσ : ∀ i, 0 < σ i)
    {δ : ℝ} (hδ : 0 ≤ δ) : Fin r → ℝ≥0 :=
  fun i => ⟨2 * δ / σ i, div_nonneg (mul_nonneg zero_le_two hδ) (hσ i).le⟩

@[simp]
theorem coe_liveHalfWidths {r : ℕ} (σ : Fin r → ℝ) (hσ : ∀ i, 0 < σ i)
    {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin r) :
    (liveHalfWidths σ hσ hδ i : ℝ) = 2 * δ / σ i := rfl

/-- The diagonal coordinate box admits an explicit finite `ε`-cover with at
most `∏ i, (2⌈(2δ/σᵢ)/ε⌉₊ + 1) · (2⌈R/ε⌉₊ + 1)^k` centers. -/
theorem externalCoveringNumber_diagonalCoordinateBox_le
    (σ : Fin r → ℝ) (hσ : ∀ i, 0 < σ i)
    (x₀ : (Fin r → ℝ) × (Fin k → ℝ))
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.externalCoveringNumber ε
        (CFG.LinearTube.diagonalCoordinateBox σ x₀ R δ) ≤
      ((∏ i, (2 * gridSteps (liveHalfWidths σ hσ hδ i) ε + 1)) *
        (2 * gridSteps ⟨R, hR⟩ ε + 1) ^ k : ℕ) := by
  have hlive : Metric.IsCover ε
      (anisoBox x₀.1 (fun i => (liveHalfWidths σ hσ hδ i : ℝ)))
      (anisoGrid x₀.1 (fun i => gridSteps (liveHalfWidths σ hσ hδ i) ε) ε) :=
    isCover_anisoBox_gridSteps x₀.1 (liveHalfWidths σ hσ hδ) hε
  have hker : Metric.IsCover ε (supNormBox k R)
      (boxGrid k (gridSteps ⟨R, hR⟩ ε) ε) :=
    isCover_supNormBox_gridSteps (n := k) ⟨R, hR⟩ hε
  have hsub : CFG.LinearTube.diagonalCoordinateBox σ x₀ R δ ⊆
      anisoBox x₀.1 (fun i => (liveHalfWidths σ hσ hδ i : ℝ)) ×ˢ supNormBox k R :=
    fun x hx => ⟨hx.1, hx.2⟩
  have hcover := (isCover_prod hlive hker).anti hsub
  calc
    Metric.externalCoveringNumber ε
        (CFG.LinearTube.diagonalCoordinateBox σ x₀ R δ) ≤
        (anisoGrid x₀.1 (fun i => gridSteps (liveHalfWidths σ hσ hδ i) ε) ε ×ˢ
          boxGrid k (gridSteps ⟨R, hR⟩ ε) ε).encard :=
      hcover.externalCoveringNumber_le_encard
    _ = (anisoGrid x₀.1 (fun i => gridSteps (liveHalfWidths σ hσ hδ i) ε)
          ε).encard * (boxGrid k (gridSteps ⟨R, hR⟩ ε) ε).encard := Set.encard_prod
    _ ≤ (↑(∏ i, (2 * gridSteps (liveHalfWidths σ hσ hδ i) ε + 1)) : ℕ∞) *
          (↑((2 * gridSteps ⟨R, hR⟩ ε + 1) ^ k) : ℕ∞) :=
      mul_le_mul' (encard_anisoGrid_gridSteps_le _ _ _) (encard_boxGrid_le _ _ _)
    _ = (↑((∏ i, (2 * gridSteps (liveHalfWidths σ hσ hδ i) ε + 1)) *
          (2 * gridSteps ⟨R, hR⟩ ε + 1) ^ k) : ℕ∞) := by
      rw [Nat.cast_mul]

/-- For any anchor in a diagonal tube, the tube itself has the same explicit
finite-cover bound; nonnegativity of `R` and `δ` follows from the anchor. -/
theorem externalCoveringNumber_diagonalTube_le
    (σ : Fin r → ℝ) (hσ : ∀ i, 0 < σ i) (z : Fin r → ℝ)
    {R δ : ℝ} (x₀ : (Fin r → ℝ) × (Fin k → ℝ))
    (hx₀ : x₀ ∈ CFG.LinearTube.diagonalTube (k := k) σ z R δ)
    {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.externalCoveringNumber ε
        (CFG.LinearTube.diagonalTube (k := k) σ z R δ) ≤
      ((∏ i, (2 * gridSteps (liveHalfWidths σ hσ
          ((norm_nonneg _).trans hx₀.2) i) ε + 1)) *
        (2 * gridSteps ⟨R, (norm_nonneg _).trans hx₀.1⟩ ε + 1) ^ k : ℕ) :=
  (Metric.externalCoveringNumber_mono_set
    (CFG.LinearTube.diagonalTube_subset_coordinateBox σ hσ z R δ x₀ hx₀)).trans
    (externalCoveringNumber_diagonalCoordinateBox_le σ hσ x₀
      ((norm_nonneg _).trans hx₀.1) ((norm_nonneg _).trans hx₀.2) hε)

end CFG.Covering
