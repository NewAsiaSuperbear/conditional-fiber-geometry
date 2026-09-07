import CFG.Calculus.FiniteImageFiberAtlas
import CFG.Covering.FiniteDimensionalBall

/-!
# Quantitative local covers for the finite image-fiber atlas

This module joins the differential construction to the explicit finite grid.
Each selected chart is parameterized by a ball of finrank `d-r`, and the true
map `F ∘ chart` is Lipschitz there.  Thus its local image has a genuine
degree-`d-r` covering-number bound.
-/

namespace CFG

open Set
open scoped ENNReal NNReal

/-- The finite atlas covers the actual complete-data image fiber, not merely
the projected level set. -/
theorem exists_finite_projectedImageFiberAtlas_image_cover
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    (hcompact : IsCompact E) (hcontinuous : Continuous H)
    (A : Euc d → Euc d →L[ℝ] Euc q)
    (B : Euc d → Euc d →L[ℝ] Euc D)
    (hstrictH : ∀ v ∈ fiber E H z, HasStrictFDerivAt H (A v) v)
    (hstrictF : ∀ v ∈ fiber E H z, HasStrictFDerivAt F (B v) v)
    (hrank : ∀ v ∈ fiber E H z, r ≤ Module.finrank ℝ (A v).range) :
    ∃ (C : ∀ v : fiber E H z,
        ProjectedImageFiberChartAt r E F H z A v)
      (I : Finset (fiber E H z)),
      imageFiber E F H z ⊆
        ⋃ i ∈ I,
          (fun y => F ((C i).chart y)) ''
            Metric.ball (0 : ((C i).projection.comp (A i)).ker)
              (C i).parameterRadius := by
  classical
  obtain ⟨C, I, hI⟩ := exists_finite_projectedImageFiberAtlas
    hcompact hcontinuous A B hstrictH hstrictF hrank
  refine ⟨C, I, ?_⟩
  rintro y ⟨x, hxFiber, rfl⟩
  obtain ⟨i, hiI, hxi⟩ := mem_iUnion₂.mp (hI hxFiber)
  have hlocal : x ∈ (C i).chart ''
      Metric.ball (0 : ((C i).projection.comp (A i)).ker)
        (C i).parameterRadius :=
    (C i).fiber_inter_neighborhood_subset_chart ⟨hxFiber, hxi⟩
  obtain ⟨u, hu, hux⟩ := hlocal
  apply mem_iUnion₂.mpr
  exact ⟨i, hiI, ⟨u, hu, congrArg F hux⟩⟩

/-- Every image chart produced by the derivative construction has an explicit
degree-`d-r` external covering bound.  The factor `2` records conversion to
internal parameter-ball centers before applying the merely local Lipschitz
map. -/
theorem ProjectedImageFiberChartAt.exists_localImage_covering_bound
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    {A : Euc d → Euc d →L[ℝ] Euc q} {v : Euc d}
    (C : ProjectedImageFiberChartAt r E F H z A v)
    {η : ℝ≥0} (hη : η ≠ 0) :
    ∃ e : ((C.projection.comp (A v)).ker) ≃L[ℝ] (Fin (d - r) → ℝ),
      Metric.externalCoveringNumber
          (C.imageLipschitzConstant *
            (2 * (‖e.symm.toContinuousLinearMap‖₊ * η)))
          ((fun y => F (C.chart y)) ''
            Metric.ball (0 : (C.projection.comp (A v)).ker) C.parameterRadius) ≤
        ((2 * Covering.gridSteps
            (‖e.toContinuousLinearMap‖₊ *
              ⟨C.parameterRadius, C.parameterRadius_pos.le⟩) η + 1) ^
            (d - r) : ℕ) := by
  let R : ℝ≥0 := ⟨C.parameterRadius, C.parameterRadius_pos.le⟩
  obtain ⟨e, he⟩ :=
    Covering.exists_coveringNumber_ball_le_gridSteps_of_finrank_eq
      C.kernel_finrank R hη
  refine ⟨e, ?_⟩
  calc
    Metric.externalCoveringNumber
        (C.imageLipschitzConstant *
          (2 * (‖e.symm.toContinuousLinearMap‖₊ * η)))
        ((fun y => F (C.chart y)) ''
          Metric.ball (0 : (C.projection.comp (A v)).ker) C.parameterRadius) ≤
      Metric.coveringNumber
        (2 * (‖e.symm.toContinuousLinearMap‖₊ * η))
        (Metric.ball (0 : (C.projection.comp (A v)).ker) C.parameterRadius) :=
      Covering.externalCoveringNumber_image_le_coveringNumber
        C.imageChart_lipschitz
    _ ≤ ((2 * Covering.gridSteps
          (‖e.toContinuousLinearMap‖₊ * R) η + 1) ^ (d - r) : ℕ) := by
      change Metric.coveringNumber
          (2 * (‖e.symm.toContinuousLinearMap‖₊ * η))
          (Metric.ball (0 : (C.projection.comp (A v)).ker) (R : ℝ)) ≤ _
      exact he

/-- A fixed coordinate choice for the kernel of a projected chart. -/
noncomputable def ProjectedImageFiberChartAt.coordinates
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    {A : Euc d → Euc d →L[ℝ] Euc q} {v : Euc d}
    (C : ProjectedImageFiberChartAt r E F H z A v) :
    ((C.projection.comp (A v)).ker) ≃L[ℝ] (Fin (d - r) → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq
    (C.kernel_finrank.trans (Module.finrank_fin_fun ℝ).symm)

/-- Total radius scale incurred by internalizing the parameter cover and then
applying the local image Lipschitz map. -/
noncomputable def ProjectedImageFiberChartAt.coverScale
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    {A : Euc d → Euc d →L[ℝ] Euc q} {v : Euc d}
    (C : ProjectedImageFiberChartAt r E F H z A v) : ℝ≥0 :=
  C.imageLipschitzConstant *
    (2 * ‖C.coordinates.symm.toContinuousLinearMap‖₊)

/-- Explicit center-count expression for one chart at a desired final radius.
If the total scale vanishes, the chart image is a singleton and the bound is
one. -/
noncomputable def ProjectedImageFiberChartAt.coverBound
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    {A : Euc d → Euc d →L[ℝ] Euc q} {v : Euc d}
    (C : ProjectedImageFiberChartAt r E F H z A v) (ε : ℝ≥0) : ℕ :=
  if C.coverScale = 0 then 1
  else
    (2 * Covering.gridSteps
        (‖C.coordinates.toContinuousLinearMap‖₊ *
          ⟨C.parameterRadius, C.parameterRadius_pos.le⟩)
        (ε / C.coverScale) + 1) ^ (d - r)

/-- A local chart bound at an arbitrary requested positive target radius.
This is the scale-normalized form needed for finite-union summation. -/
theorem ProjectedImageFiberChartAt.localImage_coveringNumber_le_coverBound
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    {A : Euc d → Euc d →L[ℝ] Euc q} {v : Euc d}
    (C : ProjectedImageFiberChartAt r E F H z A v)
    {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.externalCoveringNumber ε
        ((fun y => F (C.chart y)) ''
          Metric.ball (0 : (C.projection.comp (A v)).ker) C.parameterRadius) ≤
      (C.coverBound ε : ℕ) := by
  classical
  by_cases hs : C.coverScale = 0
  · have hzero : C.imageLipschitzConstant = 0 ∨
        ‖C.coordinates.symm.toContinuousLinearMap‖₊ = 0 := by
      rw [ProjectedImageFiberChartAt.coverScale, mul_eq_zero] at hs
      rcases hs with hK | hrest
      · exact Or.inl hK
      · exact Or.inr (by simpa using hrest)
    have hsubset : ((fun y => F (C.chart y)) ''
          Metric.ball (0 : (C.projection.comp (A v)).ker) C.parameterRadius) ⊆
        {F (C.chart 0)} := by
      rintro _ ⟨y, hy, rfl⟩
      apply Set.mem_singleton_iff.mpr
      rcases hzero with hK | hinv
      · have h0mem : (0 : (C.projection.comp (A v)).ker) ∈
            Metric.ball 0 C.parameterRadius := by
          exact Metric.mem_ball_self C.parameterRadius_pos
        have hdist := C.imageChart_lipschitz hy h0mem
        have hdist0 : edist (F (C.chart y)) (F (C.chart 0)) = 0 :=
          bot_unique (by simpa [hK] using hdist)
        exact edist_eq_zero.mp hdist0
      · have hnorm : ‖C.coordinates.symm.toContinuousLinearMap‖ = 0 := by
          change ((‖C.coordinates.symm.toContinuousLinearMap‖₊ : ℝ≥0) : ℝ) = 0
          exact NNReal.coe_eq_zero.mpr hinv
        have heq : C.coordinates.symm.toContinuousLinearMap = 0 :=
          (ContinuousLinearMap.opNorm_zero_iff _).mp hnorm
        have hy0 : y = 0 := by
          calc
            y = C.coordinates.symm (C.coordinates y) :=
              (C.coordinates.symm_apply_apply y).symm
            _ = 0 := by
              change C.coordinates.symm.toContinuousLinearMap (C.coordinates y) = 0
              rw [heq]
              rfl
        rw [hy0]
    calc
      Metric.externalCoveringNumber ε
          ((fun y => F (C.chart y)) ''
            Metric.ball (0 : (C.projection.comp (A v)).ker) C.parameterRadius) ≤
          Metric.externalCoveringNumber ε {F (C.chart 0)} :=
        Metric.externalCoveringNumber_mono_set hsubset
      _ = 1 := Metric.externalCoveringNumber_singleton ε _
      _ = (C.coverBound ε : ℕ) := by simp [ProjectedImageFiberChartAt.coverBound, hs]
  · let η : ℝ≥0 := ε / C.coverScale
    have hη : η ≠ 0 := div_ne_zero hε hs
    let R : ℝ≥0 := ⟨C.parameterRadius, C.parameterRadius_pos.le⟩
    have hparam := Covering.coveringNumber_ball_le_gridSteps_with_coordinates
      C.coordinates R hη
    have himage := Covering.externalCoveringNumber_image_le_coveringNumber
      (K := C.imageLipschitzConstant)
      (ε := 2 * (‖C.coordinates.symm.toContinuousLinearMap‖₊ * η))
      (f := fun y => F (C.chart y)) C.imageChart_lipschitz
    have hradius : C.imageLipschitzConstant *
        (2 * (‖C.coordinates.symm.toContinuousLinearMap‖₊ * η)) = ε := by
      calc
        C.imageLipschitzConstant *
            (2 * (‖C.coordinates.symm.toContinuousLinearMap‖₊ * η)) =
            C.coverScale * η := by
          rw [ProjectedImageFiberChartAt.coverScale]
          ac_rfl
        _ = C.coverScale * (ε / C.coverScale) := by rfl
        _ = ε := mul_div_cancel₀ ε hs
    calc
      Metric.externalCoveringNumber ε
          ((fun y => F (C.chart y)) ''
            Metric.ball (0 : (C.projection.comp (A v)).ker) C.parameterRadius) =
          Metric.externalCoveringNumber
            (C.imageLipschitzConstant *
              (2 * (‖C.coordinates.symm.toContinuousLinearMap‖₊ * η)))
            ((fun y => F (C.chart y)) ''
              Metric.ball (0 : (C.projection.comp (A v)).ker) C.parameterRadius) := by
        rw [hradius]
      _ ≤ ((2 * Covering.gridSteps
            (‖C.coordinates.toContinuousLinearMap‖₊ * R) η + 1) ^ (d - r) : ℕ) :=
        himage.trans hparam
      _ = (C.coverBound ε : ℕ) := by
        simp [ProjectedImageFiberChartAt.coverBound, hs, η, R]

/-- A ceiling-free coefficient for the polynomial bound of one image chart. -/
noncomputable def ProjectedImageFiberChartAt.coverCoefficient
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    {A : Euc d → Euc d →L[ℝ] Euc q} {v : Euc d}
    (C : ProjectedImageFiberChartAt r E F H z A v) : ℝ :=
  (2 * (‖C.coordinates.toContinuousLinearMap‖ * C.parameterRadius *
      (C.coverScale : ℝ)) + 3) ^ (d - r)

/-- After multiplication by `ε^(d-r)`, the explicit integer grid count of a
chart is bounded by a constant independent of `ε`, for `0 < ε ≤ 1`.  This is
the ceiling-removal step behind the usual inverse-power entropy estimate. -/
theorem ProjectedImageFiberChartAt.coverBound_mul_pow_le_coverCoefficient
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    {A : Euc d → Euc d →L[ℝ] Euc q} {v : Euc d}
    (C : ProjectedImageFiberChartAt r E F H z A v)
    {ε : ℝ≥0} (hε : ε ≠ 0) (hεone : (ε : ℝ) ≤ 1) :
    (C.coverBound ε : ℝ) * (ε : ℝ) ^ (d - r) ≤ C.coverCoefficient := by
  classical
  have hεpos : 0 < (ε : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hε)
  by_cases hs : C.coverScale = 0
  · simp only [ProjectedImageFiberChartAt.coverBound, hs, ↓reduceIte, Nat.cast_one,
      one_mul, ProjectedImageFiberChartAt.coverCoefficient]
    norm_num
    have hεthree : (ε : ℝ) ≤ 3 := hεone.trans (by norm_num)
    exact pow_le_pow_left₀ (by positivity) hεthree _
  · let Q : ℝ≥0 := ‖C.coordinates.toContinuousLinearMap‖₊ *
        ⟨C.parameterRadius, C.parameterRadius_pos.le⟩
    let η : ℝ≥0 := ε / C.coverScale
    have hgrid := Covering.gridCard_real_le_polynomial (d - r) Q η
    have hηcoe : (η : ℝ) = (ε : ℝ) / (C.coverScale : ℝ) := by
      simp [η]
    have hscoe : (C.coverScale : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
    have hbase :
        (2 * ((Q : ℝ) / (η : ℝ)) + 3) * (ε : ℝ) =
          2 * (Q : ℝ) * (C.coverScale : ℝ) + 3 * (ε : ℝ) := by
      rw [hηcoe]
      field_simp
    calc
      (C.coverBound ε : ℝ) * (ε : ℝ) ^ (d - r) ≤
          (2 * ((Q : ℝ) / (η : ℝ)) + 3) ^ (d - r) *
            (ε : ℝ) ^ (d - r) := by
        apply mul_le_mul_of_nonneg_right
        · simpa [ProjectedImageFiberChartAt.coverBound, hs, Q, η] using hgrid
        · positivity
      _ = ((2 * ((Q : ℝ) / (η : ℝ)) + 3) * (ε : ℝ)) ^ (d - r) := by
        rw [mul_pow]
      _ ≤ (2 * (Q : ℝ) * (C.coverScale : ℝ) + 3) ^ (d - r) := by
        rw [hbase]
        apply pow_le_pow_left₀
        · positivity
        · have hQ : 0 ≤ (Q : ℝ) := Q.coe_nonneg
          have hsnonneg : 0 ≤ (C.coverScale : ℝ) := C.coverScale.coe_nonneg
          nlinarith
      _ = C.coverCoefficient := by
        congr 1
        have hQcoe : (Q : ℝ) =
            ‖C.coordinates.toContinuousLinearMap‖ * C.parameterRadius := rfl
        rw [hQcoe]
        ring

/-- Global common-radius quantitative cover obtained by summing the explicit
degree-`d-r` local bounds of the finite atlas.  All charts and all constants on
the right-hand side are constructed from the derivative hypotheses. -/
theorem exists_imageFiber_coveringNumber_le_sum_chartCoverBound
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    (hcompact : IsCompact E) (hcontinuous : Continuous H)
    (A : Euc d → Euc d →L[ℝ] Euc q)
    (B : Euc d → Euc d →L[ℝ] Euc D)
    (hstrictH : ∀ v ∈ fiber E H z, HasStrictFDerivAt H (A v) v)
    (hstrictF : ∀ v ∈ fiber E H z, HasStrictFDerivAt F (B v) v)
    (hrank : ∀ v ∈ fiber E H z, r ≤ Module.finrank ℝ (A v).range)
    {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ (C : ∀ v : fiber E H z,
        ProjectedImageFiberChartAt r E F H z A v)
      (I : Finset (fiber E H z)),
      Metric.externalCoveringNumber ε (imageFiber E F H z) ≤
        ∑ i ∈ I, ((C i).coverBound ε : ℕ∞) := by
  classical
  obtain ⟨C, I, hcover⟩ := exists_finite_projectedImageFiberAtlas_image_cover
    hcompact hcontinuous A B hstrictH hstrictF hrank
  refine ⟨C, I, ?_⟩
  let S : fiber E H z → Set (Euc D) := fun i =>
    (fun y => F ((C i).chart y)) ''
      Metric.ball (0 : ((C i).projection.comp (A i)).ker) (C i).parameterRadius
  calc
    Metric.externalCoveringNumber ε (imageFiber E F H z) ≤
        Metric.externalCoveringNumber ε (⋃ i ∈ I, S i) :=
      Metric.externalCoveringNumber_mono_set hcover
    _ ≤ ∑ i ∈ I, Metric.externalCoveringNumber ε (S i) :=
      Covering.externalCoveringNumber_biUnion_finset_le I S
    _ ≤ ∑ i ∈ I, ((C i).coverBound ε : ℕ∞) := by
      exact Finset.sum_le_sum fun i hi =>
        (C i).localImage_coveringNumber_le_coverBound hε

/-- The usual single-constant inverse-power formulation of the image-fiber
covering estimate.  The natural number `N` is an explicit finite certificate:
it bounds mathlib's `ℕ∞`-valued covering number and satisfies
`N * ε^(d-r) ≤ C₀`, equivalently `N ≤ C₀ / ε^(d-r)` for positive `ε`.

Returning the finite witness avoids any lossy conversion of `ℕ∞` to `ℝ`. -/
theorem exists_imageFiber_coveringNumber_polynomial_certificate
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    (hcompact : IsCompact E) (hcontinuous : Continuous H)
    (A : Euc d → Euc d →L[ℝ] Euc q)
    (B : Euc d → Euc d →L[ℝ] Euc D)
    (hstrictH : ∀ v ∈ fiber E H z, HasStrictFDerivAt H (A v) v)
    (hstrictF : ∀ v ∈ fiber E H z, HasStrictFDerivAt F (B v) v)
    (hrank : ∀ v ∈ fiber E H z, r ≤ Module.finrank ℝ (A v).range) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ≥0, ε ≠ 0 → (ε : ℝ) ≤ 1 →
      ∃ N : ℕ,
        Metric.externalCoveringNumber ε (imageFiber E F H z) ≤ (N : ℕ∞) ∧
        (N : ℝ) * (ε : ℝ) ^ (d - r) ≤ C₀ := by
  classical
  obtain ⟨C, I, hcover⟩ := exists_finite_projectedImageFiberAtlas_image_cover
    hcompact hcontinuous A B hstrictH hstrictF hrank
  let C₀ : ℝ := 1 + ∑ i ∈ I, (C i).coverCoefficient
  have hcoefficient_nonneg :
      0 ≤ ∑ i ∈ I, (C i).coverCoefficient := by
    apply Finset.sum_nonneg
    intro i hi
    rw [ProjectedImageFiberChartAt.coverCoefficient]
    apply pow_nonneg
    have hnorm : 0 ≤ ‖(C i).coordinates.toContinuousLinearMap‖ := by positivity
    have hprod : 0 ≤ ‖(C i).coordinates.toContinuousLinearMap‖ *
        (C i).parameterRadius * ((C i).coverScale : ℝ) :=
      mul_nonneg (mul_nonneg hnorm (C i).parameterRadius_pos.le)
        (C i).coverScale.coe_nonneg
    linarith
  refine ⟨C₀, by simp only [C₀]; linarith, ?_⟩
  intro ε hε hεone
  let N : ℕ := ∑ i ∈ I, (C i).coverBound ε
  refine ⟨N, ?_, ?_⟩
  · let S : fiber E H z → Set (Euc D) := fun i =>
      (fun y => F ((C i).chart y)) ''
        Metric.ball (0 : ((C i).projection.comp (A i)).ker) (C i).parameterRadius
    calc
      Metric.externalCoveringNumber ε (imageFiber E F H z) ≤
          Metric.externalCoveringNumber ε (⋃ i ∈ I, S i) :=
        Metric.externalCoveringNumber_mono_set hcover
      _ ≤ ∑ i ∈ I, Metric.externalCoveringNumber ε (S i) :=
        Covering.externalCoveringNumber_biUnion_finset_le I S
      _ ≤ ∑ i ∈ I, ((C i).coverBound ε : ℕ∞) := by
        exact Finset.sum_le_sum fun i hi =>
          (C i).localImage_coveringNumber_le_coverBound hε
      _ = (N : ℕ∞) := by simp [N]
  · calc
      (N : ℝ) * (ε : ℝ) ^ (d - r) =
          ∑ i ∈ I, ((C i).coverBound ε : ℝ) * (ε : ℝ) ^ (d - r) := by
        simp [N, Finset.sum_mul]
      _ ≤ ∑ i ∈ I, (C i).coverCoefficient := by
        exact Finset.sum_le_sum fun i hi =>
          (C i).coverBound_mul_pow_le_coverCoefficient hε hεone
      _ ≤ C₀ := by simp only [C₀]; linarith

/-- Division form of the preceding certificate: the image-fiber covering
number is bounded by a finite natural witness of order `ε^{-(d-r)}`. -/
theorem exists_imageFiber_coveringNumber_inversePower_certificate
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    (hcompact : IsCompact E) (hcontinuous : Continuous H)
    (A : Euc d → Euc d →L[ℝ] Euc q)
    (B : Euc d → Euc d →L[ℝ] Euc D)
    (hstrictH : ∀ v ∈ fiber E H z, HasStrictFDerivAt H (A v) v)
    (hstrictF : ∀ v ∈ fiber E H z, HasStrictFDerivAt F (B v) v)
    (hrank : ∀ v ∈ fiber E H z, r ≤ Module.finrank ℝ (A v).range) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ≥0, ε ≠ 0 → (ε : ℝ) ≤ 1 →
      ∃ N : ℕ,
        Metric.externalCoveringNumber ε (imageFiber E F H z) ≤ (N : ℕ∞) ∧
        (N : ℝ) ≤ C₀ / (ε : ℝ) ^ (d - r) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_imageFiber_coveringNumber_polynomial_certificate
    hcompact hcontinuous A B hstrictH hstrictF hrank
  refine ⟨C₀, hC₀, ?_⟩
  intro ε hε hεone
  obtain ⟨N, hcover, hN⟩ := hbound ε hε hεone
  refine ⟨N, hcover, ?_⟩
  have hεpos : 0 < (ε : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hε)
  exact (le_div_iff₀ (pow_pos hεpos _)).2 hN

/-- Logarithmic entropy form for a nonempty image fiber.  The logarithm is
taken on the same finite natural certificate that bounds the native
`ℕ∞`-valued covering number, so no top-value conversion is involved. -/
theorem exists_imageFiber_log_covering_certificate
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    (hcompact : IsCompact E) (hcontinuous : Continuous H)
    (A : Euc d → Euc d →L[ℝ] Euc q)
    (B : Euc d → Euc d →L[ℝ] Euc D)
    (hstrictH : ∀ v ∈ fiber E H z, HasStrictFDerivAt H (A v) v)
    (hstrictF : ∀ v ∈ fiber E H z, HasStrictFDerivAt F (B v) v)
    (hrank : ∀ v ∈ fiber E H z, r ≤ Module.finrank ℝ (A v).range)
    (hnonempty : (fiber E H z).Nonempty) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ≥0, ε ≠ 0 → (ε : ℝ) ≤ 1 →
      ∃ N : ℕ,
        Metric.externalCoveringNumber ε (imageFiber E F H z) ≤ (N : ℕ∞) ∧
        0 < N ∧
        Real.log (N : ℝ) ≤ Real.log C₀ +
          ((d - r : ℕ) : ℝ) * Real.log (1 / (ε : ℝ)) := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    exists_imageFiber_coveringNumber_inversePower_certificate
      hcompact hcontinuous A B hstrictH hstrictF hrank
  refine ⟨C₀, hC₀, ?_⟩
  intro ε hε hεone
  obtain ⟨N, hcover, hN⟩ := hbound ε hε hεone
  have himage : (imageFiber E F H z).Nonempty := by
    simpa [imageFiber] using hnonempty.image F
  have hcoverpos : 0 < Metric.externalCoveringNumber ε (imageFiber E F H z) :=
    Metric.externalCoveringNumber_pos_iff.mpr himage
  have hNposENat : (0 : ℕ∞) < (N : ℕ∞) := hcoverpos.trans_le hcover
  have hNpos : 0 < N := by exact_mod_cast hNposENat
  refine ⟨N, hcover, hNpos, ?_⟩
  have hεpos : 0 < (ε : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hε)
  have hpowpos : 0 < (ε : ℝ) ^ (d - r) := pow_pos hεpos _
  calc
    Real.log (N : ℝ) ≤ Real.log (C₀ / (ε : ℝ) ^ (d - r)) :=
      Real.log_le_log (by exact_mod_cast hNpos) hN
    _ = Real.log C₀ - Real.log ((ε : ℝ) ^ (d - r)) :=
      Real.log_div hC₀.ne' hpowpos.ne'
    _ = Real.log C₀ + ((d - r : ℕ) : ℝ) * Real.log (1 / (ε : ℝ)) := by
      rw [Real.log_pow]
      simp only [one_div, Real.log_inv]
      ring

end CFG
