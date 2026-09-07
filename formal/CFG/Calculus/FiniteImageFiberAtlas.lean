import CFG.Calculus.FiniteFiberAtlas

/-!
# Finite Lipschitz atlases for compact image fibers

At each regular fiber point this module constructs the projected implicit
chart and simultaneously shrinks it until the true complete-data composition
is Lipschitz on a positive-radius parameter ball.  Compactness then selects a
finite subfamily.  No chart or covering certificate is assumed as input.
-/

namespace CFG

open Filter Set
open scoped NNReal Topology

/-- A projected local fiber chart on which the actual complete-data map
composed with the chart is Lipschitz. -/
structure ProjectedImageFiberChartAt
    {d D q : ℕ} (r : ℕ) (E : Set (Euc d)) (F : Euc d → Euc D)
    (H : Euc d → Euc q) (z : Euc q)
    (A : Euc d → Euc d →L[ℝ] Euc q) (v : Euc d) where
  center_mem : v ∈ fiber E H z
  projection : Euc q →L[ℝ] Euc r
  projection_surjective : (projection.comp (A v)).range = ⊤
  kernel_finrank : Module.finrank ℝ (projection.comp (A v)).ker = d - r
  imageLipschitzConstant : NNReal
  parameterRadius : ℝ
  parameterRadius_pos : 0 < parameterRadius
  chart : (projection.comp (A v)).ker → Euc d
  neighborhood : Set (Euc d)
  neighborhood_open : IsOpen neighborhood
  center_mem_neighborhood : v ∈ neighborhood
  imageChart_lipschitz : LipschitzOnWith imageLipschitzConstant
    (fun y => F (chart y)) (Metric.ball 0 parameterRadius)
  chart_projected_level :
    ∀ y ∈ Metric.ball (0 : (projection.comp (A v)).ker) parameterRadius,
      projection (H (chart y)) = projection (H v)
  chart_zero : chart 0 = v
  fiber_inter_neighborhood_subset_chart :
    fiber E H z ∩ neighborhood ⊆ chart '' Metric.ball 0 parameterRadius

/-- A pointwise rank lower bound and true strict derivatives of both `H` and
`F` construct an image-Lipschitz projected chart on a parameter ball. -/
theorem exists_projectedImageFiberChartAt
    {d D q r : ℕ} {E : Set (Euc d)} {F : Euc d → Euc D}
    {H : Euc d → Euc q} {z : Euc q}
    {A : Euc d → Euc d →L[ℝ] Euc q}
    {B : Euc d → Euc d →L[ℝ] Euc D} {v : Euc d}
    (hv : v ∈ fiber E H z) (hH : HasStrictFDerivAt H (A v) v)
    (hF : HasStrictFDerivAt F (B v) v)
    (hrank : r ≤ Module.finrank ℝ (A v).range) :
    Nonempty (ProjectedImageFiberChartAt r E F H z A v) := by
  obtain ⟨L, hsurj⟩ := exists_surjective_outputProjection (A v) hrank
  have hrankNullity := (L.comp (A v)).toLinearMap.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (L.comp (A v)).range = r := by
    rw [hsurj, finrank_top, finrank_euclideanSpace_fin]
  have hdomain : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  have hker : Module.finrank ℝ (L.comp (A v)).ker = d - r := by omega
  have hprojected : HasStrictFDerivAt (fun x => L (H x)) (L.comp (A v)) v :=
    L.hasStrictFDerivAt.comp v hH
  obtain ⟨K, R, hR, hLip, hlevel, hcontains, hzero⟩ :=
    CFG.HasStrictFDerivAt.exists_localLipschitz_imageFiberChart_ball
      hprojected hsurj hF
  obtain ⟨W, hWsub, hWopen, hvW⟩ := mem_nhds_iff.mp hcontains
  refine ⟨{
    center_mem := hv
    projection := L
    projection_surjective := hsurj
    kernel_finrank := hker
    imageLipschitzConstant := K
    parameterRadius := R
    parameterRadius_pos := hR
    chart := hprojected.implicitFunction (fun x => L (H x)) (L.comp (A v))
      hsurj (L (H v))
    neighborhood := W
    neighborhood_open := hWopen
    center_mem_neighborhood := hvW
    imageChart_lipschitz := hLip
    chart_projected_level := hlevel
    chart_zero := hzero
    fiber_inter_neighborhood_subset_chart := ?_
  }⟩
  rintro x ⟨hxFiber, hxW⟩
  have hHx : H x = H v := hxFiber.2.trans hv.2.symm
  obtain ⟨y, hy, hyx⟩ := hWsub hxW (congrArg L hHx)
  exact ⟨y, hy, hyx⟩

/-- Compactness selects finitely many image-Lipschitz ball charts constructed
from pointwise derivative data. -/
theorem exists_finite_projectedImageFiberAtlas
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
      fiber E H z ⊆ ⋃ i ∈ I, (C i).neighborhood := by
  classical
  have hcharts : ∀ v : fiber E H z,
      Nonempty (ProjectedImageFiberChartAt r E F H z A v) := fun v =>
    exists_projectedImageFiberChartAt v.property
      (hstrictH v v.property) (hstrictF v v.property) (hrank v v.property)
  let C : ∀ v : fiber E H z, ProjectedImageFiberChartAt r E F H z A v :=
    fun v => Classical.choice (hcharts v)
  have hcompactFiber : IsCompact (fiber E H z) :=
    isCompact_fiber hcompact hcontinuous
  obtain ⟨I, hI⟩ := hcompactFiber.elim_finite_subcover
    (fun v : fiber E H z => (C v).neighborhood)
    (fun v => (C v).neighborhood_open) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, (C ⟨x, hx⟩).center_mem_neighborhood⟩)
  exact ⟨C, I, hI⟩

end CFG
