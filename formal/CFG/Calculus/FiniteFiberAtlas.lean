import CFG.Calculus.RankProjection

/-!
# Finite projected atlases for compact regular fibers

This file closes the compactness step between the pointwise projected
implicit-function theorem and a finite collection of genuine local charts.
The chart parameter spaces may depend on the selected fiber point.
-/

namespace CFG

open Filter Set
open scoped NNReal Topology

/-- Data actually constructed at a point of a fiber from a strict derivative
whose rank is at least `r`.  The ambient fiber is locally contained in the
image of the chart.  Only the projected level equation is asserted in the
opposite direction, as required by the rank-lower-bound route. -/
structure ProjectedFiberChartAt
    {d q : ℕ} (r : ℕ) (E : Set (Euc d)) (H : Euc d → Euc q) (z : Euc q)
    (A : Euc d → Euc d →L[ℝ] Euc q) (v : Euc d) where
  center_mem : v ∈ fiber E H z
  projection : Euc q →L[ℝ] Euc r
  projection_surjective : (projection.comp (A v)).range = ⊤
  kernel_finrank : Module.finrank ℝ (projection.comp (A v)).ker = d - r
  lipschitzConstant : NNReal
  parameterRadius : ℝ
  parameterRadius_pos : 0 < parameterRadius
  chart : (projection.comp (A v)).ker → Euc d
  neighborhood : Set (Euc d)
  neighborhood_open : IsOpen neighborhood
  center_mem_neighborhood : v ∈ neighborhood
  chart_lipschitz :
    LipschitzOnWith lipschitzConstant chart (Metric.ball 0 parameterRadius)
  chart_projected_level :
    ∀ y ∈ Metric.ball (0 : (projection.comp (A v)).ker) parameterRadius,
      projection (H (chart y)) = projection (H v)
  chart_zero : chart 0 = v
  fiber_inter_neighborhood_subset_chart :
    fiber E H z ∩ neighborhood ⊆ chart '' Metric.ball 0 parameterRadius

/-- The local projected chart, including an honest open ambient neighborhood,
is obtained from the derivative hypotheses rather than supplied as an input
certificate. -/
theorem HasStrictFDerivAt.exists_projectedFiberChartAt
    {d q r : ℕ} {E : Set (Euc d)} {H : Euc d → Euc q} {z : Euc q}
    {A : Euc d → Euc d →L[ℝ] Euc q} {v : Euc d}
    (hv : v ∈ fiber E H z) (hH : HasStrictFDerivAt H (A v) v)
    (hrank : r ≤ Module.finrank ℝ (A v).range) :
    Nonempty (ProjectedFiberChartAt r E H z A v) := by
  obtain ⟨L, hsurj, hker, K, R, hR, ψ, hLip, hlevel, hcontains, hzero⟩ :=
    CFG.HasStrictFDerivAt.exists_projected_localLipschitz_fiberChart_ball hH hrank
  obtain ⟨W, hWsub, hWopen, hvW⟩ := mem_nhds_iff.mp hcontains
  refine ⟨{
    center_mem := hv
    projection := L
    projection_surjective := hsurj
    kernel_finrank := hker
    lipschitzConstant := K
    parameterRadius := R
    parameterRadius_pos := hR
    chart := ψ
    neighborhood := W
    neighborhood_open := hWopen
    center_mem_neighborhood := hvW
    chart_lipschitz := hLip
    chart_projected_level := hlevel
    chart_zero := hzero
    fiber_inter_neighborhood_subset_chart := ?_
  }⟩
  rintro x ⟨hxFiber, hxW⟩
  have hHx : H x = H v := hxFiber.2.trans hv.2.symm
  obtain ⟨y, hyU, hyx⟩ := hWsub hxW hHx
  exact ⟨y, hyU, hyx⟩

/-- A compact fiber with pointwise rank at least `r` is covered by finitely
many of the projected charts constructed from its true strict derivatives.
The family `C` is produced by choice from the preceding existence theorem;
the finite set `I` is then produced by compactness from the open chart
neighborhoods. -/
theorem exists_finite_projectedFiberAtlas
    {d q r : ℕ} {E : Set (Euc d)} {H : Euc d → Euc q} {z : Euc q}
    (hcompact : IsCompact E) (hcontinuous : Continuous H)
    (A : Euc d → Euc d →L[ℝ] Euc q)
    (hstrict : ∀ v ∈ fiber E H z, HasStrictFDerivAt H (A v) v)
    (hrank : ∀ v ∈ fiber E H z, r ≤ Module.finrank ℝ (A v).range) :
    ∃ (C : ∀ v : fiber E H z, ProjectedFiberChartAt r E H z A v)
      (I : Finset (fiber E H z)),
      fiber E H z ⊆ ⋃ i ∈ I, (C i).neighborhood := by
  classical
  have hcharts : ∀ v : fiber E H z,
      Nonempty (ProjectedFiberChartAt r E H z A v) := fun v =>
    CFG.HasStrictFDerivAt.exists_projectedFiberChartAt
      v.property (hstrict v v.property) (hrank v v.property)
  let C : ∀ v : fiber E H z, ProjectedFiberChartAt r E H z A v :=
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
