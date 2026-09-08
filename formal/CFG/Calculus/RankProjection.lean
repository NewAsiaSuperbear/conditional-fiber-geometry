import CFG.Calculus.LocalFiberChart
import CFG.Basic.Fiber
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.DiscreteSubset

/-!
# Selecting observable output directions from a rank lower bound

This module turns a rank lower bound for a Euclidean derivative into an
actual continuous linear output projection whose composite derivative is
surjective.  It then feeds that projection into the local fiber-chart theorem.
-/

namespace CFG

open Filter

open scoped Topology

/-- If a Euclidean linear map has rank at least `r`, some continuous linear
map on its codomain makes the composite onto `ℝ^r`. -/
theorem exists_surjective_outputProjection
    {d q r : ℕ} (A : Euc d →L[ℝ] Euc q)
    (hrank : r ≤ Module.finrank ℝ A.range) :
    ∃ L : Euc q →L[ℝ] Euc r, (L.comp A).range = ⊤ := by
  have hdim : Module.finrank ℝ (Euc r) ≤ Module.finrank ℝ A.range := by
    simpa only [finrank_euclideanSpace_fin] using hrank
  obtain ⟨i, hi⟩ := (finrank_le_iff_exists_linearMap.mp hdim)
  let j : Euc r →ₗ[ℝ] Euc q := A.range.subtype.comp i
  have hj : Function.Injective j := A.range.injective_subtype.comp hi
  obtain ⟨L, hL⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  let Lc : Euc q →L[ℝ] Euc r :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  refine ⟨Lc, LinearMap.range_eq_top.mpr ?_⟩
  intro y
  obtain ⟨x, hx⟩ := (i y).property
  refine ⟨x, ?_⟩
  change L (A x) = y
  calc
    L (A x) = L (i y : Euc q) := congrArg L hx
    _ = y := by
      have hLy := LinearMap.congr_fun hL y
      simpa [j] using hLy

/-- A rank lower bound produces a projected strict derivative to which the
surjective implicit-function chart applies.  The chart parameter kernel has
the expected dimension `d - r`; the original level set is locally contained
in the projected level set represented by the chart. -/
theorem HasStrictFDerivAt.exists_projected_localLipschitz_fiberChart
    {d q r : ℕ} {H : Euc d → Euc q} {A : Euc d →L[ℝ] Euc q} {a : Euc d}
    (hH : HasStrictFDerivAt H A a)
    (hrank : r ≤ Module.finrank ℝ A.range) :
    ∃ (L : Euc q →L[ℝ] Euc r),
      (L.comp A).range = ⊤ ∧
      Module.finrank ℝ (L.comp A).ker = d - r ∧
      ∃ (K : NNReal) (U : Set (L.comp A).ker) (ψ : (L.comp A).ker → Euc d),
        U ∈ 𝓝 0 ∧
          LipschitzOnWith K ψ U ∧
            (∀ y ∈ U, L (H (ψ y)) = L (H a)) ∧
              (∀ᶠ x in 𝓝 a, H x = H a → ∃ y ∈ U, ψ y = x) ∧
                ψ 0 = a := by
  obtain ⟨L, hsurj⟩ := exists_surjective_outputProjection A hrank
  refine ⟨L, hsurj, ?_, ?_⟩
  · have hrankNullity := (L.comp A).toLinearMap.finrank_range_add_finrank_ker
    have hrange : Module.finrank ℝ (L.comp A).range = r := by
      rw [hsurj, finrank_top, finrank_euclideanSpace_fin]
    have hdomain : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
    omega
  · have hprojected : HasStrictFDerivAt (fun x => L (H x)) (L.comp A) a :=
      L.hasStrictFDerivAt.comp a hH
    obtain ⟨K, U, hU, hLip, hlevel, hcontains, hzero⟩ :=
      CFG.HasStrictFDerivAt.exists_localLipschitz_fiberChart hprojected
        hsurj
    refine ⟨K, U, _, hU, hLip, hlevel, ?_, hzero⟩
    filter_upwards [hcontains] with x hx hxeq
    exact hx (congrArg L hxeq)

/-- Ball-domain version of the projected chart.  In addition to the expected
kernel dimension, this exposes a strictly positive parameter radius, which is
the form needed by quantitative Euclidean covering estimates. -/
theorem HasStrictFDerivAt.exists_projected_localLipschitz_fiberChart_ball
    {d q r : ℕ} {H : Euc d → Euc q} {A : Euc d →L[ℝ] Euc q} {a : Euc d}
    (hH : HasStrictFDerivAt H A a)
    (hrank : r ≤ Module.finrank ℝ A.range) :
    ∃ (L : Euc q →L[ℝ] Euc r),
      (L.comp A).range = ⊤ ∧
      Module.finrank ℝ (L.comp A).ker = d - r ∧
      ∃ (K : NNReal) (R : ℝ), 0 < R ∧
        ∃ ψ : (L.comp A).ker → Euc d,
          LipschitzOnWith K ψ (Metric.ball 0 R) ∧
          (∀ y ∈ Metric.ball (0 : (L.comp A).ker) R,
            L (H (ψ y)) = L (H a)) ∧
          (∀ᶠ x in nhds a, H x = H a →
            ∃ y ∈ Metric.ball (0 : (L.comp A).ker) R, ψ y = x) ∧
          ψ 0 = a := by
  obtain ⟨L, hsurj⟩ := exists_surjective_outputProjection A hrank
  refine ⟨L, hsurj, ?_, ?_⟩
  · have hrankNullity := (L.comp A).toLinearMap.finrank_range_add_finrank_ker
    have hrange : Module.finrank ℝ (L.comp A).range = r := by
      rw [hsurj, finrank_top, finrank_euclideanSpace_fin]
    have hdomain : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
    omega
  · have hprojected : HasStrictFDerivAt (fun x => L (H x)) (L.comp A) a :=
      L.hasStrictFDerivAt.comp a hH
    obtain ⟨K, R, hR, hLip, hlevel, hcontains, hzero⟩ :=
      CFG.HasStrictFDerivAt.exists_localLipschitz_fiberChart_ball
        hprojected hsurj
    refine ⟨K, R, hR, _, hLip, hlevel, ?_, hzero⟩
    filter_upwards [hcontains] with x hx hxeq
    exact hx (congrArg L hxeq)

/-- A compact level set is finite when its strict derivative has full domain
rank at every point.  The proof uses the zero-dimensional projected charts to
show that the fiber is discrete, then compactness. -/
theorem finite_fiber_of_fullRank_strictFDeriv
    {d q : ℕ} {E : Set (Euc d)} {H : Euc d → Euc q} {z : Euc q}
    (hcompact : IsCompact E)
    (hH : Continuous H)
    (A : Euc d → Euc d →L[ℝ] Euc q)
    (hstrict : ∀ v ∈ fiber E H z, HasStrictFDerivAt H (A v) v)
    (hfull : ∀ v ∈ fiber E H z, d ≤ Module.finrank ℝ (A v).range) :
    (fiber E H z).Finite := by
  have hcompactFiber : IsCompact (fiber E H z) :=
    isCompact_fiber hcompact hH
  apply hcompactFiber.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro v hv
  obtain ⟨L, hsurj, hker, K, U, ψ, hU, hLip, hlevel, hcontains, hzero⟩ :=
    CFG.HasStrictFDerivAt.exists_projected_localLipschitz_fiberChart
      (hstrict v hv) (hfull v hv)
  have hker0 : Module.finrank ℝ (L.comp (A v)).ker = 0 := by
    simpa using hker
  let _ : Subsingleton (L.comp (A v)).ker :=
    (Module.finrank_zero_iff.mp hker0)
  obtain ⟨W, hWsub, hWopen, hvW⟩ := mem_nhds_iff.mp hcontains
  refine ⟨W, hWopen, ?_⟩
  ext x
  constructor
  · rintro ⟨hxW, hxfiber⟩
    have hxproperty := hWsub hxW
    have hHx : H x = H v := hxfiber.2.trans hv.2.symm
    obtain ⟨y, hyU, hψx⟩ := hxproperty hHx
    have hy0 : y = 0 := Subsingleton.elim _ _
    rw [hy0, hzero] at hψx
    exact Set.mem_singleton_iff.mpr hψx.symm
  · intro hx
    have hxv : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨hvW, hv⟩

end CFG
