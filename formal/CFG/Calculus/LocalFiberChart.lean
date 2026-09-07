import Mathlib.Analysis.Calculus.Implicit

/-!
# A genuine local Lipschitz chart for a regular fiber

This module packages the exact fixed-observation consequence needed by the
covering route. It uses mathlib's implicit function produced from a real
strict derivative with surjective derivative. The result includes both
directions locally: chart points lie in the level set, and nearby level-set
points are represented by chart parameters.
-/

namespace CFG

open Filter
open Set
open scoped NNReal Topology

theorem HasStrictFDerivAt.exists_localLipschitz_fiberChart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hsurj : f'.range = ⊤) :
    ∃ (K : ℝ≥0) (U : Set f'.ker),
      U ∈ 𝓝 (0 : f'.ker) ∧
      LipschitzOnWith K (hf.implicitFunction f f' hsurj (f a)) U ∧
      (∀ y ∈ U, f (hf.implicitFunction f f' hsurj (f a) y) = f a) ∧
      (∀ᶠ x in 𝓝 a, f x = f a →
        ∃ y ∈ U, hf.implicitFunction f f' hsurj (f a) y = x) ∧
      hf.implicitFunction f f' hsurj (f a) 0 = a := by
  let chart : f'.ker → E := hf.implicitFunction f f' hsurj (f a)
  have hstrict : HasStrictFDerivAt chart f'.ker.subtypeL 0 :=
    hf.to_implicitFunction hsurj
  obtain ⟨K, U₀, hU₀, hLip⟩ := hstrict.exists_lipschitzOnWith
  have hlevel : {y | f (chart y) = f a} ∈ 𝓝 (0 : f'.ker) := by
    have hslice : Tendsto (fun y : f'.ker => (f a, y)) (𝓝 0) (𝓝 (f a, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    simpa [chart] using hslice (hf.map_implicitFunction_eq hsurj)
  let U : Set f'.ker := U₀ ∩ {y | f (chart y) = f a}
  have hU : U ∈ 𝓝 (0 : f'.ker) := inter_mem hU₀ hlevel
  refine ⟨K, U, hU, hLip.mono inter_subset_left, ?_, ?_, ?_⟩
  · intro y hy
    exact hy.2
  · let e := hf.implicitToOpenPartialHomeomorph f f' hsurj
    have he_cont : ContinuousAt e a := e.continuousAt (hf.mem_implicitToOpenPartialHomeomorph_source hsurj)
    have hcoord_cont : ContinuousAt (fun x => (e x).2) a := he_cont.snd
    have hcoord_zero : (e a).2 = 0 := by
      rw [HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self hf hsurj]
    have hcoordU : ∀ᶠ x in 𝓝 a, (e x).2 ∈ U := by
      rw [← hcoord_zero] at hU
      exact hcoord_cont hU
    filter_upwards [hcoordU, hf.eq_implicitFunction hsurj] with x hxU hxChart
    intro hfx
    refine ⟨(e x).2, hxU, ?_⟩
    simpa [chart, e, hfx] using hxChart
  · exact hf.implicitFunction_apply_image hsurj

/-- The same genuine implicit chart can be restricted to a parameter ball of
strictly positive radius.  The nearby-level-set containment is reproved using
the continuous local inverse coordinates, so the witness really lies in this
smaller ball. -/
theorem HasStrictFDerivAt.exists_localLipschitz_fiberChart_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hsurj : f'.range = ⊤) :
    ∃ (K : ℝ≥0) (R : ℝ), 0 < R ∧
      LipschitzOnWith K (hf.implicitFunction f f' hsurj (f a))
          (Metric.ball 0 R) ∧
      (∀ y ∈ Metric.ball (0 : f'.ker) R,
        f (hf.implicitFunction f f' hsurj (f a) y) = f a) ∧
      (∀ᶠ x in nhds a, f x = f a →
        ∃ y ∈ Metric.ball (0 : f'.ker) R,
          hf.implicitFunction f f' hsurj (f a) y = x) ∧
      hf.implicitFunction f f' hsurj (f a) 0 = a := by
  let chart : f'.ker → E := hf.implicitFunction f f' hsurj (f a)
  have hstrict : HasStrictFDerivAt chart f'.ker.subtypeL 0 :=
    hf.to_implicitFunction hsurj
  obtain ⟨K, U₀, hU₀, hLip⟩ := hstrict.exists_lipschitzOnWith
  have hlevel : {y | f (chart y) = f a} ∈ nhds (0 : f'.ker) := by
    have hslice : Tendsto (fun y : f'.ker => (f a, y)) (nhds 0) (nhds (f a, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    simpa [chart] using hslice (hf.map_implicitFunction_eq hsurj)
  have hgood : U₀ ∩ {y | f (chart y) = f a} ∈ nhds (0 : f'.ker) :=
    inter_mem hU₀ hlevel
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨K, R, hR, hLip.mono (hball.trans inter_subset_left), ?_, ?_, ?_⟩
  · intro y hy
    exact (hball hy).2
  · let e := hf.implicitToOpenPartialHomeomorph f f' hsurj
    have he_cont : ContinuousAt e a :=
      e.continuousAt (hf.mem_implicitToOpenPartialHomeomorph_source hsurj)
    have hcoord_cont : ContinuousAt (fun x => (e x).2) a := he_cont.snd
    have hcoord_zero : (e a).2 = 0 := by
      rw [HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self hf hsurj]
    have hcoordBall : ∀ᶠ x in nhds a, (e x).2 ∈ Metric.ball (0 : f'.ker) R := by
      have hballNhds : Metric.ball (0 : f'.ker) R ∈ nhds 0 :=
        Metric.ball_mem_nhds _ hR
      exact hcoord_cont (by simpa [hcoord_zero] using hballNhds)
    filter_upwards [hcoordBall, hf.eq_implicitFunction hsurj] with x hxBall hxChart
    intro hfx
    refine ⟨(e x).2, hxBall, ?_⟩
    simpa [chart, e, hfx] using hxChart
  · exact hf.implicitFunction_apply_image hsurj

/-- If a second map `g` is strictly differentiable at the fiber point, then
its composition with the genuine implicit chart is Lipschitz on a sufficiently
small positive-radius parameter ball.  This is the direct local bridge needed
for covering the image of a fiber. -/
theorem HasStrictFDerivAt.exists_localLipschitz_imageFiberChart_ball
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {f' : E →L[ℝ] F} {g : E → G} {g' : E →L[ℝ] G} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hsurj : f'.range = ⊤)
    (hg : HasStrictFDerivAt g g' a) :
    ∃ (K : ℝ≥0) (R : ℝ), 0 < R ∧
      LipschitzOnWith K
        (fun y => g (hf.implicitFunction f f' hsurj (f a) y))
        (Metric.ball 0 R) ∧
      (∀ y ∈ Metric.ball (0 : f'.ker) R,
        f (hf.implicitFunction f f' hsurj (f a) y) = f a) ∧
      (∀ᶠ x in nhds a, f x = f a →
        ∃ y ∈ Metric.ball (0 : f'.ker) R,
          hf.implicitFunction f f' hsurj (f a) y = x) ∧
      hf.implicitFunction f f' hsurj (f a) 0 = a := by
  let chart : f'.ker → E := hf.implicitFunction f f' hsurj (f a)
  have hchart : HasStrictFDerivAt chart f'.ker.subtypeL 0 :=
    hf.to_implicitFunction hsurj
  have hchart0 : chart 0 = a := hf.implicitFunction_apply_image hsurj
  have hcomp : HasStrictFDerivAt (fun y => g (chart y))
      (g'.comp f'.ker.subtypeL) 0 := by
    have hgchart : HasStrictFDerivAt g g' (chart 0) := by
      simpa [hchart0] using hg
    exact hgchart.comp 0 hchart
  obtain ⟨K, U₀, hU₀, hLip⟩ := hcomp.exists_lipschitzOnWith
  have hlevel : {y | f (chart y) = f a} ∈ nhds (0 : f'.ker) := by
    have hslice : Tendsto (fun y : f'.ker => (f a, y)) (nhds 0) (nhds (f a, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    simpa [chart] using hslice (hf.map_implicitFunction_eq hsurj)
  have hgood : U₀ ∩ {y | f (chart y) = f a} ∈ nhds (0 : f'.ker) :=
    inter_mem hU₀ hlevel
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨K, R, hR, hLip.mono (hball.trans inter_subset_left), ?_, ?_, ?_⟩
  · intro y hy
    exact (hball hy).2
  · let e := hf.implicitToOpenPartialHomeomorph f f' hsurj
    have he_cont : ContinuousAt e a :=
      e.continuousAt (hf.mem_implicitToOpenPartialHomeomorph_source hsurj)
    have hcoord_cont : ContinuousAt (fun x => (e x).2) a := he_cont.snd
    have hcoord_zero : (e a).2 = 0 := by
      rw [HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self hf hsurj]
    have hcoordBall : ∀ᶠ x in nhds a, (e x).2 ∈ Metric.ball (0 : f'.ker) R := by
      have hballNhds : Metric.ball (0 : f'.ker) R ∈ nhds 0 :=
        Metric.ball_mem_nhds _ hR
      exact hcoord_cont (by simpa [hcoord_zero] using hballNhds)
    filter_upwards [hcoordBall, hf.eq_implicitFunction hsurj] with x hxBall hxChart
    intro hfx
    refine ⟨(e x).2, hxBall, ?_⟩
    simpa [chart, e, hfx] using hxChart
  · exact hf.implicitFunction_apply_image hsurj

end CFG
