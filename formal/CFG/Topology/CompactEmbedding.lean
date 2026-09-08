import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact injective restrictions are embeddings

This closes the topological first step of M13 independently of its later
tangent and curvature estimates.
-/

namespace CFG

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- A continuous map that is injective on a compact set restricts to a closed
embedding of that compact subtype into the Hausdorff target. -/
theorem isClosedEmbedding_restrict_of_isCompact
    {K : Set X} {f : X → Y} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hinj : Set.InjOn f K) :
    Topology.IsClosedEmbedding (K.domRestrict f) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply hf.domRestrict.isClosedEmbedding
  intro x y hxy
  exact Subtype.ext (hinj x.property y.property hxy)

/-- In particular, the restricted map is a topological embedding. -/
theorem isEmbedding_restrict_of_isCompact
    {K : Set X} {f : X → Y} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hinj : Set.InjOn f K) :
    Topology.IsEmbedding (K.domRestrict f) :=
  (isClosedEmbedding_restrict_of_isCompact hK hf hinj).toIsEmbedding

end CFG
