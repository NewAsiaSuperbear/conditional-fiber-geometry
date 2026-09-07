import CFG.Statistics.RankInterval
import Mathlib.Tactic

/-!
# Exchangeability implies a uniform tie-free rank

This module supplies the probabilistic bridge deliberately left open in
`CFG.Statistics.RankInterval`.  We work with a discrete joint PMF on a finite
coordinate vector.  Its coordinates comprise one distinguished truth and the generated samples.
Exchangeability means invariance of this *joint law* under every coordinate
permutation; the no-ties assumption holds on the support of the joint law.
-/

namespace CFG.Statistics

open scoped ENNReal BigOperators

noncomputable section

variable {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]

/-- Reindex a finite vector by a permutation of its coordinates. -/
def reindex (σ : Equiv.Perm ι) (x : ι → α) : ι → α := fun i => x (σ i)

/-- A joint PMF is exchangeable when every coordinate permutation preserves
the complete joint law.  Thus the distinguished truth and all generated
samples are required to be identically distributed as part of one
exchangeable vector, not merely to have unrelated equal marginals. -/
def Exchangeable (p : PMF (ι → α)) : Prop :=
  ∀ σ : Equiv.Perm ι, p.map (reindex σ) = p

/-- The zero-based rank of coordinate `i`, before packaging the cardinality
bound into a `Fin`. -/
def rankNat (x : ι → α) (i : ι) : ℕ :=
  (Finset.univ.filter fun j => x j < x i).card

omit [Nonempty ι] in
theorem rankNat_lt_card (x : ι → α) (i : ι) : rankNat x i < Fintype.card ι := by
  unfold rankNat
  apply Finset.card_lt_card
  rw [Finset.filter_ssubset]
  exact ⟨i, Finset.mem_univ _, lt_irrefl _⟩

/-- The zero-based rank as one of the `card ι` possible rank positions. -/
def coordinateRank (x : ι → α) (i : ι) : Fin (Fintype.card ι) :=
  ⟨rankNat x i, rankNat_lt_card x i⟩

omit [Nonempty ι] in
@[simp]
theorem coordinateRank_val (x : ι → α) (i : ι) :
    (coordinateRank x i).val = rankNat x i := rfl

omit [Nonempty ι] in
theorem rankNat_reindex (σ : Equiv.Perm ι) (x : ι → α) (i : ι) :
    rankNat (reindex σ x) i = rankNat x (σ i) := by
  unfold rankNat reindex
  apply Finset.card_bijective σ σ.bijective
  intro j
  simp

omit [Nonempty ι] in
theorem coordinateRank_reindex (σ : Equiv.Perm ι) (x : ι → α) (i : ι) :
    coordinateRank (reindex σ x) i = coordinateRank x (σ i) := by
  apply Fin.ext
  exact rankNat_reindex σ x i

omit [Nonempty ι] in
theorem rankNat_strictMono_on_coordinates {x : ι → α} {i j : ι}
    (hij : x i < x j) : rankNat x i < rankNat x j := by
  unfold rankNat
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_trans hk hij
  · intro hEq
    have hiRight : i ∈ Finset.univ.filter (fun k => x k < x j) := by
      simp [hij]
    have hiLeft : i ∉ Finset.univ.filter (fun k => x k < x i) := by
      simp
    exact hiLeft (hEq ▸ hiRight)

omit [Nonempty ι] in
/-- If all coordinates are distinct, their ranks are distinct. -/
theorem coordinateRank_injective {x : ι → α} (hx : Function.Injective x) :
    Function.Injective (coordinateRank x) := by
  intro i j hrank
  by_contra hij
  rcases lt_or_gt_of_ne (hx.ne hij) with hlt | hgt
  · have h := rankNat_strictMono_on_coordinates hlt
    exact h.ne (congrArg Fin.val hrank)
  · have h := rankNat_strictMono_on_coordinates hgt
    exact h.ne (congrArg Fin.val hrank).symm

/-- A bijection sends the uniform PMF on one finite type to the uniform PMF
on the other. -/
theorem uniformOfFintype_map_of_bijective {β γ : Type*}
    [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ]
    (f : β → γ) (hf : Function.Bijective f) :
    (PMF.uniformOfFintype β).map f = PMF.uniformOfFintype γ := by
  classical
  ext k
  rw [PMF.map_apply]
  obtain ⟨i, hi⟩ := hf.surjective k
  rw [tsum_eq_single i]
  · simp only [hi.symm, ite_true, PMF.uniformOfFintype_apply]
    exact congrArg Inv.inv (congrArg Nat.cast
      (Fintype.card_congr (Equiv.ofBijective f hf)))
  · intro j hji
    have hkj : k ≠ f j := by
      intro h
      exact hji (hf.injective (hi.trans h).symm)
    simp [hkj]

/-- Under the tie-free condition, a uniformly selected coordinate has a
uniform rank for each fixed vector. -/
theorem uniform_coordinate_map_rank {x : ι → α} (hx : Function.Injective x) :
    (PMF.uniformOfFintype ι).map (coordinateRank x) =
      PMF.uniformOfFintype (Fin (Fintype.card ι)) := by
  exact uniformOfFintype_map_of_bijective (coordinateRank x)
    ((Fintype.bijective_iff_injective_and_card (coordinateRank x)).2
      ⟨coordinateRank_injective hx, by simp⟩)

omit [Nonempty ι] in
/-- Exchangeability of the full vector law makes the rank distribution of
every coordinate equal. -/
theorem Exchangeable.map_coordinateRank_eq {p : PMF (ι → α)}
    (hp : Exchangeable p) (i j : ι) :
    p.map (fun x => coordinateRank x i) =
      p.map (fun x => coordinateRank x j) := by
  classical
  let σ : Equiv.Perm ι := Equiv.swap i j
  calc
    p.map (fun x => coordinateRank x i) =
        (p.map (reindex σ)).map (fun x => coordinateRank x i) := by
      rw [hp σ]
    _ = p.map ((fun x => coordinateRank x i) ∘ reindex σ) :=
      PMF.map_comp _ _ _
    _ = p.map (fun x => coordinateRank x j) := by
      congr 1
      funext x
      change coordinateRank (reindex σ x) i = coordinateRank x j
      rw [coordinateRank_reindex]
      exact congrArg (coordinateRank x) (Equiv.swap_apply_left i j)

/-- There are no ties with positive probability: every vector in the support
of the joint PMF has pairwise distinct coordinate values. -/
def NoTies (p : PMF (ι → α)) : Prop :=
  ∀ x ∈ p.support, Function.Injective x

/-- The central bridge: invariance of the full joint law under coordinate
permutations, together with support-wise absence of ties, forces the rank of
any distinguished coordinate to have the genuine uniform PMF. -/
theorem exchangeable_coordinateRank_eq_uniform (p : PMF (ι → α))
    (hp : Exchangeable p) (hNoTies : NoTies p) (truth : ι) :
    p.map (fun x => coordinateRank x truth) =
      PMF.uniformOfFintype (Fin (Fintype.card ι)) := by
  let u : PMF ι := PMF.uniformOfFintype ι
  let ur : PMF (Fin (Fintype.card ι)) :=
    PMF.uniformOfFintype (Fin (Fintype.card ι))
  have hmixed :
      p.bind (fun x => u.map (coordinateRank x)) = ur := by
    ext k
    rw [PMF.bind_apply]
    calc
      (∑' x, p x * (u.map (coordinateRank x)) k) =
          ∑' x, p x * ur k := by
        apply tsum_congr
        intro x
        by_cases hx : x ∈ p.support
        · rw [show u.map (coordinateRank x) = ur by
            simpa [u, ur] using uniform_coordinate_map_rank (hNoTies x hx)]
        · have hpx : p x = 0 := (p.apply_eq_zero_iff x).2 hx
          simp [hpx]
      _ = ur k := by
        rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
  have hcomm :
      p.bind (fun x => u.map (coordinateRank x)) =
        u.bind (fun i => p.map (fun x => coordinateRank x i)) := by
    simpa [PMF.map, Function.comp_def] using
      (PMF.bind_comm p u (fun x i => PMF.pure (coordinateRank x i)))
  calc
    p.map (fun x => coordinateRank x truth) =
        u.bind (fun _ => p.map (fun x => coordinateRank x truth)) := by
      rw [PMF.bind_const]
    _ = u.bind (fun i => p.map (fun x => coordinateRank x i)) := by
      congr 1
      funext i
      exact (hp.map_coordinateRank_eq i truth).symm
    _ = p.bind (fun x => u.map (coordinateRank x)) := hcomm.symm
    _ = ur := hmixed
    _ = PMF.uniformOfFintype (Fin (Fintype.card ι)) := rfl

section TruthAndSamples

variable {α : Type*} [LinearOrder α]

/-- For a vector indexed by `Fin (n+1)`, coordinate zero is the distinguished
truth and the other `n` coordinates are the generated samples. -/
def truthRank (n : ℕ) (x : Fin (n + 1) → α) : Fin (n + 1) :=
  Fin.cast (Fintype.card_fin (n + 1))
    (coordinateRank x (0 : Fin (n + 1)))

@[simp]
theorem truthRank_val (n : ℕ) (x : Fin (n + 1) → α) :
    (truthRank n x).val = rankNat x 0 := rfl

/-- An exchangeable, tie-free joint law of one truth and `n` samples gives
the truth a uniform rank among all `n+1` coordinates. -/
theorem exchangeable_truthRank_eq_uniform (n : ℕ)
    (p : PMF (Fin (n + 1) → α))
    (hp : Exchangeable p) (hNoTies : NoTies p) :
    p.map (truthRank n) = PMF.uniformOfFintype (Fin (n + 1)) := by
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    (Fin.castOrderIso (Fintype.card_fin (n + 1))).toEquiv
  calc
    p.map (truthRank n) =
        (p.map (fun x => coordinateRank x (0 : Fin (n + 1)))).map e := by
      rw [PMF.map_comp]
      congr 1
    _ = (PMF.uniformOfFintype (Fin (Fintype.card (Fin (n + 1))))).map e := by
      rw [exchangeable_coordinateRank_eq_uniform p hp hNoTies
        (0 : Fin (n + 1))]
    _ = PMF.uniformOfFintype (Fin (n + 1)) :=
      uniformOfFintype_map_of_bijective e e.bijective

/-- Consequently, the probability that the truth lies strictly between the
minimum and maximum of the `n` samples is exactly `(n-1)/(n+1)`.  This is the
exchangeability/no-ties bridge composed with
`uniformRank_interior_probability`. -/
theorem exchangeable_truthRank_interior_probability (n : ℕ)
    (p : PMF (Fin (n + 1) → α))
    (hp : Exchangeable p) (hNoTies : NoTies p) :
    (p.map (truthRank n)).toOuterMeasure (Set.range (interiorRank n)) =
      ((n - 1 : ℕ) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) := by
  rw [exchangeable_truthRank_eq_uniform n p hp hNoTies]
  exact uniformRank_interior_probability n

/-- With sixteen generated samples, exchangeability and no ties yield the
exact interior-rank coverage `15/17`. -/
theorem exchangeable_truthRank_sixteen_probability
    (p : PMF (Fin 17 → α))
    (hp : Exchangeable p) (hNoTies : NoTies p) :
    (p.map (truthRank 16)).toOuterMeasure (Set.range (interiorRank 16)) =
      (15 : ℝ≥0∞) / 17 := by
  simpa using exchangeable_truthRank_interior_probability 16 p hp hNoTies

end TruthAndSamples

end

end CFG.Statistics
