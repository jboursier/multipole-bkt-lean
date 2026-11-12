/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Clustering
public import MultipoleBKT.Main.TheoremTwo.GoodPoints
public import MultipoleBKT.Frozen.TruncationScale
public import MultipoleBKT.Frozen.ClusterThreshold

/-!
# Bad points computed among a subset of the labels (`I_bad^V`)

The paper: the proof of Lemma 5.16
introduces, for `V ⊆ [N]`, the set `I_bad^V` of bad points "computed only among `(x_i, y_i)_{i ∈ V}`",
and Section 5.3 fixes the convention for frozen configurations of bad points `Z`: "the bad sets
and radii are computed from `Z`, keeping `N` in the count thresholds". Here a configuration is a
dipole configuration `d : Fin N → ℂ × ℂ` (the ambient `N` is the length, so it stays in the
thresholds of Definition 5.3) and the computation is restricted to the labels of
`V : Finset (Fin N)`:

* `typeOneOn`, `typeTwoOn`, `typeThreeOn`, `badPointsOn`: Definitions 5.2–5.5 with `[N]`
  replaced by `V` (the clusterings of Definition 5.1 run on `V`, `U = V ∖ I^1`, multipoles
  computed on `U`, `J^3` and `I^3` among `V ∖ (I^1 ∪ I^2)`);
* `clusterRemovalValueOn`, `clusterRadiusOn`: the removal value and the radius
  `τ_i = max(λ, removal value)` of Definition 5.1 for the clustering run on `V`;
* `badRadiusPlusOn`, `badRadiusMinusOn`: the radii `τ_i^{±,Z} = max(τ_i^±, λ)` of Definition 5.8
  for the bad points, computed on `V`.

For `V = [N]` these are the frozen definitions and the radii of
`MultipoleBKT.UpperBound.clusterRadius` (`typeOneOn_univ`, …, `badPointsOn_univ`,
`clusterRadiusOn_univ`), by `rfl`. All of them depend
only on the dipoles of `V` (`badPointsOn_congr`, `badRadiusPlusOn_congr`, …; the clustering itself:
`sameSignClustering_congr`).
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

open TheoremTwo

variable {N : ℕ}

/-! ### The definitions -/

section Definitions

open scoped Classical in
/-- Bad points of type 1 computed among the labels of `V` (Definition 5.2 with `[N]` replaced by
`V`): `J^{1,±}_V = {i ∈ V : r_i > ε₀ R̄} ∪ ⋃_{S ∈ Clus^±_V, |S| = q(β)+1} S`, with `Clus^±_V` the
`q(β)`-clusterings of the charges of `V`. -/
noncomputable def typeOneOn (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N)) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  let J : (Fin N → ℂ) → Finset (Fin N) := fun z =>
    V.filter (fun i => ε₀ * truncationScale p₀ β lam < ‖(d i).1 - (d i).2‖) ∪
      ((sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
          (fun i => ‖(d i).1 - (d i).2‖) V).filter
        (fun Sτ => Sτ.1.card = clusterThreshold p₀ β + 1)).biUnion Prod.fst
  J (fun i => (d i).1) ∪ J (fun i => (d i).2)

open scoped Classical in
/-- Bad points of type 2 computed among the labels of `V` (Definition 5.3 with `U = V ∖ I^1_V`;
the count thresholds keep the ambient `N`). -/
noncomputable def typeTwoOn (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N))
    (d : Fin N → ℂ × ℂ) : Finset (Fin N) :=
  let U := V \ typeOneOn p₀ β lam ε₀ V d
  U.filter (fun i => pBeta p₀ β < (multipoleClassOn M lam d U i).card) ∪
    (Finset.Icc 1 (pBeta p₀ β)).biUnion fun k =>
      if ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) <
          ((U.filter fun i => (multipoleClassOn M lam d U i).card = k).card : ℝ)
      then U.filter fun i => (multipoleClassOn M lam d U i).card = k
      else ∅

open scoped Classical in
/-- Bad points of type 3 computed among the labels of `V` (Definition 5.4 with `[N]` replaced
by `V`). -/
noncomputable def typeThreeOn (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N))
    (d : Fin N → ℂ × ℂ) : Finset (Fin N) :=
  let I₁₂ := typeOneOn p₀ β lam ε₀ V d ∪ typeTwoOn p₀ β lam M ε₀ V d
  let U := V \ typeOneOn p₀ β lam ε₀ V d
  let J₃ := (V \ I₁₂).filter fun i => ∃ j ∈ I₁₂,
    min (min ‖(d i).1 - (d j).1‖ ‖(d i).1 - (d j).2‖) (min ‖(d i).2 - (d j).1‖ ‖(d i).2 - (d j).2‖)
      ≤ M * max ‖(d i).1 - (d i).2‖ lam
  (V \ I₁₂).filter fun i => (multipoleClassOn M lam d U i ∩ J₃).Nonempty

/-- **`I_bad^V`**: the bad points computed only among the dipoles of `V` (proof of Lemma 5.16), with the
ambient `N` in the count thresholds (Section 5.3). -/
noncomputable def badPointsOn (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N))
    (d : Fin N → ℂ × ℂ) : Finset (Fin N) :=
  typeOneOn p₀ β lam ε₀ V d ∪ typeTwoOn p₀ β lam M ε₀ V d ∪ typeThreeOn p₀ β lam M ε₀ V d

/-- The removal value of `i` in the `q`-clustering run on the labels of `V` (Definition 5.1). -/
noncomputable def clusterRemovalValueOn (q : ℕ) (h : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ)
    (V : Finset (Fin N)) (i : Fin N) : ℝ :=
  sSup (Prod.snd '' {p | p ∈ sameSignClustering q h z r V ∧ i ∈ p.1})

/-- The radius `max(λ, removal value)` of Definition 5.1 for the clustering run on `V`. -/
noncomputable def clusterRadiusOn (q : ℕ) (h lam : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ)
    (V : Finset (Fin N)) (i : Fin N) : ℝ :=
  max lam (clusterRemovalValueOn q h z r V i)

/-- **`τ_i^{+,Z}` for a bad point** (Definition 5.8), computed from the dipoles of
`V`: `max(τ_i^+, λ)` with `τ_i^+` the radius of the `q(β)`-clustering of the positive charges of
`V`. -/
noncomputable def badRadiusPlusOn (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N))
    (d : Fin N → ℂ × ℂ) (i : Fin N) : ℝ :=
  max (clusterRadiusOn (clusterThreshold p₀ β) ((ε₀ * truncationScale p₀ β lam)) lam
    (fun k => (d k).1) (fun k => ‖(d k).1 - (d k).2‖) V i) lam

/-- **`τ_i^{-,Z}` for a bad point** (Definition 5.8), computed from the dipoles of `V`. -/
noncomputable def badRadiusMinusOn (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N))
    (d : Fin N → ℂ × ℂ) (i : Fin N) : ℝ :=
  max (clusterRadiusOn (clusterThreshold p₀ β) ((ε₀ * truncationScale p₀ β lam)) lam
    (fun k => (d k).2) (fun k => ‖(d k).1 - (d k).2‖) V i) lam

end Definitions

/-! ### `V = [N]`: the frozen definitions -/

section Univ

variable (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ)

theorem typeOneOn_univ : typeOneOn p₀ β lam ε₀ Finset.univ d = badPointsTypeOne p₀ β lam ε₀ d :=
  rfl

theorem typeTwoOn_univ :
    typeTwoOn p₀ β lam M ε₀ Finset.univ d = badPointsTypeTwo p₀ β lam M ε₀ d :=
  rfl

theorem typeThreeOn_univ :
    typeThreeOn p₀ β lam M ε₀ Finset.univ d = badPointsTypeThree p₀ β lam M ε₀ d :=
  rfl

theorem badPointsOn_univ : badPointsOn p₀ β lam M ε₀ Finset.univ d = badPoints p₀ β lam M ε₀ d :=
  rfl

theorem clusterRemovalValueOn_univ (q : ℕ) (h : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ) (i : Fin N) :
    clusterRemovalValueOn q h z r Finset.univ i = clusterRemovalValue q h z r i :=
  rfl

theorem clusterRadiusOn_univ (q : ℕ) (h : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ) (i : Fin N) :
    clusterRadiusOn q h lam z r Finset.univ i = clusterRadius q h lam z r i :=
  rfl

end Univ

/-! ### Elementary facts -/

section Basic

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)} {d : Fin N → ℂ × ℂ}

theorem typeOneOn_subset : typeOneOn p₀ β lam ε₀ V d ⊆ V := by
  classical
  intro i hi
  simp only [typeOneOn, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion] at hi
  rcases hi with (⟨hi, -⟩ | ⟨p, hp, hip⟩) | (⟨hi, -⟩ | ⟨p, hp, hip⟩)
  · exact hi
  · exact fst_subset_of_mem_clustering hp.1 hip
  · exact hi
  · exact fst_subset_of_mem_clustering hp.1 hip

theorem typeTwoOn_subset : typeTwoOn p₀ β lam M ε₀ V d ⊆ V := by
  classical
  intro i hi
  simp only [typeTwoOn, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion] at hi
  rcases hi with ⟨hi, -⟩ | ⟨k, -, hk⟩
  · exact (Finset.mem_sdiff.1 hi).1
  · split_ifs at hk
    · exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hk).1).1
    · exact absurd hk (Finset.notMem_empty _)

theorem typeThreeOn_subset : typeThreeOn p₀ β lam M ε₀ V d ⊆ V := by
  classical
  intro i hi
  simp only [typeThreeOn, Finset.mem_filter, Finset.mem_sdiff] at hi
  exact hi.1.1

theorem badPointsOn_subset : badPointsOn p₀ β lam M ε₀ V d ⊆ V :=
  Finset.union_subset (Finset.union_subset typeOneOn_subset typeTwoOn_subset) typeThreeOn_subset

end Basic

/-! ### Dependence on the dipoles of `V` only -/

section Congr

variable {q : ℕ} {h : ℝ}

/-- The clustering on `I` depends only on the charges and lengths of the labels of `I`. -/
theorem sameSignClustering_congr {z z' : Fin N → ℂ} {r r' : Fin N → ℝ} (I : Finset (Fin N))
    (hz : ∀ i ∈ I, z i = z' i) (hr : ∀ i ∈ I, r i = r' i) :
    sameSignClustering q h z r I = sameSignClustering q h z' r' I := by
  classical
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · rw [sameSignClustering_of_empty, sameSignClustering_of_empty]
  have hcrowd : ∀ t, crowdedSet q z I t = crowdedSet q z' I t := by
    intro t
    rw [crowdedSet_eq, crowdedSet_eq]
    refine Finset.filter_congr fun i hi => ?_
    rw [Finset.filter_congr fun j hj => by rw [hz i hi, hz j hj]]
  have hinf : I.inf' hI r = I.inf' hI r' := Finset.inf'_congr hI rfl fun i hi => hr i hi
  have hτ : clusterTau q h z r I hI = clusterTau q h z' r' I hI := by
    unfold clusterTau
    simp only [hcrowd, hinf]
  have hfilt : ∀ τ : ℝ, (I.filter fun i => r i / 4 = τ) = I.filter fun i => r' i / 4 = τ :=
    fun τ => Finset.filter_congr fun i hi => by rw [hr i hi]
  have hkey : ∀ τ : ℝ, I.image (clusterKey q z r I τ) = I.image (clusterKey q z' r' I τ) := by
    intro τ
    refine Finset.image_congr fun j hj => ?_
    simp only [clusterKey, hcrowd, hr j hj]
  have hchosen : ∀ τ : ℝ, clusterChosen q z r I τ hI = clusterChosen q z' r' I τ hI := by
    intro τ
    unfold clusterChosen
    simp only [hkey]
  have hJ : ∀ τ : ℝ, clusterJ q z r I τ hI = clusterJ q z' r' I τ hI := by
    intro τ
    unfold clusterJ
    rw [hchosen τ]
    congr 1
    refine Finset.filter_congr fun j hj => ?_
    rw [hz j hj, hz _ ?_]
    obtain ⟨j', hj', hj'k⟩ := Finset.mem_image.1
      ((I.image (clusterKey q z' r' I τ)).min'_mem (hI.image _))
    have : clusterChosen q z' r' I τ hI = j' := by
      simp only [clusterChosen, ← hj'k]; rfl
    exact this ▸ hj'
  rw [sameSignClustering_eq_of_nonempty q h z r I hI,
    sameSignClustering_eq_of_nonempty q h z' r' I hI, hτ]
  set τ := clusterTau q h z' r' I hI
  by_cases h1 : τ = h
  · rw [ite_eq_left h1, ite_eq_left h1]
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases hs : (I.filter fun i => r i / 4 = τ).Nonempty
  · have hs' : (I.filter fun i => r' i / 4 = τ).Nonempty := hfilt τ ▸ hs
    rw [dite_eq_left hs, dite_eq_left hs']
    have hmin : (I.filter fun i => r i / 4 = τ).min' hs =
        (I.filter fun i => r' i / 4 = τ).min' hs' := by
      simp only [hfilt τ]
    rw [hmin]
    have hsub : I.erase ((I.filter fun i => r' i / 4 = τ).min' hs') ⊂ I :=
      Finset.erase_ssubset (Finset.mem_filter.1 (Finset.min'_mem _ hs')).1
    rw [ih _ hsub (fun i hi => hz i (Finset.mem_of_mem_erase hi))
      (fun i hi => hr i (Finset.mem_of_mem_erase hi))]
  · have hs' : ¬ (I.filter fun i => r' i / 4 = τ).Nonempty := hfilt τ ▸ hs
    rw [dite_eq_right hs, dite_eq_right hs', hJ τ]
    have hJne : (clusterJ q z' r' I τ hI).Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
    have hJsub : clusterJ q z' r' I τ hI ⊆ I := by
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · obtain ⟨j', hj', hj'k⟩ := Finset.mem_image.1
          ((I.image (clusterKey q z' r' I τ)).min'_mem (hI.image _))
        have : clusterChosen q z' r' I τ hI = j' := by
          simp only [clusterChosen, ← hj'k]; rfl
        exact this ▸ hj'
      · exact (Finset.mem_filter.1 hj).1
    rw [ih _ (sdiff_ssubset_of_nonempty hJsub hJne)
      (fun i hi => hz i (Finset.mem_sdiff.1 hi).1) (fun i hi => hr i (Finset.mem_sdiff.1 hi).1)]

theorem clusterRemovalValueOn_congr {z z' : Fin N → ℂ} {r r' : Fin N → ℝ} (V : Finset (Fin N))
    (hz : ∀ i ∈ V, z i = z' i) (hr : ∀ i ∈ V, r i = r' i) (i : Fin N) :
    clusterRemovalValueOn q h z r V i = clusterRemovalValueOn q h z' r' V i := by
  unfold clusterRemovalValueOn
  rw [sameSignClustering_congr V hz hr]

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)} {d d' : Fin N → ℂ × ℂ}

/-- The multipole classes on `U` depend only on the dipoles of `U`. -/
theorem multipoleClassOn_congr_on {U : Finset (Fin N)} (hd : ∀ i ∈ U, d i = d' i) (i : Fin N) :
    multipoleClassOn M lam d U i = multipoleClassOn M lam d' U i := by
  have hG : (SimpleGraph.fromRel fun a b : Fin N =>
      a ∈ U ∧ b ∈ U ∧ MultipoleLinked M lam (d a) (d b)) =
      SimpleGraph.fromRel fun a b : Fin N =>
        a ∈ U ∧ b ∈ U ∧ MultipoleLinked M lam (d' a) (d' b) := by
    ext a b
    simp only [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hab, h | h⟩
      · exact ⟨hab, Or.inl ⟨h.1, h.2.1, by rw [← hd a h.1, ← hd b h.2.1]; exact h.2.2⟩⟩
      · exact ⟨hab, Or.inr ⟨h.1, h.2.1, by rw [← hd b h.1, ← hd a h.2.1]; exact h.2.2⟩⟩
    · rintro ⟨hab, h | h⟩
      · exact ⟨hab, Or.inl ⟨h.1, h.2.1, by rw [hd a h.1, hd b h.2.1]; exact h.2.2⟩⟩
      · exact ⟨hab, Or.inr ⟨h.1, h.2.1, by rw [hd b h.1, hd a h.2.1]; exact h.2.2⟩⟩
  unfold multipoleClassOn
  rw [hG]

theorem typeOneOn_congr (hd : ∀ i ∈ V, d i = d' i) :
    typeOneOn p₀ β lam ε₀ V d = typeOneOn p₀ β lam ε₀ V d' := by
  classical
  have hr : ∀ i ∈ V, ‖(d i).1 - (d i).2‖ = ‖(d' i).1 - (d' i).2‖ := fun i hi => by rw [hd i hi]
  have hx := sameSignClustering_congr (q := clusterThreshold p₀ β)
    (h := ε₀ * truncationScale p₀ β lam) V (fun i hi => by rw [hd i hi]) hr
    (z := fun i => (d i).1) (z' := fun i => (d' i).1)
  have hy := sameSignClustering_congr (q := clusterThreshold p₀ β)
    (h := ε₀ * truncationScale p₀ β lam) V (fun i hi => by rw [hd i hi]) hr
    (z := fun i => (d i).2) (z' := fun i => (d' i).2)
  have hf : V.filter (fun i => ε₀ * truncationScale p₀ β lam < ‖(d i).1 - (d i).2‖) =
      V.filter (fun i => ε₀ * truncationScale p₀ β lam < ‖(d' i).1 - (d' i).2‖) :=
    Finset.filter_congr fun i hi => by rw [hr i hi]
  unfold typeOneOn
  simp only []
  rw [hx, hy, hf]

theorem typeTwoOn_congr (hd : ∀ i ∈ V, d i = d' i) :
    typeTwoOn p₀ β lam M ε₀ V d = typeTwoOn p₀ β lam M ε₀ V d' := by
  have h1 := typeOneOn_congr (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) hd
  have hcls : ∀ i, multipoleClassOn M lam d (V \ typeOneOn p₀ β lam ε₀ V d') i =
      multipoleClassOn M lam d' (V \ typeOneOn p₀ β lam ε₀ V d') i :=
    multipoleClassOn_congr_on fun i hi => hd i (Finset.mem_sdiff.1 hi).1
  unfold typeTwoOn
  simp only []
  rw [h1]
  simp only [hcls]

theorem typeThreeOn_congr (hd : ∀ i ∈ V, d i = d' i) :
    typeThreeOn p₀ β lam M ε₀ V d = typeThreeOn p₀ β lam M ε₀ V d' := by
  classical
  have h1 := typeOneOn_congr (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) hd
  have h2 := typeTwoOn_congr (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) hd
  have hcls : ∀ i, multipoleClassOn M lam d (V \ typeOneOn p₀ β lam ε₀ V d') i =
      multipoleClassOn M lam d' (V \ typeOneOn p₀ β lam ε₀ V d') i :=
    multipoleClassOn_congr_on fun i hi => hd i (Finset.mem_sdiff.1 hi).1
  have hI₁₂ : typeOneOn p₀ β lam ε₀ V d' ∪ typeTwoOn p₀ β lam M ε₀ V d' ⊆ V :=
    Finset.union_subset typeOneOn_subset typeTwoOn_subset
  unfold typeThreeOn
  simp only []
  rw [h1, h2]
  simp only [hcls]
  refine Finset.filter_congr fun i _ => ?_
  refine Iff.of_eq (congrArg Finset.Nonempty (congrArg _ (Finset.filter_congr fun j hj => ?_)))
  have hjV : j ∈ V := (Finset.mem_sdiff.1 hj).1
  refine exists_congr fun l => and_congr_right fun hl => ?_
  rw [hd j hjV, hd l (hI₁₂ hl)]

theorem badPointsOn_congr (hd : ∀ i ∈ V, d i = d' i) :
    badPointsOn p₀ β lam M ε₀ V d = badPointsOn p₀ β lam M ε₀ V d' := by
  unfold badPointsOn
  rw [typeOneOn_congr hd, typeTwoOn_congr hd, typeThreeOn_congr hd]

theorem badRadiusPlusOn_congr (hd : ∀ i ∈ V, d i = d' i) (i : Fin N) :
    badRadiusPlusOn p₀ β lam ε₀ V d i = badRadiusPlusOn p₀ β lam ε₀ V d' i := by
  unfold badRadiusPlusOn clusterRadiusOn
  rw [clusterRemovalValueOn_congr V (fun i hi => by rw [hd i hi]) (fun i hi => by rw [hd i hi])]

theorem badRadiusMinusOn_congr (hd : ∀ i ∈ V, d i = d' i) (i : Fin N) :
    badRadiusMinusOn p₀ β lam ε₀ V d i = badRadiusMinusOn p₀ β lam ε₀ V d' i := by
  unfold badRadiusMinusOn clusterRadiusOn
  rw [clusterRemovalValueOn_congr V (fun i hi => by rw [hd i hi]) (fun i hi => by rw [hd i hi])]

end Congr

/-! ### Bounds on the radii -/

section Radii

variable {p₀ : ℕ} {β lam ε₀ : ℝ} {V : Finset (Fin N)} {d : Fin N → ℂ × ℂ}

theorem clusterRemovalValueOn_eq {q : ℕ} {h : ℝ} {z : Fin N → ℂ} {r : Fin N → ℝ}
    {p : Finset (Fin N) × ℝ} (hp : p ∈ sameSignClustering q h z r V) {i : Fin N} (hi : i ∈ p.1) :
    clusterRemovalValueOn q h z r V i = p.2 := by
  have hset : Prod.snd '' {p' | p' ∈ sameSignClustering q h z r V ∧ i ∈ p'.1} = {p.2} := by
    ext t
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p', ⟨hp', hip'⟩, rfl⟩
      rw [eq_of_mem_clustering _ p' hp' p hp i hip' hi]
    · rintro rfl
      exact ⟨p, ⟨hp, hi⟩, rfl⟩
  rw [clusterRemovalValueOn, hset, csSup_singleton]

theorem clusterRemovalValueOn_le {q : ℕ} {h : ℝ} {z : Fin N → ℂ} {r : Fin N → ℝ} {i : Fin N}
    (hi : i ∈ V) : clusterRemovalValueOn q h z r V i ≤ h := by
  obtain ⟨p, hp, hip⟩ := exists_mem_clustering (q := q) (h := h) (z := z) (r := r) V i hi
  rw [clusterRemovalValueOn_eq hp hip]
  exact snd_le_of_mem_clustering hp

theorem lam_le_badRadiusPlusOn (i : Fin N) : lam ≤ badRadiusPlusOn p₀ β lam ε₀ V d i :=
  le_max_right _ _

theorem lam_le_badRadiusMinusOn (i : Fin N) : lam ≤ badRadiusMinusOn p₀ β lam ε₀ V d i :=
  le_max_right _ _

/-- `τ_i^{+,Z} ≤ max(λ, ε₀ R̄)` for `i ∈ V`. -/
theorem badRadiusPlusOn_le {i : Fin N} (hi : i ∈ V) :
    badRadiusPlusOn p₀ β lam ε₀ V d i ≤ max lam ((ε₀ * truncationScale p₀ β lam)) := by
  unfold badRadiusPlusOn clusterRadiusOn
  exact max_le (max_le (le_max_left _ _) ((clusterRemovalValueOn_le hi).trans (le_max_right _ _)))
    (le_max_left _ _)

theorem badRadiusMinusOn_le {i : Fin N} (hi : i ∈ V) :
    badRadiusMinusOn p₀ β lam ε₀ V d i ≤ max lam ((ε₀ * truncationScale p₀ β lam)) := by
  unfold badRadiusMinusOn clusterRadiusOn
  exact max_le (max_le (le_max_left _ _) ((clusterRemovalValueOn_le hi).trans (le_max_right _ _)))
    (le_max_left _ _)

end Radii

end UpperBound

end MultipoleBKT

end
