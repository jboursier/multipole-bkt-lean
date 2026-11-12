/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.ClusterLocality
public import MultipoleBKT.UpperBound.Hierarchical.FrozenData

/-!
# Bad points are determined by the bad dipoles (Remark 5.17)

The paper: Remark 5.17 and its consumers: the frozen
configuration convention, eq. (5.62) ( `{I_bad = V_bad} ⊆ {I_bad^{V_bad} = V_bad}`) and the inclusion `I_good ⊆ I_good^Z`. The equality of the bad sets computed among the bad
dipoles alone with those of the full configuration is used without argument in the paper. We prove it for every configuration whose same-sign distances are pairwise
distinct (`ClusterGeneric`, Lebesgue-almost every configuration, `ae_clusterGeneric`), with
`V = I_bad`:

* `typeOneOn_badPoints`, `typeTwoOn_badPoints`, `typeThreeOn_badPoints`, `badPointsOn_badPoints`:
  `I^k_bad` computed on `V` is `I^k_bad`, `k = 1, 2, 3`, hence `I_bad^V = V`. (Type 1: the good
  dipoles are in singleton clusters, so the clusterings on `V` are the clusterings on `[N]` without
  them, `sameSignClustering_sdiff`. Types 2 and 3: the `U`-classes of the bad points avoid the good
  points (Remark 5.6), and a count of type-2.2 classes above the threshold makes all of them bad.)
* `badRadiusPlusOn_badPoints`, `badRadiusMinusOn_badPoints`: the radii `τ_i^{±,Z}` of the bad
  points computed on `V` are those of the full configuration (Remark 5.17 proper);
  `goodRadiusZ_badPoints`: the radius `τ_i^Z` of a good point is that of the full configuration;
  together `radii_eq_of_good`, `radii_eq_of_bad` (for `radiusPlusZ`, `radiusMinusZ` of
  `MultipoleBKT.UpperBound.Radii`).
* `isGoodZ_of_good` (`I_good ⊆ I_good^Z`), from Remark 5.6:
  `MultipoleBKT.UpperBound.not_multipoleLinked_of_good_of_bad` (a good and a bad dipole are not
  linked) and the definition of `J^3_bad`.
-/

@[expose] public section

open Finset MeasureTheory

namespace MultipoleBKT

namespace UpperBound

open TheoremTwo

variable {N : ℕ}

/-- A configuration whose same-sign distances are pairwise distinct, for the positive and for the
negative charges. -/
def ClusterGeneric (d : Fin N → ℂ × ℂ) : Prop :=
  SameSignGeneric (fun i => (d i).1) ∧ SameSignGeneric (fun i => (d i).2)

theorem ae_clusterGeneric : ∀ᵐ c ∂(volume : Measure (Fin N → ℂ × ℂ)), ClusterGeneric c :=
  ae_sameSignGeneric

/-! ### Remark 5.6 -/

section Remark

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

/-- Good and bad points are complementary. -/
theorem mem_badPoints_or_goodPoints (i : Fin N) :
    i ∈ badPoints p₀ β lam M ε₀ d ∨ i ∈ goodPoints p₀ β lam M ε₀ d := by
  by_cases h : i ∈ badPoints p₀ β lam M ε₀ d
  · exact Or.inl h
  · exact Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h⟩)

theorem not_mem_goodPoints_of_mem_badPoints {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d) :
    i ∉ goodPoints p₀ β lam M ε₀ d :=
  fun h => (Finset.mem_sdiff.1 h).2 hi

end Remark

/-! ### Multipole classes on a smaller set -/

section Classes

variable {M lam : ℝ} {d : Fin N → ℂ × ℂ}

/-- If the class of `i` on `U` lies in `U' ⊆ U`, it is also its class on `U'`. -/
theorem multipoleClassOn_eq_of_subset {U U' : Finset (Fin N)} (hU : U' ⊆ U) {i : Fin N}
    (hcls : multipoleClassOn M lam d U i ⊆ U') :
    multipoleClassOn M lam d U' i = multipoleClassOn M lam d U i := by
  ext j
  rw [mem_classOn_iff, mem_classOn_iff]
  constructor
  · intro h
    refine h.mono fun a b hab => ?_
    rw [SimpleGraph.fromRel_adj] at hab ⊢
    refine ⟨hab.1, ?_⟩
    rcases hab.2 with h' | h'
    · exact Or.inl ⟨hU h'.1, hU h'.2.1, h'.2.2⟩
    · exact Or.inr ⟨hU h'.1, hU h'.2.1, h'.2.2⟩
  · intro h
    refine (mem_of_reachable_of_closed
      (T := fun v => v ∈ multipoleClassOn M lam d U i ∧ (classGraph M lam d U').Reachable i v)
      (fun a b ha hab => ?_) ⟨mem_classOn_self U i, SimpleGraph.Reachable.refl i⟩ h).2
    have hb : b ∈ multipoleClassOn M lam d U i :=
      mem_classOn_iff.2 ((mem_classOn_iff.1 ha.1).trans hab.reachable)
    refine ⟨hb, ha.2.trans (SimpleGraph.Adj.reachable ?_)⟩
    rw [SimpleGraph.fromRel_adj] at hab ⊢
    refine ⟨hab.1, ?_⟩
    rcases hab.2 with h' | h'
    · exact Or.inl ⟨hcls ha.1, hcls hb, h'.2.2⟩
    · exact Or.inr ⟨hcls hb, hcls ha.1, h'.2.2⟩

end Classes

/-! ### Locality of the bad sets -/

section Locality

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

/-- A good dipole lies in a singleton cluster of the clustering of the positive and of the
negative charges. -/
theorem card_eq_one_of_good (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d) :
    (∀ p ∈ sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
        (fun i => (d i).1) (fun i => ‖(d i).1 - (d i).2‖) Finset.univ,
      ∀ g ∈ goodPoints p₀ β lam M ε₀ d, g ∈ p.1 → p.1.card = 1) ∧
    (∀ p ∈ sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
        (fun i => (d i).2) (fun i => ‖(d i).1 - (d i).2‖) Finset.univ,
      ∀ g ∈ goodPoints p₀ β lam M ε₀ d, g ∈ p.1 → p.1.card = 1) := by
  classical
  have hg1 : ∀ g ∈ goodPoints p₀ β lam M ε₀ d, g ∉ badPointsTypeOne p₀ β lam ε₀ d :=
    fun g hg => (mem_goodPoints_iff.1 hg).1
  constructor
  · intro p hp g hg hgp
    rcases card_eq_one_or_of_mem_clustering hq hgen.1 _ p hp with h | h
    · exact h
    · exfalso
      refine hg1 g hg ?_
      simp only [badPointsTypeOne, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
      exact Or.inl (Or.inr ⟨p, ⟨hp, h⟩, hgp⟩)
  · intro p hp g hg hgp
    rcases card_eq_one_or_of_mem_clustering hq hgen.2 _ p hp with h | h
    · exact h
    · exfalso
      refine hg1 g hg ?_
      simp only [badPointsTypeOne, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
      exact Or.inr (Or.inr ⟨p, ⟨hp, h⟩, hgp⟩)

theorem univ_sdiff_goodPoints :
    Finset.univ \ goodPoints p₀ β lam M ε₀ d = badPoints p₀ β lam M ε₀ d := by
  ext i
  simp [goodPoints]

/-- The clustering of the charges of the bad dipoles is the clustering of all charges without the
singleton clusters of the good ones. -/
theorem sameSignClustering_badPoints (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d)
    (z : Fin N → ℂ)
    (hz : z = (fun i => (d i).1) ∨ z = fun i => (d i).2) :
    sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
        (fun i => ‖(d i).1 - (d i).2‖) (badPoints p₀ β lam M ε₀ d) =
      (sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
        (fun i => ‖(d i).1 - (d i).2‖) Finset.univ).filter
          fun p => Disjoint p.1 (goodPoints p₀ β lam M ε₀ d) := by
  have hsing := card_eq_one_of_good (M := M) (lam := lam) (ε₀ := ε₀) hq hgen
  rw [← univ_sdiff_goodPoints (M := M)]
  refine sameSignClustering_sdiff hq _ _ (Finset.subset_univ _) ?_
  rcases hz with rfl | rfl
  · exact hsing.1
  · exact hsing.2

open scoped Classical in
/-- **Type 1 on `V = I_bad`.** -/
theorem typeOneOn_badPoints (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d) :
    typeOneOn p₀ β lam ε₀ (badPoints p₀ β lam M ε₀ d) d = badPointsTypeOne p₀ β lam ε₀ d := by
  set V := badPoints p₀ β lam M ε₀ d
  set G := goodPoints p₀ β lam M ε₀ d
  have hlong : V.filter (fun i => ε₀ * truncationScale p₀ β lam < ‖(d i).1 - (d i).2‖) =
      Finset.univ.filter (fun i => ε₀ * truncationScale p₀ β lam < ‖(d i).1 - (d i).2‖) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rcases mem_badPoints_or_goodPoints (M := M) (d := d) (p₀ := p₀) (β := β) (lam := lam)
      (ε₀ := ε₀) i with hb | hg
    · exact hb
    · exact absurd (norm_le_of_good hg) (not_le.2 h)
  have hcl : ∀ z : Fin N → ℂ, (z = (fun i => (d i).1) ∨ z = fun i => (d i).2) →
      ((sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
          (fun i => ‖(d i).1 - (d i).2‖) V).filter
        (fun Sτ => Sτ.1.card = clusterThreshold p₀ β + 1)) =
      ((sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
          (fun i => ‖(d i).1 - (d i).2‖) Finset.univ).filter
        (fun Sτ => Sτ.1.card = clusterThreshold p₀ β + 1)) := by
    intro z hz
    rw [sameSignClustering_badPoints hq hgen z hz, Finset.filter_filter]
    refine Finset.filter_congr fun p hp => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [Finset.disjoint_left]
    intro g hgp hgG
    have hsing := card_eq_one_of_good (M := M) (lam := lam) (ε₀ := ε₀) hq hgen
    have h1 : p.1.card = 1 := by
      rcases hz with rfl | rfl
      · exact hsing.1 p hp g hgG hgp
      · exact hsing.2 p hp g hgG hgp
    have := hq
    omega
  unfold typeOneOn badPointsTypeOne
  simp only []
  rw [hlong, hcl _ (Or.inl rfl), hcl _ (Or.inr rfl)]

/-- The `U`-class of a bad point not of type 1 consists of bad points. -/
theorem multipoleClassOn_subset_of_bad {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d)
    (hiU : i ∈ typeOneComplement p₀ β lam ε₀ d) :
    goodClass p₀ β lam M ε₀ d i ⊆
      badPoints p₀ β lam M ε₀ d \ badPointsTypeOne p₀ β lam ε₀ d := by
  intro w hw
  have hwU : w ∈ typeOneComplement p₀ β lam ε₀ d :=
    mem_of_classGraph_reachable hiU (mem_classOn_iff.mp hw)
  refine Finset.mem_sdiff.2 ⟨?_, (Finset.mem_sdiff.1 hwU).2⟩
  rcases mem_badPoints_or_goodPoints (M := M) (d := d) (p₀ := p₀) (β := β) (lam := lam)
    (ε₀ := ε₀) w with hb | hg
  · exact hb
  · exfalso
    have hcls : goodClass p₀ β lam M ε₀ d w = goodClass p₀ β lam M ε₀ d i := classOn_eq_of_mem hw
    have hiw : i ∈ goodClass p₀ β lam M ε₀ d w := by
      rw [hcls]
      exact mem_classOn_self _ i
    exact not_mem_badPoints_of_good (good_of_mem_classOn hg hiw) hi

/-- On `U' = V ∖ I^1 ⊆ U`, the classes of the bad points are their classes on `U`. -/
theorem multipoleClassOn_badPoints_eq {i : Fin N}
    (hi : i ∈ badPoints p₀ β lam M ε₀ d \ badPointsTypeOne p₀ β lam ε₀ d) :
    multipoleClassOn M lam d (badPoints p₀ β lam M ε₀ d \ badPointsTypeOne p₀ β lam ε₀ d) i =
      goodClass p₀ β lam M ε₀ d i := by
  have hiU : i ∈ typeOneComplement p₀ β lam ε₀ d :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hi).2⟩
  refine multipoleClassOn_eq_of_subset (fun w hw => ?_) (multipoleClassOn_subset_of_bad
    (Finset.mem_sdiff.1 hi).1 hiU)
  exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hw).2⟩

/-- Membership in `I^2_bad` computed on `V`. -/
theorem mem_typeTwoOn_iff {V : Finset (Fin N)} {i : Fin N} :
    i ∈ typeTwoOn p₀ β lam M ε₀ V d ↔
      i ∈ V \ typeOneOn p₀ β lam ε₀ V d ∧
        (pBeta p₀ β < (multipoleClassOn M lam d (V \ typeOneOn p₀ β lam ε₀ V d) i).card ∨
          ((multipoleClassOn M lam d (V \ typeOneOn p₀ β lam ε₀ V d) i).card ∈
              Finset.Icc 1 (pBeta p₀ β) ∧
            ε₀ ^ (-alphaExponent β) * N *
                lam ^ (2 * ((multipoleClassOn M lam d (V \ typeOneOn p₀ β lam ε₀ V d) i).card - 1)) <
              (((V \ typeOneOn p₀ β lam ε₀ V d).filter fun u =>
                (multipoleClassOn M lam d (V \ typeOneOn p₀ β lam ε₀ V d) u).card =
                  (multipoleClassOn M lam d (V \ typeOneOn p₀ β lam ε₀ V d) i).card).card : ℝ))) := by
  classical
  set U := V \ typeOneOn p₀ β lam ε₀ V d
  unfold typeTwoOn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro (⟨hU, hp⟩ | ⟨k, hk, hmem⟩)
    · exact ⟨hU, Or.inl hp⟩
    · split_ifs at hmem with hcond
      · rw [Finset.mem_filter] at hmem
        refine ⟨hmem.1, Or.inr ⟨hmem.2 ▸ hk, ?_⟩⟩
        rw [hmem.2]
        exact hcond
      · exact absurd hmem (Finset.notMem_empty _)
  · rintro ⟨hU, hp | ⟨hk, hcond⟩⟩
    · exact Or.inl ⟨hU, hp⟩
    · refine Or.inr ⟨_, hk, ?_⟩
      rw [ite_eq_left hcond, Finset.mem_filter]
      exact ⟨hU, rfl⟩

/-- **Type 2 on `V = I_bad`.** -/
theorem typeTwoOn_badPoints (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d) :
    typeTwoOn p₀ β lam M ε₀ (badPoints p₀ β lam M ε₀ d) d = badPointsTypeTwo p₀ β lam M ε₀ d := by
  classical
  have h1 := typeOneOn_badPoints (lam := lam) (M := M) (ε₀ := ε₀) hq hgen
  set V := badPoints p₀ β lam M ε₀ d
  set U := typeOneComplement p₀ β lam ε₀ d
  set U' := V \ badPointsTypeOne p₀ β lam ε₀ d
  have hU'U : U' ⊆ U := fun w hw =>
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hw).2⟩
  have hcls : ∀ u ∈ U', multipoleClassOn M lam d U' u =
      multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) u :=
    fun u hu => multipoleClassOn_badPoints_eq hu
  -- the classes of size `k` of `U'` are those of `U` when the count exceeds the threshold
  have hfilt : ∀ k, (U'.filter fun u => (multipoleClassOn M lam d U' u).card = k) ⊆
      U.filter fun u => (multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) u).card = k := by
    intro k u hu
    rw [Finset.mem_filter] at hu ⊢
    exact ⟨hU'U hu.1, by rw [← hcls u hu.1]; exact hu.2⟩
  ext i
  rw [mem_typeTwoOn_iff, h1, mem_badPointsTypeTwo_iff]
  constructor
  · rintro ⟨hiU', hp | ⟨hk, hcond⟩⟩
    · exact ⟨hU'U hiU', Or.inl (by rw [← hcls i hiU']; exact hp)⟩
    · refine ⟨hU'U hiU', Or.inr ⟨by rw [← hcls i hiU']; exact hk, ?_⟩⟩
      rw [← hcls i hiU']
      refine hcond.trans_le ?_
      exact_mod_cast Finset.card_le_card (hfilt _)
  · rintro ⟨hiU, hrest⟩
    have hiV : i ∈ V := by
      unfold V badPoints
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (mem_badPointsTypeTwo_iff.2 ⟨hiU, hrest⟩))
    have hiU' : i ∈ U' := Finset.mem_sdiff.2 ⟨hiV, (Finset.mem_sdiff.1 hiU).2⟩
    rcases hrest with hp | ⟨hk, hcond⟩
    · exact ⟨hiU', Or.inl (by rw [hcls i hiU']; exact hp)⟩
    · refine ⟨hiU', Or.inr ⟨by rw [hcls i hiU']; exact hk, ?_⟩⟩
      rw [hcls i hiU']
      refine hcond.trans_le ?_
      refine Nat.cast_le.2 (Finset.card_le_card fun u hu => ?_)
      rw [Finset.mem_filter] at hu ⊢
      have huV : u ∈ V := by
        unfold V badPoints
        refine Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_badPointsTypeTwo_iff.2 ⟨hu.1, Or.inr ⟨by rw [hu.2]; exact hk, ?_⟩⟩))
        rw [hu.2]
        exact hcond
      have huU' : u ∈ U' := Finset.mem_sdiff.2 ⟨huV, (Finset.mem_sdiff.1 hu.1).2⟩
      exact ⟨huU', by rw [hcls u huU']; exact hu.2⟩

theorem typeOneTwo_subset_badPoints :
    badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d ⊆
      badPoints p₀ β lam M ε₀ d :=
  Finset.subset_union_left

/-- **Type 3 on `V = I_bad`.** -/
theorem typeThreeOn_badPoints (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d) :
    typeThreeOn p₀ β lam M ε₀ (badPoints p₀ β lam M ε₀ d) d =
      badPointsTypeThree p₀ β lam M ε₀ d := by
  classical
  have h1 := typeOneOn_badPoints (lam := lam) (M := M) (ε₀ := ε₀) hq hgen
  have h2 := typeTwoOn_badPoints (lam := lam) (M := M) (ε₀ := ε₀) hq hgen
  set V := badPoints p₀ β lam M ε₀ d
  set I₁₂ := badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d
  have hcls : ∀ u ∈ V \ badPointsTypeOne p₀ β lam ε₀ d,
      multipoleClassOn M lam d (V \ badPointsTypeOne p₀ β lam ε₀ d) u =
        multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) u :=
    fun u hu => multipoleClassOn_badPoints_eq hu
  ext i
  unfold typeThreeOn
  simp only []
  rw [h1, h2, mem_badPointsTypeThree_iff]
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hiV, hi12⟩, j, hj⟩
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff] at hj
    have hiV1 : i ∈ V \ badPointsTypeOne p₀ β lam ε₀ d :=
      Finset.mem_sdiff.2 ⟨hiV, fun h => hi12 (Finset.mem_union_left _ h)⟩
    refine ⟨hi12, j, Finset.mem_inter.2 ⟨by rw [← hcls i hiV1]; exact hj.1, ?_⟩⟩
    rw [Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨⟨Finset.mem_univ _, hj.2.1.2⟩, hj.2.2⟩
  · rintro ⟨hi12, j, hj⟩
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff] at hj
    have hiV : i ∈ V := by
      unfold V badPoints
      exact Finset.mem_union_right _ (mem_badPointsTypeThree_iff.2 ⟨hi12, j,
        Finset.mem_inter.2 ⟨hj.1, Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 hj.2.1, hj.2.2⟩⟩⟩)
    have hiV1 : i ∈ V \ badPointsTypeOne p₀ β lam ε₀ d :=
      Finset.mem_sdiff.2 ⟨hiV, fun h => hi12 (Finset.mem_union_left _ h)⟩
    have hiU : i ∈ typeOneComplement p₀ β lam ε₀ d :=
      Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hiV1).2⟩
    have hjV : j ∈ V := (Finset.mem_sdiff.1 (multipoleClassOn_subset_of_bad hiV hiU hj.1)).1
    refine ⟨⟨hiV, hi12⟩, j, Finset.mem_inter.2 ⟨by rw [hcls i hiV1]; exact hj.1, ?_⟩⟩
    rw [Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨⟨hjV, hj.2.1.2⟩, hj.2.2⟩

/-- **`I_bad^V = V` for `V = I_bad`** (the inclusion `{I_bad = V_bad} ⊆ {I_bad^{V_bad} = V_bad}` of
eq. (5.62)). -/
theorem badPointsOn_badPoints (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d) :
    badPointsOn p₀ β lam M ε₀ (badPoints p₀ β lam M ε₀ d) d = badPoints p₀ β lam M ε₀ d := by
  unfold badPointsOn
  rw [typeOneOn_badPoints hq hgen, typeTwoOn_badPoints hq hgen, typeThreeOn_badPoints hq hgen]
  rfl

end Locality

/-! ### The radii -/

section Radii

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

/-- The removal values of the bad points in the clusterings on `V = I_bad` are those of the full
clusterings. -/
theorem clusterRemovalValueOn_badPoints (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d)
    (z : Fin N → ℂ) (hz : z = (fun i => (d i).1) ∨ z = fun i => (d i).2) {i : Fin N}
    (hi : i ∈ badPoints p₀ β lam M ε₀ d) :
    clusterRemovalValueOn (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
        (fun i => ‖(d i).1 - (d i).2‖) (badPoints p₀ β lam M ε₀ d) i =
      clusterRemovalValue (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
        (fun i => ‖(d i).1 - (d i).2‖) i := by
  classical
  obtain ⟨p, hp, hip, hpi⟩ := exists_mem_clustering_univ (q := clusterThreshold p₀ β)
    (h := ε₀ * truncationScale p₀ β lam) (z := z) (r := fun i => ‖(d i).1 - (d i).2‖) i
  have hsing := card_eq_one_of_good (M := M) (lam := lam) (ε₀ := ε₀) hq hgen
  have hdisj : Disjoint p.1 (goodPoints p₀ β lam M ε₀ d) := by
    rw [Finset.disjoint_left]
    intro g hgp hgG
    have h1 : p.1.card = 1 := by
      rcases hz with rfl | rfl
      · exact hsing.1 p hp g hgG hgp
      · exact hsing.2 p hp g hgG hgp
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
    rw [ha, Finset.mem_singleton] at hgp hip
    rw [hip, ← hgp] at hi
    exact not_mem_badPoints_of_good hgG hi
  have hpV : p ∈ sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
      (fun i => ‖(d i).1 - (d i).2‖) (badPoints p₀ β lam M ε₀ d) := by
    rw [sameSignClustering_badPoints hq hgen z hz]
    exact Finset.mem_filter.2 ⟨hp, hdisj⟩
  rw [clusterRemovalValueOn_eq hpV hip, hpi]

theorem badRadiusPlusOn_badPoints (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d)
    {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d) :
    badRadiusPlusOn p₀ β lam ε₀ (badPoints p₀ β lam M ε₀ d) d i = radiusPlusZ p₀ β lam M ε₀ d i := by
  unfold badRadiusPlusOn radiusPlusZ clusterRadiusOn
  rw [ite_eq_right (not_mem_goodPoints_of_mem_badPoints hi), clusterRemovalValueOn_badPoints hq hgen _
    (Or.inl rfl) hi]
  rfl

theorem badRadiusMinusOn_badPoints (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d)
    {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d) :
    badRadiusMinusOn p₀ β lam ε₀ (badPoints p₀ β lam M ε₀ d) d i =
      radiusMinusZ p₀ β lam M ε₀ d i := by
  unfold badRadiusMinusOn radiusMinusZ clusterRadiusOn
  rw [ite_eq_right (not_mem_goodPoints_of_mem_badPoints hi), clusterRemovalValueOn_badPoints hq hgen _
    (Or.inr rfl) hi]
  rfl

/-- `min'` of `insert a (s.image f)` is the fold of `min` from `a`. -/
theorem min'_insert_image_eq_fold {α : Type*} [DecidableEq α] (s : Finset α) (a : ℝ) (f : α → ℝ) :
    (insert a (s.image f)).min' (Finset.insert_nonempty _ _) = s.fold min a f := by
  refine le_antisymm ?_ ?_
  · refine (Finset.le_fold_min _).2 ⟨Finset.min'_le _ _ (Finset.mem_insert_self _ _),
      fun x hx => Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hx))⟩
  · have hmem := Finset.min'_mem (insert a (s.image f)) (Finset.insert_nonempty _ _)
    rcases Finset.mem_insert.1 hmem with h | h
    · rw [h]
      exact (Finset.fold_min_le _).2 (Or.inl le_rfl)
    · obtain ⟨x, hx, hfx⟩ := Finset.mem_image.1 h
      rw [← hfx]
      exact (Finset.fold_min_le _).2 (Or.inr ⟨x, hx, le_rfl⟩)

theorem badDist_eq_badDistZ (i : Fin N) :
    badDist p₀ β lam M ε₀ d i =
      badDistZ p₀ β lam ε₀ (badPoints p₀ β lam M ε₀ d) d (d i) := by
  classical
  unfold badDist badDistZ
  convert min'_insert_image_eq_fold (badPoints p₀ β lam M ε₀ d) _ (fun j => dipoleDist (d i) (d j))

theorem goodRadiusZ_badPoints {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    goodRadiusZ p₀ β lam ε₀ (badPoints p₀ β lam M ε₀ d) d (d i) =
      radiusPlusZ p₀ β lam M ε₀ d i := by
  unfold goodRadiusZ radiusPlusZ
  rw [ite_eq_left hi, badDist_eq_badDistZ]

/-- The radii of a good point are `(τ_i^Z, τ_i^Z)`. -/
theorem radii_eq_of_good {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    (radiusPlusZ p₀ β lam M ε₀ d i, radiusMinusZ p₀ β lam M ε₀ d i) =
      (goodRadiusZ p₀ β lam ε₀ (badPoints p₀ β lam M ε₀ d) d (d i),
        goodRadiusZ p₀ β lam ε₀ (badPoints p₀ β lam M ε₀ d) d (d i)) := by
  rw [goodRadiusZ_badPoints hi, radiusMinusZ_eq_radiusPlusZ hi]

/-- The radii of a bad point are those computed on `V = I_bad`. -/
theorem radii_eq_of_bad (hq : 1 ≤ clusterThreshold p₀ β) (hgen : ClusterGeneric d) {i : Fin N}
    (hi : i ∈ badPoints p₀ β lam M ε₀ d) :
    (radiusPlusZ p₀ β lam M ε₀ d i, radiusMinusZ p₀ β lam M ε₀ d i) =
      badRadiiZ p₀ β lam ε₀ (badPoints p₀ β lam M ε₀ d) d i := by
  rw [badRadiiZ, badRadiusPlusOn_badPoints hq hgen hi,
    badRadiusMinusOn_badPoints hq hgen hi]

end Radii

/-! ### `I_good ⊆ I_good^Z` -/

section GoodZ

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

/-- **`I_good ⊆ I_good^Z`** (Definition 5.13): a good point is compatible with the frozen bad points. -/
theorem isGoodZ_of_good (hq : 1 ≤ clusterThreshold p₀ β) (hM : 0 ≤ M) (hgen : ClusterGeneric d)
    {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    IsGoodZ p₀ β lam M ε₀ (badPoints p₀ β lam M ε₀ d) d (d i) := by
  classical
  rw [IsGoodZ, typeOneOn_badPoints hq hgen, typeTwoOn_badPoints hq hgen,
    typeThreeOn_badPoints hq hgen]
  obtain ⟨hi1, hi2, hi3⟩ := mem_goodPoints_iff.1 hi
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · by_contra hle
    push Not at hle
    apply hi3
    refine mem_badPointsTypeThree_iff.2 ⟨?_, i, Finset.mem_inter.2 ⟨mem_classOn_self _ i, ?_⟩⟩
    · rw [Finset.mem_union, not_or]
      exact ⟨hi1, hi2⟩
    · rw [Finset.mem_filter, Finset.mem_sdiff]
      refine ⟨⟨Finset.mem_univ _, ?_⟩, j, hj, hle⟩
      rw [Finset.mem_union, not_or]
      exact ⟨hi1, hi2⟩
  · have hjb : j ∈ badPoints p₀ β lam M ε₀ d := Finset.mem_union_right _ hj
    have h := not_multipoleLinked_of_good_of_bad hM hi hjb
    unfold MultipoleLinked at h
    push Not at h
    rw [← max_min_distrib_right] at h
    exact h

end GoodZ

end UpperBound

end MultipoleBKT

end
