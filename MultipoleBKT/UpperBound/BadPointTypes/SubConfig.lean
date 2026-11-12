/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneData
public import MultipoleBKT.UpperBound.BadPointTypes.ClassRecursion
public import MultipoleBKT.UpperBound.BadPointTypes.Relabel

/-!
# Bad sets of sub-configurations

The paper: proof of Lemma 5.39: "Deleting all type-3 dipoles preserves the bad classes and radii on `B`", "The
restriction to `V_bad^1` preserves its clustering and radii. The type-2 components and count
thresholds are computed on `V_bad^2`." The sub-configuration on the labels `W ⊆ [n]` is
`d ∘ e` with `e : Fin |W| ↪o Fin n` the increasing enumeration of `W`.

* `mem_badPointsTypeOne_comp_iff`, `radiusPlus_comp`, `radiusMinus_comp`: if the complement of
  `W` is a union of clusters (of both clusterings), the type-1 set and the radii of `d ∘ e` are
  those of `d` on `W`.
* `classOn_comp_map`, `classOn_of_union`: the multipole classes of `d ∘ e` are those of `d` when
  `W` is a union of classes.
* `typeTwoBad_comp_eq_univ`: if `W` is exactly the type-2 set of `d` and the complement of `W`
  is a union of clusters, every label of `d ∘ e` is of type 2 (with the same ambient threshold).
* `mem_typeTwoBad_iff`, `typeTwoBad_mem_of_mem_classOn`: type 2 is a union of `U`-classes.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset TheoremTwo UpperBound

variable {m n : ℕ} {M lam : ℝ}

/-! ### Clusters and type 1 -/

section TypeOne

variable {q : ℕ} {h : ℝ} {z : Fin n → ℂ} {r : Fin n → ℝ}

theorem card_clusterOf_eq_iff (i : Fin n) (k : ℕ) :
    (clusterOf q h z r i).card = k ↔
      ∃ p ∈ sameSignClustering q h z r univ, i ∈ p.1 ∧ p.1.card = k := by
  obtain ⟨p, hp, hip, hpi, -⟩ := clusterOf_spec (q := q) (h := h) (z := z) (r := r) i
  constructor
  · intro hk
    exact ⟨p, hp, hip, hpi ▸ hk⟩
  · rintro ⟨p', hp', hip', hk⟩
    rw [hpi, eq_of_mem_clustering _ p hp p' hp' i hip hip']
    exact hk

/-- The cluster sizes of a sub-configuration whose complement is a union of clusters. -/
theorem card_clusterOf_comp (e : Fin m ↪o Fin n)
    (hunion : ∀ p ∈ sameSignClustering q h z r univ,
      p.1 ⊆ univ \ univ.map e.toEmbedding ∨ Disjoint p.1 (univ \ univ.map e.toEmbedding))
    (a : Fin m) :
    (clusterOf q h (z ∘ e) (r ∘ e) a).card = (clusterOf q h z r (e a)).card := by
  obtain ⟨p, hp, hap, -⟩ := clusterOf_spec (q := q) (h := h) (z := z ∘ e) (r := r ∘ e) a
  have h1 := (card_clusterOf_eq_iff (q := q) (h := h) (z := z ∘ e) (r := r ∘ e) a
    (clusterOf q h (z ∘ e) (r ∘ e) a).card).1 rfl
  obtain ⟨p', hp', hap', hk⟩ := (exists_cluster_comp_iff e hunion
    (fun c _ => c = (clusterOf q h (z ∘ e) (r ∘ e) a).card) a).1 h1
  exact ((card_clusterOf_eq_iff (q := q) (h := h) (z := z) (r := r) (e a) _).2
    ⟨p', hp', hap', hk⟩).symm

end TypeOne

/-- Membership in the type-1 set: a long dipole, or a member of an overcrowded cluster of one of
the two clusterings. -/
theorem mem_badPointsTypeOne_iff {p₀ : ℕ} {β ε₀ : ℝ} {d : Fin n → ℂ × ℂ} (i : Fin n) :
    i ∈ badPointsTypeOne p₀ β lam ε₀ d ↔
      cutoff p₀ β lam ε₀ < dipoleLength d i ∨
        (clusterOf (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) (fun k => (d k).1)
          (dipoleLength d) i).card = clusterThreshold p₀ β + 1 ∨
        (clusterOf (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) (fun k => (d k).2)
          (dipoleLength d) i).card = clusterThreshold p₀ β + 1 := by
  unfold badPointsTypeOne
  simp only []
  rw [mem_union, mem_J_iff, mem_J_iff]
  tauto

/-- The complement of `G` is a union of clusters of both clusterings of `d`. -/
def ClusterUnion (p₀ : ℕ) (β lam ε₀ : ℝ) (d : Fin n → ℂ × ℂ) (G : Finset (Fin n)) : Prop :=
  (∀ p ∈ sameSignClustering (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) (fun k => (d k).1)
      (dipoleLength d) univ, p.1 ⊆ G ∨ Disjoint p.1 G) ∧
    (∀ p ∈ sameSignClustering (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) (fun k => (d k).2)
      (dipoleLength d) univ, p.1 ⊆ G ∨ Disjoint p.1 G)

section Comp

variable {p₀ : ℕ} {β ε₀ : ℝ} {d : Fin n → ℂ × ℂ} (e : Fin m ↪o Fin n)

/-- **Type 1 of a sub-configuration.** -/
theorem mem_badPointsTypeOne_comp_iff
    (hU : ClusterUnion p₀ β lam ε₀ d (univ \ univ.map e.toEmbedding)) (a : Fin m) :
    a ∈ badPointsTypeOne p₀ β lam ε₀ (d ∘ e) ↔ e a ∈ badPointsTypeOne p₀ β lam ε₀ d := by
  rw [mem_badPointsTypeOne_iff, mem_badPointsTypeOne_iff]
  have h1 := card_clusterOf_comp (q := clusterThreshold p₀ β) (h := cutoff p₀ β lam ε₀)
    (z := fun k => (d k).1) (r := dipoleLength d) e hU.1 a
  have h2 := card_clusterOf_comp (q := clusterThreshold p₀ β) (h := cutoff p₀ β lam ε₀)
    (z := fun k => (d k).2) (r := dipoleLength d) e hU.2 a
  have e1 : (fun k => ((d ∘ e) k).1) = (fun k => (d k).1) ∘ e := rfl
  have e2 : (fun k => ((d ∘ e) k).2) = (fun k => (d k).2) ∘ e := rfl
  have e3 : dipoleLength (d ∘ e) = dipoleLength d ∘ e := rfl
  rw [e1, e2, e3, h1, h2]
  rfl

theorem radiusPlus_comp (hU : ClusterUnion p₀ β lam ε₀ d (univ \ univ.map e.toEmbedding))
    (a : Fin m) : radiusPlus p₀ β lam ε₀ (d ∘ e) a = radiusPlus p₀ β lam ε₀ d (e a) :=
  clusterRadius_comp (z := fun k => (d k).1) (r := dipoleLength d) e hU.1 lam a

theorem radiusMinus_comp (hU : ClusterUnion p₀ β lam ε₀ d (univ \ univ.map e.toEmbedding))
    (a : Fin m) : radiusMinus p₀ β lam ε₀ (d ∘ e) a = radiusMinus p₀ β lam ε₀ d (e a) :=
  clusterRadius_comp (z := fun k => (d k).2) (r := dipoleLength d) e hU.2 lam a

end Comp

/-! ### Multipole classes -/

section Classes

variable {d : Fin n → ℂ × ℂ}

/-- Classes along an embedding. -/
theorem classOn_comp_map (e : Fin m ↪ Fin n) (U : Finset (Fin m)) (a : Fin m) :
    (multipoleClassOn M lam (d ∘ e) U a).map e = multipoleClassOn M lam d (U.map e) (e a) := by
  ext j
  rw [Finset.mem_map, mem_classOn_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [mem_classOn_iff] at hb
    let f : classGraph M lam (d ∘ e) U →g classGraph M lam d (U.map e) :=
      ⟨e, fun {x y} hxy => by
        rw [SimpleGraph.fromRel_adj] at hxy ⊢
        refine ⟨fun h => hxy.1 (e.injective h), ?_⟩
        rcases hxy.2 with h' | h'
        · exact Or.inl ⟨Finset.mem_map_of_mem e h'.1, Finset.mem_map_of_mem e h'.2.1, h'.2.2⟩
        · exact Or.inr ⟨Finset.mem_map_of_mem e h'.1, Finset.mem_map_of_mem e h'.2.1, h'.2.2⟩⟩
    exact hb.map f
  · intro hj
    obtain ⟨b, rfl, hb⟩ := mem_of_reachable_of_closed
      (T := fun v => ∃ b, v = e b ∧ (classGraph M lam (d ∘ e) U).Reachable a b)
      (fun u v hu huv => by
        obtain ⟨b, rfl, hb⟩ := hu
        rw [SimpleGraph.fromRel_adj] at huv
        have hvU : v ∈ U.map e := by
          rcases huv.2 with h' | h'
          · exact h'.2.1
          · exact h'.1
        obtain ⟨c, hc, rfl⟩ := Finset.mem_map.1 hvU
        refine ⟨c, rfl, hb.trans (SimpleGraph.Adj.reachable ?_)⟩
        rw [SimpleGraph.fromRel_adj]
        refine ⟨fun h => huv.1 (congrArg e h), ?_⟩
        rcases huv.2 with h' | h'
        · exact Or.inl ⟨(Finset.mem_map' e).1 h'.1, hc, h'.2.2⟩
        · exact Or.inr ⟨hc, (Finset.mem_map' e).1 h'.2.1, h'.2.2⟩)
      ⟨a, rfl, SimpleGraph.Reachable.refl a⟩ hj
    exact ⟨b, mem_classOn_iff.2 hb, rfl⟩

/-- On a union `W ⊆ U` of `U`-classes, the `W`-classes are the `U`-classes. -/
theorem classOn_of_union {U W : Finset (Fin n)} (hWU : W ⊆ U)
    (hW : ∀ i ∈ W, multipoleClassOn M lam d U i ⊆ W) {i : Fin n} (hi : i ∈ W) :
    multipoleClassOn M lam d W i = multipoleClassOn M lam d U i := by
  ext j
  rw [mem_classOn_iff, mem_classOn_iff]
  constructor
  · intro h
    refine h.mono fun u v huv => ?_
    rw [SimpleGraph.fromRel_adj] at huv ⊢
    refine ⟨huv.1, ?_⟩
    rcases huv.2 with h' | h'
    · exact Or.inl ⟨hWU h'.1, hWU h'.2.1, h'.2.2⟩
    · exact Or.inr ⟨hWU h'.1, hWU h'.2.1, h'.2.2⟩
  · intro h
    have key := mem_of_reachable_of_closed
      (T := fun v => v ∈ multipoleClassOn M lam d U i ∧ (classGraph M lam d W).Reachable i v)
      (fun u v hu huv => by
        have hv : v ∈ multipoleClassOn M lam d U i := mem_classOn_of_adj hu.1 huv
        refine ⟨hv, hu.2.trans (SimpleGraph.Adj.reachable ?_)⟩
        have huW := hW i hi hu.1
        have hvW := hW i hi hv
        rw [SimpleGraph.fromRel_adj] at huv ⊢
        refine ⟨huv.1, ?_⟩
        rcases huv.2 with h' | h'
        · exact Or.inl ⟨huW, hvW, h'.2.2⟩
        · exact Or.inr ⟨hvW, huW, h'.2.2⟩)
      ⟨mem_classOn_self U i, SimpleGraph.Reachable.refl i⟩ h
    exact key.2

end Classes

/-! ### Type 2 -/

section TypeTwo

variable {p₀ : ℕ} {β ε₀ : ℝ} {d : Fin n → ℂ × ℂ}

/-- The ambient count threshold of type `(2,2,k)`. -/
noncomputable abbrev countThreshold (Nₐ : ℕ) (β lam ε₀ : ℝ) (k : ℕ) : ℝ :=
  ε₀ ^ (-alphaExponent β) * Nₐ * lam ^ (2 * (k - 1))

/-- Membership in the type-2 set (with ambient threshold) depends only on membership in `U` and
on the size of the `U`-class. -/
theorem mem_typeTwoBad_iff (Nₐ : ℕ) {i : Fin n} :
    i ∈ typeTwoBad Nₐ p₀ β lam M ε₀ d ↔
      i ∈ univ \ badPointsTypeOne p₀ β lam ε₀ d ∧
        (pBeta p₀ β < (multipoleClassOn M lam d (univ \ badPointsTypeOne p₀ β lam ε₀ d) i).card ∨
          ((multipoleClassOn M lam d (univ \ badPointsTypeOne p₀ β lam ε₀ d) i).card ∈
              Finset.Icc 1 (pBeta p₀ β) ∧
            countThreshold Nₐ β lam ε₀
                (multipoleClassOn M lam d (univ \ badPointsTypeOne p₀ β lam ε₀ d) i).card <
              (((univ \ badPointsTypeOne p₀ β lam ε₀ d).filter fun u =>
                (multipoleClassOn M lam d (univ \ badPointsTypeOne p₀ β lam ε₀ d) u).card =
                  (multipoleClassOn M lam d (univ \ badPointsTypeOne p₀ β lam ε₀ d) i).card).card :
                ℝ))) := by
  classical
  unfold typeTwoBad typeTwoOneBad typeTwoTwoBad
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

/-- The type-2 set is a union of `U`-classes. -/
theorem typeTwoBad_mem_of_mem_classOn (Nₐ : ℕ) {i j : Fin n}
    (hi : i ∈ typeTwoBad Nₐ p₀ β lam M ε₀ d)
    (hj : j ∈ multipoleClassOn M lam d (univ \ badPointsTypeOne p₀ β lam ε₀ d) i) :
    j ∈ typeTwoBad Nₐ p₀ β lam M ε₀ d := by
  rw [mem_typeTwoBad_iff] at hi ⊢
  have hjU : j ∈ univ \ badPointsTypeOne p₀ β lam ε₀ d := classOn_subset hi.1 hj
  rw [classOn_eq_of_mem hj]
  exact ⟨hjU, hi.2⟩

/-- **Type 2 of the sub-configuration on the type-2 labels.** If `e` enumerates exactly the
type-2 set of `d` and the complement of its range is a union of clusters, every label of `d ∘ e`
is of type 2 (with the same ambient threshold `Nₐ`). -/
theorem typeTwoBad_comp_eq_univ (Nₐ : ℕ) (e : Fin m ↪o Fin n)
    (hrange : univ.map e.toEmbedding = typeTwoBad Nₐ p₀ β lam M ε₀ d)
    (hU : ClusterUnion p₀ β lam ε₀ d (univ \ univ.map e.toEmbedding)) :
    typeTwoBad Nₐ p₀ β lam M ε₀ (d ∘ e) = univ := by
  classical
  set W := typeTwoBad Nₐ p₀ β lam M ε₀ d with hW
  set U := univ \ badPointsTypeOne p₀ β lam ε₀ d with hUdef
  have hWU : W ⊆ U := fun i hi => ((mem_typeTwoBad_iff Nₐ).1 hi).1
  -- type 1 of the sub-configuration is empty
  have hone : badPointsTypeOne p₀ β lam ε₀ (d ∘ e) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
    rw [mem_badPointsTypeOne_comp_iff e hU] at ha
    have hea : e a ∈ W := by
      rw [← hrange]
      exact Finset.mem_map_of_mem _ (Finset.mem_univ a)
    exact (Finset.mem_sdiff.1 (hWU hea)).2 ha
  have hU' : univ \ badPointsTypeOne p₀ β lam ε₀ (d ∘ e) = univ := by
    rw [hone, Finset.sdiff_empty]
  -- the classes
  have hWcl : ∀ i ∈ W, multipoleClassOn M lam d U i ⊆ W := fun i hi j hj =>
    typeTwoBad_mem_of_mem_classOn Nₐ hi hj
  have hclass : ∀ a, (multipoleClassOn M lam (d ∘ e) univ a).map e.toEmbedding =
      multipoleClassOn M lam d U (e a) := by
    intro a
    have hea : e a ∈ W := by
      rw [← hrange]
      exact Finset.mem_map_of_mem _ (Finset.mem_univ a)
    have h := classOn_comp_map (d := d) (M := M) (lam := lam) e.toEmbedding univ a
    rw [hrange] at h
    exact h.trans (classOn_of_union hWU hWcl hea)
  have hcard : ∀ a, (multipoleClassOn M lam (d ∘ e) univ a).card =
      (multipoleClassOn M lam d U (e a)).card := fun a => by
    rw [← hclass a, Finset.card_map]
  refine Finset.eq_univ_of_forall fun a => ?_
  have hea : e a ∈ W := by
    rw [← hrange]
    exact Finset.mem_map_of_mem _ (Finset.mem_univ a)
  have h1 := (mem_typeTwoBad_iff Nₐ).1 hea
  rw [mem_typeTwoBad_iff, hU', hcard]
  refine ⟨Finset.mem_univ a, ?_⟩
  rcases h1.2 with hp | ⟨hk, hcond⟩
  · exact Or.inl hp
  · refine Or.inr ⟨hk, hcond.trans_le ?_⟩
    -- the counts agree: all labels of `U` with a class of this size are of type 2
    set k := (multipoleClassOn M lam d U (e a)).card
    have hsub : (U.filter fun u => (multipoleClassOn M lam d U u).card = k) ⊆ W := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [mem_typeTwoBad_iff]
      refine ⟨hu.1, Or.inr ⟨hu.2 ▸ hk, ?_⟩⟩
      rw [hu.2]
      exact hcond
    have heq : (U.filter fun u => (multipoleClassOn M lam d U u).card = k) =
        ((univ : Finset (Fin m)).filter fun b =>
          (multipoleClassOn M lam (d ∘ e) univ b).card = k).map e.toEmbedding := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨huU, hu⟩
        have huW : u ∈ W := hsub (Finset.mem_filter.2 ⟨huU, hu⟩)
        rw [← hrange] at huW
        obtain ⟨b, -, rfl⟩ := Finset.mem_map.1 huW
        exact ⟨b, (hcard b).trans hu, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        have hbW : e.toEmbedding b ∈ W := by
          rw [← hrange]; exact Finset.mem_map_of_mem _ (Finset.mem_univ b)
        exact ⟨hWU hbW, (hcard b).symm.trans hb⟩
    rw [heq, Finset.card_map]

end TypeTwo

end BadPointTypes

end MultipoleBKT

end
