/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Leaf removal for Prüfer encoding and ordering

The graph operations used in the proofs of Lemma A.1 and Lemma A.9.
Removing a leaf preserves the tree property. Attaching it again inverts restriction,
and changes only the degree of its neighbour.
-/

@[expose] public section

namespace MultipoleBKT

namespace Cayley

universe u

open SimpleGraph Finset
open scoped Classical

/-! ### Degrees -/

/-- The degree of `i` in `T`, as the cardinality of its neighbour set (instance free). -/
noncomputable def deg {V : Type u} (T : SimpleGraph V) (i : V) : ℕ := Nat.card (T.neighborSet i)

theorem deg_eq_degree {V : Type u} (T : SimpleGraph V) (i : V) [Fintype (T.neighborSet i)] :
    deg T i = T.degree i := by
  rw [deg, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]

section Degree

variable {V : Type u} [Fintype V]

theorem deg_eq_sum (T : SimpleGraph V) (i : V) :
    deg T i = ∑ u, if T.Adj i u then 1 else 0 := by
  rw [deg_eq_degree]
  unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
  rw [sum_boole, Set.toFinset_ofPred]
  simp only [Nat.cast_id]

/-- Removing a vertex `v` lowers the degree of `j` by one exactly when `j ~ v`. -/
theorem deg_eq_comap_add (T : SimpleGraph V) (v : V) (j : {i // i ≠ v}) :
    deg T j.1 = deg (T.comap Subtype.val) j + if T.Adj j.1 v then 1 else 0 := by
  rw [deg_eq_sum, deg_eq_sum, Fintype.sum_eq_add_sum_subtype_ne _ v, add_comm]
  simp [SimpleGraph.comap_adj]

theorem deg_eq_one_iff (T : SimpleGraph V) (i : V) : deg T i = 1 ↔ ∃! w, T.Adj i w := by
  rw [deg_eq_degree]
  exact degree_eq_one_iff_existsUnique_adj

omit [Fintype V] in
theorem deg_congr {G H : SimpleGraph V} (h : G = H) (j : V) : deg G j = deg H j := by
  subst h
  rfl

theorem one_le_deg_of_isTree [Nontrivial V] {T : SimpleGraph V} (hT : T.IsTree) (i : V) :
    1 ≤ deg T i := by
  rw [deg_eq_degree]
  exact (hT.preconnected.minDegree_pos_of_nontrivial).trans_le (T.minDegree_le_degree i)

theorem sum_deg_of_isTree [Nonempty V] {T : SimpleGraph V} (hT : T.IsTree) :
    ∑ i, deg T i = 2 * (Fintype.card V - 1) := by
  simp only [deg_eq_degree]
  rw [T.sum_degrees_eq_twice_card_edges]
  have := hT.card_edgeFinset
  omega

end Degree

/-! ### Attaching a leaf -/

section AddLeaf

variable {V : Type u} [Fintype V] {v : V}

/-- The graph on `V` obtained from a graph `T'` on `V ∖ {v}` by adding the vertex `v`, joined by a
single edge to `p`. -/
def addLeaf (v : V) (p : {i // i ≠ v}) (T' : SimpleGraph {i // i ≠ v}) : SimpleGraph V :=
  T'.map (Function.Embedding.subtype _) ⊔ edge v p.1

variable {p : {i // i ≠ v}} {T' : SimpleGraph {i // i ≠ v}}

omit [Fintype V] in
theorem map_subtype_adj (a b : V) :
    (T'.map (Function.Embedding.subtype (fun i => i ≠ v))).Adj a b ↔
      ∃ (ha : a ≠ v) (hb : b ≠ v), T'.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
  rw [map_adj]
  constructor
  · rintro ⟨a', b', h, rfl, rfl⟩
    exact ⟨a'.2, b'.2, h⟩
  · rintro ⟨ha, hb, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h, rfl, rfl⟩

omit [Fintype V] in
theorem addLeaf_adj_of_ne (a b : {i // i ≠ v}) :
    (addLeaf v p T').Adj a.1 b.1 ↔ T'.Adj a b := by
  rw [addLeaf, sup_adj, map_subtype_adj, edge_adj]
  constructor
  · rintro (⟨_, _, h⟩ | ⟨(⟨h1, -⟩ | ⟨-, h1⟩), -⟩)
    · exact h
    · exact absurd h1 a.2
    · exact absurd h1 b.2
  · intro h
    exact Or.inl ⟨a.2, b.2, h⟩

omit [Fintype V] in
theorem addLeaf_adj_left (u : V) : (addLeaf v p T').Adj v u ↔ u = p.1 := by
  rw [addLeaf, sup_adj, map_subtype_adj, edge_adj]
  constructor
  · rintro (⟨h1, -⟩ | ⟨(⟨-, h1⟩ | ⟨h1, -⟩), -⟩)
    · exact absurd rfl h1
    · exact h1
    · exact absurd h1.symm p.2
  · rintro rfl
    exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, p.2.symm⟩

omit [Fintype V] in
theorem addLeaf_adj_right (u : V) : (addLeaf v p T').Adj u v ↔ u = p.1 := by
  rw [SimpleGraph.adj_comm, addLeaf_adj_left]

omit [Fintype V] in
theorem comap_addLeaf : (addLeaf v p T').comap Subtype.val = T' := by
  ext a b
  simp [SimpleGraph.comap_adj, addLeaf_adj_of_ne]

theorem addLeaf_comap {T : SimpleGraph V} (hv : deg T v = 1) (hp : T.Adj v p.1) :
    addLeaf v p (T.comap Subtype.val) = T := by
  obtain ⟨w, hw, hwu⟩ := (deg_eq_one_iff T v).mp hv
  have hpw : p.1 = w := hwu _ hp
  ext a b
  by_cases ha : a = v
  · subst ha
    rw [addLeaf_adj_left]
    constructor
    · rintro rfl; exact hp
    · intro h; rw [hpw]; exact hwu _ h
  by_cases hb : b = v
  · subst hb
    rw [addLeaf_adj_right]
    constructor
    · rintro rfl; exact hp.symm
    · intro h; rw [hpw]; exact hwu _ h.symm
  · have := addLeaf_adj_of_ne (v := v) (p := p) (T' := T.comap Subtype.val) ⟨a, ha⟩ ⟨b, hb⟩
    simp only [SimpleGraph.comap_adj] at this
    exact this


theorem isTree_addLeaf (hT' : T'.IsTree) : (addLeaf v p T').IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · have hp : ∀ u, (addLeaf v p T').Reachable u p.1 := by
      intro u
      by_cases hu : u = v
      · subst hu
        exact ((addLeaf_adj_left _).mpr rfl).reachable
      · have h1 := hT'.connected.preconnected ⟨u, hu⟩ p
        have h2 := h1.map (Embedding.map (Function.Embedding.subtype _) T').toHom
        exact h2.mono le_sup_left
    exact (connected_iff _).mpr ⟨fun a b => (hp a).trans (hp b).symm, ⟨v⟩⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
    have h1 := hT'.card_edgeFinset
    have hnadj : ¬ (T'.map (Function.Embedding.subtype _)).Adj v p.1 := by
      rw [map_subtype_adj]
      rintro ⟨h, -⟩
      exact h rfl
    have h2 := @card_edgeFinset_sup_edge V (T'.map (Function.Embedding.subtype _)) v p.1 _ _
      ((addLeaf v p T').fintypeEdgeSet) hnadj p.2.symm
    have h3 : #(addLeaf v p T').edgeFinset = #T'.edgeFinset + 1 := by
      rw [← card_edgeFinset_map (Function.Embedding.subtype (fun i => i ≠ v)) T']
      exact h2
    have h4 : Fintype.card {i // i ≠ v} + 1 = Fintype.card V := by
      have := Fintype.card_subtype_compl (fun i : V => i = v)
      simp only [Fintype.card_subtype_eq] at this
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
      simp only [ne_eq]
      omega
    omega

theorem isTree_comap {T : SimpleGraph V} (hT : T.IsTree) (hv : deg T v = 1) :
    (T.comap (Subtype.val : {i // i ≠ v} → V)).IsTree := by
  rw [deg_eq_degree] at hv
  exact ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
    hT.isAcyclic.comap ⟨Subtype.val, fun h => h⟩ Subtype.val_injective⟩

theorem deg_addLeaf_left : deg (addLeaf v p T') v = 1 := by
  rw [deg_eq_one_iff]
  exact ⟨p.1, (addLeaf_adj_left _).mpr rfl, fun w hw => (addLeaf_adj_left _).mp hw⟩

theorem deg_addLeaf (j : {i // i ≠ v}) :
    deg (addLeaf v p T') j.1 = deg T' j + if j = p then 1 else 0 := by
  rw [deg_eq_comap_add, deg_congr comap_addLeaf j]
  congr 1
  by_cases h : j = p
  · simp [h, addLeaf_adj_right]
  · have : ¬ j.1 = p.1 := fun h' => h (Subtype.ext h')
    simp [h, addLeaf_adj_right, this]

end AddLeaf

theorem card_subtype_ne_add_one {V : Type u} [Fintype V] (v : V) : Fintype.card {i // i ≠ v} + 1 = Fintype.card V := by
  have := Fintype.card_subtype_compl (fun i : V => i = v)
  simp only [Fintype.card_subtype_eq] at this
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  simp only [ne_eq]
  omega

end Cayley

end MultipoleBKT

end
