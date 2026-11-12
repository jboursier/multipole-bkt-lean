/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Relative

/-!
# Strict ear decompositions relative to a partition (Definition 4.39)

We formalize Definition 4.39. The vertices carry a block map `b : V → β` (for a subpartition `X`, `V = V_X`,
`β = X` and `b = [·]^X`, see `MultipoleBKT.blockOf`); the multigraph quotient of an edge set by
the blocks has the blocks as vertices and one edge `[i][j]` per edge `ij`.

An ear is written as the sequence of its oriented edges `(a₁, b₁), …, (a_m, b_m)` with
`[b_k] = [a_{k+1}]`: in the paper's notation `v₁v₂', v₂v₃', …, v_{n-1}v_n'` (Definition 4.43), with
`a_k = v_k` and `b_k = v_{k+1}'`. Its multigraph quotient is the walk of blocks
`[a₁], [b₁], …, [b_m]`. We store the first edge, the middle edges and the last edge separately
(`MultipoleBKT.Peeling.Ear`), so that `m ≥ 2` holds by construction.

* `MultipoleBKT.Peeling.IsEar b E U P`: `P` is an ear of `E` relative to the set `U` of blocks
  already covered: its edges are distinct edges of `E`, its interior blocks `[b₁], …, [b_{m-1}]`
  are distinct and outside `U`, and its end blocks `[a₁]`, `[b_m]` lie in `U`. Thus its
  multigraph quotient is a simple path with at least two edges joining two blocks of `U`, or a
  simple cycle meeting `U` at exactly one block (condition (2) of the definition).
* `MultipoleBKT.Peeling.IsStrictEarDecompOn b E S₁ Ps`: `Ps = (P₁, …, P_K)` is a strict ear
  decomposition of `E` whose base cycle `P₁` starts at the block `S₁`. The base cycle is an ear
  relative to `{S₁}`, so its quotient is a simple cycle through `S₁` (condition (1); cycles of two
  parallel edges are allowed); each later ear is an ear relative to the blocks covered before it;
  the ears are pairwise edge-disjoint, their union is `E`, and they cover every block.
* `MultipoleBKT.Peeling.IsStrictEarDecomp hX E S₁ Ps`: the same for a subpartition `X`.

The main facts:

* `MultipoleBKT.Peeling.IsStrictEarDecompOn.card_edges`: `|E| + 1 = |β| + K`, and
  `MultipoleBKT.Peeling.IsStrictEarDecompOn.card_edges_le`: `|E| ≤ 2(|β| - 1)` (the edge count
  in the proof of Corollary 4.47);
* `MultipoleBKT.Peeling.IsStrictEarDecompOn.connected_keptGraph`,
  `MultipoleBKT.Peeling.IsStrictEarDecompOn.card_keptGraph`: deleting one edge from each ear
  leaves a graph `T` with `(V, T ∪ same-block edges)` connected and `|T| + 1 = |β|`;
* `MultipoleBKT.Peeling.IsStrictEarDecomp.isRelTree_keptGraph`: for a subpartition, such a `T`
  is a tree relative to `X` (the claim `𝒯^X ∈ 𝖳^X` at the end of Definition 4.43).
-/

@[expose] public section

namespace MultipoleBKT

namespace Peeling

open Finset SimpleGraph

variable {V β : Type*}

/-- An ear, written as its oriented edges `(a₁, b₁), …, (a_m, b_m)` (`m ≥ 2`): the first edge,
the middle edges `(a₂, b₂), …, (a_{m-1}, b_{m-1})` and the last edge. -/
structure Ear (V : Type*) where
  /-- The first oriented edge `(a₁, b₁)`. -/
  first : V × V
  /-- The middle oriented edges. -/
  mid : List (V × V)
  /-- The last oriented edge `(a_m, b_m)`. -/
  last : V × V

/-- The unordered edge `s(p.1, p.2)` of an oriented edge `p`. -/
def edge (p : V × V) : Sym2 V := s(p.1, p.2)

theorem edge_apply (p : V × V) : edge p = s(p.1, p.2) := rfl

theorem edge_swap (p : V × V) : edge p.swap = edge p := Sym2.eq_swap

namespace Ear

/-- The oriented edges of the ear, in order. -/
def toList (P : Ear V) : List (V × V) := P.first :: (P.mid ++ [P.last])

/-- The (unordered) edges of the ear, in order. -/
def edges (P : Ear V) : List (Sym2 V) := P.toList.map edge

variable (b : V → β)

/-- The block `[a₁]` where the ear starts. -/
def startBlock (P : Ear V) : β := b P.first.1

/-- The block `[b_m]` where the ear ends. -/
def endBlock (P : Ear V) : β := b P.last.2

/-- The interior blocks `[b₁], …, [b_{m-1}]` of the ear. -/
def interior (P : Ear V) : List β := b P.first.2 :: P.mid.map fun p => b p.2

/-- The blocks of the ear: its two end blocks and its interior blocks. -/
def blocks [DecidableEq β] (P : Ear V) : Finset β :=
  insert (P.startBlock b) (insert (P.endBlock b) (P.interior b).toFinset)

variable {b}

theorem toList_ne_nil (P : Ear V) : P.toList ≠ [] := List.cons_ne_nil _ _

theorem length_toList (P : Ear V) : P.toList.length = P.mid.length + 2 := by
  simp [toList]

theorem length_edges (P : Ear V) : P.edges.length = P.mid.length + 2 := by
  simp [edges, length_toList]

theorem length_interior (P : Ear V) : (P.interior b).length = P.mid.length + 1 := by
  simp [interior]

theorem first_mem_toList (P : Ear V) : P.first ∈ P.toList := List.mem_cons_self

theorem last_mem_toList (P : Ear V) : P.last ∈ P.toList := by simp [toList]

theorem mem_edges {P : Ear V} {e : Sym2 V} : e ∈ P.edges ↔ ∃ p ∈ P.toList, edge p = e := by
  simp [edges]

/-- The interior blocks are the blocks of the heads of all edges but the last. -/
theorem interior_eq (P : Ear V) :
    P.interior b = (P.first :: P.mid).map fun p => b p.2 := by
  simp [interior]

end Ear

variable (b : V → β)

/-- The relation between consecutive oriented edges of an ear: the head of the first and the tail
of the second lie in the same block. -/
def ChainRel (p q : V × V) : Prop := b p.2 = b q.1

/-- `P` is an ear of `E` relative to the set `U` of blocks covered so far (Definition 4.39(2)):
its edges are distinct edges of `E` forming a walk of blocks, its interior blocks are distinct
and outside `U`, and its two end blocks lie in `U`. -/
structure IsEar (E : SimpleGraph V) (U : Finset β) (P : Ear V) : Prop where
  adj : ∀ p ∈ P.toList, E.Adj p.1 p.2
  nodup_edges : P.edges.Nodup
  isChain : P.toList.IsChain (ChainRel b)
  nodup_interior : (P.interior b).Nodup
  interior_notMem : ∀ B ∈ P.interior b, B ∉ U
  startBlock_mem : P.startBlock b ∈ U
  endBlock_mem : P.endBlock b ∈ U

variable [DecidableEq β]

/-- A sequence of ears, each relative to the blocks covered by the previous ones (starting from
the set `U`). -/
def IsEarSeq (E : SimpleGraph V) : Finset β → List (Ear V) → Prop
  | _, [] => True
  | U, P :: Ps => IsEar b E U P ∧ IsEarSeq E (U ∪ P.blocks b) Ps

/-- The blocks covered after the ears `Ps`, starting from the set `U`. -/
def covered : Finset β → List (Ear V) → Finset β
  | U, [] => U
  | U, P :: Ps => covered (U ∪ P.blocks b) Ps

/-- `Ps = (P₁, …, P_K)` is a strict ear decomposition of `(V, E)` whose base cycle `P₁` starts
at the block `S₁` (Definition 4.39): `P₁` is an ear relative to `{S₁}`, hence a simple cycle of the
multigraph quotient through `S₁`; every later ear is an ear relative to the blocks covered before
it; the ears are pairwise edge-disjoint, their union is `E` and they cover every block. -/
structure IsStrictEarDecompOn [Fintype β] (E : SimpleGraph V) (S₁ : β) (Ps : List (Ear V)) :
    Prop where
  ne_nil : Ps ≠ []
  isEarSeq : IsEarSeq b E {S₁} Ps
  nodup : (Ps.flatMap Ear.edges).Nodup
  mem_iff : ∀ e, e ∈ Ps.flatMap Ear.edges ↔ e ∈ E.edgeSet
  covered_eq : covered b {S₁} Ps = univ

/-- A strict ear decomposition relative to a subpartition `X` (Definition 4.39), whose base cycle starts at the block `S₁ ∈ X`. -/
def IsStrictEarDecomp {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (E : SimpleGraph (X.biUnion id)) (S₁ : X) (Ps : List (Ear (X.biUnion id))) : Prop :=
  IsStrictEarDecompOn (blockOf hX) E S₁ Ps

/-! ### Basic properties of ears -/

section EarFacts

variable {b} {E : SimpleGraph V} {U : Finset β} {P : Ear V}

omit [DecidableEq β] in
theorem IsEar.mem_edgeSet (h : IsEar b E U P) {e : Sym2 V} (he : e ∈ P.edges) :
    e ∈ E.edgeSet := by
  obtain ⟨p, hp, rfl⟩ := Ear.mem_edges.mp he
  exact h.adj p hp

/-- The blocks of an ear relative to `U` add exactly its interior blocks to `U`. -/
theorem IsEar.union_blocks (h : IsEar b E U P) :
    U ∪ P.blocks b = U ∪ (P.interior b).toFinset := by
  ext B
  simp only [Ear.blocks, mem_union, mem_insert, List.mem_toFinset]
  constructor
  · rintro (hB | rfl | rfl | hB)
    · exact Or.inl hB
    · exact Or.inl h.startBlock_mem
    · exact Or.inl h.endBlock_mem
    · exact Or.inr hB
  · rintro (hB | hB)
    · exact Or.inl hB
    · exact Or.inr (Or.inr (Or.inr hB))

theorem IsEar.card_union_blocks (h : IsEar b E U P) :
    (U ∪ P.blocks b).card = U.card + (P.mid.length + 1) := by
  rw [h.union_blocks, card_union_of_disjoint, List.toFinset_card_of_nodup h.nodup_interior,
    Ear.length_interior]
  rw [Finset.disjoint_left]
  intro B hBU hB
  exact h.interior_notMem B (List.mem_toFinset.mp hB) hBU

theorem IsEar.subset_union_blocks (U' : Finset β) : U' ⊆ U' ∪ P.blocks b := subset_union_left

end EarFacts

/-! ### Sequences of ears -/

section Seq

variable {b} {E : SimpleGraph V}

theorem subset_covered : ∀ (U : Finset β) (Ps : List (Ear V)), U ⊆ covered b U Ps
  | _, [] => le_rfl
  | U, P :: Ps => subset_union_left.trans (subset_covered (U ∪ P.blocks b) Ps)

theorem covered_nil (U : Finset β) : covered b U [] = U := rfl

theorem covered_cons (U : Finset β) (P : Ear V) (Ps : List (Ear V)) :
    covered b U (P :: Ps) = covered b (U ∪ P.blocks b) Ps := rfl

theorem covered_append : ∀ (U : Finset β) (Ps Qs : List (Ear V)),
    covered b U (Ps ++ Qs) = covered b (covered b U Ps) Qs
  | _, [], _ => rfl
  | U, P :: Ps, Qs => covered_append (U ∪ P.blocks b) Ps Qs

theorem isEarSeq_nil (U : Finset β) : IsEarSeq b E U [] := trivial

theorem isEarSeq_cons {U : Finset β} {P : Ear V} {Ps : List (Ear V)} :
    IsEarSeq b E U (P :: Ps) ↔ IsEar b E U P ∧ IsEarSeq b E (U ∪ P.blocks b) Ps := Iff.rfl

theorem isEarSeq_append : ∀ {U : Finset β} {Ps Qs : List (Ear V)},
    IsEarSeq b E U (Ps ++ Qs) ↔ IsEarSeq b E U Ps ∧ IsEarSeq b E (covered b U Ps) Qs
  | _, [], _ => by simp [isEarSeq_nil, covered_nil]
  | U, P :: Ps, Qs => by
    rw [List.cons_append, isEarSeq_cons, isEarSeq_cons, isEarSeq_append, covered_cons, and_assoc]

/-- The number of covered blocks grows by `m - 1` with each ear of `m` edges. -/
theorem IsEarSeq.card_covered : ∀ {U : Finset β} {Ps : List (Ear V)}, IsEarSeq b E U Ps →
    (covered b U Ps).card = U.card + (Ps.map fun P => P.mid.length + 1).sum
  | _, [], _ => by simp [covered_nil]
  | U, P :: Ps, ⟨hP, hPs⟩ => by
    rw [covered_cons, hPs.card_covered, hP.card_union_blocks, List.map_cons, List.sum_cons]
    ring

theorem length_flatMap_edges (Ps : List (Ear V)) :
    (Ps.flatMap Ear.edges).length = (Ps.map fun P => P.mid.length + 2).sum := by
  induction Ps with
  | nil => simp
  | cons P Ps ih => simp [List.flatMap_cons, ih, Ear.length_edges]

theorem IsEarSeq.mem_edgeSet : ∀ {U : Finset β} {Ps : List (Ear V)}, IsEarSeq b E U Ps →
    ∀ e ∈ Ps.flatMap Ear.edges, e ∈ E.edgeSet
  | _, [], _ => by simp
  | _, P :: Ps, ⟨hP, hPs⟩ => by
    intro e he
    rw [List.flatMap_cons, List.mem_append] at he
    rcases he with he | he
    · exact hP.mem_edgeSet he
    · exact hPs.mem_edgeSet e he

/-- Every interior block of an ear of the sequence is covered at the end. -/
theorem IsEarSeq.mem_covered_of_mem_interior : ∀ {U : Finset β} {Ps : List (Ear V)},
    IsEarSeq b E U Ps → ∀ P ∈ Ps, ∀ B ∈ P.interior b, B ∈ covered b U Ps
  | _, [], _ => by simp
  | U, Q :: Ps, ⟨_, hPs⟩ => by
    intro P hP B hB
    rw [covered_cons]
    rcases List.mem_cons.mp hP with rfl | hP
    · refine subset_covered _ _ (mem_union_right _ ?_)
      simp only [Ear.blocks, mem_insert, List.mem_toFinset]
      exact Or.inr (Or.inr hB)
    · exact hPs.mem_covered_of_mem_interior P hP B hB

end Seq

/-! ### Reachability along an ear -/

section Reach

variable {b} {G : SimpleGraph V}

omit [DecidableEq β] in
/-- Along a chain of edges of `G`, every endpoint is reachable from the first vertex in
`G ∪ (same-block edges)`. -/
theorem reachable_of_isChain : ∀ {p : V × V} {L : List (V × V)},
    (p :: L).IsChain (ChainRel b) → (∀ q ∈ p :: L, G.Adj q.1 q.2) →
    ∀ q ∈ p :: L, (G ⊔ sameBlockGraph b).Reachable p.1 q.1 ∧
      (G ⊔ sameBlockGraph b).Reachable p.1 q.2
  | p, [], _, hadj => by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨Reachable.refl _, (Adj.reachable (Or.inl (hadj q List.mem_cons_self)))⟩
  | p, r :: L, hch, hadj => by
    rw [List.isChain_cons_cons] at hch
    have hpr : (G ⊔ sameBlockGraph b).Reachable p.1 r.1 :=
      (Adj.reachable (Or.inl (hadj p List.mem_cons_self))).trans
        (reachable_sup_sameBlockGraph_of_eq hch.1)
    have ih := reachable_of_isChain hch.2 fun q hq => hadj q (List.mem_cons_of_mem _ hq)
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨Reachable.refl _, Adj.reachable (Or.inl (hadj q List.mem_cons_self))⟩
    · exact ⟨hpr.trans (ih q hq).1, hpr.trans (ih q hq).2⟩

omit [DecidableEq β] in
/-- Along a chain with one edge `e` possibly missing from `G`, every endpoint is reachable from
the first vertex or from the last vertex (`l` is the last edge). -/
theorem reachable_of_isChain_erase {e : Sym2 V} : ∀ {p l : V × V} {L : List (V × V)},
    (p :: (L ++ [l])).IsChain (ChainRel b) → ((p :: (L ++ [l])).map edge).Nodup →
    (∀ q ∈ p :: (L ++ [l]), edge q ≠ e → G.Adj q.1 q.2) →
    ∀ q ∈ p :: (L ++ [l]),
      ((G ⊔ sameBlockGraph b).Reachable p.1 q.1 ∨ (G ⊔ sameBlockGraph b).Reachable q.1 l.2) ∧
      ((G ⊔ sameBlockGraph b).Reachable p.1 q.2 ∨ (G ⊔ sameBlockGraph b).Reachable q.2 l.2)
  | p, l, [], hch, hnd, hadj => by
    rw [List.nil_append, List.isChain_cons_cons] at hch
    rw [List.nil_append, List.map_cons, List.map_singleton, List.nodup_cons,
      List.mem_singleton] at hnd
    intro q hq
    rw [List.nil_append] at hq
    by_cases hpe : edge p = e
    · -- the first edge is missing: everything after it reaches the last edge's head
      have hl : G.Adj l.1 l.2 := hadj l (by simp) fun h => hnd.1 (hpe.trans h.symm)
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨Or.inl (Reachable.refl _), Or.inr
          ((reachable_sup_sameBlockGraph_of_eq hch.1).trans (Adj.reachable (Or.inl hl)))⟩
      · rw [List.mem_singleton] at hq
        subst hq
        exact ⟨Or.inr (Adj.reachable (Or.inl hl)), Or.inr (Reachable.refl _)⟩
    · have hp : G.Adj p.1 p.2 := hadj p List.mem_cons_self hpe
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨Or.inl (Reachable.refl _), Or.inl (Adj.reachable (Or.inl hp))⟩
      · rw [List.mem_singleton] at hq
        subst hq
        have h1 : (G ⊔ sameBlockGraph b).Reachable p.1 q.1 :=
          (Adj.reachable (Or.inl hp)).trans (reachable_sup_sameBlockGraph_of_eq hch.1)
        exact ⟨Or.inl h1, Or.inr (Reachable.refl _)⟩
  | p, l, r :: L, hch, hnd, hadj => by
    rw [List.cons_append, List.isChain_cons_cons] at hch
    rw [List.cons_append, List.map_cons, List.nodup_cons] at hnd
    have hadj' : ∀ q ∈ r :: (L ++ [l]), edge q ≠ e → G.Adj q.1 q.2 :=
      fun q hq => hadj q (by rw [List.cons_append]; exact List.mem_cons_of_mem _ hq)
    intro q hq
    rw [List.cons_append] at hq
    by_cases hpe : edge p = e
    · -- the missing edge is the first one: the rest is a chain of edges of `G`
      have hall : ∀ q ∈ r :: (L ++ [l]), G.Adj q.1 q.2 := fun q hq =>
        hadj' q hq fun h => hnd.1 (hpe ▸ h ▸ List.mem_map_of_mem hq)
      have hreach := reachable_of_isChain hch.2 hall
      have hrl := (hreach l (by simp)).2
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨Or.inl (Reachable.refl _),
          Or.inr ((reachable_sup_sameBlockGraph_of_eq hch.1).trans hrl)⟩
      · exact ⟨Or.inr ((hreach q hq).1.symm.trans hrl),
          Or.inr ((hreach q hq).2.symm.trans hrl)⟩
    · have hp : G.Adj p.1 p.2 := hadj p List.mem_cons_self hpe
      have hpr : (G ⊔ sameBlockGraph b).Reachable p.1 r.1 :=
        (Adj.reachable (Or.inl hp)).trans (reachable_sup_sameBlockGraph_of_eq hch.1)
      have ih := reachable_of_isChain_erase (p := r) (l := l) (L := L) hch.2 hnd.2 hadj'
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨Or.inl (Reachable.refl _), Or.inl (Adj.reachable (Or.inl hp))⟩
      · have := ih q hq
        exact ⟨this.1.imp_left hpr.trans, this.2.imp_left hpr.trans⟩

end Reach

/-! ### Deleting one edge from each ear -/

section Removal

variable {b} {E : SimpleGraph V}

/-- The discarded edges of a list of ears, each paired with the oriented edge removed from it. -/
def removedEdges (Qs : List (Ear V × (V × V))) : List (Sym2 V) := Qs.map fun Q => edge Q.2

/-- The graph `𝓕` of the discarded edges. -/
def removedGraph (Qs : List (Ear V × (V × V))) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | e ∈ removedEdges Qs}

/-- The graph `𝓣 = E ∖ 𝓕` of the kept edges. -/
def keptGraph (E : SimpleGraph V) (Qs : List (Ear V × (V × V))) : SimpleGraph V :=
  E.deleteEdges {e | e ∈ removedEdges Qs}

/-- Each ear is paired with one of its own edges. -/
def IsRemoval (Qs : List (Ear V × (V × V))) : Prop := ∀ Q ∈ Qs, edge Q.2 ∈ Q.1.edges

theorem removedEdges_cons (Q : Ear V × (V × V)) (Qs : List (Ear V × (V × V))) :
    removedEdges (Q :: Qs) = edge Q.2 :: removedEdges Qs := rfl

theorem IsRemoval.mem_flatMap {Qs : List (Ear V × (V × V))} (h : IsRemoval Qs) {e : Sym2 V}
    (he : e ∈ removedEdges Qs) : e ∈ (Qs.map Prod.fst).flatMap Ear.edges := by
  obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp he
  exact List.mem_flatMap.mpr ⟨Q.1, List.mem_map_of_mem hQ, h Q hQ⟩

/-- Within an ear, the only discarded edge is its own removed edge. -/
theorem IsRemoval.mem_removedEdges_iff : ∀ {Qs : List (Ear V × (V × V))}, IsRemoval Qs →
    ((Qs.map Prod.fst).flatMap Ear.edges).Nodup →
    ∀ Q ∈ Qs, ∀ e ∈ Q.1.edges, (e ∈ removedEdges Qs ↔ e = edge Q.2)
  | [], _, _ => by simp
  | Q' :: Qs, hR, hnd => by
    rw [List.map_cons, List.flatMap_cons, List.nodup_append] at hnd
    have hR' : IsRemoval Qs := fun Q hQ => hR Q (List.mem_cons_of_mem _ hQ)
    intro Q hQ e he
    rw [removedEdges_cons, List.mem_cons]
    rcases List.mem_cons.mp hQ with rfl | hQ
    · refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
      exact hnd.2.2 e he e (hR'.mem_flatMap h') rfl
    · have heQ : e ∈ (Qs.map Prod.fst).flatMap Ear.edges :=
        List.mem_flatMap.mpr ⟨Q.1, List.mem_map_of_mem hQ, he⟩
      have hne : e ≠ edge Q'.2 := fun h => hnd.2.2 _ (hR Q' List.mem_cons_self) e heQ h.symm
      rw [or_iff_right hne]
      exact mem_removedEdges_iff hR' hnd.2.1 Q hQ e he

theorem IsRemoval.nodup_removedEdges : ∀ {Qs : List (Ear V × (V × V))}, IsRemoval Qs →
    ((Qs.map Prod.fst).flatMap Ear.edges).Nodup → (removedEdges Qs).Nodup
  | [], _, _ => List.nodup_nil
  | Q' :: Qs, hR, hnd => by
    rw [List.map_cons, List.flatMap_cons, List.nodup_append] at hnd
    have hR' : IsRemoval Qs := fun Q hQ => hR Q (List.mem_cons_of_mem _ hQ)
    rw [removedEdges_cons, List.nodup_cons]
    exact ⟨fun h => hnd.2.2 _ (hR Q' List.mem_cons_self) _ (hR'.mem_flatMap h) rfl,
      nodup_removedEdges hR' hnd.2.1⟩

theorem length_removedEdges (Qs : List (Ear V × (V × V))) :
    (removedEdges Qs).length = Qs.length := List.length_map _

/-- Every vertex of a covered block is reachable from `x₀` through the kept edges, if every
vertex of a block of `U` is. -/
theorem reachable_of_isEarSeq {T : SimpleGraph V} {x₀ : V} :
    ∀ {U : Finset β} {Qs : List (Ear V × (V × V))}, IsEarSeq b E U (Qs.map Prod.fst) →
    (∀ Q ∈ Qs, ∀ p ∈ Q.1.toList, edge p ≠ edge Q.2 → T.Adj p.1 p.2) →
    (∀ v, b v ∈ U → (T ⊔ sameBlockGraph b).Reachable x₀ v) →
    ∀ v, b v ∈ covered b U (Qs.map Prod.fst) → (T ⊔ sameBlockGraph b).Reachable x₀ v
  | _, [], _, _, hU => hU
  | U, Q :: Qs, ⟨hP, hPs⟩, hT, hU => by
    refine reachable_of_isEarSeq (U := U ∪ Q.1.blocks b) (Qs := Qs) hPs
      (fun Q' hQ' => hT Q' (List.mem_cons_of_mem _ hQ')) ?_
    intro v hv
    rw [hP.union_blocks, mem_union, List.mem_toFinset] at hv
    rcases hv with hv | hv
    · exact hU v hv
    rw [Ear.interior_eq, List.mem_map] at hv
    obtain ⟨q, hq, hqv⟩ := hv
    have hqmem : q ∈ Q.1.first :: (Q.1.mid ++ [Q.1.last]) := by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hq)
    have hreach := (reachable_of_isChain_erase (e := edge Q.2) hP.isChain hP.nodup_edges
      (hT Q List.mem_cons_self) q hqmem).2
    have hsame : (T ⊔ sameBlockGraph b).Reachable q.2 v :=
      reachable_sup_sameBlockGraph_of_eq hqv
    rcases hreach with h | h
    · exact (hU _ hP.startBlock_mem).trans (h.trans hsame)
    · exact (hU _ hP.endBlock_mem).trans (h.symm.trans hsame)

end Removal

/-! ### Counting edges and blocks of a strict ear decomposition -/

section Decomp

/-- The number of elements of a duplicate-free list, as a set. -/
theorem natCard_setOf_mem_of_nodup {α : Type*} [DecidableEq α] {L : List α} (h : L.Nodup) :
    Nat.card {x | x ∈ L} = L.length := by
  have : {x | x ∈ L} = ((L.toFinset : Finset α) : Set α) := by ext; simp
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup h]

omit [DecidableEq β] in
/-- A quotient by blocks has at most as many edges as the graph. -/
theorem natCard_blockQuotient_edgeSet_le [Finite V] {E : SimpleGraph V}
    (hE : E ≤ crossBlockGraph b) :
    Nat.card (blockQuotient b E).edgeSet ≤ Nat.card E.edgeSet := by
  let f : E.edgeSet → (blockQuotient b E).edgeSet := fun e => ⟨e.1.map b, by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | h i j =>
      rw [mem_edgeSet] at he
      simpa using blockQuotient_adj_of_adj he (crossBlockGraph_adj.mp (hE he))⟩
  refine Nat.card_le_card_of_surjective f ?_
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | h B B' =>
    rw [mem_edgeSet] at he
    obtain ⟨-, i, j, rfl, rfl, hij⟩ := blockQuotient_adj.mp he
    exact ⟨⟨s(i, j), hij⟩, by simp [f]⟩

variable {b} [Fintype β] {E : SimpleGraph V} {S₁ : β} {Ps : List (Ear V)}

theorem IsStrictEarDecompOn.card_eq (hD : IsStrictEarDecompOn b E S₁ Ps) :
    Fintype.card β = 1 + (Ps.map fun P => P.mid.length + 1).sum := by
  rw [← card_univ, ← hD.covered_eq, hD.isEarSeq.card_covered, card_singleton]

theorem IsStrictEarDecompOn.two_le_card (hD : IsStrictEarDecompOn b E S₁ Ps) :
    2 ≤ Fintype.card β := by
  rw [hD.card_eq]
  obtain ⟨P, Ps', rfl⟩ := List.exists_cons_of_ne_nil hD.ne_nil
  rw [List.map_cons, List.sum_cons]
  omega

theorem IsStrictEarDecompOn.edgeSet_eq (hD : IsStrictEarDecompOn b E S₁ Ps) :
    E.edgeSet = {e | e ∈ Ps.flatMap Ear.edges} := by
  ext e
  exact (hD.mem_iff e).symm

theorem IsStrictEarDecompOn.natCard_edgeSet [DecidableEq V]
    (hD : IsStrictEarDecompOn b E S₁ Ps) :
    Nat.card E.edgeSet = (Ps.map fun P => P.mid.length + 2).sum := by
  rw [hD.edgeSet_eq, natCard_setOf_mem_of_nodup hD.nodup, length_flatMap_edges]

/-- `|E| + 1 = |β| + K` for a strict ear decomposition into `K` ears. -/
theorem IsStrictEarDecompOn.natCard_edgeSet_add_one [DecidableEq V]
    (hD : IsStrictEarDecompOn b E S₁ Ps) :
    Nat.card E.edgeSet + 1 = Fintype.card β + Ps.length := by
  rw [hD.natCard_edgeSet, hD.card_eq]
  clear hD
  induction Ps with
  | nil => simp
  | cons P Ps ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- The edge count in the proof of Corollary 4.47: each ear has at least
two edges, so `|E| ≤ 2(|β| - 1)`. -/
theorem IsStrictEarDecompOn.natCard_edgeSet_le [DecidableEq V]
    (hD : IsStrictEarDecompOn b E S₁ Ps) :
    Nat.card E.edgeSet ≤ 2 * (Fintype.card β - 1) := by
  rw [hD.natCard_edgeSet, hD.card_eq, Nat.add_sub_cancel_left]
  clear hD
  induction Ps with
  | nil => simp
  | cons P Ps ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

variable [DecidableEq V] {Qs : List (Ear V × (V × V))}

omit [DecidableEq V] in
/-- The kept edges of each ear are edges of `𝓣 = E ∖ 𝓕`. -/
theorem IsStrictEarDecompOn.keptGraph_adj (hD : IsStrictEarDecompOn b E S₁ (Qs.map Prod.fst))
    (hR : IsRemoval Qs) :
    ∀ Q ∈ Qs, ∀ p ∈ Q.1.toList, edge p ≠ edge Q.2 → (keptGraph E Qs).Adj p.1 p.2 := by
  intro Q hQ p hp hne
  rw [keptGraph, deleteEdges_adj]
  have hpE : edge p ∈ Q.1.edges := List.mem_map_of_mem hp
  have hmem : edge p ∈ (Qs.map Prod.fst).flatMap Ear.edges :=
    List.mem_flatMap.mpr ⟨Q.1, List.mem_map_of_mem hQ, hpE⟩
  refine ⟨(hD.mem_iff _).mp hmem, ?_⟩
  change ¬ (edge p ∈ removedEdges Qs)
  rw [hR.mem_removedEdges_iff hD.nodup Q hQ _ hpE]
  exact hne

omit [DecidableEq V] in
/-- Deleting one edge from each ear leaves a graph connected relative to the blocks. -/
theorem IsStrictEarDecompOn.connected_keptGraph
    (hD : IsStrictEarDecompOn b E S₁ (Qs.map Prod.fst)) (hR : IsRemoval Qs) :
    (keptGraph E Qs ⊔ sameBlockGraph b).Connected := by
  have hne : Qs ≠ [] := fun h => hD.ne_nil (by rw [h, List.map_nil])
  obtain ⟨Q, Qs', hQs⟩ := List.exists_cons_of_ne_nil hne
  have hst : b Q.1.first.1 = S₁ := by
    have := hD.isEarSeq
    rw [hQs, List.map_cons] at this
    exact mem_singleton.mp this.1.startBlock_mem
  have hU : ∀ v, b v ∈ ({S₁} : Finset β) →
      (keptGraph E Qs ⊔ sameBlockGraph b).Reachable Q.1.first.1 v := fun v hv =>
    reachable_sup_sameBlockGraph_of_eq (hst.trans (mem_singleton.mp hv).symm)
  have hall := reachable_of_isEarSeq hD.isEarSeq (hD.keptGraph_adj hR) hU
  rw [hD.covered_eq] at hall
  have : Nonempty V := ⟨Q.1.first.1⟩
  exact ⟨fun u v => (hall u (mem_univ _)).symm.trans (hall v (mem_univ _))⟩

/-- Deleting one edge from each ear leaves `|β| - 1` edges. -/
theorem IsStrictEarDecompOn.natCard_keptGraph
    (hD : IsStrictEarDecompOn b E S₁ (Qs.map Prod.fst)) (hR : IsRemoval Qs) :
    Nat.card (keptGraph E Qs).edgeSet + 1 = Fintype.card β := by
  set L := (Qs.map Prod.fst).flatMap Ear.edges
  have hRnd := hR.nodup_removedEdges hD.nodup
  have hset : (keptGraph E Qs).edgeSet =
      ((L.toFinset \ (removedEdges Qs).toFinset : Finset (Sym2 V)) : Set (Sym2 V)) := by
    ext e
    simp only [keptGraph, edgeSet_deleteEdges, Set.mem_sdiff, ← hD.mem_iff, Set.mem_ofPred_eq,
      coe_sdiff, List.coe_toFinset]
    exact Iff.rfl
  have hsub : (removedEdges Qs).toFinset ⊆ L.toFinset := fun e he =>
    List.mem_toFinset.mpr (hR.mem_flatMap (List.mem_toFinset.mp he))
  have hcardE := hD.natCard_edgeSet_add_one
  rw [hD.edgeSet_eq, natCard_setOf_mem_of_nodup hD.nodup, List.length_map] at hcardE
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_sdiff_of_subset hsub,
    List.toFinset_card_of_nodup hD.nodup, List.toFinset_card_of_nodup hRnd,
    length_removedEdges]
  have hle : Qs.length ≤ L.length := by
    have := card_le_card hsub
    rwa [List.toFinset_card_of_nodup hD.nodup, List.toFinset_card_of_nodup hRnd,
      length_removedEdges] at this
  have hle' : Qs.length ≤ ((Qs.map Prod.fst).flatMap Ear.edges).length := hle
  omega

end Decomp

/-- Deleting one edge from each ear of a strict ear decomposition relative to a subpartition `X`
leaves a tree relative to `X` (Definition 4.43: `𝒯^X ∈ 𝖳^X`). -/
theorem IsStrictEarDecomp.isRelTree_keptGraph {X : Finset (Finset ℕ)} {hX : IsSubpartition X}
    {E : SimpleGraph (X.biUnion id)} {S₁ : X} {Qs : List (Ear (X.biUnion id) × _)}
    (hE : E ≤ interEdges X) (hD : IsStrictEarDecomp hX E S₁ (Qs.map Prod.fst))
    (hR : IsRemoval Qs) : IsRelTree X (keptGraph E Qs) := by
  have hT : keptGraph E Qs ≤ interEdges X := (deleteEdges_le _).trans hE
  have hconn := IsStrictEarDecompOn.connected_keptGraph hD hR
  rw [← intraEdges_eq hX, connected_sup_intraEdges_iff hX] at hconn
  have hcard := IsStrictEarDecompOn.natCard_keptGraph hD hR
  rw [Fintype.card_coe] at hcard
  have h2 := IsStrictEarDecompOn.two_le_card hD
  rw [Fintype.card_coe] at h2
  have hQle : Nat.card (quotientGraph X (keptGraph E Qs)).edgeSet ≤
      Nat.card (keptGraph E Qs).edgeSet := by
    rw [quotientGraph_eq hX]
    rw [interEdges_eq hX] at hT
    exact natCard_blockQuotient_edgeSet_le _ hT
  have hQge := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hQge
  have htree : (quotientGraph X (keptGraph E Qs)).IsTree := by
    rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card (α := X), Fintype.card_coe]
    exact ⟨hconn, by omega⟩
  have h₀ : IsRelTree₀ X (keptGraph E Qs) := (isRelTree₀_iff_card hX).mpr ⟨hT, htree, hcard⟩
  exact h₀.resolve_right fun h => by omega

end Peeling

end MultipoleBKT

end
