/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.RouteLift.Attachments

/-!
# Lifting heavy-light paths through extracted block trees

The paper: proof of Corollary 5.34,
Step 2, and Step 4.

`BlockTree` records the extracted tree on the parts, the bridge-tree on its blocks,
and the actual two endpoints of every parent bridge. A heavy chain crosses a block
only between its parent bridge and its heavy child bridge. Its other incoming paths
stop at their bridge attachment. This gives disjoint lifted paths and the bound
by the number of edges of the extracted tree.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic.RouteLift

open CoreForest

variable {Λ V : Type*} [Fintype Λ] [DecidableEq Λ]
  [Fintype V] [DecidableEq V] {τ : SimpleGraph Λ} [DecidableRel τ.Adj]
  {a : Λ} {T : SimpleGraph V}

/-- An extracted tree of blocks with the endpoints of its parent bridges. The
last field says each block is connected in the extracted tree. -/
structure BlockTree (τ : SimpleGraph Λ) (a : Λ) (T : SimpleGraph V) where
  block : V → Λ
  childEnd : Nonroot a → V
  parentEnd : Nonroot a → V
  child_block : ∀ v, block (childEnd v) = v
  parent_block : ∀ v, IsParent τ a (block (parentEnd v)) v
  bridge_adj : ∀ v, T.Adj (childEnd v) (parentEnd v)
  inside : ∀ x y, block x = block y →
    ∃ w : T.Walk x y, ∀ z ∈ w.support, block z = block x

namespace BlockTree

variable (D : BlockTree τ a T) (hτ : τ.IsTree) (hT : T.IsTree) {h : Λ → Λ}

/-- The starting part of a nonroot leaf block. -/
def start (l : Leaf τ a) : V := D.childEnd ⟨l, (mem_erase.1 l.property).1⟩

/-- The set `X*` of Step 2, as the actual parts at the leaf bridges. -/
noncomputable def xStar : Finset V := univ.image D.start

omit [Fintype V] [DecidableEq V] in
theorem block_start (l : Leaf τ a) : D.block (D.start l) = l := D.child_block _

omit [Fintype V] [DecidableEq V] in
theorem start_injective : Function.Injective D.start := by
  intro l l' heq
  apply Subtype.ext
  rw [← D.block_start l, ← D.block_start l', heq]

omit [Fintype V] in
/-- Every part in `X*` belongs to one unique leaf block. -/
theorem mem_xStar_iff (S : V) : S ∈ D.xStar ↔ ∃! l : Leaf τ a, D.start l = S := by
  rw [xStar, mem_image]
  constructor
  · rintro ⟨l, -, hl⟩
    exact ⟨l, hl, fun l' hl' => D.start_injective (hl'.trans hl.symm)⟩
  · rintro ⟨l, hl, -⟩
    exact ⟨l, mem_univ _, hl⟩

/-- The attachment map `loc` on the actual set `X*`. The leaf indexing a part is
unique by `start_injective`. -/
noncomputable def locPart (S : D.xStar) : V :=
  loc (h := h) hτ D.parentEnd ((D.mem_xStar_iff S).1 S.property).choose

omit [Fintype V] in
theorem locPart_start (l : Leaf τ a) :
    D.locPart (h := h) hτ ⟨D.start l, mem_image.2 ⟨l, mem_univ _, rfl⟩⟩ =
      loc (h := h) hτ D.parentEnd l := by
  unfold locPart
  congr 1
  exact D.start_injective (((D.mem_xStar_iff (D.start l)).1
    (mem_image.2 ⟨l, mem_univ _, rfl⟩)).choose_spec.1)

include hT

omit [Fintype Λ] [DecidableEq Λ] [DecidableRel τ.Adj] in
/-- The unique tree path between two parts of a block stays in that block. -/
theorem path_sameBlock {x y s t : V} (hxy : D.block x = D.block y)
    (he : s(s, t) ∈ pathEdges T x y) :
    D.block s = D.block x ∧ D.block t = D.block x := by
  obtain ⟨w, hw⟩ := D.inside x y hxy
  have hp := w.bypass_isPath
  have he' := (mem_pathEdges_iff_of_isPath hT hp).1 he
  exact ⟨hw _ (w.support_bypass_subset_support (w.bypass.fst_mem_support_of_mem_edges he')),
    hw _ (w.support_bypass_subset_support (w.bypass.snd_mem_support_of_mem_edges he'))⟩

/-- The internal crossing in a nonroot block, from its heavy child bridge to
its parent bridge. There is no internal crossing in a childless block. -/
noncomputable def internalEdges (v : Nonroot a) : Finset (Sym2 V) :=
  ((univ : Finset (Nonroot a)).filter fun c => IsParent τ a v.val c.val ∧ h v.val = c.val).biUnion
    fun c => pathEdges T (D.parentEnd c) (D.childEnd v)

/-- One bridge and the possible internal crossing below it. -/
noncomputable def segment (v : Nonroot a) : Finset (Sym2 V) :=
  {s(D.childEnd v, D.parentEnd v)} ∪ D.internalEdges (h := h) v

/-- The edges available to the lift of the heavy chain ending at `l`. -/
noncomputable def chainEdges (l : Leaf τ a) : Finset (Sym2 V) :=
  ((univ : Finset (Nonroot a)).filter fun v => IsHeavyChain τ a h v.val l.val).biUnion
    (D.segment (h := h))

/-- The lifted path in the extracted tree, ending exactly at the last bridge
attachment, rather than at a chosen representative of the terminal block. -/
noncomputable def liftedPath (l : Leaf τ a) : Finset (Sym2 V) :=
  pathEdges T (D.start l) (loc (h := h) hτ D.parentEnd l)

include hτ

omit [DecidableRel τ.Adj] in
theorem internal_sameBlock {v : Nonroot a} {s t : V}
    (he : s(s, t) ∈ D.internalEdges (h := h) v) : D.block s = v ∧ D.block t = v := by
  obtain ⟨c, hc, he⟩ := mem_biUnion.1 he
  have hp := (mem_filter.1 hc).2.1
  have hbc : D.block (D.parentEnd c) = v := (D.parent_block c).unique hτ hp
  have hxy : D.block (D.parentEnd c) = D.block (D.childEnd v) := hbc.trans (D.child_block v).symm
  obtain ⟨hs, ht⟩ := D.path_sameBlock hT hxy he
  exact ⟨hs.trans hbc, ht.trans hbc⟩

omit [DecidableRel τ.Adj] in
/-- A segment belongs to a unique nonroot block. Its bridge is recognized by
its two different block labels, and its internal crossing by its single label. -/
theorem segment_owner {v w : Nonroot a} {e : Sym2 V}
    (hv : e ∈ D.segment (h := h) v) (hw : e ∈ D.segment (h := h) w) : v = w := by
  rcases mem_union.1 hv with hv | hv <;> rcases mem_union.1 hw with hw | hw
  · have he : s(D.childEnd v, D.parentEnd v) = s(D.childEnd w, D.parentEnd w) :=
      (mem_singleton.1 hv).symm.trans (mem_singleton.1 hw)
    apply Subtype.ext
    rcases Sym2.eq_iff.1 he with ⟨hc, -⟩ | ⟨hc, hp⟩
    · rw [← D.child_block v, ← D.child_block w, hc]
    · have hvp := D.parent_block v
      have hwp := D.parent_block w
      rw [hp, D.child_block w] at hvp
      rw [← hc, D.child_block v] at hwp
      have := hvp.dist_lt
      have := hwp.dist_lt
      omega
  · rw [mem_singleton.1 hv] at hw
    obtain ⟨hc, hp⟩ := D.internal_sameBlock hτ hT hw
    have hparent := D.parent_block v
    rw [hp, ← D.child_block v, hc] at hparent
    exact (hparent.ne rfl).elim
  · rw [mem_singleton.1 hw] at hv
    obtain ⟨hc, hp⟩ := D.internal_sameBlock hτ hT hv
    have hparent := D.parent_block w
    rw [hp, ← D.child_block w, hc] at hparent
    exact (hparent.ne rfl).elim
  · induction e using Sym2.ind with
    | h s t =>
      exact Subtype.ext ((D.internal_sameBlock hτ hT hv).1.symm.trans
        (D.internal_sameBlock hτ hT hw).1)

/-- The edge containers of distinct lifted chains are disjoint. Only the heavy
chain assigned to a block uses its internal crossing. -/
theorem chainEdges_disjoint {l l' : Leaf τ a} (hne : l ≠ l') :
    Disjoint (D.chainEdges (h := h) l) (D.chainEdges (h := h) l') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨v, hv, he⟩ := mem_biUnion.1 he
  obtain ⟨w, hw, he'⟩ := mem_biUnion.1 he'
  have hvw := D.segment_owner hτ hT he he'
  subst hvw
  have hvl := (mem_filter.1 hv).2
  have hvl' := (mem_filter.1 hw).2
  apply hne
  apply Subtype.ext
  exact hvl.eq_of_leaf hvl'
    ((mem_leaves_iff_of_ne hτ (mem_erase.1 l.property).1).1 (mem_erase.1 l.property).2)
    ((mem_leaves_iff_of_ne hτ (mem_erase.1 l'.property).1).1 (mem_erase.1 l'.property).2)

omit hτ in
/-- A heavy chain can be lifted from the starting part to the parent endpoint
of its top bridge, using just the segments assigned to this chain. -/
theorem exists_chain_walk {l : Leaf τ a} {v : Nonroot a}
    (hc : IsHeavyChain τ a h v l) :
    ∃ w : T.Walk (D.start l) (D.parentEnd v),
      ∀ e ∈ w.edges, e ∈ D.chainEdges (h := h) l := by
  have key : ∀ {v' : Λ}, (hv' : v' ≠ a) → IsHeavyChain τ a h v' l →
      ∃ w : T.Walk (D.start l) (D.parentEnd ⟨v', hv'⟩),
        ∀ e ∈ w.edges, e ∈ D.chainEdges (h := h) l := by
    intro v' hv' hchain
    induction hchain using Relation.ReflTransGen.head_induction_on with
    | refl =>
      refine ⟨(D.bridge_adj ⟨l, hv'⟩).toWalk, ?_⟩
      intro e he
      have heq : e = s(D.childEnd ⟨l, hv'⟩, D.parentEnd ⟨l, hv'⟩) := by
        change e ∈ (D.bridge_adj ⟨l, hv'⟩).toWalk.edges at he
        simpa only [Adj.edges_toWalk, List.mem_singleton] using he
      apply mem_biUnion.2
      refine ⟨⟨l, hv'⟩, mem_filter.2 ⟨mem_univ _, Relation.ReflTransGen.refl⟩, ?_⟩
      exact mem_union_left _ (mem_singleton.2 heq)
    | @head u c huc hcl ih =>
      have hcne : c ≠ a := fun he => not_isParent_root _ (he ▸ huc.1)
      obtain ⟨w, hw⟩ := ih hcne
      obtain ⟨q, hq, -⟩ := hT.connected.exists_path_of_dist
        (D.parentEnd ⟨c, hcne⟩) (D.childEnd ⟨u, hv'⟩)
      let z := (D.bridge_adj ⟨u, hv'⟩).toWalk
      refine ⟨w.append (q.append z), ?_⟩
      intro e he
      rw [Walk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact hw e he
      · apply mem_biUnion.2
        refine ⟨⟨u, hv'⟩, mem_filter.2 ⟨mem_univ _,
          Relation.ReflTransGen.head huc hcl⟩, ?_⟩
        rw [Walk.edges_append, List.mem_append] at he
        rcases he with he | he
        · apply mem_union_right
          apply mem_biUnion.2
          exact ⟨⟨c, hcne⟩, mem_filter.2 ⟨mem_univ _, huc⟩,
            (mem_pathEdges_iff_of_isPath hT hq).2 he⟩
        · apply mem_union_left
          apply mem_singleton.2
          simpa only [z, Adj.edges_toWalk, List.mem_singleton] using he
  exact key v.property hc

/-- The unique lifted path uses only its assigned bridge and internal segments. -/
theorem liftedPath_subset_chainEdges (l : Leaf τ a) :
    D.liftedPath (h := h) hτ l ⊆ D.chainEdges (h := h) l := by
  obtain ⟨w, hw⟩ := D.exists_chain_walk hT (terminalChild_spec (h := h) hτ l).2.1
  intro e he
  have he' := (mem_pathEdges_iff_of_isPath hT w.bypass_isPath).1 he
  exact hw e (w.edges_bypass_subset_edges he')

/-- The lifted paths are edge-disjoint, as claimed immediately before (5.94).
This is stronger than disjointness of their projections to the bridge-tree. -/
theorem liftedPath_pairwiseDisjoint :
    (Set.univ : Set (Leaf τ a)).PairwiseDisjoint (D.liftedPath (h := h) hτ) := by
  intro l _ l' _ hne
  exact Finset.disjoint_of_subset_left (D.liftedPath_subset_chainEdges hτ hT l)
    (Finset.disjoint_of_subset_right (D.liftedPath_subset_chainEdges hτ hT l')
      (D.chainEdges_disjoint hτ hT hne))

/-- The total length of the lifts is at most `|X| - 1`, the number of edges
of the extracted tree on the parts, in Step 4 before (5.94). -/
theorem total_lifted_length_le :
    ∑ l : Leaf τ a, T.dist (D.start l) (loc (h := h) hτ D.parentEnd l) ≤
      Fintype.card V - 1 := by
  classical
  have hd := D.liftedPath_pairwiseDisjoint (h := h) hτ hT
  calc ∑ l : Leaf τ a, T.dist (D.start l) (loc (h := h) hτ D.parentEnd l)
      = ∑ l : Leaf τ a, (D.liftedPath (h := h) hτ l).card :=
        sum_congr rfl fun l _ => (card_pathEdges hT _ _).symm
    _ = (univ.biUnion (D.liftedPath (h := h) hτ)).card := (card_biUnion (fun l _ l' _ hne => hd (Set.mem_univ _) (Set.mem_univ _) hne)).symm
    _ ≤ T.edgeFinset.card := card_le_card (by
      intro e he
      obtain ⟨l, -, he⟩ := mem_biUnion.1 he
      exact pathEdges_subset_edgeFinset _ _ he)
    _ = Fintype.card V - 1 := by have := hT.card_edgeFinset; omega

/-- The length bound in the paper's literal indexing by `S' ∈ X*`.
The canonical leaf-to-part bijection changes no length. -/
theorem total_xStar_length_le :
    ∑ S' : D.xStar, T.dist S' (D.locPart (h := h) hτ S') ≤ Fintype.card V - 1 := by
  have heq : (∑ l : Leaf τ a, T.dist (D.start l) (loc (h := h) hτ D.parentEnd l)) =
      ∑ S' : D.xStar, T.dist S' (D.locPart (h := h) hτ S') := by
    refine Finset.sum_bij
      (fun l _ => (⟨D.start l, mem_image.2 ⟨l, mem_univ _, rfl⟩⟩ : D.xStar))
      (fun _ _ => mem_univ _) ?_ ?_ ?_
    · intro l _ l' _ hl
      exact D.start_injective (congrArg Subtype.val hl)
    · intro S' _
      obtain ⟨l, hl, -⟩ := (D.mem_xStar_iff S').1 S'.property
      exact ⟨l, mem_univ _, Subtype.ext hl⟩
    · intro l _
      rw [D.locPart_start]
  rw [← heq]
  exact D.total_lifted_length_le hτ hT

end BlockTree

end MultipoleBKT.UpperBound.Quadratic.RouteLift

end
