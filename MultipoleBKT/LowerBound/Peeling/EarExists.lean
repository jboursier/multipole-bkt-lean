/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.Ear
public import MultipoleBKT.LowerBound.Peeling.TwoEdge

/-!
# Existence of strict ear decompositions (Lemma 4.40)

We prove Lemma 4.40:
a graph that is minimally 2-edge-connected relative to `X` admits a strict ear decomposition, and
the first cycle may be prescribed.

The proof follows the paper. Starting from the prescribed cycle, while some block is not
covered, a component outside the covered blocks has two edges to them (no bridge); joining them
by a simple path in that component gives an ear with new interior blocks
(`MultipoleBKT.Peeling.exists_isEar_of_boundary`). The ears produced cover all blocks and their
union is 2-edge-connected relative to the blocks (`MultipoleBKT.Peeling.EarInv`), so by
minimality it is the whole graph (`MultipoleBKT.Peeling.EarInv.isStrictEarDecompOn`).

The main results:

* `MultipoleBKT.Peeling.exists_isStrictEarDecompOn_cons`: generic form, for a block map `b`;
* `MultipoleBKT.Peeling.exists_isStrictEarDecomp_cons`: Lemma 4.40 with a prescribed first cycle;
* `MultipoleBKT.Peeling.exists_isStrictEarDecomp_first`: the base cycle may be chosen to start
  with any prescribed oriented edge (used in Step 2 of the proof of Lemma A.7);
* `MultipoleBKT.Peeling.exists_isStrictEarDecomp`: the base cycle may be chosen to start at any
  prescribed block (used in Definition 4.43, which starts at the block of maximal radius).
-/

@[expose] public section

namespace MultipoleBKT

namespace Peeling

open Finset SimpleGraph

variable {V β : Type*} {b : V → β}

/-! ### Lifting walks of the quotient -/

/-- A walk of blocks in the quotient of `G` lifts to a chain of oriented edges of `G`. -/
theorem exists_lift_walk {G : SimpleGraph V} {B B' : β} (p : (blockQuotient b G).Walk B B') :
    ∃ L : List (V × V), (∀ q ∈ L, G.Adj q.1 q.2) ∧
      L.map (fun q => (edge q).map b) = p.edges ∧
      L.map (fun q => b q.2) = p.support.tail ∧
      ∀ x y, b y = B → ((x, y) :: L).IsChain (ChainRel b) ∧
        ∀ z w, b z = B' → ((x, y) :: (L ++ [(z, w)])).IsChain (ChainRel b) := by
  induction p with
  | nil =>
    refine ⟨[], by simp, by simp, by simp, fun x y hy => ⟨List.IsChain.singleton _, ?_⟩⟩
    intro z w hz
    simp [ChainRel, hy, hz]
  | @cons B C B' h p ih =>
    obtain ⟨-, i, j, hi, hj, hij⟩ := blockQuotient_adj.mp h
    obtain ⟨L, hadj, hedges, hsupp, hchain⟩ := ih
    refine ⟨(i, j) :: L, ?_, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      exacts [hij, hadj q hq]
    · rw [List.map_cons, hedges, Walk.edges_cons, edge_apply, Sym2.map_mk, hi, hj]
    · rw [List.map_cons, hsupp, Walk.support_cons, List.tail_cons, hj, Walk.cons_tail_support]
    · intro x y hy
      have hc := hchain i j hj
      refine ⟨List.isChain_cons_cons.mpr ⟨hy.trans hi.symm, hc.1⟩, fun z w hz => ?_⟩
      rw [List.cons_append]
      exact List.isChain_cons_cons.mpr ⟨hy.trans hi.symm, hc.2 z w hz⟩

/-! ### Facts about the vertices of an ear -/

/-- Along a chain, the heads of all edges but the last are in the blocks of the tails of all
edges but the first. -/
theorem map_dropLast_snd_of_isChain : ∀ {p : V × V} {L : List (V × V)},
    (p :: L).IsChain (ChainRel b) →
      (p :: L).dropLast.map (fun q => b q.2) = L.map fun q => b q.1
  | _, [], _ => rfl
  | p, q :: L, h => by
    rw [List.isChain_cons_cons] at h
    rw [List.dropLast_cons_cons, List.map_cons, map_dropLast_snd_of_isChain h.2, List.map_cons]
    exact congrArg (· :: _) h.1

/-- The interior blocks are also the blocks of the tails of all edges but the first. -/
theorem Ear.interior_eq_fst {P : Ear V} (h : P.toList.IsChain (ChainRel b)) :
    P.interior b = (P.mid ++ [P.last]).map fun q => b q.1 := by
  rw [Ear.interior_eq, ← map_dropLast_snd_of_isChain h, ← List.cons_append,
    List.dropLast_concat]

variable [DecidableEq β] {E : SimpleGraph V}

omit [DecidableEq β] in
/-- Each edge of an ear meets an interior block. -/
theorem IsEar.exists_interior {U : Finset β} {P : Ear V} (h : IsEar b E U P) :
    ∀ p ∈ P.toList, b p.1 ∈ P.interior b ∨ b p.2 ∈ P.interior b := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact Or.inr List.mem_cons_self
  · rw [h.isChain |> Ear.interior_eq_fst]
    exact Or.inl (List.mem_map_of_mem hp)

/-- The endpoints of the edges of an ear lie in its blocks. -/
theorem IsEar.mem_blocks {U : Finset β} {P : Ear V} (h : IsEar b E U P) :
    ∀ p ∈ P.toList, b p.1 ∈ P.blocks b ∧ b p.2 ∈ P.blocks b := by
  have hint : ∀ B ∈ P.interior b, B ∈ P.blocks b := fun B hB => by
    simp only [Ear.blocks, mem_insert, List.mem_toFinset]
    exact Or.inr (Or.inr hB)
  intro p hp
  constructor
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact mem_insert_self _ _
    · rw [h.isChain |> Ear.interior_eq_fst] at hint
      exact hint _ (List.mem_map_of_mem hp)
  · rcases List.mem_append.mp (show p ∈ (P.first :: P.mid) ++ [P.last] from hp) with hp | hp
    · rw [Ear.interior_eq] at hint
      exact hint _ (List.mem_map_of_mem hp)
    · rw [List.mem_singleton] at hp
      subst hp
      simp [Ear.blocks, Ear.endBlock]

/-! ### Constructing one ear -/

/-- The edges of `E` with both endpoints in blocks outside `U`. -/
def outsideGraph (E : SimpleGraph V) (U : Finset β) : SimpleGraph V :=
  E.deleteEdges {e | ∃ v ∈ e, b v ∈ U}

omit [DecidableEq β] in
theorem outsideGraph_adj {U : Finset β} {u v : V} :
    (outsideGraph (b := b) E U).Adj u v ↔ E.Adj u v ∧ b u ∉ U ∧ b v ∉ U := by
  simp only [outsideGraph, deleteEdges_adj, Set.mem_ofPred_eq, Sym2.mem_iff, not_exists, not_and]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h, fun hu => hn u (Or.inl rfl) hu, fun hv => hn v (Or.inr rfl) hv⟩
  · rintro ⟨h, hu, hv⟩
    refine ⟨h, fun w hw => ?_⟩
    rcases hw with rfl | rfl
    exacts [hu, hv]

omit [DecidableEq β] in
/-- A walk in the quotient of the outside graph starting outside `U` stays outside `U`. -/
theorem notMem_of_mem_support {U : Finset β} {B B' : β}
    (p : (blockQuotient b (outsideGraph (b := b) E U)).Walk B B') (hB : B ∉ U) :
    ∀ C ∈ p.support, C ∉ U := by
  induction p with
  | nil =>
    intro C hC
    rw [Walk.support_nil, List.mem_singleton] at hC
    exact hC ▸ hB
  | @cons B C' B' h p ih =>
    obtain ⟨-, i, j, hi, hj, hij⟩ := blockQuotient_adj.mp h
    have hC' : C' ∉ U := hj ▸ (outsideGraph_adj.mp hij).2.2
    intro C hC
    rw [Walk.support_cons, List.mem_cons] at hC
    rcases hC with rfl | hC
    exacts [hB, ih hC' C hC]

/-- An edge leaving the covered blocks `U` starts an ear relative to `U`, if `E` is
2-edge-connected relative to the blocks. This is the construction in the proof of Lemma 4.40
(proof of Lemma 4.40): the component outside `U` has a second edge to `U`, and the two edges are
joined by a simple path of blocks outside `U`. -/
theorem exists_isEar_of_boundary (h2 : TwoEdgeConnOn b E) {U : Finset β} {x y : V}
    (hxy : E.Adj x y) (hx : b x ∈ U) (hy : b y ∉ U) :
    ∃ P : Ear V, P.first = (x, y) ∧ IsEar b E U P := by
  classical
  set Eout := outsideGraph (b := b) E U
  -- a walk from `y` back to `x` avoiding the edge `xy`
  obtain ⟨w⟩ := (h2.2 s(x, y) hxy).preconnected y x
  set Comp : Set V := {v | b v ∉ U ∧ (Eout ⊔ sameBlockGraph b).Reachable y v}
  obtain ⟨d, -, hd1, hd2⟩ := w.exists_boundary_dart Comp ⟨hy, Reachable.refl _⟩
    (fun h => h.1 hx)
  set z := d.fst
  set w' := d.snd
  have hdadj : (E.deleteEdges {s(x, y)} ⊔ sameBlockGraph b).Adj z w' := d.adj
  -- the second edge `zw'` enters `U`
  have hw'U : b w' ∈ U := by
    by_contra hw'
    refine hd2 ⟨hw', hd1.2.trans (Adj.reachable ?_)⟩
    rcases hdadj with h | h
    · rw [deleteEdges_adj] at h
      exact Or.inl (outsideGraph_adj.mpr ⟨h.1, hd1.1, hw'⟩)
    · exact Or.inr h
  have hzw : E.Adj z w' ∧ s(z, w') ≠ s(x, y) := by
    rcases hdadj with h | h
    · rw [deleteEdges_adj] at h
      exact ⟨h.1, fun heq => h.2 (Set.mem_singleton_iff.mpr heq)⟩
    · exact absurd ((sameBlockGraph_adj.mp h).2 ▸ hw'U) hd1.1
  -- a simple path of blocks outside `U` from `[y]` to `[z]`
  obtain ⟨p, hp⟩ := (reachable_blockQuotient_of_reachable hd1.2).exists_isPath
  obtain ⟨L, hadj, hedges, hsupp, hchain⟩ := exists_lift_walk p
  have hout := notMem_of_mem_support p hy
  have hLout : ∀ q ∈ L, b q.1 ∉ U ∧ b q.2 ∉ U := fun q hq =>
    (outsideGraph_adj.mp (hadj q hq)).2
  refine ⟨⟨(x, y), L, (z, w')⟩, rfl, ?_⟩
  have hint : (⟨(x, y), L, (z, w')⟩ : Ear V).interior b = p.support := by
    rw [Ear.interior, hsupp, Walk.cons_tail_support]
  refine ⟨?_, ?_, (hchain x y rfl).2 z w' rfl, ?_, ?_, hx, hw'U⟩
  · intro q hq
    simp only [Ear.toList, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | hq | rfl
    · exact hxy
    · exact (outsideGraph_adj.mp (hadj q hq)).1
    · exact hzw.1
  · -- the edges are distinct
    have hLnd : (L.map edge).Nodup := by
      refine List.Nodup.of_map (Sym2.map b) ?_
      rw [List.map_map]
      exact hedges ▸ hp.edges_nodup
    have hnotL : ∀ v, b v ∈ U → ∀ e ∈ L.map edge, v ∉ e := by
      intro v hv e he hve
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      exacts [(hLout q hq).1 hv, (hLout q hq).2 hv]
    simp only [Ear.edges, Ear.toList, List.map_cons, List.map_append, List.map_nil]
    rw [List.nodup_cons, List.nodup_append]
    refine ⟨fun h => ?_, hLnd, List.nodup_singleton _, ?_⟩
    · rcases List.mem_append.mp h with h | h
      · exact hnotL x hx _ h (Sym2.mem_mk_left _ _)
      · exact hzw.2 (List.mem_singleton.mp h).symm
    · intro e he e' he' heq
      rw [List.mem_singleton] at he'
      subst he' heq
      exact hnotL w' hw'U _ he (Sym2.mem_mk_right _ _)
  · rw [hint]
    exact hp.support_nodup
  · rw [hint]
    exact hout

/-- If `E ∪ (same-block edges)` is connected, some edge of `E` leaves any nonempty proper set of
blocks. -/
theorem exists_boundary_edge [Fintype β] (hb : Function.Surjective b)
    (hconn : (E ⊔ sameBlockGraph b).Connected) {U : Finset β} (hU : U.Nonempty)
    (hne : U ≠ univ) : ∃ x y, E.Adj x y ∧ b x ∈ U ∧ b y ∉ U := by
  obtain ⟨B, hB⟩ : ∃ B, B ∉ U := by
    by_contra h
    push Not at h
    exact hne (eq_univ_iff_forall.mpr h)
  obtain ⟨S, hS⟩ := hU
  obtain ⟨u, rfl⟩ := hb S
  obtain ⟨z, rfl⟩ := hb B
  obtain ⟨w⟩ := hconn.preconnected u z
  obtain ⟨d, -, hd1, hd2⟩ := w.exists_boundary_dart {v | b v ∈ U} hS hB
  rcases d.adj with h | h
  · exact ⟨_, _, h, hd1, hd2⟩
  · exact absurd (show b d.snd ∈ U by rw [← (sameBlockGraph_adj.mp h).2]; exact hd1) hd2

/-! ### The invariant of the construction -/

variable [DecidableEq V]

/-- The graph whose edges are the elements of `L`. -/
def graphOf (L : List (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∈ L}

omit [DecidableEq V] in
theorem graphOf_adj {L : List (Sym2 V)} {u v : V} :
    (graphOf L).Adj u v ↔ s(u, v) ∈ L ∧ u ≠ v := by
  rw [graphOf, fromEdgeSet_adj, Set.mem_ofPred_eq]

omit [DecidableEq V] in
theorem graphOf_mono {L L' : List (Sym2 V)} (h : ∀ e ∈ L, e ∈ L') : graphOf L ≤ graphOf L' :=
  fromEdgeSet_mono fun e he => h e he

variable (E) in
/-- The invariant of the ear-by-ear construction: the ears built so far form an ear sequence
with distinct edges inside the covered blocks, and their union is 2-edge-connected relative to
the covered blocks. -/
structure EarInv (S₁ : β) (Ps : List (Ear V)) : Prop where
  isEarSeq : IsEarSeq b E {S₁} Ps
  nodup : (Ps.flatMap Ear.edges).Nodup
  covered_of_mem : ∀ e ∈ Ps.flatMap Ear.edges, ∀ v ∈ e, b v ∈ covered b {S₁} Ps
  reach : ∀ u v, b u ∈ covered b {S₁} Ps → b v ∈ covered b {S₁} Ps →
    (graphOf (Ps.flatMap Ear.edges) ⊔ sameBlockGraph b).Reachable u v
  noBridge : ∀ x y, s(x, y) ∈ Ps.flatMap Ear.edges →
    ((graphOf (Ps.flatMap Ear.edges)).deleteEdges {s(x, y)} ⊔ sameBlockGraph b).Reachable x y

omit [DecidableEq V] in
theorem earInv_nil (S₁ : β) : EarInv (b := b) E S₁ [] where
  isEarSeq := trivial
  nodup := List.nodup_nil
  covered_of_mem := by simp
  reach := fun u v hu hv => reachable_sup_sameBlockGraph_of_eq
    ((mem_singleton.mp hu).trans (mem_singleton.mp hv).symm)
  noBridge := by simp

omit [DecidableEq V] in
/-- Adding an ear keeps the invariant. -/
theorem EarInv.append {S₁ : β} {Ps : List (Ear V)} (hI : EarInv (b := b) E S₁ Ps) {P : Ear V}
    (hP : IsEar b E (covered b {S₁} Ps) P) : EarInv (b := b) E S₁ (Ps ++ [P]) := by
  set U := covered b {S₁} Ps
  set L := Ps.flatMap Ear.edges
  have hL' : (Ps ++ [P]).flatMap Ear.edges = L ++ P.edges := by
    simp [L, List.flatMap_append]
  have hcov : covered b {S₁} (Ps ++ [P]) = U ∪ P.blocks b := by
    rw [covered_append, covered_cons, covered_nil]
  -- the new edges meet blocks outside `U`
  have hfresh : ∀ e ∈ P.edges, e ∉ L := by
    intro e he heL
    obtain ⟨p, hp, rfl⟩ := Ear.mem_edges.mp he
    rcases hP.exists_interior p hp with h | h
    · exact hP.interior_notMem _ h (hI.covered_of_mem _ heL _ (Sym2.mem_mk_left _ _))
    · exact hP.interior_notMem _ h (hI.covered_of_mem _ heL _ (Sym2.mem_mk_right _ _))
  set G' := graphOf (L ++ P.edges)
  have hGle : graphOf L ≤ G' := graphOf_mono fun e he => List.mem_append_left _ he
  have hPadj : ∀ q ∈ P.toList, G'.Adj q.1 q.2 := fun q hq =>
    graphOf_adj.mpr ⟨List.mem_append_right _ (List.mem_map_of_mem hq), (hP.adj q hq).ne⟩
  have hx₀ : (graphOf L ⊔ sameBlockGraph b).Reachable P.first.1 P.last.2 :=
    hI.reach _ _ hP.startBlock_mem hP.endBlock_mem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isEarSeq_append.mpr ⟨hI.isEarSeq, hP, trivial⟩
  · rw [hL', List.nodup_append]
    exact ⟨hI.nodup, hP.nodup_edges, fun a ha e he hae => hfresh e he (hae ▸ ha)⟩
  · rw [hL', hcov]
    intro e he v hv
    rcases List.mem_append.mp he with he | he
    · exact mem_union_left _ (hI.covered_of_mem e he v hv)
    · obtain ⟨p, hp, rfl⟩ := Ear.mem_edges.mp he
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      exacts [mem_union_right _ (hP.mem_blocks p hp).1, mem_union_right _ (hP.mem_blocks p hp).2]
  · rw [hL', hcov]
    have hall : ∀ v, b v ∈ U ∪ P.blocks b → (G' ⊔ sameBlockGraph b).Reachable P.first.1 v := by
      intro v hv
      rw [hP.union_blocks, mem_union, List.mem_toFinset] at hv
      rcases hv with hv | hv
      · exact (hI.reach _ _ hP.startBlock_mem hv).mono (sup_le_sup_right hGle _)
      · rw [Ear.interior_eq, List.mem_map] at hv
        obtain ⟨q, hq, hqv⟩ := hv
        have hq' : q ∈ P.toList := by
          rcases List.mem_cons.mp hq with rfl | hq
          · exact P.first_mem_toList
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ hq)
        exact ((reachable_of_isChain hP.isChain hPadj) q hq').2.trans
          (reachable_sup_sameBlockGraph_of_eq hqv)
    intro u v hu hv
    exact (hall u hu).symm.trans (hall v hv)
  · rw [hL']
    intro x y hxy
    rcases List.mem_append.mp hxy with hxy | hxy
    · exact (hI.noBridge x y hxy).mono
        (sup_le_sup_right (deleteEdges_mono (graphOf_mono fun e he =>
          List.mem_append_left _ he)) _)
    · obtain ⟨p, hp, hpe⟩ := Ear.mem_edges.mp hxy
      set H := G'.deleteEdges {edge p}
      have hHadj : ∀ q ∈ P.toList, edge q ≠ edge p → H.Adj q.1 q.2 := fun q hq hne =>
        deleteEdges_adj.mpr ⟨hPadj q hq, fun h => hne (Set.mem_singleton_iff.mp h)⟩
      have hLH : graphOf L ≤ H := by
        intro u v huv
        refine deleteEdges_adj.mpr ⟨hGle huv, fun h => ?_⟩
        rw [Set.mem_singleton_iff] at h
        exact hfresh _ (List.mem_map_of_mem hp) (h ▸ (graphOf_adj.mp huv).1)
      have hFL : (H ⊔ sameBlockGraph b).Reachable P.first.1 P.last.2 :=
        hx₀.mono (sup_le_sup_right hLH _)
      have hr := reachable_of_isChain_erase (e := edge p) hP.isChain hP.nodup_edges hHadj p hp
      have h1 : (H ⊔ sameBlockGraph b).Reachable p.1 P.first.1 :=
        hr.1.elim Reachable.symm fun h => h.trans hFL.symm
      have h2 : (H ⊔ sameBlockGraph b).Reachable p.2 P.first.1 :=
        hr.2.elim Reachable.symm fun h => h.trans hFL.symm
      have h12 := h1.trans h2.symm
      rw [edge_apply] at hpe
      rw [← hpe]
      rcases Sym2.eq_iff.mp hpe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h12
      · exact h12.symm

/-- Once all blocks are covered, the invariant and minimality force the ears to use every edge. -/
theorem EarInv.isStrictEarDecompOn [Fintype β] (hmin : MinTwoEdgeConnOn b E) {S₁ : β}
    {Ps : List (Ear V)} (hI : EarInv (b := b) E S₁ Ps) (hcov : covered b {S₁} Ps = univ)
    (hne : Ps ≠ []) : IsStrictEarDecompOn b E S₁ Ps := by
  refine ⟨hne, hI.isEarSeq, hI.nodup, fun e => ⟨hI.isEarSeq.mem_edgeSet e, fun he => ?_⟩, hcov⟩
  by_contra heL
  set L := Ps.flatMap Ear.edges
  have hall : ∀ u v, (graphOf L ⊔ sameBlockGraph b).Reachable u v := fun u v =>
    hI.reach u v (hcov ▸ mem_univ _) (hcov ▸ mem_univ _)
  have : Nonempty V := by
    obtain ⟨P, -, -⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨P.first.1⟩
  have h2 : TwoEdgeConnOn b (graphOf L) := by
    refine ⟨⟨hall⟩, fun f hf => ⟨fun u v => ?_⟩⟩
    refine (reachable_comp_of_forall_adj id (fun a a' haa' => ?_) (hall u v) : _)
    rcases haa' with h | h
    · by_cases hf' : s(a, a') = f
      · rw [← hf'] at hf ⊢
        exact hI.noBridge a a' (graphOf_adj.mp h).1
      · exact Adj.reachable (Or.inl (deleteEdges_adj.mpr ⟨h, fun h' => hf' h'⟩))
    · exact Adj.reachable (Or.inr h)
  refine hmin.2 e he (h2.mono fun u v huv => ?_)
  obtain ⟨huvL, -⟩ := graphOf_adj.mp huv
  refine deleteEdges_adj.mpr ⟨hI.isEarSeq.mem_edgeSet _ huvL, fun h => ?_⟩
  rw [Set.mem_singleton_iff] at h
  exact heL (h ▸ huvL)

omit [DecidableEq V] in
/-- Extending the ears until every block is covered. -/
theorem exists_extension [Fintype β] (hb : Function.Surjective b) (h2 : TwoEdgeConnOn b E)
    {S₁ : β} : ∀ (n : ℕ) (Ps : List (Ear V)), EarInv (b := b) E S₁ Ps →
      (univ \ covered b {S₁} Ps).card = n →
      ∃ Ps', EarInv (b := b) E S₁ (Ps ++ Ps') ∧ covered b {S₁} (Ps ++ Ps') = univ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Ps hI hn
    by_cases hcov : covered b {S₁} Ps = univ
    · exact ⟨[], by simpa using hI, by simpa using hcov⟩
    have hU : (covered b {S₁} Ps).Nonempty :=
      ⟨S₁, subset_covered _ _ (mem_singleton_self _)⟩
    obtain ⟨x, y, hxy, hx, hy⟩ := exists_boundary_edge hb h2.1 hU hcov
    obtain ⟨P, -, hP⟩ := exists_isEar_of_boundary h2 hxy hx hy
    have hI' := hI.append hP
    have hlt : (univ \ covered b {S₁} (Ps ++ [P])).card < n := by
      rw [← hn, covered_append, covered_cons, covered_nil]
      refine card_lt_card ⟨sdiff_subset_sdiff le_rfl subset_union_left, fun h => ?_⟩
      have hmem : b P.first.2 ∈ P.interior b := List.mem_cons_self
      have hB : b P.first.2 ∈ univ \ covered b {S₁} Ps :=
        mem_sdiff.mpr ⟨mem_univ _, hP.interior_notMem _ hmem⟩
      refine (mem_sdiff.mp (h hB)).2 (mem_union_right _ ?_)
      simp only [Ear.blocks, mem_insert, List.mem_toFinset]
      exact Or.inr (Or.inr hmem)
    obtain ⟨Ps', hI'', hcov''⟩ := ih _ hlt (Ps ++ [P]) hI' rfl
    refine ⟨P :: Ps', ?_, ?_⟩
    · simpa using hI''
    · simpa using hcov''

/-- **Lemma 4.40** (generic form, prescribed first cycle): if `E` is minimally 2-edge-connected
relative to the blocks of a surjective block map, every cycle `P` of the multigraph quotient
(an ear relative to `{S₁}`) is the first ear of a strict ear decomposition of `E`. -/
theorem exists_isStrictEarDecompOn_cons [Fintype β] (hb : Function.Surjective b)
    (hmin : MinTwoEdgeConnOn b E) {S₁ : β} {P : Ear V} (hP : IsEar b E {S₁} P) :
    ∃ Ps, IsStrictEarDecompOn b E S₁ (P :: Ps) := by
  have hI := (earInv_nil (b := b) (E := E) S₁).append (Ps := []) hP
  obtain ⟨Ps, hI', hcov⟩ := exists_extension hb hmin.1 _ ([] ++ [P]) hI rfl
  refine ⟨Ps, ?_⟩
  have h := hI'.isStrictEarDecompOn hmin hcov (by simp)
  simpa using h

/-- Generic form of Lemma 4.40 with a prescribed first oriented edge. -/
theorem exists_isStrictEarDecompOn_first [Fintype β] (hb : Function.Surjective b)
    (hE : E ≤ crossBlockGraph b) (hmin : MinTwoEdgeConnOn b E) {x y : V} (hxy : E.Adj x y) :
    ∃ P Ps, P.first = (x, y) ∧ IsStrictEarDecompOn b E (b x) (P :: Ps) := by
  have hy : b y ∉ ({b x} : Finset β) := fun h =>
    crossBlockGraph_adj.mp (hE hxy) (mem_singleton.mp h).symm
  obtain ⟨P, hPf, hP⟩ := exists_isEar_of_boundary hmin.1 hxy (mem_singleton_self _) hy
  obtain ⟨Ps, hPs⟩ := exists_isStrictEarDecompOn_cons hb hmin hP
  exact ⟨P, Ps, hPf, hPs⟩

/-- Generic form of Lemma 4.40 with a prescribed base block. -/
theorem exists_isStrictEarDecompOn [Fintype β] (hb : Function.Surjective b)
    (hE : E ≤ crossBlockGraph b) (hmin : MinTwoEdgeConnOn b E) (h1 : Fintype.card β ≠ 1)
    (S₁ : β) : ∃ Ps, IsStrictEarDecompOn b E S₁ Ps := by
  have hne : ({S₁} : Finset β) ≠ univ := by
    intro h
    apply h1
    rw [← card_univ, ← h, card_singleton]
  obtain ⟨x, y, hxy, hx, -⟩ := exists_boundary_edge hb hmin.1.1 (singleton_nonempty S₁) hne
  obtain ⟨P, Ps, -, hPs⟩ := exists_isStrictEarDecompOn_first hb hE hmin hxy
  rw [mem_singleton.mp hx] at hPs
  exact ⟨P :: Ps, hPs⟩

/-! ### Lemma 4.40 relative to a subpartition -/

section Subpartition

variable {X : Finset (Finset ℕ)} {hX : IsSubpartition X} {E : SimpleGraph (X.biUnion id)}

/-- **Lemma 4.40**: a graph minimally 2-edge-connected
relative to `X` admits a strict ear decomposition relative to `X`, and the first cycle may be
prescribed: any cycle `P` of the multigraph quotient (an ear relative to `{S₁}`) is the first
ear of one. -/
theorem exists_isStrictEarDecomp_cons (hE : Parity.IsRelMinTwoEdgeConnected X E) {S₁ : X}
    {P : Ear (X.biUnion id)} (hP : IsEar (blockOf hX) E {S₁} P) :
    ∃ Ps, IsStrictEarDecomp hX E S₁ (P :: Ps) :=
  exists_isStrictEarDecompOn_cons (blockOf_surjective hX)
    ((isRelMinTwoEdgeConnected_iff_on hX).mp hE).2.2 hP

/-- Lemma 4.40 with a prescribed first oriented edge `(x, y)` of the base cycle. -/
theorem exists_isStrictEarDecomp_first (hE : Parity.IsRelMinTwoEdgeConnected X E)
    {x y : X.biUnion id} (hxy : E.Adj x y) :
    ∃ P Ps, P.first = (x, y) ∧ IsStrictEarDecomp hX E (blockOf hX x) (P :: Ps) := by
  obtain ⟨hle, -, hmin⟩ := (isRelMinTwoEdgeConnected_iff_on hX).mp hE
  rw [interEdges_eq hX] at hle
  exact exists_isStrictEarDecompOn_first (blockOf_surjective hX) hle hmin hxy

/-- Lemma 4.40 with a prescribed base block `S₁` of the base cycle. -/
theorem exists_isStrictEarDecomp (hE : Parity.IsRelMinTwoEdgeConnected X E) (S₁ : X) :
    ∃ Ps, IsStrictEarDecomp hX E S₁ Ps := by
  obtain ⟨hle, h1, hmin⟩ := (isRelMinTwoEdgeConnected_iff_on hX).mp hE
  rw [interEdges_eq hX] at hle
  exact exists_isStrictEarDecompOn (blockOf_surjective hX) hle hmin
    (by rwa [Fintype.card_coe]) S₁

end Subpartition

end Peeling

end MultipoleBKT

end
