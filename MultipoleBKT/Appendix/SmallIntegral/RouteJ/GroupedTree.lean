/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.GroupedBlocks
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.RetainedTrees

/-!
# The even tree on the coarse partition

See Lemma A.4. Collapsing each odd group gives
exactly the coarse tree used in the first application of Lemma A.1.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open Finset SimpleGraph Limits
open scoped Classical

variable {V B C : Type*} [Fintype V] [Fintype B] [Fintype C]
  [DecidableEq V] [DecidableEq B] [DecidableEq C]

omit [Fintype V] [DecidableEq V] in
/-- A relative tree given by edges has an injective edge map onto its quotient. -/
theorem quotient_tree (b : V → C) (hb : Function.Surjective b)
    (E : Finset (Sym2 V)) (hdiag : ∀ e ∈ E, ¬ (Sym2.map b e).IsDiag)
    (hc : ∀ i j, (sameBlockGraph b ⊔ fromEdgeSet (E : Set (Sym2 V))).Reachable i j)
    [Nonempty V] (hcard : E.card + 1 ≤ Fintype.card C) :
    (fromEdgeSet (E.image (Sym2.map b) : Set (Sym2 C))).IsTree ∧
      (fromEdgeSet (E.image (Sym2.map b) : Set (Sym2 C))).edgeFinset = E.image (Sym2.map b) ∧
      Set.InjOn (Sym2.map b) (E : Set (Sym2 V)) := by
  let Q := E.image (Sym2.map b)
  have hQdiag : ∀ e ∈ Q, ¬e.IsDiag := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    exact hdiag f hf
  have hQc : (fromEdgeSet (Q : Set (Sym2 C))).Connected := by
    rw [connected_iff]
    have : Nonempty C := Nonempty.map b inferInstance
    refine ⟨fun c d => ?_, inferInstance⟩
    obtain ⟨i, rfl⟩ := hb c
    obtain ⟨j, rfl⟩ := hb d
    apply reachable_comp_of_forall_adj b _ (hc i j)
    intro a d hadj
    rcases (sup_adj _ _ _ _).mp hadj with h | h
    · rw [(sameBlockGraph_adj.mp h).2]
    · obtain ⟨he, hne⟩ := (fromEdgeSet_adj _).mp h
      have hn : b a ≠ b d := fun heq => hdiag _ he (by simp [heq])
      apply Adj.reachable
      rw [fromEdgeSet_adj]
      exact ⟨mem_image.mpr ⟨s(a, d), he, rfl⟩, hn⟩
  have hle : Q.card ≤ E.card := card_image_le
  obtain ⟨ht, _, hq⟩ := isTree_fromEdgeSet_of_card hQdiag hQc (by omega)
  refine ⟨ht, ?_, card_image_iff.mp (by change Q.card = E.card; omega)⟩
  ext e
  rw [mem_edgeFinset, edgeSet_fromEdgeSet]
  exact ⟨fun h => h.1, fun h => ⟨h, hQdiag e h⟩⟩

variable {n : ℕ}

omit [Fintype V] in
/-- The even edges become a tree after the odd groups are collapsed.
The inputs are the structural conclusions of `trees_structure`. -/
theorem grouped_even_tree [Nonempty V] (blk : V → B) (hblk : Function.Surjective blk)
    (G : Fin n → Finset B) (hG : ∀ l l', l ≠ l' → Disjoint (G l) (G l'))
    (A : Fin n → Finset (Sym2 V)) (E : Finset (Sym2 V))
    (hAG : ∀ l, ∀ e ∈ A l, ∀ i ∈ e, blk i ∈ G l)
    (hAc : ∀ l, (A l).card + 1 = (G l).card)
    (hc : ∀ i j, (sameBlockGraph blk ⊔
      fromEdgeSet ((univ.biUnion A ∪ E : Finset (Sym2 V)) : Set (Sym2 V))).Reachable i j)
    (hcard : (∑ l, (A l).card) + E.card + 1 ≤ Fintype.card B)
    (hat : Fin n → B) (hhat : ∀ l, hat l ∈ G l) :
    let b := groupedOf G hG ∘ blk
    (fromEdgeSet (E.image (Sym2.map b) : Set (Sym2 (GroupedBlock G)))).IsTree ∧
      (fromEdgeSet (E.image (Sym2.map b) : Set (Sym2 (GroupedBlock G)))).edgeFinset =
        E.image (Sym2.map b) ∧
      Set.InjOn (Sym2.map b) (E : Set (Sym2 V)) := by
  let grp := groupedOf G hG
  let b := grp ∘ blk
  have hgrp : Function.Surjective grp := fun c =>
    ⟨groupedHat G hat c, groupedHat_right_inverse G hG hat hhat c⟩
  have hbs : Function.Surjective b := hgrp.comp hblk
  have hco : ∀ i j, (sameBlockGraph b ⊔ fromEdgeSet (E : Set (Sym2 V))).Reachable i j := by
    intro i j
    apply reachable_comp_of_forall_adj id _ (hc i j)
    intro a d hadj
    rcases (sup_adj _ _ _ _).mp hadj with h | h
    · exact reachable_sup_sameBlockGraph_of_eq (E := fromEdgeSet (E : Set (Sym2 V)))
        (congrArg grp (sameBlockGraph_adj.mp h).2) |>.mono (by rw [sup_comm])
    · obtain ⟨he, hne⟩ := (fromEdgeSet_adj _).mp h
      rcases mem_union.mp he with he | he
      · obtain ⟨l, _, he⟩ := mem_biUnion.mp he
        have ha := hAG l _ he a (Sym2.mem_mk_left _ _)
        have hd := hAG l _ he d (Sym2.mem_mk_right _ _)
        have heq : b a = b d :=
          ((groupedOf_eq_inl G hG _ l).mpr ha).trans ((groupedOf_eq_inl G hG _ l).mpr hd).symm
        exact reachable_sup_sameBlockGraph_of_eq (E := fromEdgeSet (E : Set (Sym2 V))) heq
          |>.mono (by rw [sup_comm])
      · exact Adj.reachable (Or.inr ((fromEdgeSet_adj _).mpr ⟨he, hne⟩) :
          (sameBlockGraph b ⊔ fromEdgeSet (E : Set (Sym2 V))).Adj a d)
  have hC := card_groupedBlock G hG (fun l => (A l).card) hAc
  have hn : ∀ e ∈ E, ¬ (Sym2.map b e).IsDiag := by
    intro e he hd
    -- Any loop in the quotient would leave too few edges for connectivity.
    have hconnQ : (blockQuotient b (fromEdgeSet (E : Set (Sym2 V)))).Connected := by
      rw [← connected_sup_sameBlockGraph_iff hbs, sup_comm, connected_iff]
      exact ⟨hco, inferInstance⟩
    have hset : (blockQuotient b (fromEdgeSet (E : Set (Sym2 V)))).edgeFinset ⊆
        (E.erase e).image (Sym2.map b) := by
      intro f hf
      induction f using Sym2.ind with
      | h c d =>
        obtain ⟨hcd, i, j, hi, hj, hij⟩ := blockQuotient_adj.mp (mem_edgeFinset.mp hf)
        obtain ⟨hijE, _⟩ := (fromEdgeSet_adj _).mp hij
        have hne : s(i, j) ≠ e := by
          intro heq
          have : (Sym2.map b s(i, j)).IsDiag := heq ▸ hd
          simp only [Sym2.map_mk, Sym2.mk_isDiag_iff, hi, hj] at this
          exact hcd this
        exact mem_image.mpr ⟨s(i, j), mem_erase.mpr ⟨hne, hijE⟩, by simp [hi, hj]⟩
    have hlow := hconnQ.card_vert_le_card_edgeSet_add_one
    simp only [Nat.card_eq_fintype_card, ← edgeFinset_card] at hlow
    have hu := (card_le_card hset).trans (card_image_le)
    have hecard := card_erase_of_mem he
    have hEpos : 0 < E.card := card_pos.mpr ⟨e, he⟩
    omega
  exact quotient_tree b hbs E hn hco (by omega)

end MultipoleBKT.SmallIntegral.RouteJ

end
