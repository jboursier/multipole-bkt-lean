/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.JGraphs

/-!
# Retaining the three edge families

See Lemma A.4. The union of the chosen near trees,
the odd trees, and the coarse even tree is a tree on the dipole labels.
The families remain separate throughout this construction.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open Finset SimpleGraph Limits
open scoped Classical

variable {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]

/-- The near forest obtained by embedding a tree from each block fibre.
See (A.21). -/
noncomputable def nearForest (blk : V → B)
    (R : ∀ b, SimpleGraph {i // blk i = b}) : Finset (Sym2 V) :=
  univ.biUnion fun b => (R b).edgeFinset.image (Sym2.map Subtype.val)

/-- Membership in the retained near forest records its original block tree. -/
theorem mem_nearForest (blk : V → B) (R : ∀ b, SimpleGraph {i // blk i = b})
    (e : Sym2 V) :
    e ∈ nearForest blk R ↔ ∃ b, ∃ f ∈ (R b).edgeFinset, Sym2.map Subtype.val f = e := by
  simp [nearForest]

/-- Every near edge lies inside one block and has distinct endpoints. -/
theorem nearForest_endpoints (blk : V → B) (R : ∀ b, SimpleGraph {i // blk i = b})
    {i j : V} (h : s(i, j) ∈ nearForest blk R) : i ≠ j ∧ blk i = blk j := by
  obtain ⟨b, e, he, heq⟩ := (mem_nearForest blk R _).mp h
  induction e using Sym2.ind with
  | h a c =>
    have ha := a.property
    have hc := c.property
    have hne := (mem_edgeFinset.mp he : (R b).Adj a c).ne
    simp only [Sym2.map_mk, Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun h => hne (Subtype.ext h), ha.trans hc.symm⟩
    · exact ⟨fun h => hne (Subtype.ext h.symm), hc.trans ha.symm⟩

/-- Distinct block fibres give disjoint embedded edge families. -/
theorem nearForest_disjoint (blk : V → B) (R : ∀ b, SimpleGraph {i // blk i = b}) :
    ((univ : Finset B) : Set B).PairwiseDisjoint
      (fun b => (R b).edgeFinset.image (Sym2.map Subtype.val)) := by
  intro b _ c _ hbc
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a, _, rfl⟩ := mem_image.mp he
  obtain ⟨d, _, hd⟩ := mem_image.mp hf
  induction a using Sym2.ind with
  | h i j =>
    induction d using Sym2.ind with
    | h p q =>
      simp only [Sym2.map_mk, Sym2.eq_iff] at hd
      rcases hd with ⟨h, _⟩ | ⟨h, _⟩
      · exact hbc (i.property.symm.trans ((congrArg blk h).symm.trans p.property))
      · exact hbc (j.property.symm.trans ((congrArg blk h).symm.trans p.property))

/-- The near forest has exactly `|V| - |B|` edges. -/
theorem card_nearForest (blk : V → B) (R : ∀ b, SimpleGraph {i // blk i = b})
    (hR : ∀ b, (R b).IsTree) :
    (nearForest blk R).card + Fintype.card B = Fintype.card V := by
  have hfib : ∑ b, Fintype.card {i // blk i = b} = Fintype.card V := by
    rw [← card_univ (α := V), card_eq_sum_card_fiberwise (f := blk) (fun i _ => mem_univ _)]
    exact sum_congr rfl fun b _ => by
      change Fintype.card ({i | blk i = b} : Set V) = _
      rw [Fintype.card_ofFinset]
      rfl
  unfold nearForest
  rw [card_biUnion (nearForest_disjoint blk R)]
  have he : ∀ b, ((R b).edgeFinset.image (Sym2.map Subtype.val)).card =
      (R b).edgeFinset.card := fun b =>
    card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
  simp_rw [he]
  calc
    _ = ∑ b, ((R b).edgeFinset.card + 1) := by simp [sum_add_distrib]
    _ = _ := (sum_congr rfl fun b _ => (hR b).card_edgeFinset).trans hfib

/-- Each block remains connected using only its retained near edges. -/
theorem nearForest_reachable (blk : V → B) (R : ∀ b, SimpleGraph {i // blk i = b})
    (hR : ∀ b, (R b).IsTree) {i j : V} (hij : blk i = blk j) :
    (fromEdgeSet (nearForest blk R : Set (Sym2 V))).Reachable i j := by
  let f : R (blk i) →g fromEdgeSet (nearForest blk R : Set (Sym2 V)) :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        exact (fromEdgeSet_adj _).mpr ⟨(mem_nearForest blk R _).mpr
          ⟨blk i, s(a, b), mem_edgeFinset.mpr hab, rfl⟩,
          fun heq => hab.ne (Subtype.ext heq)⟩ }
  exact ((hR (blk i)).connected.preconnected ⟨i, rfl⟩ ⟨j, hij.symm⟩).map f

/-- The retained near, odd, and even edges form one tree, without replacing
either far family by a power weight.
See the proof of Lemma A.4. -/
theorem retained_tree [Nonempty V] (blk : V → B)
    (R : ∀ b, SimpleGraph {i // blk i = b}) (hR : ∀ b, (R b).IsTree)
    (A E : Finset (Sym2 V))
    (hinter : ∀ e ∈ A ∪ E, ¬ (Sym2.map blk e).IsDiag)
    (hconn : ∀ i j, (sameBlockGraph blk ⊔
      fromEdgeSet ((A ∪ E : Finset (Sym2 V)) : Set (Sym2 V))).Reachable i j)
    (hcount : A.card + E.card + 1 ≤ Fintype.card B) :
    (fromEdgeSet ((nearForest blk R ∪ (A ∪ E) : Finset (Sym2 V)) : Set (Sym2 V))).IsTree ∧
      (fromEdgeSet ((nearForest blk R ∪ (A ∪ E) : Finset (Sym2 V)) : Set (Sym2 V))).edgeFinset =
        nearForest blk R ∪ (A ∪ E) ∧
      Disjoint (nearForest blk R) (A ∪ E) ∧ Disjoint A E ∧
      A.card + E.card + 1 = Fintype.card B := by
  let F := nearForest blk R
  let U := F ∪ (A ∪ E)
  have hdiag : ∀ e ∈ U, ¬ e.IsDiag := by
    intro e he
    rcases mem_union.mp he with he | he
    · induction e using Sym2.ind with
      | h i j => exact mt Sym2.mk_isDiag_iff.mp (nearForest_endpoints blk R he).1
    · exact fun hd => hinter e he (by
        induction e using Sym2.ind with
        | h i j => simp only [Sym2.mk_isDiag_iff, Sym2.map_mk, Sym2.mk_isDiag_iff.mp hd])
  have hwithin : ∀ i j, blk i = blk j → (fromEdgeSet (U : Set (Sym2 V))).Reachable i j := by
    intro i j hij
    exact (nearForest_reachable blk R hR hij).mono
      (fromEdgeSet_mono (Finset.coe_subset.mpr subset_union_left))
  have hc : (fromEdgeSet (U : Set (Sym2 V))).Connected := by
    rw [connected_iff]
    refine ⟨fun i j => ?_, inferInstance⟩
    apply reachable_comp_of_forall_adj id _ (hconn i j)
    intro a b hab
    rcases (sup_adj _ _ _ _).mp hab with hab | hab
    · exact hwithin a b (sameBlockGraph_adj.mp hab).2
    · exact ((fromEdgeSet_adj _).mpr ⟨mem_union_right _ ((fromEdgeSet_adj _).mp hab).1,
        ((fromEdgeSet_adj _).mp hab).2⟩).reachable
  have hF := card_nearForest blk R hR
  have hAE := card_union_le A E
  have hU := card_union_le F (A ∪ E)
  obtain ⟨hT, _, hTc⟩ := isTree_fromEdgeSet_of_card hdiag hc (by dsimp only [U, F] at hU ⊢; omega)
  refine ⟨hT, ?_, ?_, ?_, by dsimp only [U, F] at hTc hU; omega⟩
  · ext e
    rw [mem_edgeFinset, edgeSet_fromEdgeSet]
    exact ⟨fun h => h.1, fun h => ⟨h, hdiag e h⟩⟩
  · have h := card_union_add_card_inter F (A ∪ E)
    rw [disjoint_iff_inter_eq_empty, ← card_eq_zero]
    change (F ∩ (A ∪ E)).card = 0
    dsimp only [F]
    dsimp only [U, F] at hTc hU h
    omega
  · have h := card_union_add_card_inter A E
    rw [disjoint_iff_inter_eq_empty, ← card_eq_zero]
    dsimp only [U, F] at hTc hU h
    omega

end MultipoleBKT.SmallIntegral.RouteJ

end
