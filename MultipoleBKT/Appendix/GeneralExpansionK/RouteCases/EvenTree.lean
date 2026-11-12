/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.OrderingTree
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The two trees on the sides of a marked edge

See case E of
the proof of Lemma A.7. Deleting the mark splits the label tree
into two trees. Apply Lemma A.1 on each side, rooted at the
corresponding endpoint. Both endpoint squares are supplied by (A.62).
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Removing a marked edge of a tree leaves exactly its two endpoint components. -/
theorem marked_tree_two_sides {T : SimpleGraph V} (hT : T.IsTree)
    {x y : V} (hxy : T.Adj x y) :
    let G := T.deleteEdges {s(x, y)}
    ¬ G.Reachable x y ∧ ∀ v, G.Reachable x v ∨ G.Reachable y v := by
  dsimp only
  let G := T.deleteEdges {s(x, y)}
  have hsep : ¬ G.Reachable x y := (isAcyclic_iff_forall_adj_isBridge.1 hT.isAcyclic) hxy
  refine ⟨hsep, ?_⟩
  have hstep : ∀ u v, T.Adj u v →
      (G.Reachable x u ∨ G.Reachable y u) → (G.Reachable x v ∨ G.Reachable y v) := by
    intro u v huv hu
    by_cases he : s(u, v) = s(x, y)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Reachable.refl _)
      · exact Or.inl (Reachable.refl _)
    · have hG : G.Adj u v := deleteEdges_adj.2 ⟨huv, he⟩
      exact hu.elim (fun hx => Or.inl (hx.trans hG.reachable)) (fun hy => Or.inr (hy.trans hG.reachable))
  have hw : ∀ u v, T.Walk u v →
      (G.Reachable x u ∨ G.Reachable y u) → (G.Reachable x v ∨ G.Reachable y v) := by
    intro u v p
    induction p with
    | nil => exact id
    | cons huv p ih => exact fun hu => ih (hstep _ _ huv hu)
  intro v
  obtain ⟨p⟩ := hT.connected.preconnected x v
  exact hw x v p (Or.inl (Reachable.refl _))

open scoped Classical in
/-- The two-sided ordering estimate. The marked edge contributes both endpoint
squares, and every remaining edge contributes its smaller endpoint square. -/
theorem marked_tree_radius_allocation {T : SimpleGraph V} (hT : T.IsTree)
    {x y : V} (hxy : T.Adj x y) (r : V → ℝ) (f : ℝ → ℝ)
    (hf : Monotone f) (hf0 : ∀ a, 0 ≤ f a) :
    f (r x) * f (r y) * (∏ e ∈ T.edgeFinset.erase s(x, y), edgeMin f r e) ≤
      ∏ i, f (r i) := by
  let G := T.deleteEdges {s(x, y)}
  let A : Set V := {v | G.Reachable x v}
  let B : Set V := {v | ¬ G.Reachable x v}
  let TA := G.induce A
  let TB := G.induce B
  have hsplit := marked_tree_two_sides hT hxy
  have hx : x ∈ A := Reachable.refl _
  have hy : y ∈ B := hsplit.1
  have hA : TA.IsTree := by
    have heq : A = (G.connectedComponentMk x).supp := by
      ext v
      exact ⟨fun hv => ConnectedComponent.sound hv.symm,
        fun hv => ConnectedComponent.exact hv.symm⟩
    refine ⟨?_, (hT.isAcyclic.anti (deleteEdges_le _)).induce A⟩
    rw [show TA = G.induce A from rfl, heq]
    exact (G.connectedComponentMk x).connected_toSimpleGraph
  have hB : TB.IsTree := by
    have heq : B = (G.connectedComponentMk y).supp := by
      ext v
      constructor
      · intro hv
        exact ConnectedComponent.sound ((hsplit.2 v).resolve_left hv).symm
      · intro hv hxv
        exact hsplit.1 (hxv.trans (ConnectedComponent.exact hv))
    refine ⟨?_, (hT.isAcyclic.anti (deleteEdges_le _)).induce B⟩
    rw [show TB = G.induce B from rfl, heq]
    exact (G.connectedComponentMk y).connected_toSimpleGraph
  let ia : A ↪ V := Function.Embedding.subtype A
  let ib : B ↪ V := Function.Embedding.subtype B
  have hgraphs : G = TA.map ia ⊔ TB.map ib := by
    ext u v
    constructor
    · intro huv
      by_cases hu : u ∈ A
      · have hv : v ∈ A := hu.trans huv.reachable
        exact Or.inl ((map_adj _ _ _ _).2 ⟨⟨u, hu⟩, ⟨v, hv⟩, huv, rfl, rfl⟩)
      · have hv : v ∈ B := fun hv => hu (hv.trans huv.symm.reachable)
        exact Or.inr ((map_adj _ _ _ _).2 ⟨⟨u, hu⟩, ⟨v, hv⟩, huv, rfl, rfl⟩)
    · rintro (huv | huv)
      · obtain ⟨u', v', huv', rfl, rfl⟩ := (map_adj _ _ _ _).1 huv
        exact huv'
      · obtain ⟨u', v', huv', rfl, rfl⟩ := (map_adj _ _ _ _).1 huv
        exact huv'
  have hdisj : Disjoint (TA.map ia).edgeFinset (TB.map ib).edgeFinset := by
    refine disjoint_left.2 fun e hea heb => ?_
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨uA, vA, -, huA, -⟩ := (map_adj _ _ _ _).1 (mem_edgeFinset.1 hea)
      obtain ⟨uB, vB, -, huB, -⟩ := (map_adj _ _ _ _).1 (mem_edgeFinset.1 heb)
      have hab : uA.val = uB.val := huA.trans huB.symm
      exact uB.property (hab ▸ uA.property)
  have hprod : (∏ e ∈ T.edgeFinset.erase s(x, y), edgeMin f r e) =
      (∏ e ∈ TA.edgeFinset, edgeMin f (fun i : A => r i.1) e) *
        ∏ e ∈ TB.edgeFinset, edgeMin f (fun i : B => r i.1) e := by
    have hE : G.edgeFinset = T.edgeFinset.erase s(x, y) := by
      ext e
      simp only [mem_edgeFinset, G, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff, mem_erase]
      tauto
    have hGE : G.edgeFinset = (TA.map ia ⊔ TB.map ib).edgeFinset := by
      ext e
      rw [mem_edgeFinset, mem_edgeFinset]
      exact congrArg (fun H : SimpleGraph V => e ∈ H.edgeSet) hgraphs |>.to_iff
    rw [← hE, hGE, edgeFinset_sup, prod_union hdisj, edgeFinset_map, edgeFinset_map, prod_map, prod_map]
    congr 1 <;> apply prod_congr rfl <;> intro e _ <;> induction e using Sym2.ind <;> rfl
  have hboundA := prod_edgeMin_le_prod_erase hA hf hf0 (fun i : A => r i.1) ⟨x, hx⟩
  have hboundB := prod_edgeMin_le_prod_erase hB hf hf0 (fun i : B => r i.1) ⟨y, hy⟩
  have hsideA : f (r x) * (∏ e ∈ TA.edgeFinset, edgeMin f (fun i : A => r i.1) e) ≤
      ∏ i : A, f (r i.1) := by
    calc _ ≤ f (r x) * ∏ i ∈ univ.erase (⟨x, hx⟩ : A), f (r i.1) :=
               mul_le_mul_of_nonneg_left hboundA (hf0 _)
         _ = _ := mul_prod_erase _ (fun i : A => f (r i.1)) (mem_univ ⟨x, hx⟩)
  have hsideB : f (r y) * (∏ e ∈ TB.edgeFinset, edgeMin f (fun i : B => r i.1) e) ≤
      ∏ i : B, f (r i.1) := by
    calc _ ≤ f (r y) * ∏ i ∈ univ.erase (⟨y, hy⟩ : B), f (r i.1) :=
               mul_le_mul_of_nonneg_left hboundB (hf0 _)
         _ = _ := mul_prod_erase _ (fun i : B => f (r i.1)) (mem_univ ⟨y, hy⟩)
  rw [hprod]
  calc _ = (f (r x) * ∏ e ∈ TA.edgeFinset, edgeMin f (fun i : A => r i.1) e) *
        (f (r y) * ∏ e ∈ TB.edgeFinset, edgeMin f (fun i : B => r i.1) e) := by ring
       _ ≤ (∏ i : A, f (r i.1)) * ∏ i : B, f (r i.1) :=
         mul_le_mul hsideA hsideB
           (mul_nonneg (hf0 _) (prod_nonneg fun e _ => Sym2.inductionOn e (fun _ _ => hf0 _)))
           (prod_nonneg fun i _ => hf0 _)
       _ = _ := Fintype.prod_subtype_mul_prod_subtype (fun v => G.Reachable x v) (fun i => f (r i))

end MultipoleBKT.ExpansionK.RouteCases

end
