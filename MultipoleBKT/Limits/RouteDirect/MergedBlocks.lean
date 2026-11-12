/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.DipoleTerms
public import MultipoleBKT.Cluster.Relative

/-!
# Merging the original multipole parts along the near edges

See Lemma 4.26 of the paper. The merged parts contain the original blocks and all
selected near edges. Their induced near graphs remain connected.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open Finset Set SimpleGraph SmallIntegral
open scoped Classical

variable {I B : Type*} [Fintype I] [LinearOrder I] [Fintype B] [DecidableEq B]

/-- The partition obtained by joining original parts and selected near edges. -/
def mergedGraph (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I)) : SimpleGraph I :=
  nearPart E F ⊔ sameBlockGraph blk

/-- The merged part of a label. -/
abbrev mergedOf (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I)) :=
  (mergedGraph blk E F).connectedComponentMk

omit [Fintype I] [LinearOrder I] [Fintype B] [DecidableEq B] in
/-- An original block is contained in one merged part. -/
theorem mergedOf_eq_of_block_eq (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I))
    {i j : I} (h : blk i = blk j) : mergedOf blk E F i = mergedOf blk E F j :=
  ConnectedComponent.sound ((reachable_sameBlockGraph_iff.mpr h).mono le_sup_right)

/-- The unique merger map on the original blocks. Its value is independent
of the chosen representative because each original block is contained in a part. -/
noncomputable def mergedBlockOf (blk : I → B) (hblk : Function.Surjective blk)
    (E : SimpleGraph I) (F : Finset (Sym2 I)) (b : B) : (mergedGraph blk E F).ConnectedComponent :=
  mergedOf blk E F (hblk b).choose

omit [Fintype I] [LinearOrder I] [Fintype B] [DecidableEq B] in
/-- The merger map factors the label map. -/
theorem mergedBlockOf_apply (blk : I → B) (hblk : Function.Surjective blk)
    (E : SimpleGraph I) (F : Finset (Sym2 I)) (i : I) :
    mergedBlockOf blk hblk E F (blk i) = mergedOf blk E F i :=
  mergedOf_eq_of_block_eq blk E F (hblk (blk i)).choose_spec

omit [Fintype I] [LinearOrder I] [Fintype B] [DecidableEq B] in
/-- The selected near edges lie inside the merged parts. -/
theorem mergedOf_eq_of_near (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I))
    {i j : I} (h : E.Adj i j) (he : s(i, j) ∉ F) :
    mergedOf blk E F i = mergedOf blk E F j :=
  ConnectedComponent.sound (Adj.reachable (G := mergedGraph blk E F) (Or.inl ⟨h, he⟩))

/-- The far original edges between the merged parts. -/
def mergedInter (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I)) : SimpleGraph I where
  Adj i j := E.Adj i j ∧ mergedOf blk E F i ≠ mergedOf blk E F j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

omit [Fintype I] [Fintype B] [DecidableEq B] in
/-- Every edge between merged parts belongs to the selected far set. -/
theorem mem_far_of_mergedInter (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I))
    {i j : I} (h : (mergedInter blk E F).Adj i j) : s(i, j) ∈ F := by
  by_contra hn
  exact h.2 (mergedOf_eq_of_near blk E F h.1 hn)

omit [Fintype I] [LinearOrder I] [Fintype B] [DecidableEq B] in
/-- Far edges connect the merged parts whenever the augmented original graph
is connected. -/
theorem mergedInter_reachable (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I))
    (hconn : (E ⊔ sameBlockGraph blk).Connected)
    [Fintype (mergedInter blk E F).edgeSet]
    (a b : (mergedGraph blk E F).ConnectedComponent) :
    (nodeGraph (Sym2.map (mergedOf blk E F)) (mergedInter blk E F).edgeFinset).Reachable a b := by
  have hw : ∀ i j (p : (E ⊔ sameBlockGraph blk).Walk i j),
      (nodeGraph (Sym2.map (mergedOf blk E F)) (mergedInter blk E F).edgeFinset).Reachable
        (mergedOf blk E F i) (mergedOf blk E F j) := by
    intro i j p
    induction p with
    | nil => exact Reachable.refl _
    | @cons i j k hij p ih =>
      refine Reachable.trans ?_ ih
      rcases hij with hij | hij
      · by_cases hh : mergedOf blk E F i = mergedOf blk E F j
        · rw [hh]
        · have he : s(i, j) ∈ (mergedInter blk E F).edgeFinset := mem_edgeFinset.mpr ⟨hij, hh⟩
          exact (nodeGraph_adj_of_mem (e := s(i, j)) he (by rw [Sym2.map_mk]) hh).reachable
      · rw [mergedOf_eq_of_block_eq blk E F (sameBlockGraph_adj.mp hij).2]
  obtain ⟨i, rfl⟩ := a.exists_rep
  obtain ⟨j, rfl⟩ := b.exists_rep
  obtain ⟨p⟩ := hconn.preconnected i j
  exact hw i j p

omit [Fintype I] [LinearOrder I] [Fintype B] [DecidableEq B] in
/-- Near-connected original blocks joined by the selected near edges give
near-connected merged parts. -/
theorem merged_near_connected (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I))
    {M lam : ℝ} (c : I → ℂ × ℂ)
    (hblocks : ∀ b, ((nearGraph M lam c).induce {i | blk i = b}).Connected)
    (hedges : ∀ i j, E.Adj i j → s(i, j) ∉ F → MultipoleLinked M lam (c i) (c j))
    (C : (mergedGraph blk E F).ConnectedComponent) :
    ((nearGraph M lam c).induce {i | mergedOf blk E F i = C}).Connected := by
  let H := (nearGraph M lam c).induce {i | mergedOf blk E F i = C}
  have hstep {i j : I} (hi : mergedOf blk E F i = C) (hj : mergedOf blk E F j = C)
      (hij : (mergedGraph blk E F).Adj i j) : H.Reachable ⟨i, hi⟩ ⟨j, hj⟩ := by
    rcases hij with hij | hij
    · exact Adj.reachable (G := H) (nearGraph_adj.mpr ⟨hij.1.ne, hedges i j hij.1 hij.2⟩)
    · have hblk := (sameBlockGraph_adj.mp hij).2
      let f : ((nearGraph M lam c).induce {v | blk v = blk i}) →g H :=
        { toFun := fun v => ⟨v.val, (mergedOf_eq_of_block_eq blk E F v.property).trans hi⟩
          map_rel' := fun h => h }
      exact ((hblocks (blk i)).preconnected ⟨i, rfl⟩ ⟨j, hblk.symm⟩).map f
  have hw : ∀ i j (p : (mergedGraph blk E F).Walk i j)
      (hi : mergedOf blk E F i = C) (hj : mergedOf blk E F j = C),
      H.Reachable ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i j p
    induction p with
    | nil => intro hi hj; exact Reachable.refl _
    | @cons i j k hij p ih =>
      intro hi hk
      have hj : mergedOf blk E F j = C := (ConnectedComponent.sound hij.reachable).symm.trans hi
      exact (hstep hi hj hij).trans (ih hj hk)
  have hne : Nonempty {i | mergedOf blk E F i = C} := by
    obtain ⟨i, hi⟩ := C.exists_rep
    exact ⟨⟨i, hi⟩⟩
  refine ⟨fun i j => ?_⟩
  obtain ⟨p⟩ := ConnectedComponent.exact (i.property.trans j.property.symm)
  exact hw i j p i.property j.property

end MultipoleBKT.Limits.RouteDirect

end
