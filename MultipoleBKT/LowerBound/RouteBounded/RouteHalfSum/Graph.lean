/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.ComponentBound
public import MultipoleBKT.Limits.RouteBase.Activity
public import MultipoleBKT.Limits.RouteOdd.Forest

/-!
# Translating the half-sum ear trees to relative trees

(A.30) in the proof of Lemma A.5, applied in proof of Proposition 4.23.
The edges remain label edges while their endpoints are mapped to blocks.
The ear construction therefore retains parallel quotient edges until deletion.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded.RouteHalfSum

open Finset SimpleGraph Limits
open UpperBound.BoundedUpper
open scoped Classical NNReal

/-- The endpoint graph on blocks is the quotient graph. -/
theorem nodeGraph_eq_quotient {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)
    (G : SimpleGraph (Y.biUnion id)) :
    nodeGraph (Sym2.map (Limits.blockOf Y)) G.edgeFinset = quotientGraph Y G := by
  ext S T
  rw [nodeGraph_adj, quotientGraph_eq hY, blockQuotient_adj]
  have hb (i : Y.biUnion id) : Limits.blockOf Y i = MultipoleBKT.blockOf hY i :=
    Limits.blockOf_eq hY (MultipoleBKT.blockOf hY i).2 (MultipoleBKT.mem_blockOf hY i)
  constructor
  · rintro ⟨hne, e, he, hend⟩
    induction e using Sym2.ind with
    | h i j =>
      simp only [Sym2.map_mk, hb] at hend
      rcases Sym2.eq_iff.1 hend with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact ⟨hne, i, j, hi, hj, mem_edgeFinset.1 he⟩
      · exact ⟨hne, j, i, hj, hi, (mem_edgeFinset.1 he).symm⟩
  · rintro ⟨hne, i, j, hi, hj, hij⟩
    exact ⟨hne, s(i, j), mem_edgeFinset.2 hij, by simp [hb, hi, hj]⟩

/-- A subfamily of label edges has exactly its given edge finset. -/
theorem edgeFinset_from_subset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {F : Finset (Sym2 V)} (hF : F ⊆ G.edgeFinset)
    {inst : Fintype (fromEdgeSet (F : Set (Sym2 V))).edgeSet} :
    @SimpleGraph.edgeFinset V (fromEdgeSet (F : Set (Sym2 V))) inst = F := by
  ext e
  induction e using Sym2.ind with
  | h i j =>
    simp only [mem_edgeFinset, mem_edgeSet, fromEdgeSet_adj, Finset.mem_coe]
    exact ⟨And.left, fun he => ⟨he, (mem_edgeFinset.1 (hF he)).ne⟩⟩

/-- The cardinality and connectivity supplied by ear deletion give a relative tree. -/
theorem isRelTree_of_ear_edges {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)
    {G : SimpleGraph (Y.biUnion id)} (hG : IsRelConnected Y G)
    {F : Finset (Sym2 (Y.biUnion id))} (hFG : F ⊆ G.edgeFinset)
    (root : Y) (hr : ∀ S, (nodeGraph (Sym2.map (Limits.blockOf Y)) F).Reachable root S)
    (hc : F.card + 1 = Fintype.card Y) :
    IsRelTree Y (fromEdgeSet (F : Set (Sym2 (Y.biUnion id)))) := by
  let T := fromEdgeSet (F : Set (Sym2 (Y.biUnion id)))
  have heq : T.edgeFinset = F := edgeFinset_from_subset hFG
  have hTG : T ≤ G := by
    intro i j hij
    have hi : s(i, j) ∈ T.edgeFinset := by simpa using hij
    have : s(i, j) ∈ G.edgeFinset := hFG (heq ▸ hi)
    simpa using this
  have htree : (quotientGraph Y T).IsTree := by
    rw [← nodeGraph_eq_quotient hY T]
    convert nodeGraph_isTree_of_card (Sym2.map (Limits.blockOf Y)) F root hr hc using 1
    exact congrArg (nodeGraph (Sym2.map (Limits.blockOf Y))) (edgeFinset_from_subset hFG)
  have hT₀ : IsRelTree₀ Y T := (isRelTree₀_iff_card hY).2
    ⟨hTG.trans hG.1, htree, by
      rw [Nat.card_eq_fintype_card, ← edgeFinset_card, heq]
      simpa only [Fintype.card_coe] using hc⟩
  rcases hT₀ with hT | ⟨hcard, -⟩
  · exact hT
  · exact False.elim ((isRelConnected_iff.1 hG).2 hcard)

/-- The finite minimum tail is bounded by the maximal-distance tail.
The radius is positive, including when the retained edge family is empty. -/
theorem globalTail_le_treeTail {V : Type*} [Fintype V] [DecidableEq V]
    (d : Sym2 V → ℝ) (hd : ∀ e, 0 ≤ d e) (T : SimpleGraph V)
    {R : ℝ} (hR : 0 < R) :
    globalTail R d T.edgeFinset ≤ treeTail d T R := by
  by_cases hsmall : ((T.edgeFinset.sup fun e => (d e).toNNReal : ℝ≥0) : ℝ) ≤ R
  · simpa only [treeTail, max_eq_right hsmall, div_self hR.ne', one_pow] using
      globalTail_le_one R d T.edgeFinset
  · have hsup : 0 < ((T.edgeFinset.sup fun e => (d e).toNNReal : ℝ≥0) : ℝ) :=
      hR.trans (lt_of_not_ge hsmall)
    have hne : T.edgeFinset.Nonempty := by
      by_contra hn
      simp [not_nonempty_iff_eq_empty.1 hn] at hsup
    obtain ⟨e, he, hm⟩ := exists_mem_eq_sup T.edgeFinset hne (fun e => (d e).toNNReal)
    have hb := (globalTail_le (R := R) (d := d) he).trans (min_le_right _ _)
    unfold treeTail
    rw [hm, Real.coe_toNNReal _ (hd e)]
    have hlarge : R ≤ d e := by
      rw [hm, Real.coe_toNNReal _ (hd e)] at hsmall
      exact (lt_of_not_ge hsmall).le
    simpa only [max_eq_left hlarge, div_pow] using hb

end MultipoleBKT.LowerBound.RouteBounded.RouteHalfSum

end
