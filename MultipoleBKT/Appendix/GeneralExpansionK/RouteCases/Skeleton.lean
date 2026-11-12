/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.MarkedBound
public import MultipoleBKT.Limits.RouteOdd.Majorant

/-!
# The minimal odd skeletons and their marked trees

See Step 2 of
the proof of Lemma A.7 and case D.
Each nontrivial odd component is treated relative to its own subpartition.
Its skeleton is the lexicographically selected minimal bridgeless subgraph.
The marked tree is obtained from strict ears with the marked edge first.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Peeling

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
variable {E : SimpleGraph (X.biUnion id)}

/-- The minimal odd skeleton is the fixed lexicographic selector. In particular,
its choice precedes the inspection of the five error subsets. -/
noncomputable def oddSkeleton (E : SimpleGraph (X.biUnion id))
    (hE : Parity.IsRelEulerianConnected X E) : SimpleGraph (X.biUnion id) :=
  peeledSkeleton E (Parity.lemma_4_37 hX hE)

/-- The selected skeleton is contained in the odd component and is minimally
2-edge-connected relative to the component's own subpartition. -/
theorem oddSkeleton_spec (hE : Parity.IsRelEulerianConnected X E) :
    oddSkeleton hX E hE ≤ E ∧
      Parity.IsRelMinTwoEdgeConnected X (oddSkeleton hX E hE) := by
  have hs := peeledSkeleton_spec E (Parity.lemma_4_37 hX hE)
  exact ⟨hs.1, hs.isRelMinTwoEdgeConnected hX⟩

open scoped Classical in
/-- The actual tree and (A.60) for the chosen skeleton of an odd component.
No path avoiding the mark is used to choose this tree. -/
theorem caseD_component (hE : Parity.IsRelEulerianConnected X E)
    {x y : X.biUnion id} (hxy : (oddSkeleton hX E hE).Adj x y)
    (r : X.biUnion id → ℝ) (ρ : X → ℝ) (d c : Sym2 (X.biUnion id) → ℝ)
    (hr : ∀ v, 0 ≤ r v) (hρ : ∀ S, 0 ≤ ρ S)
    (hrρ : ∀ v, r v ≤ ρ (MultipoleBKT.blockOf hX v))
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1) :
    ∃ (P : Ear (X.biUnion id)) (Qs : List (Ear (X.biUnion id) × _)) (T : SimpleGraph (X.biUnion id)),
      MarkedEarData (MultipoleBKT.blockOf hX) (oddSkeleton hX E hE) r d
        (univ.sup' (by exact ⟨x, mem_univ _⟩) r) x y P Qs ∧
      T = keptGraph (oddSkeleton hX E hE) ((P, (x, y)) :: Qs) ∧
      IsRelTree X T ∧ T ≤ oddSkeleton hX E hE ∧ s(x, y) ∉ T.edgeSet ∧
      r x * r y * (∏ e ∈ (oddSkeleton hX E hE).edgeFinset.erase s(x, y), absWeight r d c e) ≤
        (∏ S, ρ S ^ 2) * ∏ e ∈ T.edgeFinset, keptWeight d c e := by
  let K := oddSkeleton hX E hE
  have hmin := (oddSkeleton_spec hX hE).2
  obtain ⟨hinter, -, hminOn⟩ := (isRelMinTwoEdgeConnected_iff_on hX).1 hmin
  rw [interEdges_eq hX] at hinter
  let R := univ.sup' (by exact ⟨x, mem_univ _⟩) r
  obtain ⟨P, Qs, hm⟩ := exists_marked_ears (MultipoleBKT.blockOf_surjective hX) hinter hminOn hxy r d R
  let T := keptGraph K ((P, (x, y)) :: Qs)
  have hdecomp : IsStrictEarDecomp hX K (MultipoleBKT.blockOf hX x)
      (((P, (x, y)) :: Qs).map Prod.fst) := hm.decomp
  have htree : IsRelTree X T := hdecomp.isRelTree_keptGraph
    ((isRelMinTwoEdgeConnected_iff_on hX).1 hmin).1 hm.isRemoval
  refine ⟨P, Qs, T, hm, rfl, htree, deleteEdges_le _, hm.tree_facts.2.2, ?_⟩
  exact marked_skeleton_product hm hr hρ hrρ hd hc hc1 (fun v => le_sup' r (mem_univ v))

open scoped Classical in
/-- The ordinary tree in every unmarked odd component is the prescribed peeling
of its selected skeleton. The factors `g ≤ 1` are dropped after the ear estimate. -/
theorem ordinary_component (hE : Parity.IsRelEulerianConnected X E)
    (r : X.biUnion id → ℝ) (d c : Sym2 (X.biUnion id) → ℝ)
    (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e)
    (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1) :
    ∃ (v : X.biUnion id) (T : SimpleGraph (X.biUnion id)),
      IsRelTree X T ∧ T ≤ oddSkeleton hX E hE ∧
      (∀ i, r i ≤ r v) ∧
      ∏ e ∈ (oddSkeleton hX E hE).edgeFinset, absWeight r d c e ≤
        (∏ S ∈ univ.erase (MultipoleBKT.blockOf hX v), blockRadius hX r S ^ 2) *
          ∏ e ∈ T.edgeFinset, keptWeight d c e := by
  obtain ⟨v, e₀, Qs, hp⟩ := exists_isPeeling (hX := hX) (oddSkeleton_spec hX hE).2 r d
  have htree := hp.isRelTree ((isRelMinTwoEdgeConnected_iff_on hX).1 (oddSkeleton_spec hX hE).2).1
  refine ⟨v, keptGraph _ Qs, htree, deleteEdges_le _, hp.le_radius, ?_⟩
  have hbound := quadratic_estimate hp hr hd hc
  have hg := hp.prod_peelWeight_le_one hr hc hc1
  exact hbound.trans (mul_le_of_le_one_right
    (mul_nonneg (prod_nonneg fun S _ => sq_nonneg _) (prod_nonneg fun e _ => keptWeight_nonneg hc e)) hg)

end MultipoleBKT.ExpansionK.RouteCases

end
