/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ComponentBounds
public import MultipoleBKT.UpperBound.BoundedUpper.Components

/-!
# Odd components and skeletons on the original label sets

See Step 2 of
the proof of Lemma A.7. Restrict the odd graph to each nontrivial
relative component. Its parity is inherited from the original graph, so its
minimal bridgeless skeleton is defined. The components are connected by a
separate even tree on the coarse subpartition, including isolated blocks.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Multipole Hierarchical Parity UpperBound.BoundedUpper SetPartition

variable {X : Finset (Finset ℕ)}

/-- Every nontrivial odd component is Eulerian and connected relative to its own
subpartition. This justifies selecting each minimal skeleton independently. -/
theorem source_odd_component_eulerian (hX : IsSubpartition X) {O : Finset (ℕ × ℕ)}
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅)
    {Y : Finset (Finset ℕ)} (hY : Y ∈ oddComponents X O) :
    IsSubpartition Y ∧ IsRelEulerianConnected Y (pairGraph (Y.biUnion id) (O ∩ interPairs Y)) := by
  have hYc := (mem_oddComponents.1 hY).1
  have hYs := isSubpartition_mono hX (subset_of_mem_relComponents hYc)
  refine ⟨hYs, isRelConnected_pairGraph hX hOX hY, pairGraph_le_interEdges inter_subset_right, ?_⟩
  have hOff := isRelEulerianOff_pairGraph hX hOX hpar hYc
  intro S hS
  have hp := hOff.2 S hS
  have hm : marksOn Y ∅ = ∅ := by
    classical
    ext i
    simp [marksOn]
  simpa only [hm, inter_empty, card_empty, add_zero] using hp

/-- The actual original skeleton of an odd component is the fixed lexicographic
minimal skeleton. The paper's edge family `E₁,l′` is `O ∩ interPairs Y`. -/
noncomputable def sourceOddSkeleton (hX : IsSubpartition X) {O : Finset (ℕ × ℕ)}
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅)
    (Y : oddComponents X O) : SimpleGraph (Y.val.biUnion id) :=
  oddSkeleton (source_odd_component_eulerian hX hOX hpar Y.property).1
    (pairGraph _ (O ∩ interPairs Y.val))
    (source_odd_component_eulerian hX hOX hpar Y.property).2

/-- The separate odd components, their minimal skeletons and the connecting
coarse even tree, in the paper's label representation. -/
theorem source_skeletons_and_even_tree (hX : IsSubpartition X) {E O : Finset (ℕ × ℕ)}
    (hE : E ∈ relEdgeSets₀ X) (hOE : O ⊆ E) (hpar : IsParityPair X O ∅) :
    ((oddComponents X O : Set (Finset (Finset ℕ))).PairwiseDisjoint id) ∧
      (∀ Y : oddComponents X O,
        sourceOddSkeleton hX (hOE.trans (mem_relEdgeSets₀.1 hE).1) hpar Y ≤
          pairGraph (Y.val.biUnion id) (O ∩ interPairs Y.val) ∧
        IsRelMinTwoEdgeConnected Y.val
          (sourceOddSkeleton hX (hOE.trans (mem_relEdgeSets₀.1 hE).1) hpar Y)) ∧
      ∃ Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id),
        IsRelTree₀ (coarsen X (oddComponents X O)) Tb ∧ graphPairs Tb ⊆ E \ O := by
  refine ⟨pairwiseDisjoint_oddComponents hX O, ?_, ?_⟩
  · intro Y
    exact oddSkeleton_spec (source_odd_component_eulerian hX
      (hOE.trans (mem_relEdgeSets₀.1 hE).1) hpar Y.property).1
      (source_odd_component_eulerian hX (hOE.trans (mem_relEdgeSets₀.1 hE).1) hpar Y.property).2
  · exact exists_isRelTree₀_even hX hE hOE rfl

open scoped Classical in
/-- The case-D pointwise bound on the component selected by the actual original odd graph. This entry point constructs its strict marked tree internally. -/
theorem source_caseD_pointwise (hX : IsSubpartition X) {O : Finset (ℕ × ℕ)}
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅)
    (Y : oddComponents X O) {x y : Y.val.biUnion id}
    (hxy : (sourceOddSkeleton hX hOX hpar Y).Adj x y)
    (r : Y.val.biUnion id → ℝ) (d c : Sym2 (Y.val.biUnion id) → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hfar : ∀ i j, (pairGraph (Y.val.biUnion id) (O ∩ interPairs Y.val)).Adj i j →
      min (r i) (r j) ≤ d s(i, j)) :
    let hY := (source_odd_component_eulerian hX hOX hpar Y.property).1
    ∃ T : SimpleGraph (Y.val.biUnion id), IsRelTree Y.val T ∧ T ≤ sourceOddSkeleton hX hOX hpar Y ∧
      s(x, y) ∉ T.edgeSet ∧
      r x * r y * (∏ e ∈ (pairGraph (Y.val.biUnion id) (O ∩ interPairs Y.val)).edgeFinset.erase s(x, y),
        Peeling.absWeight r d c e) ≤
        (∏ S : Y.val, Peeling.blockRadius hY r S ^ 2) * ∏ e ∈ T.edgeFinset, Peeling.keptWeight d c e := by
  dsimp only
  exact marked_odd_component (source_odd_component_eulerian hX hOX hpar Y.property).1
    (source_odd_component_eulerian hX hOX hpar Y.property).2 r d c hr hd hc hc1 hfar hxy

end MultipoleBKT.ExpansionK.RouteCases

end
