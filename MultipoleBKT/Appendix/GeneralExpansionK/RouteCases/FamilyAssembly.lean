/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ComponentFamily
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SubsetTransport

/-!
# Skeleton products and complete component families

See (A.55)–(A.58)
and the conclusion after (A.60). Ordinary skeletons
are reduced simultaneously. The marked component retains its full radius
product, while the other components omit their maximal-radius roots.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Peeling Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

open scoped Classical in
/-- A family of relative odd trees and their maximal-radius roots. This records
only graph and radius data, never a desired product inequality. -/
structure OddFamily (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) where
  root : (Y : oddComponents X O) → Y.val.biUnion id
  tree : (Y : oddComponents X O) → SimpleGraph (Y.val.biUnion id)
  tree_spec : ∀ Y, IsRelTree Y.val (tree Y) ∧ tree Y ≤ sourceOddSkeleton hX hOX hpar Y
  root_max : ∀ Y (i : Y.val.biUnion id), r i ≤ r (root Y)

open scoped Classical in
/-- The ordinary product to integrate, with one omitted maximal block per
component and all retained far/short factors inside the kept weights. -/
noncomputable def OddFamily.weight {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} (F : OddFamily hX hOX hpar r)
    (d c : Sym2 ℕ → ℝ) : ℝ :=
  ∏ Y : oddComponents X O,
    (∏ S ∈ univ.erase (MultipoleBKT.blockOf
        (source_odd_component_eulerian hX hOX hpar Y.property).1 (F.root Y)),
      blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
        (fun i : Y.val.biUnion id => r i) S ^ 2) *
      ∏ e ∈ (F.tree Y).edgeFinset, keptWeight (componentEdge d) (componentEdge c) e

open scoped Classical in
/-- The selected skeleton union factors exactly over its separate components. -/
theorem source_skeleton_product (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (f : Sym2 ℕ → ℝ) :
    (∏ p ∈ sourceSkeletonEdges hX hOX hpar, f s(p.1,p.2)) =
      ∏ Y : oddComponents X O,
        ∏ e ∈ (sourceOddSkeleton hX hOX hpar Y).edgeFinset, componentEdge f e := by
  unfold sourceSkeletonEdges
  rw [prod_biUnion]
  · apply prod_congr rfl
    intro Y hY
    refine (prod_graphPairs (sourceOddSkeleton hX hOX hpar Y) (fun i j => f s(i,j))
      (fun i j => congrArg f Sym2.eq_swap)).trans ?_
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with
    | h i j => rfl
  · intro Y _ Z _ hne
    have hd := UpperBound.BoundedUpper.disjoint_biUnion_of_disjoint hX
      (subset_of_mem_relComponents (oddComponents_subset O Y.property))
      (subset_of_mem_relComponents (oddComponents_subset O Z.property))
      (disjoint_of_mem_relComponents hX (oddComponents_subset O Y.property)
        (oddComponents_subset O Z.property) (fun h => hne (Subtype.ext h)))
    apply Finset.disjoint_left.2
    intro p hp hq
    exact Finset.disjoint_left.1 hd
      (mem_pairsOn.1 (graphPairs_subset_pairsOn _ hp)).1
      (mem_pairsOn.1 (graphPairs_subset_pairsOn _ hq)).1

open scoped Classical in
/-- Simultaneous ordinary tree reduction of precisely the selected skeletons.
This stronger form also applies after a surplus edge has supplied its gain. -/
theorem source_skeleton_family (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1) :
    ∃ F : OddFamily hX hOX hpar r,
      (∏ p ∈ sourceSkeletonEdges hX hOX hpar, absWeight r d c s(p.1,p.2)) ≤ F.weight d c := by
  have hall : ∀ Y : oddComponents X O,
      ∃ (v : Y.val.biUnion id) (T : SimpleGraph (Y.val.biUnion id)),
      IsRelTree Y.val T ∧ T ≤ sourceOddSkeleton hX hOX hpar Y ∧
      (∀ i : Y.val.biUnion id, r i ≤ r v) ∧
      (∏ e ∈ (sourceOddSkeleton hX hOX hpar Y).edgeFinset,
        absWeight (fun i : Y.val.biUnion id => r i) (componentEdge d) (componentEdge c) e) ≤
        (∏ S ∈ univ.erase (MultipoleBKT.blockOf
          (source_odd_component_eulerian hX hOX hpar Y.property).1 v),
          blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
            (fun i : Y.val.biUnion id => r i) S ^ 2) *
          ∏ e ∈ T.edgeFinset, keptWeight (componentEdge d) (componentEdge c) e := by
    intro Y
    exact ordinary_component (source_odd_component_eulerian hX hOX hpar Y.property).1
      (source_odd_component_eulerian hX hOX hpar Y.property).2
      (fun i : Y.val.biUnion id => r i) (componentEdge d) (componentEdge c)
      (fun i => hr i) (fun e => hd _) (fun e => hc _) (fun e => hc1 _)
  choose v T hT hTK hm hb using hall
  let F : OddFamily hX hOX hpar r := ⟨v,T,fun Y => ⟨hT Y,hTK Y⟩,hm⟩
  refine ⟨F, ?_⟩
  rw [source_skeleton_product hX hOX hpar]
  apply prod_le_prod₀
  · intro Y _
    exact prod_nonneg fun e _ => absWeight_nonneg hr hd hc _
  · intro Y _
    simpa only [componentEdge, Function.comp_apply, ← absWeight_component] using hb Y

open scoped Classical in
/-- Removing an edge outside the skeleton does not change any retained factor.
This is the geometric product step of case B. -/
theorem source_surplus_skeleton (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2))
    {em : ℕ × ℕ} (hem : em ∉ sourceSkeletonEdges hX hOX hpar) :
    (∏ p ∈ O.erase em, absWeight r d c s(p.1,p.2)) ≤
      ∏ p ∈ sourceSkeletonEdges hX hOX hpar, absWeight r d c s(p.1,p.2) := by
  have hs : sourceSkeletonEdges hX hOX hpar ⊆ O.erase em := fun p hp =>
    mem_erase.2 ⟨fun h => hem (h ▸ hp), sourceSkeletonEdges_subset hX hOX hpar hp⟩
  rw [← prod_sdiff hs]
  exact mul_le_of_le_one_left (prod_nonneg fun _ _ => absWeight_nonneg hr hd hc _)
    (prod_le_one₀ (fun _ _ => absWeight_nonneg hr hd hc _) (fun p hp =>
      absWeight_le_one_of_far hr hd hc hc1 (hfar p (mem_of_mem_erase (mem_sdiff.1 hp).1))))

end MultipoleBKT.ExpansionK.RouteCases

end
