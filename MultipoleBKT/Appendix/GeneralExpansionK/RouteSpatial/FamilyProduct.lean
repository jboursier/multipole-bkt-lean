/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.SourceRadii
public import MultipoleBKT.UpperBound.BoundedUpper.LemmaA6Bridge

/-!
# The dependent odd-family product on the ambient labels

See Lemma A.7. The tree products are transported
without losing a component or a surplus support factor.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ UpperBound.BoundedUpper BoundedLowerEps
open scoped Classical

variable {X Y : Finset (Finset ℕ)}

/-- An edge product on a component is the product on its lifted ambient graph. -/
theorem component_edge_product (hYX : Y ⊆ X)
    (T : SimpleGraph (Y.biUnion id)) (f : Sym2 ℕ → ℝ) :
    (∏ e ∈ T.edgeFinset, RouteCases.componentEdge f e) =
      ∏ e ∈ (graphOf (X.biUnion id) (edgesOf T)).edgeFinset,
        RouteCases.componentEdge f e := by
  have hs : edgesOf T ⊆ pairsOn (X.biUnion id) :=
    (edgesOf_subset_pairsOn T).trans (pairsOn_mono
      (biUnion_subset_biUnion_of_subset_left id hYX))
  have h₁ := prod_graphPairs T (fun i j => f s(i,j)) (fun i j => congrArg f Sym2.eq_swap)
  rw [graphPairs_eq_edgesOf] at h₁
  have h₂ := UpperBound.BoundedUpper.prod_pairs_eq_prod_edgeFinset hs (fun i j => f s(i,j))
    (fun i j => congrArg f Sym2.eq_swap)
  refine (prod_congr rfl (fun e _ => ?_)).trans ((h₁.symm.trans h₂).trans
    (prod_congr rfl (fun e _ => ?_))) <;> induction e using Sym2.ind <;> rfl

/-- Lift the selected odd-tree edge sets, retaining their component index. -/
noncomputable def oddEdges {O : Finset (ℕ × ℕ)} {hX : IsSubpartition X}
    {hOX : O ⊆ interPairs X} {hpar : IsParityPair X O ∅} {r : ℕ → ℝ}
    (F : RouteCases.OddFamily hX hOX hpar r) : Finset (Sym2 (X.biUnion id)) :=
  univ.biUnion fun Y : oddComponents X O =>
    (graphOf (X.biUnion id) (edgesOf (F.tree Y))).edgeFinset

/-- The lifted component edge sets are disjoint because the components have
disjoint label carriers. -/
theorem oddEdges_disjoint {O : Finset (ℕ × ℕ)} {hX : IsSubpartition X}
    {hOX : O ⊆ interPairs X} {hpar : IsParityPair X O ∅} {r : ℕ → ℝ}
    (F : RouteCases.OddFamily hX hOX hpar r) :
    ((univ : Finset (oddComponents X O)) : Set (oddComponents X O)).PairwiseDisjoint
      (fun Y => (graphOf (X.biUnion id) (edgesOf (F.tree Y))).edgeFinset) := by
  intro Y _ Z _ hne
  apply Finset.disjoint_left.2
  intro e he hf
  induction e using Sym2.ind with
  | h i j =>
    have hmem (Y : oddComponents X O)
        (he : s(i,j) ∈ (graphOf (X.biUnion id) (edgesOf (F.tree Y))).edgeFinset) :
        i.val ∈ Y.val.biUnion id := by
      have hh := mem_edgeFinset.1 he
      change (Multipole.graphOf (X.biUnion id) (edgesOf (F.tree Y))).Adj i j at hh
      rw [Multipole.graphOf, fromRel_adj] at hh
      rcases hh.2 with h | h
      · exact (mem_pairsOn.1 (edgesOf_subset_pairsOn (F.tree Y) h)).1
      · exact (mem_pairsOn.1 (edgesOf_subset_pairsOn (F.tree Y) h)).2.1
    exact Finset.disjoint_left.1 (UpperBound.BoundedUpper.disjoint_biUnion_of_disjoint hX
      (subset_of_mem_relComponents (oddComponents_subset O Y.property))
      (subset_of_mem_relComponents (oddComponents_subset O Z.property))
      (disjoint_of_mem_relComponents hX (oddComponents_subset O Y.property)
        (oddComponents_subset O Z.property) (fun h => hne (Subtype.ext h))))
      (hmem Y he) (hmem Z hf)

/-- the complete weight is exactly the transported odd product times its
regularized radius prefactor. This is an equality on every configuration. -/
theorem oddFamily_weight_eq {O : Finset (ℕ × ℕ)} {hX : IsSubpartition X}
    {hOX : O ⊆ interPairs X} {hpar : IsParityPair X O ∅} {r : ℕ → ℝ}
    (F : RouteCases.OddFamily hX hOX hpar r) (d c : Sym2 ℕ → ℝ) :
    F.weight d c = oddPrefactor F *
      ∏ e ∈ oddEdges F, keptWeight (RouteCases.componentEdge d) (RouteCases.componentEdge c) e := by
  unfold RouteCases.OddFamily.weight
  rw [prod_mul_distrib]
  congr 1
  rw [oddEdges, prod_biUnion (oddEdges_disjoint F)]
  apply prod_congr rfl
  intro Y _
  have hYX := subset_of_mem_relComponents (oddComponents_subset O Y.property)
  have hs := component_edge_product hYX (F.tree Y) (keptWeight d c)
  simpa only [RouteCases.componentEdge, Function.comp_apply, keptWeight] using hs

/-- The component enumeration in the forest lift has exactly the same odd
edge set as the dependent product above. -/
theorem oddEdges_enum {O : Finset (ℕ × ℕ)} {hX : IsSubpartition X}
    {hOX : O ⊆ interPairs X} {hpar : IsParityPair X O ∅} {r : ℕ → ℝ}
    (F : RouteCases.OddFamily hX hOX hpar r)
    (e : Fin (Fintype.card (oddComponents X O)) ≃ oddComponents X O) :
    (univ.biUnion fun l => (graphOf (X.biUnion id) (edgesOf (F.tree (e l)))).edgeFinset) = oddEdges F := by
  ext a
  simp only [oddEdges, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨l,hl⟩
    exact ⟨e l,hl⟩
  · rintro ⟨Y,hY⟩
    obtain ⟨l,rfl⟩ := e.surjective Y
    exact ⟨l,hY⟩

/-- Structural conclusions for every fixed near-tree choice. These permit
splitting all three profile products without counting an edge twice. -/
theorem source_family_structure {O : Finset (ℕ × ℕ)} (hX : IsSubpartition X)
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)]
    (r : ℕ → ℝ) (F : RouteCases.OddFamily hX hOX hpar r)
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (Q : NearTreeFamily (Limits.blockOf X)) :
    let N := nearForest (Limits.blockOf X) (fun S => (Q S).val)
    let E := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
    (fromEdgeSet ((N ∪ (oddEdges F ∪ E) : Finset (Sym2 (X.biUnion id))) :
      Set (Sym2 (X.biUnion id)))).IsTree ∧
    (fromEdgeSet ((N ∪ (oddEdges F ∪ E) : Finset (Sym2 (X.biUnion id))) :
      Set (Sym2 (X.biUnion id)))).edgeFinset = N ∪ (oddEdges F ∪ E) ∧
    Disjoint N (oddEdges F ∪ E) ∧ Disjoint (oddEdges F) E ∧
    (oddEdges F).card + E.card + 1 = Fintype.card X := by
  let e := (Fintype.equivFin (oddComponents X O)).symm
  let Xs := fun l => (e l).val
  let Ta := fun l => edgesOf (F.tree (e l))
  have hXs : univ.image Xs = oddComponents X O := by
    ext Y
    constructor
    · intro hY
      obtain ⟨l,-,rfl⟩ := mem_image.1 hY
      exact (e l).property
    · intro hY
      obtain ⟨l,hl⟩ := e.surjective ⟨Y,hY⟩
      exact mem_image.2 ⟨l,mem_univ _,congrArg Subtype.val hl⟩
  have hXsX : ∀ l, Xs l ⊆ X := fun l =>
    subset_of_mem_relComponents (oddComponents_subset O (e l).property)
  have hdis : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l') := by
    intro l l' hne
    exact disjoint_of_mem_relComponents hX (oddComponents_subset O (e l).property)
      (oddComponents_subset O (e l').property) (fun h => hne (e.injective (Subtype.ext h)))
  have hTa : ∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf := fun l =>
    mem_image.2 ⟨F.tree (e l),mem_relTrees.2 (F.tree_spec (e l)).1,rfl⟩
  have hTb' : edgesOf Tb ∈ (relTrees₀ (coarsen X (univ.image Xs))).image edgesOf := by
    rw [hXs]
    exact mem_image.2 ⟨Tb,mem_relTrees₀.2 hTb,rfl⟩
  obtain ⟨-,-,-,hinter,hconn,hcard⟩ := trees_structure hX hXsX hdis hTa hTb'
  have hcount : (oddEdges F).card + (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset.card + 1 ≤ Fintype.card X := by
    have ha := card_biUnion_le (s := (univ : Finset (Fin (Fintype.card (oddComponents X O)))))
      (t := fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset)
    change _ ≤ ∑ l, (graphOf (X.biUnion id) (Ta l)).edgeFinset.card at ha
    rw [show (univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) = oddEdges F from oddEdges_enum F e] at ha
    omega
  simp_rw [show (univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) = oddEdges F from oddEdges_enum F e] at hinter hconn
  exact retained_tree (Limits.blockOf X) (fun S => (Q S).val) (fun S => (Q S).property)
    (oddEdges F) (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset hinter hconn hcount

end MultipoleBKT.ExpansionK.RouteSpatial

end
