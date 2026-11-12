/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SourceTail
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.TreeFamilies

/-!
# Lifting the selected original forest to the dipole labels

See Lemma A.7, Step 3 of the proof of Lemma A.7. Near trees inside the multipoles join the selected odd
component trees and the coarse even tree into one tree on the original labels.
The argument applies also to the prescribed case-D tree.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Limits Peeling Multipole Hierarchical Parity UpperBound.BoundedUpper
open SmallIntegral SmallIntegral.RouteJ BoundedLowerEps

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

open scoped Classical in
/-- An enumeration of the selected component trees, together with linked near
trees, yields a tree on the original labels. The enumeration is bijective and
preserves each component's original tree. -/
theorem source_forest_lifting (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (F : OddFamily hX hOX hpar r)
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (M lam : ℝ) (c : X.biUnion id → ℂ × ℂ)
    (hB : ∀ S, ((nearGraph M lam c).induce {i | Limits.blockOf X i = S}).Connected)
    [Nonempty (X.biUnion id)] :
    ∃ (e : Fin (Fintype.card (oddComponents X O)) ≃ oddComponents X O)
      (R : NearTreeFamily (Limits.blockOf X)),
      (∀ i j, s(i,j) ∈ nearForest (Limits.blockOf X) (fun S => (R S).val) →
        MultipoleLinked M lam (c i) (c j)) ∧
      let A := univ.biUnion fun l => (graphOf (X.biUnion id) (edgesOf (F.tree (e l)))).edgeFinset
      let B := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
      (fromEdgeSet ((nearForest (Limits.blockOf X) (fun S => (R S).val) ∪ (A ∪ B) :
        Finset (Sym2 (X.biUnion id))) : Set (Sym2 (X.biUnion id)))).IsTree ∧
      A.card + B.card + 1 = X.card := by
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
  obtain ⟨-, -, -, hinter, hconn, hcount⟩ := trees_structure hX hXsX hdis hTa hTb'
  obtain ⟨R,hR⟩ := exists_linked_nearTreeFamily (Limits.blockOf X) M lam c hB
  obtain ⟨hTree,-,-,-,hcard⟩ := retained_tree (Limits.blockOf X) (fun S => (R S).val)
    (fun S => (R S).property) _ _ hinter hconn (by
      have hu := card_biUnion_le (s := (univ : Finset (Fin (Fintype.card (oddComponents X O)))))
        (t := fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset)
      omega)
  exact ⟨e,R,hR,hTree,by simpa only [Fintype.card_coe] using hcard⟩

end MultipoleBKT.ExpansionK.RouteCases

end
