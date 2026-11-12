/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SourceGraph
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.Expansion

/-!
# The five cases for the selected original skeletons and even tree

See Step 2 of
the proof of Lemma A.7. Select the minimal odd skeletons and
one even tree before inspecting the five error subsets. A retained odd mark
is localized in one selected component skeleton, where the prescribed strict-ear
construction applies. A retained even mark stays on the even tree.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)}

/-- The union `E₁″` of the minimal odd-component skeletons. -/
noncomputable def sourceSkeletonEdges (hX : IsSubpartition X) {O : Finset (ℕ × ℕ)}
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅) : Finset (ℕ × ℕ) :=
  univ.biUnion fun Y : oddComponents X O => graphPairs (sourceOddSkeleton hX hOX hpar Y)

/-- Every selected skeleton edge is an original odd edge. -/
theorem sourceSkeletonEdges_subset (hX : IsSubpartition X) {O : Finset (ℕ × ℕ)}
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅) :
    sourceSkeletonEdges hX hOX hpar ⊆ O := by
  intro e he
  obtain ⟨Y, -, he⟩ := mem_biUnion.1 he
  have hs := (oddSkeleton_spec (source_odd_component_eulerian hX hOX hpar Y.property).1
    (source_odd_component_eulerian hX hOX hpar Y.property).2).1
  have he' := graphPairs_mono hs he
  rw [graphPairs_pairGraph (inter_subset_right.trans interPairs_subset_pairsOn)] at he'
  exact (mem_inter.1 he').1

open scoped Classical in
/-- The five cases of the written proof, with their graphs already constructed.
Case D identifies the particular component skeleton containing the marked odd
edge. Case E retains the original marked even-tree edge. -/
theorem source_five_cases (hX : IsSubpartition X) {E O : Finset (ℕ × ℕ)}
    (hE : E ∈ relEdgeSets₀ X) (hOE : O ⊆ E) (hpar : IsParityPair X O ∅) :
    let hOX := hOE.trans (mem_relEdgeSets₀.1 hE).1
    ∃ Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id),
      IsRelTree₀ (coarsen X (oddComponents X O)) Tb ∧ graphPairs Tb ⊆ E \ O ∧
      ∀ P ∈ (fiveSubsets O (E \ O) (Multipole.intraPairs X) (X.biUnion id)).erase
          (∅, ∅, ∅, ∅, ∅),
        (P.2.2.1.Nonempty ∨ P.2.2.2.1.Nonempty ∨ P.2.2.2.2.Nonempty) ∨
          ((O \ sourceSkeletonEdges hX hOX hpar) ∩ P.1).Nonempty ∨
          (((E \ O) \ graphPairs Tb) ∩ P.2.1).Nonempty ∨
          (∃ Y : oddComponents X O, (graphPairs (sourceOddSkeleton hX hOX hpar Y) ∩ P.1).Nonempty) ∨
          (graphPairs Tb ∩ P.2.1).Nonempty := by
  dsimp only
  obtain ⟨-, -, Tb, hTb, hTbE⟩ := source_skeletons_and_even_tree hX hE hOE hpar
  refine ⟨Tb, hTb, hTbE, fun P hP => ?_⟩
  have hcase := five_cases_exhaustive O (E \ O) (Multipole.intraPairs X) (X.biUnion id)
    (sourceSkeletonEdges hX (hOE.trans (mem_relEdgeSets₀.1 hE).1) hpar) (graphPairs Tb) (by simpa only [mem_erase] using hP)
  rcases hcase with hA | hB | hC | hD | hE
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr (Or.inl hC))
  · obtain ⟨e, he⟩ := hD
    obtain ⟨heK, heP⟩ := mem_inter.1 he
    obtain ⟨Y, -, heY⟩ := mem_biUnion.1 heK
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Y, e, mem_inter.2 ⟨heY, heP⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hE)))

end MultipoleBKT.ExpansionK.RouteCases

end
