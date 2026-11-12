/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.MixedIntegral
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ClusterOmitted

/-!
# Transporting the original single odd-family tail

See omitted domain
and case F in the proof of Lemma A.7. The tail on
the natural-label edge family is exactly the tail on its lifted family.
It remains one maximum tail after transport.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases
open scoped Classical ENNReal

variable {X Y : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- Forgetting the ambient subtype after lifting a tree recovers its original edges. -/
theorem component_edges_image (hYX : Y ⊆ X) (T : SimpleGraph (Y.biUnion id)) :
    ((graphOf (X.biUnion id) (edgesOf T)).edgeFinset.image (Sym2.map Subtype.val)) =
      T.edgeFinset.image (Sym2.map Subtype.val) := by
  have hs := (edgesOf_subset_pairsOn T).trans
    (pairsOn_mono (biUnion_subset_biUnion_of_subset_left id hYX))
  have he : (graphOf (X.biUnion id) (edgesOf T)).edgeFinset = symOf (X.biUnion id) (edgesOf T) :=
    evenEdges_eq_symOf _ hs
  rw [he]
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.1 he
    obtain ⟨i,j,hij,hp,rfl⟩ := mem_symOf.1 hf
    obtain ⟨hi,hj,-,hadj⟩ := mem_edgesOf.1 hp
    exact mem_image.2 ⟨s(⟨i,hi⟩,⟨j,hj⟩),mem_edgeFinset.2 hadj,rfl⟩
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.1 he
    induction f using Sym2.ind with
    | h i j =>
      have hadj := mem_edgeFinset.1 hf
      have hne : i.val ≠ j.val := fun he => hadj.ne (Subtype.ext he)
      let a : X.biUnion id := componentLabel hYX i
      let b : X.biUnion id := componentLabel hYX j
      rcases lt_or_gt_of_ne hne with hij | hji
      · have hp : (i.val,j.val) ∈ edgesOf T := mem_edgesOf.2 ⟨i.property,j.property,hij,hadj⟩
        exact mem_image.2 ⟨s(a,b),mem_symOf.2 ⟨a,b,hij,hp,rfl⟩,rfl⟩
      · have hp : (j.val,i.val) ∈ edgesOf T := mem_edgesOf.2 ⟨j.property,i.property,hji,hadj.symm⟩
        exact mem_image.2 ⟨s(b,a),mem_symOf.2 ⟨b,a,hji,hp,rfl⟩,by simp only [Sym2.map_mk]; exact Sym2.eq_swap⟩

/-- the complete edge carrier is the natural-label image of the ambient odd forest. -/
theorem oddEdges_image {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} (F : OddFamily hX hOX hpar r) :
    (oddEdges F).image (Sym2.map Subtype.val) = F.edges := by
  unfold oddEdges OddFamily.edges
  rw [Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro Y _
  exact component_edges_image (subset_of_mem_relComponents (oddComponents_subset O Y.property)) (F.tree Y)

/-- The global tail is transported exactly, with its quadratic exponent unchanged. -/
theorem oddFamily_globalTail {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} (F : OddFamily hX hOX hpar r)
    (R : ℝ) (d : Sym2 ℕ → ℝ) :
    globalTail R d F.edges = globalTail R (RouteCases.componentEdge d) (oddEdges F) := by
  rw [← oddEdges_image F,globalTail_image]
  rfl

end MultipoleBKT.ExpansionK.RouteSpatial

end
