/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Components
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SourceCases
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ModelExpansion

/-!
# Transport of near and far bonds to the connected original graph

See Step 2 of
the proof of Lemma A.7. Connectivity belongs to the union of the
near bonds and the far bonds. The original skeletons and coarse even tree
are constructed from that union, before inspecting any correction subsets.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Limits Multipole Hierarchical UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)}

/-- An actual label-edge set has the same block quotient in the two graph
representations. Near bonds are included in this identity. -/
theorem source_quotient_eq (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ interPairs X) :
    nodeGraph (Sym2.map (Limits.blockOf X)) (symOf (X.biUnion id) E) =
      quotientGraph X (pairGraph (X.biUnion id) E) := by
  classical
  ext S T
  constructor
  · intro h
    obtain ⟨hne, e, he, heq⟩ := nodeGraph_adj.1 h
    obtain ⟨i, j, hij, hp, rfl⟩ := mem_symOf.1 he
    simp only [Sym2.map_mk] at heq
    have hadj : (pairGraph _ E).Adj i j := pairGraph_adj.2 ⟨hij.ne, Or.inl hp⟩
    rw [quotientGraph, fromRel_adj]
    refine ⟨hne, ?_⟩
    rcases Sym2.eq_iff.1 heq with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exact Or.inl ⟨i, j, (Limits.blockOf_eq_iff hX i S).1 hi,
        (Limits.blockOf_eq_iff hX j T).1 hj, hadj⟩
    · exact Or.inr ⟨i, j, (Limits.blockOf_eq_iff hX i T).1 hi,
        (Limits.blockOf_eq_iff hX j S).1 hj, hadj⟩
  · intro h
    obtain ⟨hne, hrel⟩ := (fromRel_adj _ _ _).1 h
    have step : ∀ S T : X, S ≠ T →
        (∃ i j : X.biUnion id, (i : ℕ) ∈ (S : Finset ℕ) ∧
          (j : ℕ) ∈ (T : Finset ℕ) ∧ (pairGraph _ E).Adj i j) →
        (nodeGraph (Sym2.map (Limits.blockOf X)) (symOf (X.biUnion id) E)).Adj S T := by
      intro S T hne h
      obtain ⟨i, j, hi, hj, hij⟩ := h
      have hbi := (Limits.blockOf_eq_iff hX i S).2 hi
      have hbj := (Limits.blockOf_eq_iff hX j T).2 hj
      refine nodeGraph_adj.2 ⟨hne, s(i, j), ?_, by simp only [Sym2.map_mk, hbi, hbj]⟩
      rcases (pairGraph_adj.1 hij).2 with hp | hp
      · exact mem_symOf.2 ⟨i, j, (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hp))).2.2, hp, rfl⟩
      · exact mem_symOf.2 ⟨j, i, (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hp))).2.2, hp, Sym2.eq_swap⟩
    rcases hrel with hrel | hrel
    · exact step S T hne hrel
    · exact (step T S hne.symm hrel).symm

/-- Connected block data transport back to the connected original pair family.
This uses connectivity of the union supplied by near and far edges. -/
theorem source_graph_of_connected_blocks (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ interPairs X)
    (hconn : (nodeGraph (Sym2.map (Limits.blockOf X)) (symOf (X.biUnion id) E)).Connected) :
    E ∈ relEdgeSets₀ X := by
  classical
  rw [source_quotient_eq hX hE] at hconn
  have hc := (connected_sup_intraEdges_iff hX).2 hconn
  let G := pairGraph (X.biUnion id) E ⊔ MultipoleBKT.intraEdges X
  let K := edgeGraph (E ∪ Multipole.intraPairs X)
  let hm : G →g K :=
    { toFun := Subtype.val
      map_rel' := by
        intro i j hij
        have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij.ne (Subtype.ext h)
        refine edgeGraph_adj.2 ⟨hne, ?_⟩
        rcases hij with hij | hij
        · rcases (pairGraph_adj.1 hij).2 with hp | hp
          · exact Or.inl (mem_union_left _ hp)
          · exact Or.inr (mem_union_left _ hp)
        · rcases (intraEdges_adj hX).1 hij with ⟨-, heq⟩
          have hi := MultipoleBKT.mem_blockOf hX i
          have hj := heq ▸ MultipoleBKT.mem_blockOf hX j
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · exact Or.inl (mem_union_right _ (mem_intraPairs.2
              ⟨_, (MultipoleBKT.blockOf hX i).property, mem_pairsOn.2 ⟨hi, hj, hlt⟩⟩))
          · exact Or.inr (mem_union_right _ (mem_intraPairs.2
              ⟨_, (MultipoleBKT.blockOf hX i).property, mem_pairsOn.2 ⟨hj, hi, hlt⟩⟩)) }
  refine mem_relEdgeSets₀.2 ⟨hE, ?_, fun i hi j hj => ?_⟩
  · obtain ⟨i⟩ := hc.nonempty
    exact ⟨i, i.property⟩
  · exact (hc.preconnected (⟨i, hi⟩ : X.biUnion id) ⟨j, hj⟩).map hm

/-- For the actual cluster data, near bonds together with all far bonds form
the connected pair family required by the original case selector. -/
theorem source_cluster_graph (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ))
    (hXs : ∀ l, Xs l ⊆ X) (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l))
    (hF : F ∈ relEdgeSets₀ (coarsen X (univ.image Xs))) (hXne : X.Nonempty) :
    F ∪ univ.biUnion Es ∈ relEdgeSets₀ X := by
  have hGX : ∀ Y ∈ univ.image Xs, Y ⊆ X := by
    intro Y hY
    obtain ⟨l, -, rfl⟩ := mem_image.1 hY
    exact hXs l
  have hFX : F ⊆ interPairs X := (mem_relEdgeSets₀.1 hF).1.trans
    (AbsoluteLower.interPairs_coarsen_subset hGX)
  have hEX : univ.biUnion Es ⊆ interPairs X := by
    intro p hp
    obtain ⟨l, -, hp⟩ := mem_biUnion.1 hp
    exact interPairs_subset_of_subset hX (hXs l) ((mem_relEdgeSets.1 (hEs l)).1 hp)
  obtain ⟨S, hS⟩ := hXne
  let : Nonempty X := ⟨⟨S, hS⟩⟩
  apply source_graph_of_connected_blocks hX (union_subset hFX hEX)
  rw [symOf_union]
  exact ⟨reachable_blocks hX Xs Es F hXs hEs hF⟩

end MultipoleBKT.ExpansionK.RouteCases

end
