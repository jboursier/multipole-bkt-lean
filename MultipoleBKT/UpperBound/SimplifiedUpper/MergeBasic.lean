/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.LXi
public import MultipoleBKT.LowerBound.Peeling.Ear

/-!
# Coarsenings and relative trees as edge sets of pairs

Facts used to merge the outer and inner `b`-trees in the proof of Lemma 5.37 ("as in the proof of Lemma 4.57"):

* `card_coarsen_add`: `|Coarse_X(G)| + ∑_{Y ∈ G} |Y| = |X| + |G|` for disjoint nonempty groups;
* `exists_superset_mem_coarsen`: a coarsening along groups `𝒱` refines a coarsening along groups
  `𝒲` whose members contain those of `𝒱`;
* `mem_relTreePairs₀_iff`: `T ∈ 𝖳_0^Y` iff `T ⊆ ℰ^inter(Y)`, `T ∪ ℰ^intra(Y)` connects `V_Y`, and
  `|T| + 1 = |Y|` (a connected quotient with `|Y| - 1` edges is a tree).
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Finset SimpleGraph Multipole Hierarchical SetPartition AbsoluteLower

/-! ### Coarsenings -/

section Coarsen

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {G : Finset (Finset (Finset ℕ))}
  (hGX : ∀ Y ∈ G, Y ⊆ X) (hGne : ∀ Y ∈ G, Y.Nonempty)
  (hGd : (G : Set (Finset (Finset ℕ))).PairwiseDisjoint id)
include hX hGX hGne hGd

/-- **The number of blocks of a coarsening**: `|Coarse_X(G)| + ∑_{Y ∈ G} |Y| = |X| + |G|`. -/
theorem card_coarsen_add : (coarsen X G).card + ∑ Y ∈ G, Y.card = X.card + G.card := by
  classical
  set A := G.image fun Y : Finset (Finset ℕ) => Y.biUnion id with hA
  set F := X.filter fun S => ∀ Y ∈ G, S ∉ Y with hF
  have hAF : Disjoint A F := by
    rw [Finset.disjoint_left]
    intro B hBA hBF
    obtain ⟨Y, hY, rfl⟩ := mem_image.1 hBA
    obtain ⟨hBX, hBn⟩ := mem_filter.1 hBF
    obtain ⟨S₀, hS₀⟩ := hGne Y hY
    have hS₀X := hGX Y hY hS₀
    obtain ⟨x, hx⟩ := hX.1 S₀ hS₀X
    have hxB : x ∈ Y.biUnion id := subset_biUnion_of_mem hS₀ hx
    have := eq_of_isSubpartition hX hS₀X hBX hx hxB
    exact hBn Y hY (this ▸ hS₀)
  have hinj : Set.InjOn (fun Y : Finset (Finset ℕ) => Y.biUnion id) G := by
    intro Y hY Y' hY' heq
    by_contra hne
    obtain ⟨S₀, hS₀⟩ := hGne Y hY
    have hS₀X := hGX Y hY hS₀
    obtain ⟨x, hx⟩ := hX.1 S₀ hS₀X
    have hxY' : x ∈ Y'.biUnion id := by
      have : x ∈ Y.biUnion id := subset_biUnion_of_mem hS₀ hx
      simpa only [heq] using this
    obtain ⟨S₁, hS₁, hxS₁⟩ := mem_biUnion_id.1 hxY'
    have := eq_of_isSubpartition hX hS₀X (hGX Y' hY' hS₁) hx hxS₁
    exact Finset.disjoint_left.1 (hGd hY hY' hne) hS₀ (this ▸ hS₁)
  have hAcard : A.card = G.card := card_image_of_injOn hinj
  have hXsplit : X = F ∪ G.biUnion id := by
    ext S
    simp only [hF, mem_union, mem_filter, mem_biUnion, id]
    constructor
    · intro hS
      by_cases h : ∃ Y ∈ G, S ∈ Y
      · exact Or.inr h
      · push Not at h
        exact Or.inl ⟨hS, h⟩
    · rintro (⟨hS, -⟩ | ⟨Y, hY, hSY⟩)
      · exact hS
      · exact hGX Y hY hSY
  have hFd : Disjoint F (G.biUnion id) := by
    rw [Finset.disjoint_left]
    intro S hSF hSG
    obtain ⟨Y, hY, hSY⟩ := mem_biUnion.1 hSG
    exact (mem_filter.1 hSF).2 Y hY hSY
  have hXcard : X.card = F.card + ∑ Y ∈ G, Y.card := by
    conv_lhs => rw [hXsplit]
    rw [card_union_of_disjoint hFd, card_biUnion hGd]
    rfl
  have hcoarsen : (coarsen X G).card = A.card + F.card := by
    rw [coarsen, card_union_of_disjoint hAF]
  omega

end Coarsen

section Refine

variable {X : Finset (Finset ℕ)} {𝒲 𝒱 : Finset (Finset (Finset ℕ))}

/-- **Coarsenings refine**: if every group of `𝒱` lies in a group of `𝒲`, every block of
`Coarse_X(𝒱)` lies in a block of `Coarse_X(𝒲)`. -/
theorem exists_superset_mem_coarsen (h𝒱𝒲 : ∀ Y ∈ 𝒱, ∃ X' ∈ 𝒲, Y ⊆ X') {B : Finset ℕ}
    (hB : B ∈ coarsen X 𝒱) : ∃ B' ∈ coarsen X 𝒲, B ⊆ B' := by
  classical
  simp only [coarsen, mem_union, mem_image, mem_filter] at hB
  rcases hB with ⟨Y, hY, rfl⟩ | ⟨hS, hSn⟩
  · obtain ⟨X', hX', hYX'⟩ := h𝒱𝒲 Y hY
    exact ⟨X'.biUnion id, mem_union_left _ (mem_image_of_mem _ hX'),
      biUnion_subset_biUnion_of_subset_left id hYX'⟩
  · by_cases h : ∃ X' ∈ 𝒲, B ∈ X'
    · obtain ⟨X', hX', hBX'⟩ := h
      exact ⟨X'.biUnion id, mem_union_left _ (mem_image_of_mem _ hX'),
        subset_biUnion_of_mem hBX'⟩
    · push Not at h
      exact ⟨B, mem_union_right _ (mem_filter.2 ⟨hS, h⟩), subset_rfl⟩

/-- The inter-block pairs of a coarsening are inter-block pairs of any finer coarsening. -/
theorem interPairs_coarsen_mono (h𝒱𝒲 : ∀ Y ∈ 𝒱, ∃ X' ∈ 𝒲, Y ⊆ X')
    (h𝒲 : ∀ Y ∈ 𝒲, Y ⊆ X) (h𝒱 : ∀ Y ∈ 𝒱, Y ⊆ X) :
    interPairs (coarsen X 𝒲) ⊆ interPairs (coarsen X 𝒱) := by
  intro q hq
  rw [mem_interPairs, biUnion_coarsen h𝒲] at hq
  rw [mem_interPairs, biUnion_coarsen h𝒱]
  refine ⟨hq.1, fun ⟨B, hB, hqB⟩ => hq.2 ?_⟩
  obtain ⟨B', hB', hBB'⟩ := exists_superset_mem_coarsen h𝒱𝒲 hB
  exact ⟨B', hB', pairsOn_mono hBB' hqB⟩

end Refine

/-! ### Relative trees -/

section Trees

open scoped Classical

variable {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)
include hY

/-- A relative tree connects `V_Y` together with `ℰ^intra(Y)`. -/
theorem connOn_of_mem_relTreePairs₀ {T : Finset (ℕ × ℕ)} (hT : T ∈ relTreePairs₀ Y) :
    ConnOn (Y.biUnion id) (T ∪ intraPairs Y) := by
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hT
  have h := (isRelConnected₀_iff_mem hY).1 (mem_relTrees₀.1 hG).isRelConnected₀
  exact (mem_relEdgeSets₀.1 h).2

/-- **Relative trees as edge sets**: `T ∈ 𝖳_0^Y` iff `T ⊆ ℰ^inter(Y)`, `T ∪ ℰ^intra(Y)` connects
`V_Y`, and `|T| + 1 = |Y|`. -/
theorem mem_relTreePairs₀_iff {T : Finset (ℕ × ℕ)} :
    T ∈ relTreePairs₀ Y ↔ T ⊆ interPairs Y ∧ ConnOn (Y.biUnion id) (T ∪ intraPairs Y) ∧
      T.card + 1 = Y.card := by
  refine ⟨fun hT => ⟨subset_interPairs_of_mem_relTreePairs₀ hY hT,
    connOn_of_mem_relTreePairs₀ hY hT, card_add_one_of_mem_relTreePairs₀ hY hT⟩, ?_⟩
  rintro ⟨hTI, hconn, hcard⟩
  set V := Y.biUnion id
  set G := graphOf V T with hG
  have hTV : T ⊆ pairsOn V := hTI.trans interPairs_subset_pairsOn
  have hedges : edgesOf G = T := edgesOf_graphOf hTV
  have hle : G ≤ interEdges Y := (le_interEdges_iff_edgesOf_subset hY).2 (hedges ▸ hTI)
  have hconnG : (G ⊔ intraEdges Y).Connected :=
    connected_sup_intraEdges_iff_connOn.2 (hedges ▸ hconn)
  have hGcard : Nat.card G.edgeSet = T.card := by
    rw [← hedges, card_edgesOf, edgeFinset_card, Nat.card_eq_fintype_card]
  have hQconn : (quotientGraph Y G).Connected := (connected_sup_intraEdges_iff hY).1 hconnG
  have hQle : Nat.card (quotientGraph Y G).edgeSet ≤ Nat.card G.edgeSet := by
    rw [quotientGraph_eq hY]
    exact Peeling.natCard_blockQuotient_edgeSet_le _ (interEdges_eq hY ▸ hle)
  have hQvert := hQconn.card_vert_le_card_edgeSet_add_one
  have hYcard : Nat.card Y = Y.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hQtree : (quotientGraph Y G).IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨hQconn, ?_⟩
    rw [hYcard] at hQvert ⊢
    omega
  have hGtree : IsRelTree₀ Y G := (isRelTree₀_iff_card hY).2 ⟨hle, hQtree, by rw [hGcard, hcard]⟩
  rw [← hedges]
  exact mem_image_of_mem _ (mem_relTrees₀.2 hGtree)

end Trees

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
