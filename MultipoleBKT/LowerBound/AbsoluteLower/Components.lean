/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Majorant

/-!
# Connected components of an Eulerian edge set; the even-bond sum over a fixed odd skeleton

Step 1 of the proof of Lemma 4.54: equation (4.91) ("resumming according to the nontrivial connected components
of the odd graph") and the factorization of the inner sum over `E₂`
(Step 1 of the proof of Lemma 4.54).

For `E₁ ⊆ ℰ^inter(X)`:

* `comps X E₁`: the nontrivial connected components of `E₁` relative to `X`, i.e. the sets of
  blocks reached in `E₁ ∪ ℰ^intra(X)` from the endpoints of the pairs of `E₁`
  (`MultipoleBKT.Multipole.reachedBlocks`). They are pairwise disjoint groups of at least two
  blocks (`pairwiseDisjoint_comps`, `two_le_card_of_mem_comps`), `E₁` is the disjoint union of the
  `E₁ ∩ ℰ^inter(Y)`, `Y ∈ comps X E₁` (`eq_biUnion_comps`, `prod_eq_prod_comps`), and for
  `E₁ ∈ Eul^X` each `E₁ ∩ ℰ^inter(Y)` is in `Eulc^Y` (`inter_mem_relEulerianConnectedPairs`).
* `sum_evenEdges_le` (the inner sum of (4.91), bounded by the Penrose resummation, proof of Lemma 4.54):
  for `E₁ ∈ Eul^X` and weights `b ≥ 0` on `ℰ^inter(X)`, with `Y₀ = Coarse_X(comps X E₁)`,
  `∑_{E₂ ⊆ ℰ^inter(X) : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝖤^X} ∏_{E₂} b
  ≤ ∑_{T ∈ 𝖳_0^{Y₀}} ∏_T b ∏_{ℰ^inter(X)} (1 + b)`.
  The paper states the factorization `∏_{∪ ℰ^inter(X'_l) ∖ E_l} (1 + b) ∑_{H ∈ 𝖤_0^{Y₀}} ∏_H b`
  as an identity; only the inequality is used, and it is proved here by the injection
  `E₂ ↦ (E₂ ∖ ℰ^inter(Y₀), E₂ ∩ ℰ^inter(Y₀))`.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Multipole Hierarchical SetPartition

/-! ### Coarsenings -/

section Coarsen

variable {X : Finset (Finset ℕ)} {G : Finset (Finset (Finset ℕ))}

/-- Every block of `X` lies in a block of `Coarse_X(G)`. -/
theorem exists_mem_coarsen_superset {S : Finset ℕ} (hS : S ∈ X) :
    ∃ B ∈ coarsen X G, S ⊆ B := by
  classical
  by_cases h : ∃ Y ∈ G, S ∈ Y
  · obtain ⟨Y, hY, hSY⟩ := h
    exact ⟨Y.biUnion id, mem_union_left _ (mem_image_of_mem _ hY), subset_biUnion_of_mem hSY⟩
  · push Not at h
    exact ⟨S, mem_union_right _ (mem_filter.2 ⟨hS, h⟩), subset_rfl⟩

/-- The inter-block pairs of a coarsening are inter-block pairs of `X`. -/
theorem interPairs_coarsen_subset (hGX : ∀ Y ∈ G, Y ⊆ X) :
    interPairs (coarsen X G) ⊆ interPairs X := by
  intro p hp
  rw [mem_interPairs, biUnion_coarsen hGX] at hp
  rw [mem_interPairs]
  refine ⟨hp.1, fun ⟨S, hS, hpS⟩ => hp.2 ?_⟩
  obtain ⟨B, hB, hSB⟩ := exists_mem_coarsen_superset (G := G) hS
  exact ⟨B, hB, pairsOn_mono hSB hpS⟩

/-- A pair of `V_X` is an intra- or an inter-block pair of the coarsening. -/
theorem mem_intraPairs_or_mem_interPairs_coarsen (hGX : ∀ Y ∈ G, Y ⊆ X) {p : ℕ × ℕ}
    (hp : p ∈ pairsOn (X.biUnion id)) :
    p ∈ intraPairs (coarsen X G) ∨ p ∈ interPairs (coarsen X G) := by
  by_cases h : p ∈ intraPairs (coarsen X G)
  · exact Or.inl h
  · right
    rw [interPairs, mem_sdiff, biUnion_coarsen hGX]
    exact ⟨hp, h⟩

end Coarsen

/-! ### The components of an edge set -/

section Components

open scoped Classical

variable {X : Finset (Finset ℕ)} {E₁ : Finset (ℕ × ℕ)}

variable (X E₁) in
/-- The nontrivial connected components of `E₁` relative to `X`: the sets of blocks of `X` reached
in `E₁ ∪ ℰ^intra(X)` from the first endpoints of the pairs of `E₁`. -/
noncomputable def comps : Finset (Finset (Finset ℕ)) :=
  E₁.image fun p => reachedBlocks X E₁ p.1

theorem mem_comps {Y : Finset (Finset ℕ)} :
    Y ∈ comps X E₁ ↔ ∃ p ∈ E₁, reachedBlocks X E₁ p.1 = Y := by
  rw [comps, mem_image]

theorem reachedBlocks_subset (a : ℕ) : reachedBlocks X E₁ a ⊆ X := by
  rw [reachedBlocks]
  exact filter_subset _ _

/-- The structure of the blocks reached from a point. -/
theorem reachedBlocks_spec (hX : IsSubpartition X) (hE : E₁ ⊆ interPairs X) {B₀ : Finset ℕ}
    (hB₀ : B₀ ∈ X) {a : ℕ} (ha : a ∈ B₀) :
    E₁ ⊆ interPairs (reachedBlocks X E₁ a) ∪ interPairs (X \ reachedBlocks X E₁ a) ∧
      ConnOn ((reachedBlocks X E₁ a).biUnion id)
        (E₁ ∩ interPairs (reachedBlocks X E₁ a) ∪ intraPairs (reachedBlocks X E₁ a)) :=
  (reachedBlocks_eq_iff hX hE (reachedBlocks_subset a) (mem_reachedBlocks_self hB₀ ha) ha).1 rfl

theorem comps_subset {Y : Finset (Finset ℕ)} (hY : Y ∈ comps X E₁) : Y ⊆ X := by
  obtain ⟨p, -, rfl⟩ := mem_comps.1 hY
  exact reachedBlocks_subset _

/-- A pair of `E₁` with an endpoint in `V_Y`, `Y` a component, is in `ℰ^inter(Y)`. -/
theorem mem_interPairs_of_mem_comps (hX : IsSubpartition X) (hE : E₁ ⊆ interPairs X)
    {Y : Finset (Finset ℕ)} (hY : Y ∈ comps X E₁) {p : ℕ × ℕ} (hp : p ∈ E₁)
    (h : p.1 ∈ Y.biUnion id ∨ p.2 ∈ Y.biUnion id) : p ∈ interPairs Y := by
  obtain ⟨q, hq, rfl⟩ := mem_comps.1 hY
  have hq1 := (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hq))).1
  obtain ⟨B₀, hB₀, hqB₀⟩ := mem_biUnion_id.1 hq1
  have hsplit := (reachedBlocks_spec hX hE hB₀ hqB₀).1 hp
  rcases mem_union.1 hsplit with h' | h'
  · exact h'
  · have hdisj := disjoint_biUnion_sdiff hX (reachedBlocks_subset (E₁ := E₁) q.1)
    have hp' := interPairs_subset_pairsOn_biUnion _ h'
    rcases h with h | h
    · exact absurd hp'.1 (disjoint_left.1 hdisj h)
    · exact absurd hp'.2 (disjoint_left.1 hdisj h)

/-- A component has at least two blocks. -/
theorem two_le_card_of_mem_comps (hX : IsSubpartition X) (hE : E₁ ⊆ interPairs X)
    {Y : Finset (Finset ℕ)} (hY : Y ∈ comps X E₁) : 2 ≤ Y.card := by
  obtain ⟨q, hq, rfl⟩ := mem_comps.1 hY
  have hq1 := (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hq))).1
  obtain ⟨B₀, hB₀, hqB₀⟩ := mem_biUnion_id.1 hq1
  have hqY := mem_interPairs_of_mem_comps hX hE hY hq
    (Or.inl (subset_biUnion_of_mem (mem_reachedBlocks_self hB₀ hqB₀) hqB₀))
  obtain ⟨B, hB, B', hB', hBB', -, -⟩ := exists_of_mem_interPairs hqY
  exact one_lt_card.2 ⟨B, hB, B', hB', hBB'⟩

/-- Two blocks reached from a common block reach the same blocks. -/
theorem reachedBlocks_eq_of_mem {B : Finset ℕ} {a a' : ℕ} (h : B ∈ reachedBlocks X E₁ a)
    (h' : B ∈ reachedBlocks X E₁ a') : reachedBlocks X E₁ a = reachedBlocks X E₁ a' := by
  rw [reachedBlocks, mem_filter] at h h'
  obtain ⟨hB, i, hi, hai⟩ := h
  obtain ⟨-, i', hi', hai'⟩ := h'
  have haa' : (edgeGraph (E₁ ∪ intraPairs X)).Reachable a a' :=
    (hai.trans (reachable_of_mem_block hB E₁ hi hi')).trans hai'.symm
  ext C
  simp only [reachedBlocks, mem_filter]
  constructor
  · rintro ⟨hC, j, hj, haj⟩
    exact ⟨hC, j, hj, haa'.symm.trans haj⟩
  · rintro ⟨hC, j, hj, haj⟩
    exact ⟨hC, j, hj, haa'.trans haj⟩

/-- The components are pairwise disjoint. -/
theorem pairwiseDisjoint_comps :
    ((comps X E₁ : Finset (Finset (Finset ℕ))) : Set (Finset (Finset ℕ))).PairwiseDisjoint id := by
  intro Y hY Y' hY' hne
  obtain ⟨p, -, rfl⟩ := mem_comps.1 (mem_coe.1 hY)
  obtain ⟨p', -, rfl⟩ := mem_comps.1 (mem_coe.1 hY')
  rw [Function.onFun, id, id, disjoint_left]
  intro B hB hB'
  exact hne (reachedBlocks_eq_of_mem hB hB')

/-- `E₁` is the union of its parts `E₁ ∩ ℰ^inter(Y)` in its components `Y`. -/
theorem eq_biUnion_comps (hX : IsSubpartition X) (hE : E₁ ⊆ interPairs X) :
    E₁ = (comps X E₁).biUnion fun Y => E₁ ∩ interPairs Y := by
  ext p
  simp only [mem_biUnion, mem_inter]
  constructor
  · intro hp
    have hp1 := (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hp))).1
    obtain ⟨B₀, hB₀, hpB₀⟩ := mem_biUnion_id.1 hp1
    have hY : reachedBlocks X E₁ p.1 ∈ comps X E₁ := mem_comps.2 ⟨p, hp, rfl⟩
    exact ⟨_, hY, hp, mem_interPairs_of_mem_comps hX hE hY hp
      (Or.inl (subset_biUnion_of_mem (mem_reachedBlocks_self hB₀ hpB₀) hpB₀))⟩
  · rintro ⟨-, -, hp, -⟩
    exact hp

/-- The parts of `E₁` in distinct components are disjoint. -/
theorem pairwiseDisjoint_inter_comps (hX : IsSubpartition X) :
    ((comps X E₁ : Finset (Finset (Finset ℕ))) : Set (Finset (Finset ℕ))).PairwiseDisjoint
      fun Y => E₁ ∩ interPairs Y := by
  intro Y hY Y' hY' hne
  rw [Function.onFun, disjoint_left]
  intro p hp hp'
  have hd := disjoint_biUnion_of_disjoint hX (comps_subset (mem_coe.1 hY))
    (comps_subset (mem_coe.1 hY')) (pairwiseDisjoint_comps hY hY' hne)
  exact disjoint_left.1 hd (interPairs_subset_pairsOn_biUnion _ (mem_inter.1 hp).2).1
    (interPairs_subset_pairsOn_biUnion _ (mem_inter.1 hp').2).1

/-- Products over `E₁` are products over the parts of `E₁` in its components. -/
theorem prod_eq_prod_comps {M : Type*} [CommMonoid M] (hX : IsSubpartition X)
    (hE : E₁ ⊆ interPairs X) (f : ℕ × ℕ → M) :
    ∏ p ∈ E₁, f p = ∏ Y ∈ comps X E₁, ∏ p ∈ E₁ ∩ interPairs Y, f p := by
  conv_lhs => rw [eq_biUnion_comps hX hE]
  exact prod_biUnion (pairwiseDisjoint_inter_comps hX)

/-- The part of an Eulerian `E₁` in a component `Y` is in `Eulc^Y`. -/
theorem inter_mem_relEulerianConnectedPairs (hX : IsSubpartition X)
    (hE₁ : E₁ ∈ relEulerianPairs X) {Y : Finset (Finset ℕ)} (hY : Y ∈ comps X E₁) :
    E₁ ∩ interPairs Y ∈ relEulerianConnectedPairs Y := by
  have hE := (mem_relEulerianPairs.1 hE₁).1
  obtain ⟨q, hq, hqY⟩ := mem_comps.1 hY
  have hq1 := (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hq))).1
  obtain ⟨B₀, hB₀, hqB₀⟩ := mem_biUnion_id.1 hq1
  have hspec := reachedBlocks_spec hX hE hB₀ hqB₀
  rw [hqY] at hspec
  have hqI : q ∈ interPairs Y := mem_interPairs_of_mem_comps hX hE hY hq
    (Or.inl (subset_biUnion_of_mem (hqY ▸ mem_reachedBlocks_self hB₀ hqB₀) hqB₀))
  refine mem_relEulerianConnectedPairs.2 ⟨mem_relEdgeSets.2 ⟨inter_subset_right,
    ⟨q, mem_inter.2 ⟨hq, hqI⟩⟩, hspec.2⟩, mem_relEulerianPairs.2 ⟨inter_subset_right,
    fun S hS => ?_⟩⟩
  have hSV : S ⊆ Y.biUnion id := subset_biUnion_of_mem hS
  have heq : blockDeg (E₁ ∩ interPairs Y) S = blockDeg E₁ S := by
    rw [blockDeg, blockDeg]
    congr 2
    · ext p
      simp only [mem_filter, mem_inter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, mem_interPairs_of_mem_comps hX hE hY h.1
        (Or.inl (hSV h.2))⟩, h.2⟩⟩
    · ext p
      simp only [mem_filter, mem_inter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, mem_interPairs_of_mem_comps hX hE hY h.1
        (Or.inr (hSV h.2))⟩, h.2⟩⟩
  rw [heq]
  exact (mem_relEulerianPairs.1 hE₁).2 S (comps_subset hY hS)

/-- The coarsening by the components is a subpartition. -/
theorem isSubpartition_coarsen_comps (hX : IsSubpartition X) (hE : E₁ ⊆ interPairs X) :
    IsSubpartition (coarsen X (comps X E₁)) :=
  isSubpartition_coarsen hX (fun _ hY => comps_subset hY)
    (fun Y hY => card_pos.1 (by have := two_le_card_of_mem_comps hX hE hY; omega))
    pairwiseDisjoint_comps

/-- The components form a disjoint family of groups of at least two blocks. -/
theorem comps_mem_disjointFamilies (hX : IsSubpartition X) (hE : E₁ ⊆ interPairs X) :
    comps X E₁ ∈ disjointFamilies X (fun Y => 2 ≤ Y.card) :=
  mem_disjointFamilies.2 ⟨fun _ hY => comps_subset hY, pairwiseDisjoint_comps,
    fun _ hY => two_le_card_of_mem_comps hX hE hY⟩

/-- **The even-bond sum over a fixed odd skeleton** (Step 1 of the proof of Lemma 4.54, the inner
sum of (4.91) and its Penrose bound, proof of Lemma 4.54): for `E₁ ∈ Eul^X` and `b ≥ 0` on
`ℰ^inter(X)`, with `Y₀ = Coarse_X(comps X E₁)`,
`∑_{E₂ ⊆ ℰ^inter(X) : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝖤^X} ∏_{ij ∈ E₂} b_ij
≤ ∑_{T ∈ 𝖳_0^{Y₀}} ∏_{ij ∈ T} b_ij ∏_{ij ∈ ℰ^inter(X)} (1 + b_ij)`. -/
theorem sum_evenEdges_le (hX : IsSubpartition X) (hE₁ : E₁ ∈ relEulerianPairs X)
    (b : ℕ × ℕ → ℝ) (hb : ∀ p ∈ interPairs X, 0 ≤ b p) :
    ∑ E₂ ∈ (interPairs X).powerset.filter
        (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ p ∈ E₂, b p ≤
      (∑ T ∈ relTreePairs₀ (coarsen X (comps X E₁)), ∏ p ∈ T, b p) *
        ∏ p ∈ interPairs X, (1 + b p) := by
  have hE := (mem_relEulerianPairs.1 hE₁).1
  set G := comps X E₁ with hG
  set Y₀ := coarsen X G with hY₀def
  have hGX : ∀ Y ∈ G, Y ⊆ X := fun _ hY => comps_subset hY
  have hY₀ : IsSubpartition Y₀ := isSubpartition_coarsen_comps hX hE
  set I₀ := interPairs Y₀ with hI₀def
  have hI₀ : I₀ ⊆ interPairs X := interPairs_coarsen_subset hGX
  set F := (interPairs X).powerset.filter
    (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X) with hF
  -- `E₂ ∩ ℰ^inter(Y₀)` connects the coarsening
  have hconn : ∀ E₂ ∈ F, E₂ ∩ I₀ ∈ relEdgeSets₀ Y₀ := by
    intro E₂ hE₂
    rw [hF, mem_filter, mem_powerset] at hE₂
    obtain ⟨hE₂I, -, hE₁₂⟩ := hE₂
    obtain ⟨-, -, hcon⟩ := mem_relEdgeSets.1 hE₁₂
    refine mem_relEdgeSets₀.2 ⟨inter_subset_right, ?_⟩
    rw [biUnion_coarsen hGX]
    refine ⟨hcon.1, fun i hi j hj => (hcon.2 i hi j hj).mono (edgeGraph_mono ?_)⟩
    intro p hp
    rcases mem_union.1 hp with hp | hp
    · rcases mem_union.1 hp with hp | hp
      · apply mem_union_right
        rw [eq_biUnion_comps hX hE, mem_biUnion] at hp
        obtain ⟨Y, hY, hpY⟩ := hp
        exact mem_intraPairs.2 ⟨Y.biUnion id, mem_union_left _ (mem_image_of_mem _ hY),
          interPairs_subset_pairsOn (mem_inter.1 hpY).2⟩
      · rcases mem_intraPairs_or_mem_interPairs_coarsen hGX
          (interPairs_subset_pairsOn (hE₂I hp)) with h | h
        · exact mem_union_right _ h
        · exact mem_union_left _ (mem_inter.2 ⟨hp, h⟩)
    · obtain ⟨S, hS, hpS⟩ := mem_intraPairs.1 hp
      obtain ⟨B, hB, hSB⟩ := exists_mem_coarsen_superset (G := G) hS
      exact mem_union_right _ (mem_intraPairs.2 ⟨B, hB, pairsOn_mono hSB hpS⟩)
  -- the injection `E₂ ↦ (E₂ ∖ I₀, E₂ ∩ I₀)`
  set φ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ) × Finset (ℕ × ℕ) := fun E₂ => (E₂ \ I₀, E₂ ∩ I₀)
  have hφinj : Set.InjOn φ F := by
    intro E₂ _ E₂' _ h
    simp only [φ, Prod.mk.injEq] at h
    rw [← sdiff_union_inter E₂ I₀, ← sdiff_union_inter E₂' I₀, h.1, h.2]
  set W := ((interPairs X \ I₀).powerset ×ˢ relEdgeSets₀ Y₀) with hW
  have hφW : ∀ E₂ ∈ F, φ E₂ ∈ W := by
    intro E₂ hE₂
    refine mem_product.2 ⟨mem_powerset.2 (sdiff_subset_sdiff ?_ le_rfl), hconn E₂ hE₂⟩
    exact mem_powerset.1 (mem_filter.1 hE₂).1
  have hWnn : ∀ q ∈ W, 0 ≤ (∏ p ∈ q.1, b p) * ∏ p ∈ q.2, b p := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := mem_product.1 hq
    refine mul_nonneg (prod_nonneg fun p hp => hb p ?_) (prod_nonneg fun p hp => hb p ?_)
    · exact (sdiff_subset (mem_powerset.1 hq1 hp))
    · exact hI₀ ((mem_relEdgeSets₀.1 hq2).1 hp)
  have hsplit : ∀ E₂ ∈ F, ∏ p ∈ E₂, b p = (∏ p ∈ (φ E₂).1, b p) * ∏ p ∈ (φ E₂).2, b p := by
    intro E₂ _
    rw [mul_comm]
    exact (prod_inter_mul_prod_sdiff E₂ I₀ b).symm
  calc ∑ E₂ ∈ F, ∏ p ∈ E₂, b p
      = ∑ q ∈ F.image φ, (∏ p ∈ q.1, b p) * ∏ p ∈ q.2, b p := by
        rw [sum_image hφinj]
        exact sum_congr rfl hsplit
    _ ≤ ∑ q ∈ W, (∏ p ∈ q.1, b p) * ∏ p ∈ q.2, b p := by
        refine sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun q hq _ => hWnn q hq
        obtain ⟨E₂, hE₂, rfl⟩ := mem_image.1 hq
        exact hφW E₂ hE₂
    _ = (∏ p ∈ interPairs X \ I₀, (1 + b p)) * ∑ H ∈ relEdgeSets₀ Y₀, ∏ p ∈ H, b p := by
        rw [hW, sum_product, prod_one_add, sum_mul]
        refine sum_congr rfl fun A _ => ?_
        rw [mul_sum]
    _ ≤ (∏ p ∈ interPairs X \ I₀, (1 + b p)) *
          ((∑ T ∈ relTreePairs₀ Y₀, ∏ p ∈ T, b p) * ∏ p ∈ I₀, (1 + b p)) := by
        refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun p hp => ?_)
        · rw [sum_mul]
          exact sum_relEdgeSets₀_le hY₀ b fun p hp => hb p (hI₀ hp)
        · have := hb p (sdiff_subset hp)
          linarith
    _ = (∑ T ∈ relTreePairs₀ Y₀, ∏ p ∈ T, b p) * ∏ p ∈ interPairs X, (1 + b p) := by
        rw [← prod_sdiff hI₀ (f := fun p => 1 + b p)]
        ring

end Components

end AbsoluteLower

end MultipoleBKT

end
