/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.PairGraph
public import MultipoleBKT.UpperBound.BoundedUpper.ParityReduction

/-!
# The components of the odd edges and the tree `T^b`

The paper: proof of Proposition 5.18: "Let `X_1, …, X_n` be the connected components relative
to `X` with at least two multipoles of the graph `(V_X, ∪_l E_{l,1})`. … One may extract from
`(V_X, ∪_l E_{l,2} ∪ F)` a tree `T^b ∈ 𝖳_0^{Coarse_X(X_1, …, X_n)}`."

For an edge set `E₁ ⊆ ℰ^inter(X)` (the odd edges of a term of `abs_plusActivity_le`):

* `relComponents X E₁`: the components of `(V_X, E₁ ∪ ℰ^intra(X))`, as families of blocks
  (`MultipoleBKT.Multipole.reachedBlocks`); `oddComponents X E₁`: those with at least two blocks;
* `prod_eq_prod_oddComponents`: `∏_{p ∈ E₁} f(p) = ∏_{Y ∈ oddComponents} ∏_{p ∈ E₁ ∩ ℰ^inter(Y)} f(p)`;
* `isRelConnected_pairGraph`, `isRelEulerianOff_pairGraph`: on an odd component `Y`, the graph of
  `E₁ ∩ ℰ^inter(Y)` is in `𝖤^Y`, and in `Eul^Y(V₁ ∩ V_Y)` when `E₁ ∈ Eul^X(V₁)`
  (`IsParityPair X E₁ V₁`);
* `exists_isRelTree₀_even`: for `E ∈ 𝖤_0^X` and `E₁ ⊆ E`, a tree `T^b ∈ 𝖳_0^{Coarse_X(oddComponents)}`
  whose pairs lie in `E ∖ E₁`.
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Multipole Hierarchical SetPartition Parity

variable {X : Finset (Finset ℕ)}

/-! ### Reached blocks -/

section Reach

theorem reachedBlocks_eq_of_reachable {E : Finset (ℕ × ℕ)} {a a' : ℕ}
    (h : (edgeGraph (E ∪ intraPairs X)).Reachable a a') :
    reachedBlocks X E a = reachedBlocks X E a' := by
  classical
  ext B
  simp only [reachedBlocks, Finset.mem_filter]
  constructor
  · rintro ⟨hB, i, hi, hai⟩
    exact ⟨hB, i, hi, h.symm.trans hai⟩
  · rintro ⟨hB, i, hi, hai⟩
    exact ⟨hB, i, hi, h.trans hai⟩

theorem mem_reachedBlocks_iff {E : Finset (ℕ × ℕ)} {a : ℕ} {B : Finset ℕ} :
    B ∈ reachedBlocks X E a ↔ B ∈ X ∧ ∃ i ∈ B, (edgeGraph (E ∪ intraPairs X)).Reachable a i := by
  classical
  simp only [reachedBlocks, Finset.mem_filter]

theorem reachedBlocks_subset (E : Finset (ℕ × ℕ)) (a : ℕ) : reachedBlocks X E a ⊆ X := by
  intro B hB
  exact (mem_reachedBlocks_iff.1 hB).1

theorem reachedBlocks_eq_of_mem {E : Finset (ℕ × ℕ)} {a i : ℕ} {B : Finset ℕ}
    (hB : B ∈ reachedBlocks X E a) (hi : i ∈ B) : reachedBlocks X E i = reachedBlocks X E a := by
  obtain ⟨hBX, j, hj, haj⟩ := mem_reachedBlocks_iff.1 hB
  exact (reachedBlocks_eq_of_reachable (haj.trans (reachable_of_mem_block hBX E hj hi))).symm

theorem reachedBlocks_eq_of_mem_mem (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)} {a a' : ℕ}
    {B : Finset ℕ} (hB : B ∈ reachedBlocks X E a) (hB' : B ∈ reachedBlocks X E a') :
    reachedBlocks X E a = reachedBlocks X E a' := by
  obtain ⟨i, hi⟩ := hX.1 B (reachedBlocks_subset E a hB)
  exact (reachedBlocks_eq_of_mem hB hi).symm.trans (reachedBlocks_eq_of_mem hB' hi)

/-- An edge of `E` (inside `ℰ^inter(X)`) is an inter-block pair of the component of its first
endpoint. -/
theorem mem_interPairs_reachedBlocks (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ interPairs X) {p : ℕ × ℕ} (hp : p ∈ E) : p ∈ interPairs (reachedBlocks X E p.1) := by
  obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := exists_of_mem_interPairs (hE hp)
  have h12 := (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hp))).2.2
  have hY : IsSubpartition (reachedBlocks X E p.1) := isSubpartition_mono hX (reachedBlocks_subset E _)
  refine mem_interPairs_of hY (mem_reachedBlocks_self hB h1) ?_ hBB' h1 h2 h12
  refine mem_reachedBlocks_iff.2 ⟨hB', p.2, h2, Adj.reachable ?_⟩
  exact edgeGraph_adj.2 ⟨h12.ne, Or.inl (Finset.mem_union_left _ hp)⟩

/-- The components with an endpoint of `p ∈ E` are the component of `p.1`. -/
theorem reachedBlocks_snd_eq {E : Finset (ℕ × ℕ)} (hE : E ⊆ interPairs X) {p : ℕ × ℕ}
    (hp : p ∈ E) : reachedBlocks X E p.2 = reachedBlocks X E p.1 := by
  have h12 := (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hp))).2.2
  exact (reachedBlocks_eq_of_reachable (Adj.reachable
    (edgeGraph_adj.2 ⟨h12.ne, Or.inl (Finset.mem_union_left _ hp)⟩))).symm

end Reach

/-! ### The components -/

section Components

/-- The components of `(V_X, E ∪ ℰ^intra(X))`, as families of blocks. -/
noncomputable def relComponents (X : Finset (Finset ℕ)) (E : Finset (ℕ × ℕ)) :
    Finset (Finset (Finset ℕ)) :=
  (X.biUnion id).image (reachedBlocks X E)

/-- The components with at least two blocks (`X_1, …, X_n`). -/
noncomputable def oddComponents (X : Finset (Finset ℕ)) (E : Finset (ℕ × ℕ)) :
    Finset (Finset (Finset ℕ)) :=
  (relComponents X E).filter fun Y => 2 ≤ Y.card

theorem mem_relComponents {E : Finset (ℕ × ℕ)} {Y : Finset (Finset ℕ)} :
    Y ∈ relComponents X E ↔ ∃ a ∈ X.biUnion id, reachedBlocks X E a = Y := by
  rw [relComponents, Finset.mem_image]

theorem mem_oddComponents {E : Finset (ℕ × ℕ)} {Y : Finset (Finset ℕ)} :
    Y ∈ oddComponents X E ↔ Y ∈ relComponents X E ∧ 2 ≤ Y.card := by
  rw [oddComponents, Finset.mem_filter]

theorem subset_of_mem_relComponents {E : Finset (ℕ × ℕ)} {Y : Finset (Finset ℕ)}
    (hY : Y ∈ relComponents X E) : Y ⊆ X := by
  obtain ⟨a, -, rfl⟩ := mem_relComponents.1 hY
  exact reachedBlocks_subset E a

theorem nonempty_of_mem_relComponents {E : Finset (ℕ × ℕ)} {Y : Finset (Finset ℕ)}
    (hY : Y ∈ relComponents X E) : Y.Nonempty := by
  obtain ⟨a, ha, rfl⟩ := mem_relComponents.1 hY
  obtain ⟨B, hB, haB⟩ := mem_biUnion_id.1 ha
  exact ⟨B, mem_reachedBlocks_self hB haB⟩

theorem oddComponents_subset (E : Finset (ℕ × ℕ)) : oddComponents X E ⊆ relComponents X E :=
  Finset.filter_subset _ _

/-- Distinct components are disjoint. -/
theorem disjoint_of_mem_relComponents (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    {Y Y' : Finset (Finset ℕ)} (hY : Y ∈ relComponents X E) (hY' : Y' ∈ relComponents X E)
    (hne : Y ≠ Y') : Disjoint Y Y' := by
  obtain ⟨a, -, rfl⟩ := mem_relComponents.1 hY
  obtain ⟨a', -, rfl⟩ := mem_relComponents.1 hY'
  rw [Finset.disjoint_left]
  intro B hB hB'
  exact hne (reachedBlocks_eq_of_mem_mem hX hB hB')

theorem pairwiseDisjoint_oddComponents (hX : IsSubpartition X) (E : Finset (ℕ × ℕ)) :
    ((oddComponents X E : Finset (Finset (Finset ℕ))) : Set (Finset (Finset ℕ))).PairwiseDisjoint
      id :=
  fun _ hY _ hY' hne => disjoint_of_mem_relComponents hX (oddComponents_subset E hY)
    (oddComponents_subset E hY') hne

/-- The block sets of disjoint subfamilies are disjoint. -/
theorem disjoint_biUnion_of_disjoint (hX : IsSubpartition X) {Y Y' : Finset (Finset ℕ)}
    (hY : Y ⊆ X) (hY' : Y' ⊆ X) (h : Disjoint Y Y') : Disjoint (Y.biUnion id) (Y'.biUnion id) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨B, hB, hiB⟩ := mem_biUnion_id.1 hi
  obtain ⟨B', hB', hiB'⟩ := mem_biUnion_id.1 hi'
  have := eq_of_isSubpartition hX (hY hB) (hY' hB') hiB hiB'
  exact Finset.disjoint_left.1 h hB (this ▸ hB')

/-- **The decomposition of `E₁` along its components.** -/
theorem prod_eq_prod_oddComponents {M : Type*} [CommMonoid M] (hX : IsSubpartition X)
    {E : Finset (ℕ × ℕ)} (hE : E ⊆ interPairs X) (f : ℕ × ℕ → M) :
    ∏ p ∈ E, f p = ∏ Y ∈ oddComponents X E, ∏ p ∈ E ∩ interPairs Y, f p := by
  have hEq : E = (oddComponents X E).biUnion fun Y => E ∩ interPairs Y := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hp
      refine ⟨reachedBlocks X E p.1, mem_oddComponents.2 ⟨mem_relComponents.2 ⟨p.1,
        (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hp))).1, rfl⟩, ?_⟩, hp,
        mem_interPairs_reachedBlocks hX hE hp⟩
      obtain ⟨B, hB, B', hB', hBB', -, -⟩ :=
        exists_of_mem_interPairs (mem_interPairs_reachedBlocks hX hE hp)
      exact Finset.one_lt_card.2 ⟨B, hB, B', hB', hBB'⟩
    · rintro ⟨Y, -, hp, -⟩
      exact hp
  conv_lhs => rw [hEq]
  refine Finset.prod_biUnion fun Y hY Y' hY' hne => ?_
  have hYX := subset_of_mem_relComponents (oddComponents_subset E hY)
  have hYX' := subset_of_mem_relComponents (oddComponents_subset E hY')
  have hd := disjoint_biUnion_of_disjoint hX hYX hYX'
    (disjoint_of_mem_relComponents hX (oddComponents_subset E hY) (oddComponents_subset E hY') hne)
  rw [Function.onFun, Finset.disjoint_left]
  intro p hp hp'
  have h1 := (mem_pairsOn.1 (interPairs_subset_pairsOn (Finset.mem_inter.1 hp).2)).1
  have h1' := (mem_pairsOn.1 (interPairs_subset_pairsOn (Finset.mem_inter.1 hp').2)).1
  exact Finset.disjoint_left.1 hd h1 h1'

/-- The edges of `E` meeting a block `S` of a component `Y` are inter-block pairs of `Y`. -/
theorem blockDeg_inter_interPairs (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ interPairs X) {Y : Finset (Finset ℕ)} (hY : Y ∈ relComponents X E) {S : Finset ℕ}
    (hS : S ∈ Y) : blockDeg (E ∩ interPairs Y) S = blockDeg E S := by
  obtain ⟨a, -, rfl⟩ := mem_relComponents.1 hY
  have key : ∀ p ∈ E, (p.1 ∈ S ∨ p.2 ∈ S) → p ∈ interPairs (reachedBlocks X E a) := by
    intro p hp h
    have h1 : reachedBlocks X E p.1 = reachedBlocks X E a := by
      rcases h with h | h
      · exact reachedBlocks_eq_of_mem hS h
      · exact (reachedBlocks_snd_eq hE hp).symm.trans (reachedBlocks_eq_of_mem hS h)
    exact h1 ▸ mem_interPairs_reachedBlocks hX hE hp
  unfold blockDeg
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, key p h.1 (Or.inl h.2)⟩, h.2⟩⟩
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, key p h.1 (Or.inr h.2)⟩, h.2⟩⟩

/-- `E ∩ ℰ^inter(Y) ∪ ℰ^intra(Y)` connects the component `Y`. -/
theorem connOn_relComponents (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ interPairs X) {Y : Finset (Finset ℕ)} (hY : Y ∈ relComponents X E) :
    ConnOn (Y.biUnion id) (E ∩ interPairs Y ∪ intraPairs Y) := by
  obtain ⟨a, ha, rfl⟩ := mem_relComponents.1 hY
  obtain ⟨B, hB, haB⟩ := mem_biUnion_id.1 ha
  exact ((reachedBlocks_eq_iff hX hE (reachedBlocks_subset E a) (mem_reachedBlocks_self hB haB)
    haB).1 rfl).2

/-- Inside `Y`, the intra-block pairs alone never leave a block. -/
theorem mem_of_reachable_intraPairs {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y) {B : Finset ℕ} (hB : B ∈ Y) {i j : ℕ}
    (hi : i ∈ B) (h : (edgeGraph (intraPairs Y)).Reachable i j) : j ∈ B := by
  refine mem_of_reachable_of_closed (fun u v huv hu => ?_) hi h
  rcases exists_mem_of_edgeGraph_adj huv with h' | h'
  · obtain ⟨B', hB', hp⟩ := mem_intraPairs.1 h'
    have := eq_of_isSubpartition hY hB hB' hu (mem_pairsOn.1 hp).1
    exact this ▸ (mem_pairsOn.1 hp).2.1
  · obtain ⟨B', hB', hp⟩ := mem_intraPairs.1 h'
    have := eq_of_isSubpartition hY hB hB' hu (mem_pairsOn.1 hp).2.1
    exact this ▸ (mem_pairsOn.1 hp).1

/-- **On an odd component, the graph of the odd edges is in `𝖤^Y`.** -/
theorem isRelConnected_pairGraph (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ interPairs X) {Y : Finset (Finset ℕ)} (hY : Y ∈ oddComponents X E) :
    IsRelConnected Y (pairGraph (Y.biUnion id) (E ∩ interPairs Y)) := by
  obtain ⟨hYc, h2⟩ := mem_oddComponents.1 hY
  have hYX := subset_of_mem_relComponents hYc
  have hYs : IsSubpartition Y := isSubpartition_mono hX hYX
  have hconn := connOn_relComponents hX hE hYc
  refine ⟨pairGraph_le_interEdges Finset.inter_subset_right, ?_,
    connected_sup_intraEdges_of_connOn Finset.inter_subset_right hconn⟩
  -- an inter-block edge exists
  obtain ⟨B, hB, B', hB', hBB'⟩ := Finset.one_lt_card.1 h2
  have hEne : (E ∩ interPairs Y).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    obtain ⟨i, hi⟩ := hYs.1 B hB
    obtain ⟨j, hj⟩ := hYs.1 B' hB'
    have hr := hconn.2 i (subset_biUnion_of_mem hB hi) j (subset_biUnion_of_mem hB' hj)
    rw [h0, Finset.empty_union] at hr
    have := mem_of_reachable_intraPairs hYs hB hi hr
    exact hBB' (eq_of_isSubpartition hYs hB hB' this hj)
  obtain ⟨p, hp⟩ := hEne
  obtain ⟨h1, h2', h12⟩ := mem_pairsOn.1 (interPairs_subset_pairsOn (Finset.mem_inter.1 hp).2)
  refine ⟨s(⟨p.1, h1⟩, ⟨p.2, h2'⟩), ?_⟩
  rw [mem_edgeSet, pairGraph_adj]
  exact ⟨fun h => h12.ne (congrArg Subtype.val h), Or.inl hp⟩

open scoped Classical in
/-- The marks of a component, as vertices of its graph. -/
noncomputable def marksOn (Y : Finset (Finset ℕ)) (V₁ : Finset ℕ) : Finset (Y.biUnion id) :=
  Finset.univ.filter fun i => (i : ℕ) ∈ V₁

theorem card_blockSet_inter_marksOn {Y : Finset (Finset ℕ)} {S : Finset ℕ}
    (hS : S ⊆ Y.biUnion id) (V₁ : Finset ℕ) :
    (blockSet Y S ∩ marksOn Y V₁).card = (S ∩ V₁).card := by
  classical
  have h : blockSet Y S ∩ marksOn Y V₁ = (S ∩ V₁).subtype (· ∈ Y.biUnion id) := by
    ext i
    simp only [Finset.mem_inter, mem_blockSet, marksOn, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_subtype]
  rw [h, Finset.card_subtype]
  congr 1
  exact Finset.filter_true_of_mem fun i hi => hS (Finset.mem_inter.1 hi).1

/-- **Parity on a component**: if `E ∈ Eul^X(V₁)`, the graph of `E ∩ ℰ^inter(Y)` is in
`Eul^Y(V₁ ∩ V_Y)`. -/
theorem isRelEulerianOff_pairGraph (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ interPairs X) {V₁ : Finset ℕ} (hpar : IsParityPair X E V₁)
    {Y : Finset (Finset ℕ)} (hY : Y ∈ relComponents X E) :
    CoreForest.IsRelEulerianOff Y (marksOn Y V₁) (pairGraph (Y.biUnion id) (E ∩ interPairs Y)) := by
  classical
  have hYX := subset_of_mem_relComponents hY
  refine ⟨pairGraph_le_interEdges Finset.inter_subset_right, fun S hS => ?_⟩
  have hSY : S ⊆ Y.biUnion id := subset_biUnion_of_mem hS
  rw [blockDegree_pairGraph (Finset.inter_subset_right.trans interPairs_subset_pairsOn) hSY,
    blockDeg_inter_interPairs hX hE hY hS, card_blockSet_inter_marksOn hSY]
  exact hpar S (hYX hS)

end Components

/-! ### The tree `T^b` -/

section Tree

theorem connOn_mono {U : Finset ℕ} {E F : Finset (ℕ × ℕ)} (h : ConnOn U E) (hEF : E ⊆ F) :
    ConnOn U F :=
  ⟨h.1, fun i hi j hj => (h.2 i hi j hj).mono (edgeGraph_mono hEF)⟩

theorem isSubpartition_coarsen_oddComponents (hX : IsSubpartition X) (E : Finset (ℕ × ℕ)) :
    IsSubpartition (coarsen X (oddComponents X E)) :=
  isSubpartition_coarsen hX (fun _ hY => subset_of_mem_relComponents (oddComponents_subset E hY))
    (fun _ hY => nonempty_of_mem_relComponents (oddComponents_subset E hY))
    (pairwiseDisjoint_oddComponents hX E)

/-- Every intra-block pair of `X`, and every pair of `E₁`, is an intra-block pair of
`Coarse_X(oddComponents)`. -/
theorem mem_intraPairs_coarsen (hX : IsSubpartition X) {E₁ : Finset (ℕ × ℕ)}
    (hE₁ : E₁ ⊆ interPairs X) {p : ℕ × ℕ} (hp : p ∈ intraPairs X ∨ p ∈ E₁) :
    p ∈ intraPairs (coarsen X (oddComponents X E₁)) := by
  classical
  rcases hp with hp | hp
  · obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
    by_cases hin : ∃ Y ∈ oddComponents X E₁, B ∈ Y
    · obtain ⟨Y, hY, hBY⟩ := hin
      refine mem_intraPairs.2 ⟨Y.biUnion id, ?_, pairsOn_mono (subset_biUnion_of_mem hBY) hpB⟩
      unfold coarsen
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hY)
    · push Not at hin
      refine mem_intraPairs.2 ⟨B, ?_, hpB⟩
      unfold coarsen
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hB, hin⟩)
  · have hY : reachedBlocks X E₁ p.1 ∈ oddComponents X E₁ := by
      refine mem_oddComponents.2 ⟨mem_relComponents.2 ⟨p.1,
        (mem_pairsOn.1 (interPairs_subset_pairsOn (hE₁ hp))).1, rfl⟩, ?_⟩
      obtain ⟨B, hB, B', hB', hBB', -, -⟩ :=
        exists_of_mem_interPairs (mem_interPairs_reachedBlocks hX hE₁ hp)
      exact Finset.one_lt_card.2 ⟨B, hB, B', hB', hBB'⟩
    refine mem_intraPairs.2 ⟨(reachedBlocks X E₁ p.1).biUnion id, ?_,
      interPairs_subset_pairsOn (mem_interPairs_reachedBlocks hX hE₁ hp)⟩
    unfold coarsen
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hY)

/-- **The tree `T^b`**: for `E ∈ 𝖤_0^X` and `E₁ ⊆ E`, there is `T^b ∈ 𝖳_0^{Coarse_X(X_1, …, X_n)}`
(`X_1, …, X_n` the odd components of `E₁`) whose pairs lie in `E ∖ E₁`. -/
theorem exists_isRelTree₀_even (hX : IsSubpartition X) {E E₁ : Finset (ℕ × ℕ)}
    (hE : E ∈ relEdgeSets₀ X) (hE₁ : E₁ ⊆ E) {G : Finset (Finset (Finset ℕ))}
    (hG : G = oddComponents X E₁) :
    ∃ Tb : SimpleGraph ((coarsen X G).biUnion id),
      IsRelTree₀ (coarsen X G) Tb ∧ graphPairs Tb ⊆ E \ E₁ := by
  classical
  subst hG
  obtain ⟨hEX, hconn⟩ := mem_relEdgeSets₀.1 hE
  have hE₁X : E₁ ⊆ interPairs X := hE₁.trans hEX
  set C := coarsen X (oddComponents X E₁) with hCdef
  have hC : IsSubpartition C := isSubpartition_coarsen_oddComponents hX E₁
  have hW : C.biUnion id = X.biUnion id :=
    biUnion_coarsen fun _ hY => subset_of_mem_relComponents (oddComponents_subset E₁ hY)
  set F := (E \ E₁) ∩ interPairs C
  have hFC : F ⊆ interPairs C := Finset.inter_subset_right
  have hsub : E ∪ intraPairs X ⊆ F ∪ intraPairs C := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · by_cases h1 : p ∈ E₁
      · exact Finset.mem_union_right _ (mem_intraPairs_coarsen hX hE₁X (Or.inr h1))
      · by_cases h2 : p ∈ intraPairs C
        · exact Finset.mem_union_right _ h2
        · refine Finset.mem_union_left _ (Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨hp, h1⟩, ?_⟩)
          rw [interPairs, Finset.mem_sdiff, hW]
          exact ⟨interPairs_subset_pairsOn (hEX hp), h2⟩
    · exact Finset.mem_union_right _ (mem_intraPairs_coarsen hX hE₁X (Or.inl hp))
  have hconnC : ConnOn (C.biUnion id) (F ∪ intraPairs C) := by
    rw [hW]
    exact connOn_mono hconn hsub
  obtain ⟨T, hTG, hT⟩ := exists_isRelTree₀_le hC (pairGraph_le_interEdges hFC)
    (connected_sup_intraEdges_of_connOn hFC hconnC)
  refine ⟨T, hT, ?_⟩
  refine (graphPairs_mono hTG).trans ?_
  rw [graphPairs_pairGraph (hFC.trans interPairs_subset_pairsOn)]
  exact Finset.inter_subset_left

end Tree

end BoundedUpper

end UpperBound

end MultipoleBKT

end
