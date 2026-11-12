/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.MergeBasic

/-!
# Merging the outer and inner trees

The paper: the paragraph before Lemma 5.37: "For `|X| ≥ 2`, as
in the proof of Lemma 4.57, marking the outer edges of the merged `b`-tree determines the former
groups. The multiplicity is at most `2^{|T^b|} ≤ 2^{|X|-1}`", and the proof of Lemma 4.57.

The outer groups `𝒲` (disjoint groups of at least two blocks of `X`) carry a tree
`T^b ∈ 𝖳_0^{Coarse_X(𝒲)}`; each outer group `X' ∈ 𝒲` carries inner groups `𝒱_{X'}` and a tree
`T̃_{X'} ∈ 𝖳_0^{Coarse_{X'}(𝒱_{X'})}`. Flattened, the inner groups form `𝒱 = ⋃ 𝒱_{X'}` and the inner
trees `T̃ = ⋃ T̃_{X'}`; `Compat 𝒲 𝒱 T̃` records that `(𝒱, T̃)` comes from such a choice.

* `merged_mem_relTreePairs₀`: `T^b ∪ T̃ ∈ 𝖳_0^{Coarse_X(𝒱)}` (the merged tree);
* `disjoint_outer_inner`: `T^b ∩ T̃ = ∅`;
* `eq_of_compat`: the outer groups are determined by `(𝒱, T̃)`: they are the families `X' ⊆ X` of at
  least two blocks whose points are connected, and closed, in `T̃ ∪ ℰ^intra(Coarse_X(𝒱))`.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Finset SimpleGraph Multipole Hierarchical SetPartition AbsoluteLower

/-- Reachability transfers along a map of the edges into reachability. -/
theorem reachable_of_forall_adj_reachable {V : Type*} {G G' : SimpleGraph V}
    (h : ∀ u v, G.Adj u v → G'.Reachable u v) {x y : V} (hxy : G.Reachable x y) :
    G'.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

section Compat

open scoped Classical

/-- `(𝒱, T̃)` is a flattened choice of inner groups and inner trees for the outer groups `𝒲`: every
inner group lies in an outer group, the inner pairs in each outer group `X'` form a tree of
`Coarse_{X'}(𝒱_{X'})`, `𝒱_{X'} = {Y ∈ 𝒱 : Y ⊆ X'}`, and the inner pairs lie in the outer groups. -/
def Compat (𝒲 𝒱 : Finset (Finset (Finset ℕ))) (T : Finset (ℕ × ℕ)) : Prop :=
  (∀ Y ∈ 𝒱, ∃ X' ∈ 𝒲, Y ⊆ X') ∧
    (∀ X' ∈ 𝒲, T ∩ interPairs X' ∈ relTreePairs₀ (coarsen X' (𝒱.filter (· ⊆ X')))) ∧
    T ⊆ 𝒲.biUnion interPairs

/-- `U` is closed in the graph of the edge set `E`: edges leaving a point of `U` stay in `U`. -/
def Closed (U : Finset ℕ) (E : Finset (ℕ × ℕ)) : Prop :=
  ∀ u v, (edgeGraph E).Adj u v → u ∈ U → v ∈ U

end Compat

section Facts

open scoped Classical

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {𝒲 𝒱 : Finset (Finset (Finset ℕ))}
  (h𝒲 : 𝒲 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card))
  (h𝒱 : 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card)) {T : Finset (ℕ × ℕ)}
  (hC : Compat 𝒲 𝒱 T)

omit hX in
include h𝒲 in
theorem isSubpartition_of_mem_disjointFamilies (hX : IsSubpartition X) :
    IsSubpartition (coarsen X 𝒲) := by
  obtain ⟨hsub, hdisj, h2⟩ := mem_disjointFamilies.1 h𝒲
  exact isSubpartition_coarsen hX (fun Y hY => hsub Y hY)
    (fun Y hY => card_pos.1 (by have := h2 Y hY; omega)) hdisj

include hX h𝒲 in
/-- The points of distinct outer groups are disjoint. -/
theorem eq_of_mem_biUnion_of_mem_biUnion {X' X'' : Finset (Finset ℕ)} (hX' : X' ∈ 𝒲)
    (hX'' : X'' ∈ 𝒲) {i : ℕ} (hi' : i ∈ X'.biUnion id) (hi'' : i ∈ X''.biUnion id) :
    X' = X'' := by
  obtain ⟨hsub, hdisj, -⟩ := mem_disjointFamilies.1 h𝒲
  by_contra hne
  exact Finset.disjoint_left.1 (disjoint_biUnion_of_disjoint hX (hsub X' hX') (hsub X'' hX'')
    (hdisj hX' hX'' hne)) hi' hi''

include hX h𝒲 hC in
/-- An inner group lies in exactly the outer group containing one of its blocks. -/
theorem subset_of_mem_inner {Y X' : Finset (Finset ℕ)} (hY : Y ∈ 𝒱) (hX' : X' ∈ 𝒲)
    {S : Finset ℕ} (hSY : S ∈ Y) (hSX' : S ∈ X') : Y ⊆ X' := by
  obtain ⟨X'', hX'', hYX''⟩ := hC.1 Y hY
  obtain ⟨hsub, -, -⟩ := mem_disjointFamilies.1 h𝒲
  obtain ⟨i, hi⟩ := hX.1 S (hsub X' hX' hSX')
  have := eq_of_mem_biUnion_of_mem_biUnion hX h𝒲 hX'' hX' (subset_biUnion_of_mem (hYX'' hSY) hi)
    (subset_biUnion_of_mem hSX' hi)
  exact this ▸ hYX''

include hX h𝒲 hC in
/-- `ℰ^intra(Coarse_{X'}(𝒱_{X'})) ⊆ ℰ^intra(Coarse_X(𝒱))` for an outer group `X'`. -/
theorem intraPairs_inner_subset {X' : Finset (Finset ℕ)} (hX' : X' ∈ 𝒲) :
    intraPairs (coarsen X' (𝒱.filter (· ⊆ X'))) ⊆ intraPairs (coarsen X 𝒱) := by
  obtain ⟨hsub, -, -⟩ := mem_disjointFamilies.1 h𝒲
  intro q hq
  obtain ⟨B, hB, hqB⟩ := mem_intraPairs.1 hq
  refine mem_intraPairs.2 ⟨B, ?_, hqB⟩
  simp only [coarsen, mem_union, mem_image, mem_filter] at hB ⊢
  rcases hB with ⟨Y, ⟨hY, -⟩, rfl⟩ | ⟨hS, hSn⟩
  · exact Or.inl ⟨Y, hY, rfl⟩
  · refine Or.inr ⟨hsub X' hX' hS, fun Y hY hSY => hSn Y ⟨hY, ?_⟩ hSY⟩
    exact subset_of_mem_inner hX h𝒲 hC hY hX' hSY hS

include hX h𝒲 h𝒱 hC in
/-- **Every block of `Coarse_X(𝒲)` is closed** in `T̃ ∪ ℰ^intra(Coarse_X(𝒱))`. -/
theorem closed_of_mem_coarsen {B' : Finset ℕ} (hB' : B' ∈ coarsen X 𝒲) :
    Closed B' (T ∪ intraPairs (coarsen X 𝒱)) := by
  obtain ⟨hsub𝒲, -, -⟩ := mem_disjointFamilies.1 h𝒲
  obtain ⟨hsub𝒱, -, -⟩ := mem_disjointFamilies.1 h𝒱
  have hW := isSubpartition_of_mem_disjointFamilies h𝒲 hX
  have hV := isSubpartition_of_mem_disjointFamilies h𝒱 hX
  have hrefine : ∀ Y ∈ 𝒱, ∃ X' ∈ 𝒲, Y ⊆ X' := hC.1
  intro u v huv hu
  rcases exists_mem_of_edgeGraph_adj huv with hq | hq <;>
  · rcases mem_union.1 hq with hq | hq
    · -- an inner tree pair lies in one outer group, which is a block of `Coarse_X(𝒲)`
      obtain ⟨X', hX', hqX'⟩ := mem_biUnion.1 (hC.2.2 hq)
      have h12 := interPairs_subset_pairsOn_biUnion X' hqX'
      have hX'B : X'.biUnion id ∈ coarsen X 𝒲 := mem_union_left _ (mem_image_of_mem _ hX')
      first
        | (have := eq_of_mem_of_mem_coarsen hX hsub𝒲 (mem_disjointFamilies.1 h𝒲).2.1 hB' hX'B
            hu h12.1; rw [this]; exact h12.2)
        | (have := eq_of_mem_of_mem_coarsen hX hsub𝒲 (mem_disjointFamilies.1 h𝒲).2.1 hB' hX'B
            hu h12.2; rw [this]; exact h12.1)
    · -- an intra pair of `Coarse_X(𝒱)` lies in a block of `Coarse_X(𝒲)`
      obtain ⟨B, hB, hqB⟩ := mem_intraPairs.1 hq
      obtain ⟨B'', hB'', hBB''⟩ := exists_superset_mem_coarsen hrefine hB
      have h12 := mem_pairsOn.1 hqB
      first
        | (have := eq_of_mem_of_mem_coarsen hX hsub𝒲 (mem_disjointFamilies.1 h𝒲).2.1 hB' hB''
            hu (hBB'' h12.1); rw [this]; exact hBB'' h12.2.1)
        | (have := eq_of_mem_of_mem_coarsen hX hsub𝒲 (mem_disjointFamilies.1 h𝒲).2.1 hB' hB''
            hu (hBB'' h12.2.1); rw [this]; exact hBB'' h12.1)

include hX h𝒲 h𝒱 hC in
/-- **An outer group is connected** in `T̃ ∪ ℰ^intra(Coarse_X(𝒱))`. -/
theorem connOn_of_mem_outer {X' : Finset (Finset ℕ)} (hX' : X' ∈ 𝒲) :
    ConnOn (X'.biUnion id) (T ∪ intraPairs (coarsen X 𝒱)) := by
  obtain ⟨hsub, -, -⟩ := mem_disjointFamilies.1 h𝒲
  have hX's : IsSubpartition X' := isSubpartition_mono hX (hsub X' hX')
  have hT' := hC.2.1 X' hX'
  have hsubV : ∀ Y ∈ 𝒱.filter (· ⊆ X'), Y ⊆ X' := fun Y hY => (mem_filter.1 hY).2
  have hY' : IsSubpartition (coarsen X' (𝒱.filter (· ⊆ X'))) :=
    isSubpartition_coarsen hX's hsubV (fun Y hY => card_pos.1 (by
      have := (mem_disjointFamilies.1 h𝒱).2.2 Y (mem_filter.1 hY).1; omega))
      ((mem_disjointFamilies.1 h𝒱).2.1.subset (filter_subset _ _))
  have h := connOn_of_mem_relTreePairs₀ hY' hT'
  rw [biUnion_coarsen hsubV] at h
  refine ⟨h.1, fun i hi j hj => (h.2 i hi j hj).mono (edgeGraph_mono
    (union_subset_union inter_subset_left ?_))⟩
  exact intraPairs_inner_subset hX h𝒲 hC hX'

end Facts

/-! ### The recovery of the outer groups -/

section Recovery

open scoped Classical

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)

include hX in
/-- A subfamily of `X` is determined by its set of points. -/
theorem eq_of_biUnion_eq {X' X'' : Finset (Finset ℕ)} (hX' : X' ⊆ X) (hX'' : X'' ⊆ X)
    (h : X'.biUnion id = X''.biUnion id) : X' = X'' := by
  have key : ∀ {A B : Finset (Finset ℕ)}, A ⊆ X → B ⊆ X → A.biUnion id ⊆ B.biUnion id →
      A ⊆ B := by
    intro A B hA hB hAB S hS
    obtain ⟨i, hi⟩ := hX.1 S (hA hS)
    obtain ⟨S', hS', hiS'⟩ := mem_biUnion_id.1 (hAB (subset_biUnion_of_mem hS hi))
    have := eq_of_isSubpartition hX (hA hS) (hB hS') hi hiS'
    exact this ▸ hS'
  exact subset_antisymm (key hX' hX'' h.le) (key hX'' hX' h.ge)

variable {𝒲 𝒱 : Finset (Finset (Finset ℕ))}
  (h𝒲 : 𝒲 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card))
  (h𝒱 : 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card)) {T : Finset (ℕ × ℕ)}
  (hC : Compat 𝒲 𝒱 T)
include hX h𝒲 h𝒱 hC

/-- **The outer groups are recovered from the merged data**: `X' ∈ 𝒲` iff `X' ⊆ X`, `|X'| ≥ 2`,
and `V_{X'}` is connected and closed in `T̃ ∪ ℰ^intra(Coarse_X(𝒱))`. -/
theorem mem_outer_iff {X' : Finset (Finset ℕ)} :
    X' ∈ 𝒲 ↔ X' ⊆ X ∧ 2 ≤ X'.card ∧ ConnOn (X'.biUnion id) (T ∪ intraPairs (coarsen X 𝒱)) ∧
      Closed (X'.biUnion id) (T ∪ intraPairs (coarsen X 𝒱)) := by
  obtain ⟨hsub, hdisj, h2⟩ := mem_disjointFamilies.1 h𝒲
  constructor
  · intro hX'
    exact ⟨hsub X' hX', h2 X' hX', connOn_of_mem_outer hX h𝒲 h𝒱 hC hX',
      closed_of_mem_coarsen hX h𝒲 h𝒱 hC (mem_union_left _ (mem_image_of_mem _ hX'))⟩
  · rintro ⟨hX'X, hX'2, hconn, hclosed⟩
    obtain ⟨S, hS, S', hS', hSS'⟩ := Finset.one_lt_card.1 hX'2
    obtain ⟨i, hi⟩ := hX.1 S (hX'X hS)
    have hiV : i ∈ X'.biUnion id := subset_biUnion_of_mem hS hi
    -- the block of `Coarse_X(𝒲)` containing `i`
    have hiX : i ∈ (coarsen X 𝒲).biUnion id := by
      rw [biUnion_coarsen hsub]
      exact subset_biUnion_of_mem (hX'X hS) hi
    obtain ⟨B', hB', hiB'⟩ := mem_biUnion_id.1 hiX
    have hB'closed := closed_of_mem_coarsen hX h𝒲 h𝒱 hC hB'
    -- `V_{X'} ⊆ B'`
    have hsubB' : X'.biUnion id ⊆ B' := fun j hj =>
      mem_of_reachable_of_closed hB'closed hiB' (hconn.2 i hiV j hj)
    simp only [coarsen, mem_union, mem_image, mem_filter] at hB'
    rcases hB' with ⟨X'', hX'', rfl⟩ | ⟨hB'X, hB'n⟩
    · -- `B' = V_{X''}`; then `V_{X''} ⊆ V_{X'}` and `X' = X''`
      have hconn'' := connOn_of_mem_outer hX h𝒲 h𝒱 hC hX''
      have hsub'' : X''.biUnion id ⊆ X'.biUnion id := fun j hj =>
        mem_of_reachable_of_closed hclosed hiV (hconn''.2 i hiB' j hj)
      have := eq_of_biUnion_eq hX hX'X (hsub X'' hX'') (subset_antisymm hsubB' hsub'')
      exact this ▸ hX''
    · -- `B'` is a single block of `X`, which cannot contain two blocks of `X'`
      obtain ⟨j, hj⟩ := hX.1 S' (hX'X hS')
      have hjB' := hsubB' (subset_biUnion_of_mem hS' hj)
      have h1 := eq_of_isSubpartition hX (hX'X hS) hB'X hi hiB'
      have h2 := eq_of_isSubpartition hX (hX'X hS') hB'X hj hjB'
      exact absurd (h1.trans h2.symm) hSS'

end Recovery

/-- **The outer groups are determined by `(𝒱, T̃)`.** -/
theorem eq_of_compat {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {𝒲₁ 𝒲₂ 𝒱 : Finset (Finset (Finset ℕ))}
    (h𝒲₁ : 𝒲₁ ∈ disjointFamilies X (fun Y => 2 ≤ Y.card))
    (h𝒲₂ : 𝒲₂ ∈ disjointFamilies X (fun Y => 2 ≤ Y.card))
    (h𝒱 : 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card)) {T : Finset (ℕ × ℕ)}
    (hC₁ : Compat 𝒲₁ 𝒱 T) (hC₂ : Compat 𝒲₂ 𝒱 T) : 𝒲₁ = 𝒲₂ := by
  ext X'
  rw [mem_outer_iff hX h𝒲₁ h𝒱 hC₁, mem_outer_iff hX h𝒲₂ h𝒱 hC₂]

/-! ### The merged tree -/

section Merged

open scoped Classical

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {𝒲 𝒱 : Finset (Finset (Finset ℕ))}
  (h𝒲 : 𝒲 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card))
  (h𝒱 : 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card)) {T : Finset (ℕ × ℕ)}
  (hC : Compat 𝒲 𝒱 T) {Tb : Finset (ℕ × ℕ)} (hTb : Tb ∈ relTreePairs₀ (coarsen X 𝒲))
include hX h𝒲 h𝒱 hC hTb

omit h𝒱 in
/-- The outer tree and the inner trees are disjoint. -/
theorem disjoint_outer_inner : Disjoint Tb T := by
  have hW := isSubpartition_of_mem_disjointFamilies h𝒲 hX
  have hTbI := subset_interPairs_of_mem_relTreePairs₀ hW hTb
  rw [Finset.disjoint_left]
  intro q hqb hqT
  obtain ⟨X', hX', hqX'⟩ := mem_biUnion.1 (hC.2.2 hqT)
  refine (mem_interPairs.1 (hTbI hqb)).2 ⟨X'.biUnion id, mem_union_left _ (mem_image_of_mem _ hX'),
    ?_⟩
  have h12 := interPairs_subset_pairsOn_biUnion X' hqX'
  exact mem_pairsOn.2 ⟨h12.1, h12.2, (mem_pairsOn.1 (interPairs_subset_pairsOn hqX')).2.2⟩

/-- **The merged tree**: `T^b ∪ T̃ ∈ 𝖳_0^{Coarse_X(𝒱)}`. -/
theorem merged_mem_relTreePairs₀ : Tb ∪ T ∈ relTreePairs₀ (coarsen X 𝒱) := by
  obtain ⟨hsub𝒲, hdisj𝒲, h2𝒲⟩ := mem_disjointFamilies.1 h𝒲
  obtain ⟨hsub𝒱, hdisj𝒱, h2𝒱⟩ := mem_disjointFamilies.1 h𝒱
  have hW := isSubpartition_of_mem_disjointFamilies h𝒲 hX
  have hV := isSubpartition_of_mem_disjointFamilies h𝒱 hX
  set G := T ∪ intraPairs (coarsen X 𝒱) with hG
  rw [mem_relTreePairs₀_iff hV]
  refine ⟨union_subset ((subset_interPairs_of_mem_relTreePairs₀ hW hTb).trans
    (interPairs_coarsen_mono hC.1 hsub𝒲 hsub𝒱)) ?_, ?_, ?_⟩
  · -- the inner pairs are inter-block pairs of `Coarse_X(𝒱)`
    intro q hq
    obtain ⟨X', hX', hqX'⟩ := mem_biUnion.1 (hC.2.2 hq)
    have hX's : IsSubpartition X' := isSubpartition_mono hX (hsub𝒲 X' hX')
    have hsubF : ∀ Y ∈ 𝒱.filter (· ⊆ X'), Y ⊆ X' := fun Y hY => (mem_filter.1 hY).2
    have hY' : IsSubpartition (coarsen X' (𝒱.filter (· ⊆ X'))) :=
      isSubpartition_coarsen hX's hsubF (fun Y hY => card_pos.1 (by
        have := h2𝒱 Y (mem_filter.1 hY).1; omega)) (hdisj𝒱.subset (filter_subset _ _))
    have hqI := subset_interPairs_of_mem_relTreePairs₀ hY' (hC.2.1 X' hX')
      (mem_inter.2 ⟨hq, hqX'⟩)
    rw [mem_interPairs, biUnion_coarsen hsubF] at hqI
    rw [mem_interPairs, biUnion_coarsen hsub𝒱]
    refine ⟨pairsOn_mono (biUnion_subset_biUnion_of_subset_left id (hsub𝒲 X' hX')) hqI.1,
      fun ⟨B, hB, hqB⟩ => hqI.2 ⟨B, ?_, hqB⟩⟩
    -- the block `B` of `Coarse_X(𝒱)` lies in `X'`
    have h12 := mem_pairsOn.1 hqI.1
    simp only [coarsen, mem_union, mem_image, mem_filter] at hB ⊢
    rcases hB with ⟨Y, hY, rfl⟩ | ⟨hS, hSn⟩
    · refine Or.inl ⟨Y, ⟨hY, ?_⟩, rfl⟩
      obtain ⟨S, hS, hiS⟩ := mem_biUnion_id.1 (mem_pairsOn.1 hqB).1
      obtain ⟨S', hS', hiS'⟩ := mem_biUnion_id.1 h12.1
      have := eq_of_isSubpartition hX (hsub𝒱 Y hY hS) (hsub𝒲 X' hX' hS') hiS hiS'
      exact subset_of_mem_inner hX h𝒲 hC hY hX' hS (this ▸ hS')
    · obtain ⟨S', hS', hiS'⟩ := mem_biUnion_id.1 h12.1
      have := eq_of_isSubpartition hX hS (hsub𝒲 X' hX' hS') (mem_pairsOn.1 hqB).1 hiS'
      exact Or.inr ⟨this ▸ hS', fun Y hY hBY => hSn Y hY.1 hBY⟩
  · -- connectivity: transfer from `T^b ∪ ℰ^intra(Coarse_X(𝒲))`
    have hconnb := connOn_of_mem_relTreePairs₀ hW hTb
    rw [biUnion_coarsen hsub𝒲] at hconnb
    rw [biUnion_coarsen hsub𝒱]
    refine ⟨hconnb.1, fun i hi j hj => ?_⟩
    refine reachable_of_forall_adj_reachable (fun u v huv => ?_) (hconnb.2 i hi j hj)
    -- each edge of `T^b ∪ ℰ^intra(Coarse_X(𝒲))` is joined in the new graph
    have hmono : edgeGraph G ≤ edgeGraph (Tb ∪ T ∪ intraPairs (coarsen X 𝒱)) :=
      edgeGraph_mono (union_subset_union subset_union_right subset_rfl)
    have hne := (edgeGraph_adj.1 huv).1
    have hcase : ∀ a b, (a, b) ∈ Tb ∪ intraPairs (coarsen X 𝒲) →
        (edgeGraph (Tb ∪ T ∪ intraPairs (coarsen X 𝒱))).Reachable a b := by
      intro a b hab
      rcases mem_union.1 hab with hb | hb
      · by_cases hab' : a = b
        · rw [hab']
        · exact (edgeGraph_adj.2 ⟨hab', Or.inl (mem_union_left _ (mem_union_left _ hb))⟩).reachable
      · obtain ⟨B', hB', hqB'⟩ := mem_intraPairs.1 hb
        have h12 := mem_pairsOn.1 hqB'
        simp only [coarsen, mem_union, mem_image, mem_filter] at hB'
        rcases hB' with ⟨X', hX', rfl⟩ | ⟨hS, hSn⟩
        · exact ((connOn_of_mem_outer hX h𝒲 h𝒱 hC hX').2 a h12.1 b h12.2.1).mono hmono
        · -- a block of `X` in no outer group is a block of `Coarse_X(𝒱)`
          have hSV : B' ∈ coarsen X 𝒱 := by
            refine mem_union_right _ (mem_filter.2 ⟨hS, fun Y hY hSY => ?_⟩)
            obtain ⟨X', hX', hYX'⟩ := hC.1 Y hY
            exact hSn X' hX' (hYX' hSY)
          refine (edgeGraph_adj.2 ⟨h12.2.2.ne, Or.inl (mem_union_right _ (mem_intraPairs.2
            ⟨B', hSV, hqB'⟩))⟩).reachable
    rcases exists_mem_of_edgeGraph_adj huv with h | h
    · exact hcase u v h
    · exact (hcase v u h).symm
  · -- the number of edges
    have hTbcard := card_add_one_of_mem_relTreePairs₀ hW hTb
    have hdisjTb := disjoint_outer_inner hX h𝒲 hC hTb
    -- the inner trees
    set 𝒱' : Finset (Finset ℕ) → Finset (Finset (Finset ℕ)) := fun X' => 𝒱.filter (· ⊆ X')
      with h𝒱'
    have hinner : ∀ X' ∈ 𝒲, (T ∩ interPairs X').card + 1 = (coarsen X' (𝒱' X')).card ∧
        (coarsen X' (𝒱' X')).card + ∑ Y ∈ 𝒱' X', Y.card = X'.card + (𝒱' X').card := by
      intro X' hX'
      have hX's : IsSubpartition X' := isSubpartition_mono hX (hsub𝒲 X' hX')
      have hsubF : ∀ Y ∈ 𝒱' X', Y ⊆ X' := fun Y hY => (mem_filter.1 hY).2
      have hneF : ∀ Y ∈ 𝒱' X', Y.Nonempty := fun Y hY => card_pos.1 (by
        have := h2𝒱 Y (mem_filter.1 hY).1; omega)
      have hdF := hdisj𝒱.subset (filter_subset (· ⊆ X') 𝒱)
      have hY' : IsSubpartition (coarsen X' (𝒱' X')) := isSubpartition_coarsen hX's hsubF hneF hdF
      exact ⟨card_add_one_of_mem_relTreePairs₀ hY' (hC.2.1 X' hX'),
        card_coarsen_add hX's hsubF hneF hdF⟩
    have hneW : ∀ Y ∈ 𝒲, Y.Nonempty := fun Y hY => card_pos.1 (by have := h2𝒲 Y hY; omega)
    have hneV : ∀ Y ∈ 𝒱, Y.Nonempty := fun Y hY => card_pos.1 (by have := h2𝒱 Y hY; omega)
    have hcW := card_coarsen_add hX hsub𝒲 hneW hdisj𝒲
    have hcV := card_coarsen_add hX hsub𝒱 hneV hdisj𝒱
    -- `T` and `𝒱` split along the outer groups
    have hTsplit : T = 𝒲.biUnion fun X' => T ∩ interPairs X' := by
      ext q
      simp only [mem_biUnion, mem_inter]
      exact ⟨fun hq => by
        obtain ⟨X', hX', hqX'⟩ := mem_biUnion.1 (hC.2.2 hq)
        exact ⟨X', hX', hq, hqX'⟩, fun ⟨_, _, hq, _⟩ => hq⟩
    have hTd : (𝒲 : Set (Finset (Finset ℕ))).PairwiseDisjoint fun X' => T ∩ interPairs X' := by
      intro X' hX' X'' hX'' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro q hq hq'
      exact hne (eq_of_mem_biUnion_of_mem_biUnion hX h𝒲 hX' hX''
        (interPairs_subset_pairsOn_biUnion X' (mem_inter.1 hq).2).1
        (interPairs_subset_pairsOn_biUnion X'' (mem_inter.1 hq').2).1)
    have hVsplit : 𝒱 = 𝒲.biUnion 𝒱' := by
      ext Y
      simp only [h𝒱', mem_biUnion, mem_filter]
      exact ⟨fun hY => by
        obtain ⟨X', hX', hYX'⟩ := hC.1 Y hY
        exact ⟨X', hX', hY, hYX'⟩, fun ⟨_, _, hY, _⟩ => hY⟩
    have hVd : (𝒲 : Set (Finset (Finset ℕ))).PairwiseDisjoint 𝒱' := by
      intro X' hX' X'' hX'' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro Y hY hY'
      obtain ⟨S, hS⟩ := hneV Y (mem_filter.1 hY).1
      exact Finset.disjoint_left.1 (hdisj𝒲 hX' hX'' hne) ((mem_filter.1 hY).2 hS)
        ((mem_filter.1 hY').2 hS)
    have hTcard : T.card = ∑ X' ∈ 𝒲, (T ∩ interPairs X').card := by
      conv_lhs => rw [hTsplit]
      exact card_biUnion hTd
    have hsumY : ∑ Y ∈ 𝒱, Y.card = ∑ X' ∈ 𝒲, ∑ Y ∈ 𝒱' X', Y.card := by
      conv_lhs => rw [hVsplit]
      exact sum_biUnion hVd
    have hVcard : 𝒱.card = ∑ X' ∈ 𝒲, (𝒱' X').card := by
      conv_lhs => rw [hVsplit]
      exact card_biUnion hVd
    have hsum1 : ∑ X' ∈ 𝒲, ((T ∩ interPairs X').card + 1) =
        ∑ X' ∈ 𝒲, (coarsen X' (𝒱' X')).card := sum_congr rfl fun X' hX' => (hinner X' hX').1
    have hsum2 : ∑ X' ∈ 𝒲, ((coarsen X' (𝒱' X')).card + ∑ Y ∈ 𝒱' X', Y.card) =
        ∑ X' ∈ 𝒲, (X'.card + (𝒱' X').card) := sum_congr rfl fun X' hX' => (hinner X' hX').2
    rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at hsum1
    rw [sum_add_distrib, sum_add_distrib] at hsum2
    rw [card_union_of_disjoint hdisjTb, hTcard]
    omega

end Merged

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
