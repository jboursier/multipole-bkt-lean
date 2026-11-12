/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Model
public import MultipoleBKT.Multipole.RouteGrouping.Correspondence

/-!
# Grouping the expanded pairs and the compact activity interface

Definition 4.15, (4.36) in proof of Lemma 4.18, and Corollary 4.61.

Fix a configuration, with Mayer bonds `f(p)` and separation indicators `b(p)`.
The starting-bound expansion keeps the two edge families separate:

* expand the Mayer edges and group their components (`prod_one_add_interPairs`)
* retain the separation factors inside those components and expand the rest
  (`prod_interPairs_eq_prod_mul`)
* group the separation edges on the contracted components, then use the explicit
  correspondence `RouteGrouping.componentGroupingEquiv` to group by their union
  (`prod_eq_partitionSum_groupWeight`)
* express the resulting connected coefficient as the ordered series of
  Definition 4.15 (`clusterSeries_eq_groupWeight`). Singleton components have
  weight one (`groupWeight_singleton`), so unused blocks are retained.

The starting-bound integrals use these grouped weights directly. The compact
identity `clusterSeries_eq_sum_relEdgeSets` remains an interface for estimates.
Its identification `relConnSum_eq_groupWeight` uses induction on the number of
blocks through `eq_of_partitionSum_eq`. This induction also supports the separate
identification of the two activities in Corollary 4.61. It is not a step in the
proof of (4.36).
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition

open scoped Classical

/-! ### Products over the inter-block pairs -/

section Expansion

variable {X : Finset (Finset ℕ)}

/-- Grouping the edge sets of `ℰ^inter(Y)` by connected components relative to `Y`, for every
subfamily `Y` of a subpartition `X`. -/
theorem sum_powerset_interPairs_eq_partitionSum {R : Type*} [CommSemiring R] (g : ℕ × ℕ → R)
    (hX : IsSubpartition X) :
    ∀ Y ⊆ X, ∑ E ∈ (interPairs Y).powerset, ∏ p ∈ E, g p = partitionSum (relConnSum g) Y := by
  refine eq_partitionSum_of_root _ X ?_ fun Y hY B₀ hB₀ =>
    sum_powerset_interPairs_root (isSubpartition_mono hX hY) hB₀ g
  have : interPairs (∅ : Finset (Finset ℕ)) = ∅ := by simp [interPairs, pairsOn]
  simp [this]

/-- **The component expansion** (Step 5 of Lemma 4.18): for a subpartition `X` and a pair weight
`g`, `∏_{ij ∈ ℰ^inter(X)} (1 + g_ij) = ∑_{ρ ∈ 𝚷(X)} ∏_{D ∈ ρ} ∑_{E ∈ 𝖤_0^D} ∏_{ij ∈ E} g_ij`. -/
theorem prod_one_add_interPairs {R : Type*} [CommSemiring R] (g : ℕ × ℕ → R)
    (hX : IsSubpartition X) :
    ∏ p ∈ interPairs X, (1 + g p) = partitionSum (relConnSum g) X := by
  rw [Finset.prod_one_add]
  exact sum_powerset_interPairs_eq_partitionSum g hX X le_rfl

end Expansion

/-! ### Coarsening by a partition of the blocks -/

section Merge

/-- The coarsening `{V_T : T ∈ σ}` of a subpartition by a partition `σ` of its blocks. -/
def merge (σ : Finset (Finset (Finset ℕ))) : Finset (Finset ℕ) :=
  σ.image fun T => T.biUnion id

variable {X : Finset (Finset ℕ)}

theorem mem_partitions_self (hX : IsSubpartition X) : X ∈ partitions (X.biUnion id) :=
  mem_partitions.2 ⟨hX, rfl⟩

theorem merge_mem_partitions (hX : IsSubpartition X) {σ : Finset (Finset (Finset ℕ))}
    (hσ : σ ∈ partitions X) : merge σ ∈ partitions (X.biUnion id) :=
  image_biUnion_mem_partitions (mem_partitions_self hX) hσ

theorem isSubpartition_merge (hX : IsSubpartition X) {σ : Finset (Finset (Finset ℕ))}
    (hσ : σ ∈ partitions X) : IsSubpartition (merge σ) :=
  (mem_partitions.1 (merge_mem_partitions hX hσ)).1

/-- The unions of the blocks of two disjoint subfamilies of a subpartition are disjoint. -/
theorem disjoint_biUnion_of_disjoint (hX : IsSubpartition X) {Y Y' : Finset (Finset ℕ)}
    (hY : Y ⊆ X) (hY' : Y' ⊆ X) (h : Disjoint Y Y') :
    Disjoint (Y.biUnion id) (Y'.biUnion id) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨B, hB, hxB⟩ := mem_biUnion_id.1 hx
  obtain ⟨B', hB', hxB'⟩ := mem_biUnion_id.1 hx'
  rw [eq_of_isSubpartition hX (hY hB) (hY' hB') hxB hxB'] at hB
  exact Finset.disjoint_left.1 h hB hB'

theorem interPairs_subset_pairsOn_biUnion (Y : Finset (Finset ℕ)) {p : ℕ × ℕ}
    (hp : p ∈ interPairs Y) : p.1 ∈ Y.biUnion id ∧ p.2 ∈ Y.biUnion id :=
  ⟨(mem_pairsOn.1 (interPairs_subset_pairsOn hp)).1,
    (mem_pairsOn.1 (interPairs_subset_pairsOn hp)).2.1⟩

/-- **The inter-block pairs of a coarsening** (Step 6 of Lemma 4.18): for a partition `σ` of the
blocks of `X`, `ℰ^inter(X)` is the disjoint union of the `ℰ^inter(T)`, `T ∈ σ`, and of
`ℰ^inter(Coarse(σ))`. -/
theorem prod_interPairs_eq_prod_mul {M : Type*} [CommMonoid M] (hX : IsSubpartition X)
    {σ : Finset (Finset (Finset ℕ))} (hσ : σ ∈ partitions X) (h : ℕ × ℕ → M) :
    ∏ p ∈ interPairs X, h p =
      (∏ T ∈ σ, ∏ p ∈ interPairs T, h p) * ∏ p ∈ interPairs (merge σ), h p := by
  have hσs := (mem_partitions.1 hσ).1
  have hTX : ∀ T ∈ σ, T ⊆ X := fun T hT => subset_of_mem_partitions hσ hT
  have hmerge := isSubpartition_merge hX hσ
  have hinj := injOn_biUnion hX hσ
  have hdisjV : ∀ T ∈ σ, ∀ T' ∈ σ, T ≠ T' → Disjoint (T.biUnion id) (T'.biUnion id) :=
    fun T hT T' hT' hTT' => disjoint_biUnion_of_disjoint hX (hTX T hT) (hTX T' hT')
      (disjoint_of_isSubpartition hσs hT hT' hTT')
  -- the groups of `σ` cover the blocks of `X`
  have hgroup : ∀ B ∈ X, ∃ T ∈ σ, B ∈ T := fun B hB => exists_mem_of_mem_partitions hσ hB
  have hpd : (σ : Set (Finset (Finset ℕ))).PairwiseDisjoint interPairs := by
    intro T hT T' hT' hTT'
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    exact Finset.disjoint_left.1 (hdisjV T hT T' hT' hTT')
      (interPairs_subset_pairsOn_biUnion T hp).1 (interPairs_subset_pairsOn_biUnion T' hp').1
  have hdisj : Disjoint (σ.biUnion interPairs) (interPairs (merge σ)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨T, hT, hpT⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨D, hD, D', hD', hDD', h1, h2⟩ := exists_of_mem_interPairs hp'
    obtain ⟨h1T, h2T⟩ := interPairs_subset_pairsOn_biUnion T hpT
    have hVT : T.biUnion id ∈ merge σ := Finset.mem_image_of_mem _ hT
    exact hDD' ((eq_of_isSubpartition hmerge hD hVT h1 h1T).trans
      (eq_of_isSubpartition hmerge hD' hVT h2 h2T).symm)
  have hunion : interPairs X = σ.biUnion interPairs ∪ interPairs (merge σ) := by
    ext p
    rw [Finset.mem_union, Finset.mem_biUnion]
    constructor
    · intro hp
      obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := exists_of_mem_interPairs hp
      have h12 := (mem_pairsOn.1 (interPairs_subset_pairsOn hp)).2.2
      obtain ⟨T, hT, hBT⟩ := hgroup B hB
      obtain ⟨T', hT', hB'T'⟩ := hgroup B' hB'
      by_cases hTT' : T = T'
      · subst hTT'
        exact Or.inl ⟨T, hT, mem_interPairs_of (isSubpartition_mono hX (hTX T hT)) hBT hB'T'
          hBB' h1 h2 h12⟩
      · refine Or.inr (mem_interPairs_of hmerge (Finset.mem_image_of_mem _ hT)
          (Finset.mem_image_of_mem _ hT') (fun h => hTT' (hinj hT hT' h))
          (mem_biUnion_id.2 ⟨B, hBT, h1⟩) (mem_biUnion_id.2 ⟨B', hB'T', h2⟩) h12)
    · rintro (⟨T, hT, hpT⟩ | hp)
      · exact interPairs_subset_of_subset hX (hTX T hT) hpT
      · obtain ⟨D, hD, D', hD', hDD', h1, h2⟩ := exists_of_mem_interPairs hp
        have h12 := (mem_pairsOn.1 (interPairs_subset_pairsOn hp)).2.2
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hD
        obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hD'
        obtain ⟨B, hB, h1B⟩ := mem_biUnion_id.1 h1
        obtain ⟨B', hB', h2B'⟩ := mem_biUnion_id.1 h2
        refine mem_interPairs_of hX (hTX T hT hB) (hTX T' hT' hB') (fun hBB' => hDD' ?_) h1B
          h2B' h12
        subst hBB'
        have : T = T' := by
          by_contra hne
          exact Finset.disjoint_left.1 (disjoint_of_isSubpartition hσs hT hT' hne) hB hB'
        rw [this]
  rw [hunion, Finset.prod_union hdisj, Finset.prod_biUnion hpd]

/-- **Transport of partition sums along an injective map**: for `e` injective on `s₀` and
`s ⊆ s₀`, `∑_{ρ ∈ 𝚷(e(s))} ∏_{D ∈ ρ} K(D) = ∑_{ρ ∈ 𝚷(s)} ∏_{D ∈ ρ} K(e(D))`. -/
theorem partitionSum_image {α β R : Type*} [DecidableEq α] [DecidableEq β] [CommSemiring R]
    (e : α → β) (s₀ : Finset α) (he : Set.InjOn e s₀) (K : Finset β → R) :
    ∀ s ⊆ s₀, partitionSum K (s.image e) = partitionSum (fun D => K (D.image e)) s := by
  refine eq_partitionSum_of_root _ s₀ ?_ fun s hs a ha => ?_
  · simp only [Finset.image_empty]
    exact partitionSum_empty K
  have hes : Set.InjOn e s := he.mono (Finset.coe_subset.2 hs)
  rw [partitionSum_root K (Finset.mem_image_of_mem e ha)]
  symm
  refine Finset.sum_nbij' (fun D => D.image e) (fun D' => s.filter fun x => e x ∈ D')
    (fun D hD => ?_) (fun D' hD' => ?_) (fun D hD => ?_) (fun D' hD' => ?_) (fun D hD => ?_)
  · rw [Finset.mem_filter, Finset.mem_powerset] at hD ⊢
    exact ⟨Finset.image_subset_image hD.1, Finset.mem_image_of_mem e hD.2⟩
  · rw [Finset.mem_filter, Finset.mem_powerset] at hD' ⊢
    exact ⟨Finset.filter_subset _ _, Finset.mem_filter.2 ⟨ha, hD'.2⟩⟩
  · rw [Finset.mem_filter, Finset.mem_powerset] at hD
    ext x
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hex⟩
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hex
      rwa [← hes (hD.1 hy) hx hyx]
    · intro hx
      exact ⟨hD.1 hx, Finset.mem_image_of_mem e hx⟩
  · rw [Finset.mem_filter, Finset.mem_powerset] at hD'
    ext y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.1 hx).2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (hD'.1 hy)
      exact ⟨x, Finset.mem_filter.2 ⟨hx, hy⟩, rfl⟩
  · rw [Finset.mem_filter, Finset.mem_powerset] at hD
    rw [image_sdiff_of_injOn hes hD.1]

end Merge

/-! ### The two expansions and the identification of the block weights -/

section Weights

variable (f b : ℕ × ℕ → ℝ)

/-- The weight of a group `T` (a set of blocks connected by Mayer bonds):
`(∑_{E ∈ 𝖤_0^T} ∏_E f) ∏_{ℰ^inter(T)} (1 - b)`. -/
noncomputable def groupFactor (T : Finset (Finset ℕ)) : ℝ :=
  relConnSum f T * ∏ p ∈ interPairs T, (1 - b p)

/-- The block weight `∑_{Y ∈ 𝚷(D)} ∏_{T ∈ Y} groupFactor(T) · ∑_{F ∈ 𝖤_0^{Coarse(Y)}} ∏_F (-b)`. -/
noncomputable def groupWeight (D : Finset (Finset ℕ)) : ℝ :=
  ∑ Y ∈ partitions D, (∏ T ∈ Y, groupFactor f b T) * relConnSum (fun p => -b p) (merge Y)

variable {f b}

/-- **Direct grouping of the expanded pairs**, (4.36) in
proof of Lemma 4.18. First `σ` records the Mayer
components. The separation edges connect their unions. The partition of `σ` into
these new components is transported back to the original blocks and the inner
Mayer components are restricted to each new component. Singleton components keep
weight one. -/
theorem prod_eq_partitionSum_groupWeight {U : Finset (Finset ℕ)}
    (hU : IsSubpartition U) :
    ∏ p ∈ interPairs U, ((1 + f p) * (1 - b p)) =
      partitionSum (groupWeight f b) U := by
  rw [Finset.prod_mul_distrib, prod_one_add_interPairs f hU, partitionSum, Finset.sum_mul]
  have hG : groupWeight f b = fun D => ∑ Y ∈ partitions D,
      (fun 𝒰 : Finset (Finset (Finset ℕ)) =>
        (∏ T ∈ 𝒰, groupFactor f b T) * relConnSum (fun p => -b p) (merge 𝒰)) Y := rfl
  rw [hG, ← RouteGrouping.sum_nested_component_weights]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hσs := (mem_partitions.1 hσ).1
  rw [prod_interPairs_eq_prod_mul hU hσ]
  have h1 : ∏ p ∈ interPairs (merge σ), (1 - b p) =
      partitionSum (relConnSum fun p => -b p) (merge σ) := by
    rw [← prod_one_add_interPairs _ (isSubpartition_merge hU hσ)]
    simp_rw [sub_eq_add_neg]
  rw [h1, ← mul_assoc, ← Finset.prod_mul_distrib, merge,
    partitionSum_image (fun T => T.biUnion id) σ (injOn_biUnion hU hσ) _ σ le_rfl,
    partitionSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  have hτs := (mem_partitions.1 hτ).1
  have hτU : τ.biUnion id = σ := (mem_partitions.1 hτ).2
  have hsplit : ∏ T ∈ σ, groupFactor f b T = ∏ 𝒰 ∈ τ, ∏ T ∈ 𝒰, groupFactor f b T := by
    conv_lhs => rw [← hτU]
    exact Finset.prod_biUnion hτs.2
  change (∏ T ∈ σ, groupFactor f b T) * ∏ 𝒰 ∈ τ, relConnSum (fun p => -b p) (merge 𝒰) = _
  rw [hsplit, ← Finset.prod_mul_distrib]

/-- The compact and directly grouped partition sums have the same product expansion. -/
theorem partitionSum_relConnSum_eq_partitionSum_groupWeight {U : Finset (Finset ℕ)}
    (hU : IsSubpartition U) :
    partitionSum (relConnSum fun p => (1 + f p) * (1 - b p) - 1) U =
      partitionSum (groupWeight f b) U := by
  rw [← prod_one_add_interPairs _ hU]
  simp_rw [add_sub_cancel]
  exact prod_eq_partitionSum_groupWeight hU

/-- **Inductive identification for the compact interface**: for a nonempty
subfamily `D` of a subpartition, `∑_{E ∈ 𝖤_0^D} ∏_E ((1 + f)(1 - b) - 1) = groupWeight f b D`. -/
theorem relConnSum_eq_groupWeight {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {D : Finset (Finset ℕ)} (hD : D ⊆ X) (hne : D.Nonempty) :
    relConnSum (fun p => (1 + f p) * (1 - b p) - 1) D = groupWeight f b D :=
  eq_of_partitionSum_eq X (fun _ hU =>
    partitionSum_relConnSum_eq_partitionSum_groupWeight (isSubpartition_mono hX hU)) D hD hne

/-- An unused block has weight one in the unmarked component grouping of (4.36) in the proof of Lemma 4.18. -/
theorem groupWeight_singleton {S : Finset ℕ} (hS : S.Nonempty) :
    groupWeight f b {S} = 1 := by
  have hparts : partitions ({S} : Finset (Finset ℕ)) = {{{S}}} := by
    ext σ
    rw [Finset.mem_singleton]
    constructor
    · intro hσ
      have hblock : ∀ T ∈ σ, T = {S} := by
        intro T hT
        exact Finset.eq_singleton_iff_nonempty_unique_mem.2
          ⟨(mem_partitions.1 hσ).1.1 T hT,
            fun B hB => Finset.mem_singleton.1 (subset_of_mem_partitions hσ hT hB)⟩
      have hne := Finset.card_pos.1 (card_pos_of_mem_partitions hσ (Finset.singleton_nonempty S))
      exact Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hblock⟩
    · rintro rfl
      exact singleton_mem_partitions (Finset.singleton_nonempty S)
  rw [groupWeight, hparts, Finset.sum_singleton, Finset.prod_singleton,
    groupFactor, relConnSum_singleton hS, interPairs_singleton, Finset.prod_empty]
  simp only [merge, Finset.image_singleton, Finset.singleton_biUnion, id_eq]
  rw [relConnSum_singleton hS]
  norm_num

end Weights

/-! ### Ordered tuples of groups -/

section Tuples

variable {β : Type*} [DecidableEq β]

/-- For a fixed number `n` of entries, the sum over disjoint tuples of a function of their set of
entries is `n!` times the sum over `n`-sets. -/
theorem sum_tuples_image_eq_factorial_mul (S : Finset (Finset β)) (P : Finset β → Prop)
    (hP : ∀ x, P x → x.Nonempty) {R : Type*} [CommSemiring R] (H : Finset (Finset β) → R)
    (n : ℕ) :
    ∑ X ∈ (Fintype.piFinset fun _ : Fin n => S).filter
        (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i)),
        H (Finset.univ.image X) =
      (n.factorial : R) * ∑ 𝒱 ∈ (disjointFamilies (S.biUnion id) P).filter
        (fun 𝒱 => 𝒱 ⊆ S ∧ 𝒱.card = n), H 𝒱 := by
  set A := (Fintype.piFinset fun _ : Fin n => S).filter
    (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i))
  set B := (disjointFamilies (S.biUnion id) P).filter (fun 𝒱 => 𝒱 ⊆ S ∧ 𝒱.card = n)
  have hmaps : ∀ X ∈ A, Finset.univ.image X ∈ B := by
    intro X hX
    rw [Finset.mem_filter] at hX
    have hinj := injective_of_disjoint hX.2.1 fun i => hP _ (hX.2.2 i)
    refine Finset.mem_filter.2 ⟨mem_disjointFamilies.2 ⟨fun V hV => ?_, fun V hV W hW hVW => ?_,
      fun V hV => ?_⟩, fun V hV => ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV
      exact subset_biUnion_of_mem (Fintype.mem_piFinset.1 hX.1 i)
    · rw [Finset.mem_coe, Finset.mem_image] at hV hW
      obtain ⟨i, -, rfl⟩ := hV
      obtain ⟨j, -, rfl⟩ := hW
      exact hX.2.1 i j (fun h => hVW (h ▸ rfl))
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV
      exact hX.2.2 i
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV
      exact Fintype.mem_piFinset.1 hX.1 i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun 𝒱 h𝒱 => ?_
  rw [Finset.sum_congr rfl fun X hX => by rw [(Finset.mem_filter.1 hX).2], Finset.sum_const,
    nsmul_eq_mul, Finset.filter_filter]
  congr 1
  rw [Finset.mem_filter, mem_disjointFamilies] at h𝒱
  have hcard := card_filter_image_eq 𝒱 h𝒱.2.2 S h𝒱.2.1
    (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i))
    (fun X hinj himage => ⟨fun i j hij => ?_, fun i => ?_⟩)
    (fun X hX => injective_of_disjoint hX.1 fun i => hP _ (hX.2 i))
  · convert congrArg (Nat.cast : ℕ → R) hcard using 3
    ext X
    simp only [Finset.mem_filter]
  · have hi : X i ∈ 𝒱 := himage ▸ Finset.mem_image_of_mem X (Finset.mem_univ i)
    have hj : X j ∈ 𝒱 := himage ▸ Finset.mem_image_of_mem X (Finset.mem_univ j)
    exact h𝒱.1.2.1 hi hj (fun h => hij (hinj h))
  · exact h𝒱.1.2.2 _ (himage ▸ Finset.mem_image_of_mem X (Finset.mem_univ i))

/-- **Ordered tuples and sets.** If `P` excludes the empty set,
`∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ∈ S disjoint, P(Xᵢ)} H({X₁, …, Xₙ}) = ∑_{𝒱 ⊆ S disjoint, P} H(𝒱)`.
in particular the series has finitely many nonzero terms. -/
theorem tsum_tuples_image_eq_sum (S : Finset (Finset β)) (P : Finset β → Prop)
    (hP : ∀ x, P x → x.Nonempty) (H : Finset (Finset β) → ℝ) :
    ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => S).filter
          (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i)),
          H (Finset.univ.image X) =
      ∑ 𝒱 ∈ (disjointFamilies (S.biUnion id) P).filter (· ⊆ S), H 𝒱 := by
  have hterm : ∀ n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => S).filter
        (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i)),
        H (Finset.univ.image X) =
      ∑ 𝒱 ∈ (disjointFamilies (S.biUnion id) P).filter (fun 𝒱 => 𝒱 ⊆ S ∧ 𝒱.card = n), H 𝒱 := by
    intro n
    rw [sum_tuples_image_eq_factorial_mul S P hP H n, ← mul_assoc, one_div,
      inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]
  rw [tsum_congr hterm, tsum_eq_sum (s := Finset.range (S.card + 1)) fun n hn => ?_]
  · rw [← Finset.sum_fiberwise_of_maps_to (s := (disjointFamilies (S.biUnion id) P).filter (· ⊆ S))
      (t := Finset.range (S.card + 1)) (g := Finset.card) fun 𝒱 h𝒱 => ?_]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.filter_filter]
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Finset.card_le_card (Finset.mem_filter.1 h𝒱).2
  · refine Finset.sum_eq_zero fun 𝒱 h𝒱 => ?_
    rw [Finset.mem_filter] at h𝒱
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hn
    exact absurd (h𝒱.2.2 ▸ Finset.card_le_card h𝒱.2.1) (not_le.2 hn)

end Tuples

/-! ### The activity series as a sum over partitions -/

section Series

variable (f b : ℕ × ℕ → ℝ)

/-- The integrand series of Definition 4.15 for the pair
weights `f` (the Mayer bonds) and `b` (the indicators of `𝓑_ij`):
`∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint} ∑_{Eₗ ∈ 𝖤^{Xₗ}}
∑_{F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}} ∏_{∪ Eₗ} f ∏_{∪ ℰ^inter(Xₗ)} (1 - b) ∏_F (-b)`. -/
noncomputable def clusterSeries (X : Finset (Finset ℕ)) : ℝ :=
  ∑' n : ℕ, 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
        ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          (∏ p ∈ Finset.univ.biUnion Es, f p) *
            (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l), (1 - b p)) *
            ∏ p ∈ F, -b p

/-- The weight `(∑_{E ∈ 𝖤^Y} ∏_E f) ∏_{ℰ^inter(Y)} (1 - b)` of one group of the series. -/
noncomputable def groupFactor' (Y : Finset (Finset ℕ)) : ℝ :=
  (∑ E ∈ relEdgeSets Y, ∏ p ∈ E, f p) * ∏ p ∈ interPairs Y, (1 - b p)

variable {f b} {D : Finset (Finset ℕ)}

theorem groupFactor'_eq_zero_of_card_le_one {Y : Finset (Finset ℕ)} (h : Y.card ≤ 1) :
    groupFactor' f b Y = 0 := by
  rw [groupFactor', relEdgeSets_eq_empty_of_card_le_one h, Finset.sum_empty, zero_mul]

theorem groupFactor'_eq_groupFactor {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)
    (h2 : 2 ≤ Y.card) : groupFactor' f b Y = groupFactor f b Y := by
  rw [groupFactor', groupFactor, relConnSum_eq_sum_relEdgeSets₀, relEdgeSets₀_eq_of_two_le hY h2]

theorem groupFactor_singleton {S : Finset ℕ} (hS : S.Nonempty) :
    groupFactor f b {S} = 1 := by
  rw [groupFactor, relConnSum_singleton hS, interPairs_singleton, Finset.prod_empty, mul_one]

/-- The edge sets of disjoint groups are disjoint. -/
theorem pairwiseDisjoint_of_subset_interPairs (hD : IsSubpartition D) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) {Es : Fin n → Finset (ℕ × ℕ)}
    (hEs : ∀ l, Es l ⊆ interPairs (Xs l)) :
    ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint Es := by
  intro l _ m _ hlm
  rw [Function.onFun, Finset.disjoint_left]
  intro p hp hp'
  exact Finset.disjoint_left.1 (disjoint_biUnion_of_disjoint hD (hXs l) (hXs m) (hdisj l m hlm))
    (interPairs_subset_pairsOn_biUnion _ (hEs l hp)).1
    (interPairs_subset_pairsOn_biUnion _ (hEs m hp')).1

/-- **The inner sums factorize** over the groups: for disjoint groups `X₁, …, Xₙ ⊆ X`,
`∑_{Eₗ ∈ 𝖤^{Xₗ}} ∑_{F ∈ 𝖤_0^{Coarse}} ∏_{∪ Eₗ} f ∏_{∪ ℰ^inter(Xₗ)} (1 - b) ∏_F (-b)
= ∏ₗ groupFactor'(Xₗ) · ∑_{F ∈ 𝖤_0^{Coarse}} ∏_F (-b)`. -/
theorem sum_sum_clusterTerm_eq (hD : IsSubpartition D) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) :
    ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
        ∑ F ∈ relEdgeSets₀ (coarsen D (Finset.univ.image Xs)),
          (∏ p ∈ Finset.univ.biUnion Es, f p) *
            (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l), (1 - b p)) *
            ∏ p ∈ F, -b p =
      (∏ l, groupFactor' f b (Xs l)) *
        relConnSum (fun p => -b p) (coarsen D (Finset.univ.image Xs)) := by
  have hinter : ∏ p ∈ Finset.univ.biUnion (fun l => interPairs (Xs l)), (1 - b p) =
      ∏ l, ∏ p ∈ interPairs (Xs l), (1 - b p) :=
    Finset.prod_biUnion (pairwiseDisjoint_of_subset_interPairs hD hXs hdisj fun _ => le_rfl)
  have hE : ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∏ p ∈ Finset.univ.biUnion Es, f p = ∏ l, ∏ p ∈ Es l, f p := by
    intro Es hEs
    refine Finset.prod_biUnion (pairwiseDisjoint_of_subset_interPairs hD hXs hdisj fun l => ?_)
    exact (mem_relEdgeSets.1 (Fintype.mem_piFinset.1 hEs l)).1
  calc ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
        ∑ F ∈ relEdgeSets₀ (coarsen D (Finset.univ.image Xs)),
          (∏ p ∈ Finset.univ.biUnion Es, f p) *
            (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l), (1 - b p)) *
            ∏ p ∈ F, -b p
      = ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
          (∏ l, ∏ p ∈ Es l, f p) * (∏ l, ∏ p ∈ interPairs (Xs l), (1 - b p)) *
            ∑ F ∈ relEdgeSets₀ (coarsen D (Finset.univ.image Xs)), ∏ p ∈ F, -b p := by
        refine Finset.sum_congr rfl fun Es hEs => ?_
        rw [Finset.mul_sum, hE Es hEs, hinter]
    _ = (∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)), ∏ l, ∏ p ∈ Es l, f p) *
          (∏ l, ∏ p ∈ interPairs (Xs l), (1 - b p)) *
            ∑ F ∈ relEdgeSets₀ (coarsen D (Finset.univ.image Xs)), ∏ p ∈ F, -b p := by
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = (∏ l, groupFactor' f b (Xs l)) *
          relConnSum (fun p => -b p) (coarsen D (Finset.univ.image Xs)) := by
        rw [← Finset.prod_univ_sum (fun l => relEdgeSets (Xs l)) (fun _ E => ∏ p ∈ E, f p),
          ← Finset.prod_mul_distrib, relConnSum_eq_sum_relEdgeSets₀]
        rfl

/-- For a disjoint family `𝒱` of groups of at least two blocks, `Coarse_D(𝒱)` is the coarsening
by its completion by singletons. -/
theorem coarsen_eq_merge_complete {𝒱 : Finset (Finset (Finset ℕ))} :
    coarsen D 𝒱 = merge (complete D 𝒱) := by
  rw [coarsen, merge, complete, Finset.image_union, Finset.image_image]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_image, Function.comp_apply, Finset.mem_sdiff,
    mem_biUnion_id]
  constructor
  · rintro ⟨hS, hn⟩
    exact ⟨S, ⟨hS, fun ⟨Y, hY, hSY⟩ => hn Y hY hSY⟩, by simp⟩
  · rintro ⟨S', ⟨hS', hn⟩, rfl⟩
    simp only [Finset.singleton_biUnion, id]
    exact ⟨hS', fun Y hY hSY => hn ⟨Y, hY, hSY⟩⟩

/-- The block weight of a disjoint family of groups (of at least two blocks each) is that of its
completion by singletons. -/
theorem prod_groupFactor'_eq (hD : IsSubpartition D) {𝒱 : Finset (Finset (Finset ℕ))}
    (h𝒱 : 𝒱 ∈ disjointFamilies D fun Y => 2 ≤ Y.card) :
    ∏ V ∈ 𝒱, groupFactor' f b V = ∏ T ∈ complete D 𝒱, groupFactor f b T := by
  have h𝒱' := mem_disjointFamilies.1 h𝒱
  rw [complete, Finset.prod_union]
  · rw [Finset.prod_eq_one (s := (D \ 𝒱.biUnion id).image singleton) fun T hT => ?_, mul_one]
    · exact Finset.prod_congr rfl fun V hV =>
        groupFactor'_eq_groupFactor (isSubpartition_mono hD (h𝒱'.1 V hV)) (h𝒱'.2.2 V hV)
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
    exact groupFactor_singleton (hD.1 S (Finset.mem_sdiff.1 hS).1)
  · rw [Finset.disjoint_left]
    intro V hV hV'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hV'
    simpa using h𝒱'.2.2 _ hV

/-- **The activity series is the block weight `groupWeight`**: for a subpartition `D`,
`clusterSeries f b D = ∑_{Y ∈ 𝚷(D)} ∏_{T ∈ Y} groupFactor(T) · ∑_{F ∈ 𝖤_0^{Coarse(Y)}} ∏_F (-b)`. -/
theorem clusterSeries_eq_groupWeight (hD : IsSubpartition D) :
    clusterSeries f b D = groupWeight f b D := by
  set P : Finset (Finset ℕ) → Prop := fun Y => 2 ≤ Y.card with hPdef
  have hP2 : ∀ Y, P Y → 2 ≤ Y.card := fun _ h => h
  have hPne : ∀ Y, P Y → Y.Nonempty := fun Y h => Finset.card_pos.1 (by omega)
  set H : Finset (Finset (Finset ℕ)) → ℝ := fun 𝒱 =>
    (∏ V ∈ 𝒱, groupFactor' f b V) * relConnSum (fun p => -b p) (coarsen D 𝒱) with hH
  -- the `n`-th term of the series
  have hterm : ∀ n : ℕ,
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => D.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
          ∑ F ∈ relEdgeSets₀ (coarsen D (Finset.univ.image Xs)),
            (∏ p ∈ Finset.univ.biUnion Es, f p) *
              (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l), (1 - b p)) *
              ∏ p ∈ F, -b p =
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => D.powerset).filter
          (fun Xs => (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, P (Xs i)),
          H (Finset.univ.image Xs) := by
    intro n
    have hsub : ∀ Xs ∈ (Fintype.piFinset fun _ : Fin n => D.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)), ∀ l, Xs l ⊆ D := fun Xs hXs l =>
      Finset.mem_powerset.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hXs).1 l)
    rw [Finset.sum_congr rfl fun Xs hXs =>
      sum_sum_clusterTerm_eq hD (hsub Xs hXs) (Finset.mem_filter.1 hXs).2]
    rw [← Finset.filter_filter]
    refine (Finset.sum_filter_of_ne fun Xs _ hne => fun i => ?_).symm.trans
      (Finset.sum_congr rfl fun Xs hXs => ?_)
    · by_contra hlt
      exact hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (groupFactor'_eq_zero_of_card_le_one (by simp only [hPdef] at hlt; omega)), zero_mul])
    · rw [Finset.mem_filter, Finset.mem_filter] at hXs
      have hinj := injective_of_disjoint hXs.1.2 fun i => hPne _ (hXs.2 i)
      rw [hH]
      simp only
      rw [Finset.prod_image fun i _ j _ h => hinj h]
  have key := tsum_tuples_image_eq_sum D.powerset P hPne H
  rw [biUnion_powerset_id] at key
  rw [clusterSeries]
  simp_rw [hterm]
  rw [show (∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => D.powerset).filter
        (fun Xs => (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, P (Xs i)),
        H (Finset.univ.image Xs)) =
      ∑ 𝒱 ∈ (disjointFamilies D P).filter (· ⊆ D.powerset), H 𝒱 by convert key using 7]
  have hfilt : (disjointFamilies D P).filter (· ⊆ D.powerset) = disjointFamilies D P :=
    Finset.filter_true_of_mem fun 𝒱 h𝒱 Y hY =>
      Finset.mem_powerset.2 ((mem_disjointFamilies.1 h𝒱).1 Y hY)
  rw [hfilt, groupWeight]
  refine Finset.sum_nbij' (complete D) (fun ρ => ρ.filter P) (fun 𝒱 h𝒱 => ?_) (fun ρ hρ => ?_)
    (fun 𝒱 h𝒱 => filter_complete hP2 h𝒱) (fun ρ hρ => ?_) (fun 𝒱 h𝒱 => ?_)
  · exact complete_mem_partitions hP2 h𝒱
  · have hρs := (mem_partitions.1 hρ).1
    rw [mem_disjointFamilies]
    exact ⟨fun V hV => subset_of_mem_partitions hρ (Finset.mem_filter.1 hV).1,
      hρs.2.subset (Finset.coe_subset.2 (Finset.filter_subset _ _)),
      fun V hV => (Finset.mem_filter.1 hV).2⟩
  · refine complete_filter hρ fun T hT => ?_
    by_cases h : P T
    · exact Or.inl h
    · right
      have := Finset.card_pos.2 ((mem_partitions.1 hρ).1.1 T hT)
      simp only [hPdef] at h
      omega
  · rw [hH]
    simp only
    rw [prod_groupFactor'_eq hD h𝒱, coarsen_eq_merge_complete]

/-- **The compact form of the activity series** (remark after Definition 4.15, Section 4.5): for
a subpartition `X` with at least two blocks,
`clusterSeries f b X = ∑_{E ∈ 𝖤^X} ∏_{ij ∈ E} ((1 + f_ij)(1 - b_ij) - 1)`. -/
theorem clusterSeries_eq_sum_relEdgeSets {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (h2 : 2 ≤ X.card) :
    clusterSeries f b X = ∑ E ∈ relEdgeSets X, ∏ p ∈ E, ((1 + f p) * (1 - b p) - 1) := by
  rw [clusterSeries_eq_groupWeight hX, ← relConnSum_eq_groupWeight hX le_rfl
    (Finset.card_pos.1 (by omega)), relConnSum_eq_sum_relEdgeSets₀,
    relEdgeSets₀_eq_of_two_le hX h2]

end Series

end Hierarchical

end MultipoleBKT

end
