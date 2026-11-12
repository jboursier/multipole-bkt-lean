/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.IsSubpartition
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Partitions of a finite set and Möbius inversion on the partition lattice (Lemma 4.60)

Partitions of a finite set `U` are represented, as in the frozen definitions
(`MultipoleBKT.IsSubpartition`), by finite families of finite
sets: `π` is a partition of `U` if it is a subpartition (nonempty, pairwise disjoint blocks) with
`⋃ π = U`. The order is refinement: `σ ≤ π` (`Refines σ π`) if every block of `σ` lies in a block
of `π` (Lemma 4.60).

Main results:

* `SetPartition.partitions U`: the finite set `𝚷(U)` of partitions of `U`, with
  `mem_partitions`;
* `SetPartition.sum_partitions_split`: partitions of `U` all of whose blocks lie in `C` or in
  `U \ C` are the unions of a partition of `C` and a partition of `U \ C`;
* `SetPartition.sum_partitions_root`: the root recursion, grouping partitions by the block of a
  fixed point `a`;
* `SetPartition.partitionSum K U = ∑_{σ ∈ 𝚷(U)} ∏_{B ∈ σ} K(B)`, its root recursion
  (`partitionSum_root`), the characterization of the solutions of the recursion
  (`eq_partitionSum_of_root`) and the uniqueness of the block weights
  (`eq_of_partitionSum_eq`);
* `SetPartition.sum_partitions_refines`: the partitions finer than `τ` are the families of
  partitions of the blocks of `τ`;
* `SetPartition.sum_partitions_coarser`: the partitions coarser than `π` are the partitions of
  the set of blocks of `π`;
* `SetPartition.partitionSum_partitions`: partitions of partitions;
* `SetPartition.mobius`: the Möbius function of the partition lattice,
  `μ(π, σ) = ∏_{B ∈ σ} (-1)^{k_B - 1} (k_B - 1)!` (equation (4.139)), and
  `SetPartition.lemma_4_60_1`, `SetPartition.lemma_4_60_2`: **Lemma 4.60** in both directions.
-/

@[expose] public section

namespace MultipoleBKT

open Finset

namespace SetPartition

variable {α : Type*}

/-! ### Subpartitions -/

section Subpartition

variable {π π' : Finset (Finset α)} {S T : Finset α}

theorem isSubpartition_mono (h : IsSubpartition π) (h' : π' ⊆ π) : IsSubpartition π' :=
  ⟨fun S hS => h.1 S (h' hS), h.2.subset (by exact_mod_cast h')⟩

theorem isSubpartition_empty : IsSubpartition (∅ : Finset (Finset α)) :=
  ⟨fun _ h => absurd h (Finset.notMem_empty _), by simp⟩

theorem disjoint_of_isSubpartition (h : IsSubpartition π) (hS : S ∈ π) (hT : T ∈ π)
    (hST : S ≠ T) : Disjoint S T :=
  h.2 hS hT hST

theorem eq_of_isSubpartition (h : IsSubpartition π) (hS : S ∈ π) (hT : T ∈ π) {x : α}
    (hxS : x ∈ S) (hxT : x ∈ T) : S = T := by
  by_contra hST
  exact Finset.disjoint_left.1 (disjoint_of_isSubpartition h hS hT hST) hxS hxT

theorem empty_notMem_of_isSubpartition (h : IsSubpartition π) : ∅ ∉ π := fun h0 => by
  simpa using h.1 ∅ h0

variable [DecidableEq α]

theorem mem_biUnion_id {x : α} : x ∈ π.biUnion id ↔ ∃ S ∈ π, x ∈ S := by
  simp

theorem subset_biUnion_of_mem (hS : S ∈ π) : S ⊆ π.biUnion id := fun _ hx =>
  mem_biUnion_id.2 ⟨S, hS, hx⟩

theorem isSubpartition_union (h₁ : IsSubpartition π) (h₂ : IsSubpartition π')
    (hd : Disjoint (π.biUnion id) (π'.biUnion id)) : IsSubpartition (π ∪ π') := by
  refine ⟨fun S hS => ?_, fun S hS T hT hST => ?_⟩
  · rcases Finset.mem_union.1 hS with h | h
    exacts [h₁.1 S h, h₂.1 S h]
  · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hS hT
    rcases hS with hS | hS <;> rcases hT with hT | hT
    · exact h₁.2 hS hT hST
    · exact hd.mono (subset_biUnion_of_mem hS) (subset_biUnion_of_mem hT)
    · exact (hd.mono (subset_biUnion_of_mem hT) (subset_biUnion_of_mem hS)).symm
    · exact h₂.2 hS hT hST

theorem isSubpartition_insert (h : IsSubpartition π) (hS : S.Nonempty)
    (hd : Disjoint S (π.biUnion id)) : IsSubpartition (insert S π) := by
  rw [Finset.insert_eq]
  refine isSubpartition_union ⟨fun T hT => ?_, ?_⟩ h (by simpa using hd)
  · rw [Finset.mem_singleton] at hT
    exact hT ▸ hS
  · simp

theorem biUnion_union_id : (π ∪ π').biUnion id = π.biUnion id ∪ π'.biUnion id :=
  Finset.union_biUnion

end Subpartition

variable [DecidableEq α]

/-- The singletons of a finite set form a subpartition. -/
theorem isSubpartition_image_singleton (s : Finset α) :
    IsSubpartition (s.image singleton) := by
  refine ⟨fun S hS => ?_, fun S hS T hT hST => ?_⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hS
    exact Finset.singleton_nonempty x
  · rw [Finset.mem_coe, Finset.mem_image] at hS hT
    obtain ⟨x, -, rfl⟩ := hS
    obtain ⟨y, -, rfl⟩ := hT
    rw [Function.onFun, id, id, Finset.disjoint_singleton]
    exact fun h => hST (h ▸ rfl)

theorem biUnion_image_singleton (s : Finset α) : (s.image singleton).biUnion id = s := by
  ext x
  simp

/-! ### The partitions of a finite set -/

open scoped Classical in
/-- The finite set `𝚷(U)` of partitions of `U` (Section 2.6): the subpartitions whose
union is `U`. -/
noncomputable def partitions (U : Finset α) : Finset (Finset (Finset α)) :=
  U.powerset.powerset.filter fun π => IsSubpartition π ∧ π.biUnion id = U

theorem mem_partitions {π : Finset (Finset α)} {U : Finset α} :
    π ∈ partitions U ↔ IsSubpartition π ∧ π.biUnion id = U := by
  classical
  unfold partitions
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨fun S hS => ?_, h⟩⟩
  rw [Finset.mem_powerset, ← h.2]
  exact subset_biUnion_of_mem hS

theorem subset_of_mem_partitions {π : Finset (Finset α)} {U S : Finset α}
    (hπ : π ∈ partitions U) (hS : S ∈ π) : S ⊆ U := by
  rw [← (mem_partitions.1 hπ).2]
  exact subset_biUnion_of_mem hS

theorem exists_mem_of_mem_partitions {π : Finset (Finset α)} {U : Finset α}
    (hπ : π ∈ partitions U) {x : α} (hx : x ∈ U) : ∃ S ∈ π, x ∈ S := by
  rw [← (mem_partitions.1 hπ).2] at hx
  exact mem_biUnion_id.1 hx

theorem partitions_empty : partitions (∅ : Finset α) = {∅} := by
  ext π
  rw [mem_partitions, Finset.mem_singleton]
  constructor
  · rintro ⟨h, hU⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    obtain ⟨x, hx⟩ := h.1 S hS
    have := subset_biUnion_of_mem hS hx
    rw [hU] at this
    exact Finset.notMem_empty x this
  · rintro rfl
    exact ⟨isSubpartition_empty, rfl⟩

theorem empty_mem_partitions_iff {U : Finset α} :
    (∅ : Finset (Finset α)) ∈ partitions U ↔ U = ∅ := by
  rw [mem_partitions]
  simp [isSubpartition_empty, eq_comm]

/-- The one-block partition. -/
theorem singleton_mem_partitions {U : Finset α} (hU : U.Nonempty) : {U} ∈ partitions U := by
  rw [mem_partitions]
  refine ⟨⟨fun S hS => ?_, by simp⟩, by simp⟩
  rw [Finset.mem_singleton] at hS
  exact hS ▸ hU

/-- A partition with a single block is the one-block partition. -/
theorem eq_singleton_of_mem_partitions {U : Finset α} {π : Finset (Finset α)}
    (hπ : π ∈ partitions U) (h1 : π.card = 1) : π = {U} := by
  obtain ⟨S, rfl⟩ := Finset.card_eq_one.1 h1
  rw [(by simpa using (mem_partitions.1 hπ).2 : S = U)]

/-- A partition of a nonempty set has at least one block. -/
theorem card_pos_of_mem_partitions {U : Finset α} {π : Finset (Finset α)}
    (hπ : π ∈ partitions U) (hU : U.Nonempty) : 0 < π.card := by
  rw [Finset.card_pos]
  obtain ⟨x, hx⟩ := hU
  obtain ⟨S, hS, -⟩ := exists_mem_of_mem_partitions hπ hx
  exact ⟨S, hS⟩

/-- The blocks of a partition with at least two blocks are proper subsets. -/
theorem ssubset_of_mem_partitions {U : Finset α} {π : Finset (Finset α)}
    (hπ : π ∈ partitions U) (h2 : 2 ≤ π.card) {S : Finset α} (hS : S ∈ π) : S ⊂ U := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨subset_of_mem_partitions hπ hS, fun hSU => ?_⟩
  obtain ⟨T, hT, hTS⟩ := Finset.exists_mem_ne (by omega : 1 < π.card) S
  obtain ⟨x, hx⟩ := (mem_partitions.1 hπ).1.1 T hT
  have hxS : x ∈ S := hSU ▸ subset_of_mem_partitions hπ hT hx
  exact hTS (eq_of_isSubpartition (mem_partitions.1 hπ).1 hT hS hx hxS)

/-! ### Splitting a partition along a set -/

/-- `σ` splits along `C`: each block lies in `C` or is disjoint from it. -/
def SplitsAlong (σ : Finset (Finset α)) (C : Finset α) : Prop :=
  ∀ B ∈ σ, B ⊆ C ∨ Disjoint B C

section Split

variable {U C : Finset α}

theorem union_mem_partitions {σ₁ σ₂ : Finset (Finset α)} (hC : C ⊆ U)
    (h₁ : σ₁ ∈ partitions C) (h₂ : σ₂ ∈ partitions (U \ C)) : σ₁ ∪ σ₂ ∈ partitions U := by
  rw [mem_partitions] at h₁ h₂ ⊢
  refine ⟨isSubpartition_union h₁.1 h₂.1 ?_, ?_⟩
  · rw [h₁.2, h₂.2]
    exact Finset.disjoint_sdiff
  · rw [biUnion_union_id, h₁.2, h₂.2, Finset.union_sdiff_of_subset hC]

theorem splitsAlong_union {σ₁ σ₂ : Finset (Finset α)} (h₁ : σ₁ ∈ partitions C)
    (h₂ : σ₂ ∈ partitions (U \ C)) : SplitsAlong (σ₁ ∪ σ₂) C := by
  intro B hB
  rcases Finset.mem_union.1 hB with h | h
  · exact Or.inl (subset_of_mem_partitions h₁ h)
  · exact Or.inr (Finset.disjoint_of_subset_left (subset_of_mem_partitions h₂ h)
      Finset.sdiff_disjoint)

theorem filter_subset_mem_partitions {σ : Finset (Finset α)} (hσ : σ ∈ partitions U)
    (hC : C ⊆ U) (hs : SplitsAlong σ C) : σ.filter (· ⊆ C) ∈ partitions C := by
  rw [mem_partitions]
  refine ⟨isSubpartition_mono (mem_partitions.1 hσ).1 (Finset.filter_subset _ _), ?_⟩
  ext x
  rw [mem_biUnion_id]
  constructor
  · rintro ⟨B, hB, hx⟩
    exact (Finset.mem_filter.1 hB).2 hx
  · intro hx
    obtain ⟨B, hB, hxB⟩ := exists_mem_of_mem_partitions hσ (hC hx)
    rcases hs B hB with h | h
    · exact ⟨B, Finset.mem_filter.2 ⟨hB, h⟩, hxB⟩
    · exact absurd hx (Finset.disjoint_left.1 h hxB)

theorem filter_not_subset_mem_partitions {σ : Finset (Finset α)} (hσ : σ ∈ partitions U)
    (hs : SplitsAlong σ C) : σ.filter (fun B => ¬ B ⊆ C) ∈ partitions (U \ C) := by
  rw [mem_partitions]
  refine ⟨isSubpartition_mono (mem_partitions.1 hσ).1 (Finset.filter_subset _ _), ?_⟩
  ext x
  rw [mem_biUnion_id, Finset.mem_sdiff]
  constructor
  · rintro ⟨B, hB, hx⟩
    rw [Finset.mem_filter] at hB
    refine ⟨subset_of_mem_partitions hσ hB.1 hx, fun hxC => ?_⟩
    rcases hs B hB.1 with h | h
    · exact hB.2 h
    · exact Finset.disjoint_left.1 h hx hxC
  · rintro ⟨hx, hxC⟩
    obtain ⟨B, hB, hxB⟩ := exists_mem_of_mem_partitions hσ hx
    exact ⟨B, Finset.mem_filter.2 ⟨hB, fun h => hxC (h hxB)⟩, hxB⟩

theorem filter_subset_union {σ₁ σ₂ : Finset (Finset α)} (h₁ : σ₁ ∈ partitions C)
    (h₂ : σ₂ ∈ partitions (U \ C)) : (σ₁ ∪ σ₂).filter (· ⊆ C) = σ₁ := by
  ext B
  rw [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hB | hB, hBC⟩
    · exact hB
    · obtain ⟨x, hx⟩ := (mem_partitions.1 h₂).1.1 B hB
      exact absurd (hBC hx) (Finset.mem_sdiff.1 (subset_of_mem_partitions h₂ hB hx)).2
  · intro hB
    exact ⟨Or.inl hB, subset_of_mem_partitions h₁ hB⟩

theorem filter_not_subset_union {σ₁ σ₂ : Finset (Finset α)} (h₁ : σ₁ ∈ partitions C)
    (h₂ : σ₂ ∈ partitions (U \ C)) : (σ₁ ∪ σ₂).filter (fun B => ¬ B ⊆ C) = σ₂ := by
  ext B
  rw [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hB | hB, hBC⟩
    · exact absurd (subset_of_mem_partitions h₁ hB) hBC
    · exact hB
  · intro hB
    refine ⟨Or.inr hB, fun hBC => ?_⟩
    obtain ⟨x, hx⟩ := (mem_partitions.1 h₂).1.1 B hB
    exact (Finset.mem_sdiff.1 (subset_of_mem_partitions h₂ hB hx)).2 (hBC hx)

open scoped Classical in
/-- **Splitting.** The partitions of `U` that split along `C ⊆ U` are the unions of a partition of
`C` and a partition of `U \ C`. -/
theorem sum_partitions_split {M : Type*} [AddCommMonoid M] (hC : C ⊆ U)
    (f : Finset (Finset α) → M) :
    ∑ σ ∈ (partitions U).filter (SplitsAlong · C), f σ =
      ∑ σ₁ ∈ partitions C, ∑ σ₂ ∈ partitions (U \ C), f (σ₁ ∪ σ₂) := by
  classical
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun q => q.1 ∪ q.2)
    (fun σ => (σ.filter (· ⊆ C), σ.filter (fun B => ¬ B ⊆ C))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨σ₁, σ₂⟩ hq
    rw [Finset.mem_product] at hq
    rw [Finset.mem_filter]
    exact ⟨union_mem_partitions hC hq.1 hq.2, splitsAlong_union hq.1 hq.2⟩
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [Finset.mem_product]
    exact ⟨filter_subset_mem_partitions hσ.1 hC hσ.2, filter_not_subset_mem_partitions hσ.1 hσ.2⟩
  · rintro ⟨σ₁, σ₂⟩ hq
    rw [Finset.mem_product] at hq
    simp only [filter_subset_union hq.1 hq.2, filter_not_subset_union hq.1 hq.2]
  · intro σ _
    exact Finset.filter_union_filter_not_eq _ σ
  · intro _ _
    rfl

end Split

/-! ### The root recursion -/

section Root

variable {U : Finset α} {a : α}

theorem insert_mem_partitions {D : Finset α} {σ : Finset (Finset α)} (hDU : D ⊆ U)
    (hD : D.Nonempty) (hσ : σ ∈ partitions (U \ D)) : insert D σ ∈ partitions U := by
  rw [Finset.insert_eq]
  exact union_mem_partitions hDU (singleton_mem_partitions hD) hσ

theorem notMem_of_mem_partitions_sdiff {D : Finset α} {σ : Finset (Finset α)}
    (hD : D.Nonempty) (hσ : σ ∈ partitions (U \ D)) : D ∉ σ := by
  intro h
  obtain ⟨x, hx⟩ := hD
  exact (Finset.mem_sdiff.1 (subset_of_mem_partitions hσ h hx)).2 hx

/-- The block of `σ` containing `a` (the union of the blocks containing `a`). -/
def blockOf (σ : Finset (Finset α)) (a : α) : Finset α :=
  (σ.filter (a ∈ ·)).biUnion id

theorem blockOf_eq {σ : Finset (Finset α)} (hσ : IsSubpartition σ) {B : Finset α} (hB : B ∈ σ)
    (ha : a ∈ B) : blockOf σ a = B := by
  have : σ.filter (a ∈ ·) = {B} := by
    ext S
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => eq_of_isSubpartition hσ h.1 hB h.2 ha, fun h => h ▸ ⟨hB, ha⟩⟩
  simp [blockOf, this]

theorem blockOf_mem {σ : Finset (Finset α)} (hσ : σ ∈ partitions U) (ha : a ∈ U) :
    blockOf σ a ∈ σ ∧ a ∈ blockOf σ a := by
  obtain ⟨B, hB, haB⟩ := exists_mem_of_mem_partitions hσ ha
  rw [blockOf_eq (mem_partitions.1 hσ).1 hB haB]
  exact ⟨hB, haB⟩

/-- **Root recursion.** Group the partitions of `U` by the block containing `a ∈ U`. -/
theorem sum_partitions_root {M : Type*} [AddCommMonoid M] (ha : a ∈ U)
    (f : Finset (Finset α) → M) :
    ∑ σ ∈ partitions U, f σ =
      ∑ D ∈ U.powerset.filter (a ∈ ·), ∑ σ ∈ partitions (U \ D), f (insert D σ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ => blockOf σ a)
    (t := U.powerset.filter (a ∈ ·)) (fun σ hσ => ?_)]
  · refine Finset.sum_congr rfl fun D hD => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hD
    have hDne : D.Nonempty := ⟨a, hD.2⟩
    symm
    refine Finset.sum_nbij' (fun σ => insert D σ) (fun σ => σ.erase D) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_filter]
      have hmem := insert_mem_partitions hD.1 hDne hσ
      refine ⟨hmem, blockOf_eq (mem_partitions.1 hmem).1 (Finset.mem_insert_self _ _) hD.2⟩
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      obtain ⟨hDσ, -⟩ := blockOf_mem hσ.1 ha
      rw [hσ.2] at hDσ
      have hsplit : SplitsAlong σ D := by
        intro B hB
        by_cases hBD : B = D
        · exact Or.inl hBD.le
        · exact Or.inr (disjoint_of_isSubpartition (mem_partitions.1 hσ.1).1 hB hDσ hBD)
      have h := filter_not_subset_mem_partitions hσ.1 hsplit
      convert h using 1
      ext B
      rw [Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨hBD, hB⟩
        refine ⟨hB, fun hsub => hBD ?_⟩
        obtain ⟨x, hx⟩ := (mem_partitions.1 hσ.1).1.1 B hB
        exact eq_of_isSubpartition (mem_partitions.1 hσ.1).1 hB hDσ hx (hsub hx)
      · rintro ⟨hB, hsub⟩
        exact ⟨fun h => hsub (h ▸ le_rfl), hB⟩
    · intro σ hσ
      exact Finset.erase_insert (notMem_of_mem_partitions_sdiff hDne hσ)
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      obtain ⟨hDσ, -⟩ := blockOf_mem hσ.1 ha
      rw [hσ.2] at hDσ
      exact Finset.insert_erase hDσ
    · intro _ _
      rfl
  · rw [Finset.mem_filter, Finset.mem_powerset]
    obtain ⟨hB, haB⟩ := blockOf_mem hσ ha
    exact ⟨subset_of_mem_partitions hσ hB, haB⟩

end Root

/-! ### Partition sums -/

section PartitionSum

variable {R : Type*} [CommSemiring R]

/-- The partition sum `∑_{σ ∈ 𝚷(U)} ∏_{B ∈ σ} K(B)` of a block weight `K`. -/
noncomputable def partitionSum (K : Finset α → R) (U : Finset α) : R :=
  ∑ σ ∈ partitions U, ∏ B ∈ σ, K B

theorem partitionSum_empty (K : Finset α → R) : partitionSum K ∅ = 1 := by
  simp [partitionSum, partitions_empty]

/-- Partition sums only see the weights of the nonempty subsets. -/
theorem partitionSum_congr {K K' : Finset α → R} {U : Finset α}
    (h : ∀ D ⊆ U, D.Nonempty → K D = K' D) : partitionSum K U = partitionSum K' U :=
  Finset.sum_congr rfl fun _ hσ => Finset.prod_congr rfl fun B hB =>
    h B (subset_of_mem_partitions hσ hB) ((mem_partitions.1 hσ).1.1 B hB)

/-- The root recursion of a partition sum. -/
theorem partitionSum_root (K : Finset α → R) {U : Finset α} {a : α} (ha : a ∈ U) :
    partitionSum K U = ∑ D ∈ U.powerset.filter (a ∈ ·), K D * partitionSum K (U \ D) := by
  unfold partitionSum
  rw [sum_partitions_root ha]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hDne : D.Nonempty := ⟨a, (Finset.mem_filter.1 hD).2⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Finset.prod_insert (notMem_of_mem_partitions_sdiff hDne hσ)]

/-- A set function satisfying the root recursion of `K` on the subsets of `U₀`, with value `1`
at `∅`, is the partition sum of `K`. -/
theorem eq_partitionSum_of_root (K : Finset α → R) {F : Finset α → R} (U₀ : Finset α)
    (h0 : F ∅ = 1)
    (hrec : ∀ U ⊆ U₀, ∀ a ∈ U, F U = ∑ D ∈ U.powerset.filter (a ∈ ·), K D * F (U \ D)) :
    ∀ U ⊆ U₀, F U = partitionSum K U := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    intro hU
    rcases U.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · rw [h0, partitionSum_empty]
    · rw [hrec U hU a ha, partitionSum_root K ha]
      refine Finset.sum_congr rfl fun D hD => ?_
      rw [Finset.mem_filter] at hD
      rw [ih (U \ D) (Finset.sdiff_ssubset (Finset.mem_powerset.1 hD.1) ⟨a, hD.2⟩)
        (Finset.sdiff_subset.trans hU)]

end PartitionSum

section Uniqueness

variable {R : Type*} [CommRing R]

/-- **Uniqueness of block weights.** If two block weights have the same partition sums on all
subsets of `U₀`, they agree on the nonempty subsets of `U₀`. -/
theorem eq_of_partitionSum_eq {K K' : Finset α → R} (U₀ : Finset α)
    (h : ∀ U ⊆ U₀, partitionSum K U = partitionSum K' U) :
    ∀ U ⊆ U₀, U.Nonempty → K U = K' U := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    intro hU hne
    obtain ⟨a, ha⟩ := hne
    have hK := partitionSum_root K ha
    have hK' := partitionSum_root K' ha
    have hmem : U ∈ U.powerset.filter (a ∈ ·) :=
      Finset.mem_filter.2 ⟨Finset.mem_powerset.2 le_rfl, ha⟩
    rw [← Finset.add_sum_erase _ _ hmem, Finset.sdiff_self, partitionSum_empty,
      mul_one] at hK hK'
    have hrest : ∑ D ∈ (U.powerset.filter (a ∈ ·)).erase U, K D * partitionSum K (U \ D) =
        ∑ D ∈ (U.powerset.filter (a ∈ ·)).erase U, K' D * partitionSum K' (U \ D) := by
      refine Finset.sum_congr rfl fun D hD => ?_
      rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hD
      have hDU : D ⊂ U := Finset.ssubset_iff_subset_ne.2 ⟨hD.2.1, hD.1⟩
      rw [ih D hDU (hDU.subset.trans hU) ⟨a, hD.2.2⟩, h (U \ D) (Finset.sdiff_subset.trans hU)]
    have := h U hU
    rw [hK, hK', hrest] at this
    exact add_right_cancel this

end Uniqueness

/-! ### Refinement -/

/-- `σ` refines `τ` (`σ ≤ τ` in the partition lattice, Lemma 4.60): every block of `σ` lies in
a block of `τ`. -/
def Refines (σ τ : Finset (Finset α)) : Prop :=
  ∀ B ∈ σ, ∃ T ∈ τ, B ⊆ T

omit [DecidableEq α] in
theorem refines_refl (σ : Finset (Finset α)) : Refines σ σ := fun B hB => ⟨B, hB, le_rfl⟩

omit [DecidableEq α] in
theorem refines_trans {ρ σ τ : Finset (Finset α)} (h₁ : Refines ρ σ) (h₂ : Refines σ τ) :
    Refines ρ τ := by
  intro B hB
  obtain ⟨S, hS, hBS⟩ := h₁ B hB
  obtain ⟨T, hT, hST⟩ := h₂ S hS
  exact ⟨T, hT, hBS.trans hST⟩

section Refines

variable {U : Finset α}

theorem refines_insert_iff {σ τ : Finset (Finset α)} {T : Finset α}
    (hτ : insert T τ ∈ partitions U) (hT : T ∉ τ) :
    Refines σ (insert T τ) ↔ SplitsAlong σ T ∧ Refines (σ.filter fun B => ¬ B ⊆ T) τ := by
  constructor
  · intro h
    refine ⟨fun B hB => ?_, fun B hB => ?_⟩
    · obtain ⟨T', hT', hBT'⟩ := h B hB
      rcases Finset.mem_insert.1 hT' with rfl | hT'τ
      · exact Or.inl hBT'
      · refine Or.inr (Finset.disjoint_of_subset_left hBT' ?_)
        exact disjoint_of_isSubpartition (mem_partitions.1 hτ).1 hT'
          (Finset.mem_insert_self _ _) (fun h => hT (h ▸ hT'τ))
    · rw [Finset.mem_filter] at hB
      obtain ⟨T', hT', hBT'⟩ := h B hB.1
      rcases Finset.mem_insert.1 hT' with rfl | hT'τ
      · exact absurd hBT' hB.2
      · exact ⟨T', hT'τ, hBT'⟩
  · rintro ⟨-, h⟩ B hB
    by_cases hBT : B ⊆ T
    · exact ⟨T, Finset.mem_insert_self _ _, hBT⟩
    · obtain ⟨T', hT', hBT'⟩ := h B (Finset.mem_filter.2 ⟨hB, hBT⟩)
      exact ⟨T', Finset.mem_insert_of_mem hT', hBT'⟩

theorem filter_subset_union_of_disjoint {σ₁ σ₂ : Finset (Finset α)} {C T : Finset α}
    (h₁ : σ₁ ∈ partitions C) (hT : Disjoint T C) :
    (σ₁ ∪ σ₂).filter (· ⊆ T) = σ₂.filter (· ⊆ T) := by
  ext B
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hB | hB, hBT⟩
    · obtain ⟨x, hx⟩ := (mem_partitions.1 h₁).1.1 B hB
      exact absurd (subset_of_mem_partitions h₁ hB hx) (Finset.disjoint_left.1 hT (hBT hx))
    · exact ⟨hB, hBT⟩
  · rintro ⟨hB, hBT⟩
    exact ⟨Or.inr hB, hBT⟩

theorem erase_mem_partitions {τ : Finset (Finset α)} {T : Finset α}
    (hτ : insert T τ ∈ partitions U) (hT : T ∉ τ) : τ ∈ partitions (U \ T) := by
  have hsplit : SplitsAlong (insert T τ) T := by
    intro B hB
    rcases Finset.mem_insert.1 hB with rfl | hBτ
    · exact Or.inl le_rfl
    · exact Or.inr (disjoint_of_isSubpartition (mem_partitions.1 hτ).1
        (Finset.mem_insert_of_mem hBτ) (Finset.mem_insert_self _ _) (fun h => hT (h ▸ hBτ)))
  have h := filter_not_subset_mem_partitions hτ hsplit
  convert h using 1
  ext B
  rw [Finset.mem_filter, Finset.mem_insert]
  constructor
  · intro hB
    refine ⟨Or.inr hB, fun hBT => ?_⟩
    obtain ⟨x, hx⟩ := (mem_partitions.1 hτ).1.1 B (Finset.mem_insert_of_mem hB)
    have hd := disjoint_of_isSubpartition (mem_partitions.1 hτ).1 (Finset.mem_insert_of_mem hB)
      (Finset.mem_insert_self _ _) (fun h => hT (h ▸ hB))
    exact Finset.disjoint_left.1 hd hx (hBT hx)
  · rintro ⟨rfl | hB, hBT⟩
    · exact absurd le_rfl hBT
    · exact hB

open scoped Classical in
/-- **Refinements of a partition.** The partitions `σ` of `U` finer than `τ ∈ 𝚷(U)` are the
families `(σ|_T)_{T ∈ τ}` of partitions of the blocks of `τ`, with `σ|_T = {B ∈ σ : B ⊆ T}`. -/
theorem sum_partitions_refines {M : Type*} [CommSemiring M] {τ : Finset (Finset α)}
    (hτ : τ ∈ partitions U) (G : Finset α → Finset (Finset α) → M) :
    ∑ σ ∈ (partitions U).filter (Refines · τ), ∏ T ∈ τ, G T (σ.filter (· ⊆ T)) =
      ∏ T ∈ τ, ∑ σ ∈ partitions T, G T σ := by
  induction τ using Finset.induction_on generalizing U with
  | empty =>
    rw [empty_mem_partitions_iff] at hτ
    subst hτ
    have h0 : Refines (∅ : Finset (Finset α)) ∅ := fun B hB => absurd hB (Finset.notMem_empty B)
    rw [partitions_empty, Finset.prod_empty, Finset.filter_singleton]
    simp only [h0, ↓reduceIte, Finset.sum_singleton, Finset.prod_empty]
  | insert T τ hT ih =>
    have hTne : T.Nonempty := (mem_partitions.1 hτ).1.1 T (Finset.mem_insert_self _ _)
    have hTU : T ⊆ U := subset_of_mem_partitions hτ (Finset.mem_insert_self _ _)
    have hτ' := erase_mem_partitions hτ hT
    rw [Finset.prod_insert hT, ← ih hτ', Finset.sum_mul_sum, Finset.sum_filter]
    simp_rw [refines_insert_iff hτ hT]
    rw [← Finset.sum_filter_add_sum_filter_not (partitions U) (SplitsAlong · T)]
    have hzero : ∑ σ ∈ (partitions U).filter (fun σ => ¬ SplitsAlong σ T),
        (if SplitsAlong σ T ∧ Refines (σ.filter fun B => ¬ B ⊆ T) τ then
          ∏ T' ∈ insert T τ, G T' (σ.filter (· ⊆ T')) else 0) = 0 :=
      Finset.sum_eq_zero fun σ hσ =>
        ite_eq_right_iff.2 fun h => absurd h.1 (Finset.mem_filter.1 hσ).2
    rw [hzero, add_zero, sum_partitions_split hTU]
    refine Finset.sum_congr rfl fun σ₁ hσ₁ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun σ₂ hσ₂ => ?_
    rw [filter_not_subset_union hσ₁ hσ₂]
    simp only [splitsAlong_union hσ₁ hσ₂, true_and]
    split_ifs with h
    · rw [Finset.prod_insert hT, filter_subset_union hσ₁ hσ₂]
      congr 1
      refine Finset.prod_congr rfl fun T' hT' => ?_
      rw [filter_subset_union_of_disjoint hσ₁]
      exact disjoint_of_isSubpartition (mem_partitions.1 hτ).1 (Finset.mem_insert_of_mem hT')
        (Finset.mem_insert_self _ _) (fun h => hT (h ▸ hT'))
    · rfl

/-- A refinement `σ` of `τ` is the disjoint union of its restrictions to the blocks of `τ`. -/
theorem prod_eq_prod_prod_filter {M : Type*} [CommMonoid M] {σ τ : Finset (Finset α)}
    (hσ : σ ∈ partitions U) (hτ : τ ∈ partitions U) (h : Refines σ τ) (K : Finset α → M) :
    ∏ B ∈ σ, K B = ∏ T ∈ τ, ∏ B ∈ σ.filter (· ⊆ T), K B := by
  classical
  rw [← Finset.prod_biUnion]
  · congr 1
    ext B
    rw [Finset.mem_biUnion]
    constructor
    · intro hB
      obtain ⟨T, hT, hBT⟩ := h B hB
      exact ⟨T, hT, Finset.mem_filter.2 ⟨hB, hBT⟩⟩
    · rintro ⟨T, -, hB⟩
      exact (Finset.mem_filter.1 hB).1
  · intro T hT T' hT' hTT'
    rw [Function.onFun, Finset.disjoint_left]
    intro B hB hB'
    rw [Finset.mem_filter] at hB hB'
    obtain ⟨x, hx⟩ := (mem_partitions.1 hσ).1.1 B hB.1
    exact Finset.disjoint_left.1 (disjoint_of_isSubpartition (mem_partitions.1 hτ).1 hT hT' hTT')
      (hB.2 hx) (hB'.2 hx)

open scoped Classical in
/-- The partition sum restricted to the refinements of `τ` is the product of the partition sums
of the blocks of `τ`. -/
theorem sum_partitions_refines_prod {R : Type*} [CommSemiring R] {τ : Finset (Finset α)}
    (hτ : τ ∈ partitions U) (K : Finset α → R) :
    ∑ σ ∈ (partitions U).filter (Refines · τ), ∏ B ∈ σ, K B = ∏ T ∈ τ, partitionSum K T := by
  have h := sum_partitions_refines hτ (fun _ σ => ∏ B ∈ σ, K B)
  unfold partitionSum
  rw [← h]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Finset.mem_filter] at hσ
  exact prod_eq_prod_prod_filter hσ.1 hτ hσ.2 K

end Refines

/-! ### Coarsenings of a partition -/

section Coarser

variable {U : Finset α} {π : Finset (Finset α)}

/-- The blocks of a subpartition `π` contained in the union of a subfamily `Y ⊆ π` are the
members of `Y`. -/
theorem filter_subset_biUnion_eq (hπ : IsSubpartition π) {Y : Finset (Finset α)} (hY : Y ⊆ π) :
    π.filter (· ⊆ Y.biUnion id) = Y := by
  ext B
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hB, hBY⟩
    obtain ⟨x, hx⟩ := hπ.1 B hB
    obtain ⟨B', hB', hxB'⟩ := mem_biUnion_id.1 (hBY hx)
    rw [eq_of_isSubpartition hπ hB (hY hB') hx hxB']
    exact hB'
  · intro hB
    exact ⟨hY hB, subset_biUnion_of_mem hB⟩

/-- A block of a coarsening `ρ` of `π` is the union of the blocks of `π` it contains. -/
theorem biUnion_filter_subset_eq (hπ : π ∈ partitions U) {ρ : Finset (Finset α)}
    (hρ : ρ ∈ partitions U) (h : Refines π ρ) {D : Finset α} (hD : D ∈ ρ) :
    (π.filter (· ⊆ D)).biUnion id = D := by
  ext x
  rw [mem_biUnion_id]
  constructor
  · rintro ⟨B, hB, hx⟩
    exact (Finset.mem_filter.1 hB).2 hx
  · intro hx
    obtain ⟨B, hB, hxB⟩ := exists_mem_of_mem_partitions hπ (subset_of_mem_partitions hρ hD hx)
    obtain ⟨D', hD', hBD'⟩ := h B hB
    rw [eq_of_isSubpartition (mem_partitions.1 hρ).1 hD' hD (hBD' hxB) hx] at hBD'
    exact ⟨B, Finset.mem_filter.2 ⟨hB, hBD'⟩, hxB⟩

/-- The union map is injective on a partition of the blocks of `π`. -/
theorem injOn_biUnion (hπ : IsSubpartition π) {𝒴 : Finset (Finset (Finset α))}
    (h𝒴 : 𝒴 ∈ partitions π) : Set.InjOn (fun Y : Finset (Finset α) => Y.biUnion id) 𝒴 := by
  intro Y hY Y' hY' hYY'
  have hYπ : Y ⊆ π := subset_of_mem_partitions h𝒴 hY
  have hY'π : Y' ⊆ π := subset_of_mem_partitions h𝒴 hY'
  rw [← filter_subset_biUnion_eq hπ hYπ, ← filter_subset_biUnion_eq hπ hY'π]
  simp only at hYY'
  rw [hYY']

theorem image_biUnion_mem_partitions (hπ : π ∈ partitions U) {𝒴 : Finset (Finset (Finset α))}
    (h𝒴 : 𝒴 ∈ partitions π) : 𝒴.image (fun Y => Y.biUnion id) ∈ partitions U := by
  have hπs := (mem_partitions.1 hπ).1
  rw [mem_partitions]
  refine ⟨⟨fun D hD => ?_, fun D hD D' hD' hDD' => ?_⟩, ?_⟩
  · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hD
    obtain ⟨B, hB⟩ := (mem_partitions.1 h𝒴).1.1 Y hY
    obtain ⟨x, hx⟩ := hπs.1 B (subset_of_mem_partitions h𝒴 hY hB)
    exact ⟨x, mem_biUnion_id.2 ⟨B, hB, hx⟩⟩
  · rw [Finset.mem_coe, Finset.mem_image] at hD hD'
    obtain ⟨Y, hY, rfl⟩ := hD
    obtain ⟨Y', hY', rfl⟩ := hD'
    have hYY' : Y ≠ Y' := fun h => hDD' (h ▸ rfl)
    have hd := disjoint_of_isSubpartition (mem_partitions.1 h𝒴).1 hY hY' hYY'
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨B, hB, hxB⟩ := mem_biUnion_id.1 hx
    obtain ⟨B', hB', hxB'⟩ := mem_biUnion_id.1 hx'
    have := eq_of_isSubpartition hπs (subset_of_mem_partitions h𝒴 hY hB)
      (subset_of_mem_partitions h𝒴 hY' hB') hxB hxB'
    exact Finset.disjoint_left.1 hd hB (this ▸ hB')
  · rw [← (mem_partitions.1 hπ).2, ← (mem_partitions.1 h𝒴).2]
    ext x
    rw [mem_biUnion_id, mem_biUnion_id]
    constructor
    · rintro ⟨D, hD, hx⟩
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hD
      obtain ⟨B, hB, hxB⟩ := mem_biUnion_id.1 hx
      exact ⟨B, mem_biUnion_id.2 ⟨Y, hY, hB⟩, hxB⟩
    · rintro ⟨B, hB, hx⟩
      obtain ⟨Y, hY, hBY⟩ := mem_biUnion_id.1 hB
      exact ⟨_, Finset.mem_image_of_mem _ hY, mem_biUnion_id.2 ⟨B, hBY, hx⟩⟩

theorem refines_image_biUnion {𝒴 : Finset (Finset (Finset α))} (h𝒴 : 𝒴 ∈ partitions π) :
    Refines π (𝒴.image fun Y => Y.biUnion id) := by
  intro B hB
  obtain ⟨Y, hY, hBY⟩ := exists_mem_of_mem_partitions h𝒴 hB
  exact ⟨Y.biUnion id, Finset.mem_image_of_mem _ hY, subset_biUnion_of_mem hBY⟩

theorem image_filter_mem_partitions (hπ : π ∈ partitions U) {ρ : Finset (Finset α)}
    (hρ : ρ ∈ partitions U) (h : Refines π ρ) :
    ρ.image (fun D => π.filter (· ⊆ D)) ∈ partitions π := by
  rw [mem_partitions]
  refine ⟨⟨fun Y hY => ?_, fun Y hY Y' hY' hYY' => ?_⟩, ?_⟩
  · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.1 hY
    obtain ⟨x, hx⟩ := (mem_partitions.1 hρ).1.1 D hD
    rw [← biUnion_filter_subset_eq hπ hρ h hD] at hx
    obtain ⟨B, hB, -⟩ := mem_biUnion_id.1 hx
    exact ⟨B, hB⟩
  · rw [Finset.mem_coe, Finset.mem_image] at hY hY'
    obtain ⟨D, hD, rfl⟩ := hY
    obtain ⟨D', hD', rfl⟩ := hY'
    have hDD' : D ≠ D' := fun h => hYY' (h ▸ rfl)
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro B hB hB'
    rw [Finset.mem_filter] at hB hB'
    obtain ⟨x, hx⟩ := (mem_partitions.1 hπ).1.1 B hB.1
    exact Finset.disjoint_left.1 (disjoint_of_isSubpartition (mem_partitions.1 hρ).1 hD hD' hDD')
      (hB.2 hx) (hB'.2 hx)
  · ext B
    rw [mem_biUnion_id]
    constructor
    · rintro ⟨Y, hY, hB⟩
      obtain ⟨D, -, rfl⟩ := Finset.mem_image.1 hY
      exact (Finset.mem_filter.1 hB).1
    · intro hB
      obtain ⟨D, hD, hBD⟩ := h B hB
      exact ⟨_, Finset.mem_image_of_mem _ hD, Finset.mem_filter.2 ⟨hB, hBD⟩⟩

open scoped Classical in
/-- **Coarsenings of a partition.** The partitions of `U` coarser than `π ∈ 𝚷(U)` are the
partitions of the set of blocks of `π`: `ρ ↦ {{B ∈ π : B ⊆ D} : D ∈ ρ}`, with inverse
`𝒴 ↦ {⋃ Y : Y ∈ 𝒴}`. -/
theorem sum_partitions_coarser {M : Type*} [AddCommMonoid M] (hπ : π ∈ partitions U)
    (F : Finset (Finset α) → M) :
    ∑ ρ ∈ (partitions U).filter (Refines π ·), F ρ =
      ∑ 𝒴 ∈ partitions π, F (𝒴.image fun Y => Y.biUnion id) := by
  have hπs := (mem_partitions.1 hπ).1
  refine Finset.sum_nbij' (fun ρ => ρ.image (fun D => π.filter (· ⊆ D)))
    (fun 𝒴 => 𝒴.image fun Y => Y.biUnion id) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    exact image_filter_mem_partitions hπ hρ.1 hρ.2
  · intro 𝒴 h𝒴
    exact Finset.mem_filter.2 ⟨image_biUnion_mem_partitions hπ h𝒴, refines_image_biUnion h𝒴⟩
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := ρ)]
    exact Finset.image_congr fun D hD => biUnion_filter_subset_eq hπ hρ.1 hρ.2 hD
  · intro 𝒴 h𝒴
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := 𝒴)]
    exact Finset.image_congr fun Y hY =>
      filter_subset_biUnion_eq hπs (subset_of_mem_partitions h𝒴 hY)
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    congr 1
    rw [Finset.image_image]
    conv_lhs => rw [← Finset.image_id (s := ρ)]
    exact (Finset.image_congr fun D hD => biUnion_filter_subset_eq hπ hρ.1 hρ.2 hD).symm

open scoped Classical in
/-- **Partitions of partitions.** Summing a weight of the partitions of the set of blocks over
all partitions `π` of `U` amounts to choosing a partition `ρ` of `U` and a partition of each block
of `ρ`. -/
theorem sum_partitionSum_partitions {R : Type*} [CommSemiring R] (U : Finset α)
    (G : Finset (Finset α) → R) :
    ∑ π ∈ partitions U, partitionSum G π =
      partitionSum (fun D => ∑ Y ∈ partitions D, G Y) U := by
  have h1 : ∀ π ∈ partitions U, partitionSum G π =
      ∑ ρ ∈ (partitions U).filter (Refines π ·), ∏ D ∈ ρ, G (π.filter (· ⊆ D)) := by
    intro π hπ
    rw [sum_partitions_coarser hπ, partitionSum]
    refine Finset.sum_congr rfl fun 𝒴 h𝒴 => ?_
    rw [Finset.prod_image (injOn_biUnion (mem_partitions.1 hπ).1 h𝒴)]
    refine Finset.prod_congr rfl fun Y hY => ?_
    rw [filter_subset_biUnion_eq (mem_partitions.1 hπ).1 (subset_of_mem_partitions h𝒴 hY)]
  rw [Finset.sum_congr rfl h1, partitionSum]
  rw [Finset.sum_comm' (t' := partitions U)
    (s' := fun ρ => (partitions U).filter (Refines · ρ)) (fun π ρ => by
      simp only [Finset.mem_filter]
      tauto)]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  exact sum_partitions_refines hρ (fun _ σ => G σ)

end Coarser

/-! ### The Möbius function of the partition lattice -/

section Mobius

/-- `(-1)^{k-1} (k-1)!`, the value of the Möbius function of the partition lattice of a `k`-element
set between its bottom and top elements. -/
def mobiusWeight (k : ℕ) : ℤ :=
  (-1) ^ (k - 1) * ((k - 1).factorial : ℤ)

theorem mobiusWeight_one : mobiusWeight 1 = 1 := by
  simp [mobiusWeight]

theorem mobiusWeight_add_mul {n : ℕ} (hn : 2 ≤ n) :
    mobiusWeight n + ((n - 1 : ℕ) : ℤ) * mobiusWeight (n - 1) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [mobiusWeight, show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega,
    Nat.factorial_succ, Nat.cast_mul, pow_succ]
  push_cast
  ring

/-- The subsets `D ∋ a` of `T` with `|T \ D| ≤ 1` are `T` and the `T \ {b}`, `b ≠ a`. -/
theorem filter_card_sdiff_le_one {T : Finset α} {a : α} (ha : a ∈ T) :
    (T.powerset.filter (a ∈ ·)).filter (fun D => (T \ D).card ≤ 1) =
      insert T ((T.erase a).image fun b => T.erase b) := by
  ext D
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_image,
    Finset.mem_erase]
  constructor
  · rintro ⟨⟨hDT, haD⟩, hcard⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1
    · left
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h0
      exact le_antisymm hDT h0
    · right
      obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h1
      have hbT : b ∈ T \ D := hb ▸ Finset.mem_singleton_self b
      rw [Finset.mem_sdiff] at hbT
      refine ⟨b, ⟨fun h => hbT.2 (h ▸ haD), hbT.1⟩, ?_⟩
      ext x
      rw [Finset.mem_erase]
      constructor
      · rintro ⟨hxb, hxT⟩
        by_contra hxD
        have : x ∈ T \ D := Finset.mem_sdiff.2 ⟨hxT, hxD⟩
        rw [hb, Finset.mem_singleton] at this
        exact hxb this
      · intro hxD
        exact ⟨fun h => hbT.2 (h ▸ hxD), hDT hxD⟩
  · rintro (rfl | ⟨b, ⟨hba, hbT⟩, rfl⟩)
    · exact ⟨⟨le_rfl, ha⟩, by simp⟩
    · refine ⟨⟨Finset.erase_subset _ _, Finset.mem_erase.2 ⟨fun h => hba h.symm, ha⟩⟩, ?_⟩
      rw [Finset.sdiff_erase_self hbT, Finset.card_singleton]

/-- `∑_{σ ∈ 𝚷(T)} ∏_{Q ∈ σ} (-1)^{|Q|-1} (|Q|-1)!` is `1` if `|T| ≤ 1` and `0` otherwise. -/
theorem partitionSum_mobiusWeight {R : Type*} [CommRing R] (T : Finset α) :
    partitionSum (fun Q => (mobiusWeight Q.card : R)) T = if T.card ≤ 1 then 1 else 0 := by
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp [partitionSum_empty]
    rw [partitionSum_root _ ha]
    have h1 : ∀ D ∈ T.powerset.filter (a ∈ ·),
        (mobiusWeight D.card : R) * partitionSum (fun Q => (mobiusWeight Q.card : R)) (T \ D) =
          if (T \ D).card ≤ 1 then (mobiusWeight D.card : R) else 0 := by
      intro D hD
      rw [Finset.mem_filter, Finset.mem_powerset] at hD
      rw [ih (T \ D) (Finset.sdiff_ssubset hD.1 ⟨a, hD.2⟩)]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, filter_card_sdiff_le_one ha,
      Finset.sum_insert, Finset.sum_image]
    · have hcard : ∀ b ∈ T.erase a, (T.erase b).card = T.card - 1 := fun b hb =>
        Finset.card_erase_of_mem (Finset.mem_erase.1 hb).2
      rw [Finset.sum_congr rfl fun b hb => by rw [hcard b hb], Finset.sum_const,
        Finset.card_erase_of_mem ha, nsmul_eq_mul]
      have hT1 : 1 ≤ T.card := Finset.card_pos.2 ⟨a, ha⟩
      split_ifs with hT
      · have : T.card = 1 := le_antisymm hT hT1
        rw [this]
        simp [mobiusWeight_one]
      · have h' := congrArg (Int.cast : ℤ → R) (mobiusWeight_add_mul (n := T.card) (by omega))
        push_cast at h'
        exact h'
    · intro b hb b' _ hbb'
      have hb2 : b ∈ T := (Finset.mem_erase.1 (Finset.mem_coe.1 hb)).2
      dsimp only at hbb'
      by_contra hne
      have h1 : b ∈ T.erase b' := Finset.mem_erase.2 ⟨hne, hb2⟩
      rw [← hbb'] at h1
      exact (Finset.notMem_erase b T) h1
    · intro hT
      obtain ⟨b, hb, hbT⟩ := Finset.mem_image.1 hT
      have h1 : b ∈ T.erase b := by
        rw [hbT]
        exact (Finset.mem_erase.1 hb).2
      exact Finset.notMem_erase b T h1

open scoped Classical in
/-- The Möbius function of the partition lattice, equation (4.139):
for `π ≤ σ`, `μ(π, σ) = ∏_{B ∈ σ} (-1)^{k_B - 1} (k_B - 1)!`, where `k_B` is the number of blocks of
`π` contained in `B`; `μ(π, σ) = 0` if `π ≰ σ`. -/
noncomputable def mobius (π σ : Finset (Finset α)) : ℤ :=
  if Refines π σ then ∏ B ∈ σ, mobiusWeight (π.filter (· ⊆ B)).card else 0

open scoped Classical in
theorem mobius_of_refines {π σ : Finset (Finset α)} (h : Refines π σ) :
    mobius π σ = ∏ B ∈ σ, mobiusWeight (π.filter (· ⊆ B)).card := by
  rw [mobius, ite_eq_left h]

theorem mobius_of_not_refines {π σ : Finset (Finset α)} (h : ¬ Refines π σ) : mobius π σ = 0 := by
  rw [mobius, ite_eq_right h]

variable {E : Finset α}

/-- Two comparable partitions are equal iff each block of the coarser one contains at most one
block of the finer one. -/
theorem forall_card_filter_le_one_iff {ρ σ : Finset (Finset α)} (hρ : ρ ∈ partitions E)
    (hσ : σ ∈ partitions E) (h : Refines ρ σ) :
    (∀ T ∈ σ.image (fun C => ρ.filter (· ⊆ C)), T.card ≤ 1) ↔ ρ = σ := by
  have hρs := (mem_partitions.1 hρ).1
  have hσs := (mem_partitions.1 hσ).1
  constructor
  · intro hT
    have hσρ : σ ⊆ ρ := by
      intro C hC
      have hcard := hT _ (Finset.mem_image_of_mem _ hC)
      have hU := biUnion_filter_subset_eq hρ hσ h hC
      obtain ⟨x, hx⟩ := hσs.1 C hC
      rw [← hU] at hx
      obtain ⟨B, hB, -⟩ := mem_biUnion_id.1 hx
      obtain ⟨B', hB'⟩ := Finset.card_eq_one.1
        (le_antisymm hcard (Finset.card_pos.2 ⟨B, hB⟩))
      rw [hB'] at hU
      simp only [Finset.singleton_biUnion, id] at hU
      have : B' ∈ ρ.filter (· ⊆ C) := hB' ▸ Finset.mem_singleton_self B'
      rw [← hU]
      exact (Finset.mem_filter.1 this).1
    refine le_antisymm (fun B hB => ?_) hσρ
    obtain ⟨C, hC, hBC⟩ := h B hB
    obtain ⟨x, hx⟩ := hρs.1 B hB
    rw [eq_of_isSubpartition hρs hB (hσρ hC) hx (hBC hx)]
    exact hC
  · rintro rfl T hT
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hT
    refine Finset.card_le_one.2 fun B hB B' hB' => ?_
    rw [Finset.mem_filter] at hB hB'
    obtain ⟨x, hx⟩ := hρs.1 B hB.1
    obtain ⟨y, hy⟩ := hρs.1 B' hB'.1
    rw [eq_of_isSubpartition hρs hB.1 hC hx (hB.2 hx),
      eq_of_isSubpartition hρs hB'.1 hC hy (hB'.2 hy)]

open scoped Classical in
/-- `∑_{ρ ≤ π ≤ σ} μ(ρ, π) = δ(ρ, σ)` for `ρ ≤ σ`: the interval `[ρ, σ]` is the product of the
partition lattices of the sets of blocks of `ρ` inside the blocks of `σ`. -/
theorem sum_mobius_refines_of_refines {R : Type*} [CommRing R] {ρ σ : Finset (Finset α)}
    (hρ : ρ ∈ partitions E) (hσ : σ ∈ partitions E) (h : Refines ρ σ) :
    ∑ π ∈ partitions E, (mobius ρ π : R) * (if Refines π σ then 1 else 0) =
      if ρ = σ then 1 else 0 := by
  have hρs := (mem_partitions.1 hρ).1
  have h1 : ∑ π ∈ partitions E, (mobius ρ π : R) * (if Refines π σ then 1 else 0) =
      ∑ π ∈ (partitions E).filter (Refines ρ ·),
        (mobius ρ π : R) * (if Refines π σ then 1 else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun π _ => ?_
    by_cases hπ : Refines ρ π
    · rw [ite_eq_left hπ]
    · rw [ite_eq_right hπ, mobius_of_not_refines hπ, Int.cast_zero, zero_mul]
  set 𝒴σ := σ.image (fun C => ρ.filter (· ⊆ C)) with h𝒴σ
  have h𝒴σmem : 𝒴σ ∈ partitions ρ := image_filter_mem_partitions hρ hσ h
  have h2 : ∀ 𝒴 ∈ partitions ρ,
      (mobius ρ (𝒴.image fun Y => Y.biUnion id) : R) *
          (if Refines (𝒴.image fun Y => Y.biUnion id) σ then 1 else 0) =
        if Refines 𝒴 𝒴σ then ∏ Y ∈ 𝒴, (mobiusWeight Y.card : R) else 0 := by
    intro 𝒴 h𝒴
    rw [mobius_of_refines (refines_image_biUnion h𝒴),
      Finset.prod_image (injOn_biUnion hρs h𝒴)]
    have hprod : ∏ Y ∈ 𝒴, mobiusWeight (ρ.filter (· ⊆ Y.biUnion id)).card =
        ∏ Y ∈ 𝒴, mobiusWeight Y.card := Finset.prod_congr rfl fun Y hY => by
      rw [filter_subset_biUnion_eq hρs (subset_of_mem_partitions h𝒴 hY)]
    have hiff : Refines (𝒴.image fun Y => Y.biUnion id) σ ↔ Refines 𝒴 𝒴σ := by
      constructor
      · intro hr Y hY
        obtain ⟨C, hC, hYC⟩ := hr _ (Finset.mem_image_of_mem _ hY)
        refine ⟨ρ.filter (· ⊆ C), Finset.mem_image_of_mem _ hC, fun B hB => ?_⟩
        exact Finset.mem_filter.2 ⟨subset_of_mem_partitions h𝒴 hY hB,
          (subset_biUnion_of_mem hB).trans hYC⟩
      · intro hr D hD
        obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hD
        obtain ⟨T, hT, hYT⟩ := hr Y hY
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hT
        refine ⟨C, hC, fun x hx => ?_⟩
        obtain ⟨B, hB, hxB⟩ := mem_biUnion_id.1 hx
        exact (Finset.mem_filter.1 (hYT hB)).2 hxB
    rw [hprod, Int.cast_prod]
    by_cases hr : Refines 𝒴 𝒴σ
    · rw [ite_eq_left (hiff.2 hr), ite_eq_left hr, mul_one]
    · rw [ite_eq_right (fun h' => hr (hiff.1 h')), ite_eq_right hr, mul_zero]
  rw [h1, sum_partitions_coarser hρ, Finset.sum_congr rfl h2, ← Finset.sum_filter,
    sum_partitions_refines_prod h𝒴σmem]
  have h3 : ∀ T ∈ 𝒴σ, partitionSum (fun Q => (mobiusWeight Q.card : R)) T =
      if T.card ≤ 1 then 1 else 0 := fun T _ => partitionSum_mobiusWeight T
  rw [Finset.prod_congr rfl h3, Finset.prod_boole]
  simp only [forall_card_filter_le_one_iff hρ hσ h, h𝒴σ]

open scoped Classical in
/-- `∑_{π} μ(ρ, π) 𝟙[π ≤ σ] = δ(ρ, σ)` for all partitions `ρ`, `σ` of `E` (`μ ζ = δ` in the
incidence algebra). -/
theorem sum_mobius_refines {R : Type*} [CommRing R] {ρ σ : Finset (Finset α)}
    (hρ : ρ ∈ partitions E) (hσ : σ ∈ partitions E) :
    ∑ π ∈ partitions E, (mobius ρ π : R) * (if Refines π σ then 1 else 0) =
      if ρ = σ then 1 else 0 := by
  by_cases h : Refines ρ σ
  · exact sum_mobius_refines_of_refines hρ hσ h
  · rw [ite_eq_right (fun h' => h (by rw [← h']; exact refines_refl ρ))]
    refine Finset.sum_eq_zero fun π _ => ?_
    by_cases hπ : Refines ρ π
    · rw [ite_eq_right (fun h' => h (refines_trans hπ h')), mul_zero]
    · rw [mobius_of_not_refines hπ, Int.cast_zero, zero_mul]

open scoped Classical in
/-- `∑_{π} 𝟙[ρ ≤ π] μ(π, σ) = δ(ρ, σ)` (`ζ μ = δ`): a left inverse of the zeta matrix of the finite
poset `𝚷(E)` is a right inverse. -/
theorem sum_refines_mobius {R : Type*} [CommRing R] {ρ σ : Finset (Finset α)}
    (hρ : ρ ∈ partitions E) (hσ : σ ∈ partitions E) :
    ∑ π ∈ partitions E, (if Refines ρ π then 1 else 0) * (mobius π σ : R) =
      if ρ = σ then 1 else 0 := by
  let Z : Matrix (partitions E) (partitions E) R :=
    Matrix.of fun ρ π => if Refines (ρ : Finset (Finset α)) π then 1 else 0
  let Mu : Matrix (partitions E) (partitions E) R :=
    Matrix.of fun ρ π => (mobius (ρ : Finset (Finset α)) π : R)
  have hMZ : Mu * Z = 1 := by
    ext ρ' σ'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Mu, Z, Matrix.of_apply]
    rw [Finset.sum_coe_sort (partitions E)
      (fun π => (mobius (ρ' : Finset (Finset α)) π : R) *
        if Refines π (σ' : Finset _) then 1 else 0),
      sum_mobius_refines ρ'.2 σ'.2]
    simp only [Subtype.ext_iff]
  have hZM : Z * Mu = 1 := mul_eq_one_comm.mp hMZ
  have := congrFun (congrFun hZM ⟨ρ, hρ⟩) ⟨σ, hσ⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simp only [Mu, Z, Matrix.of_apply] at this
  rw [Finset.sum_coe_sort (partitions E)
    (fun π => (if Refines ρ π then 1 else 0) * (mobius π σ : R))] at this
  rw [this]
  simp only [Subtype.mk.injEq]

open scoped Classical in
/-- **Lemma 4.60 (1)**. Let `g : 𝚷(E) → R` and
`f(π) = ∑_{σ ≤ π} g(σ)`. Then `g(σ) = ∑_{π ≤ σ} μ(π, σ) f(π)` for every `σ ∈ 𝚷(E)`, with `μ` the
Möbius function (4.139). -/
theorem lemma_4_60_1 {R : Type*} [CommRing R] (E : Finset α) (g f : Finset (Finset α) → R)
    (hf : ∀ π ∈ partitions E, f π = ∑ σ ∈ (partitions E).filter (Refines · π), g σ) :
    ∀ σ ∈ partitions E,
      g σ = ∑ π ∈ (partitions E).filter (Refines · σ), (mobius π σ : R) * f π := by
  intro σ hσ
  have h1 : ∑ π ∈ (partitions E).filter (Refines · σ), (mobius π σ : R) * f π =
      ∑ π ∈ partitions E, ∑ ρ ∈ partitions E,
        g ρ * ((if Refines ρ π then 1 else 0) * (mobius π σ : R)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun π hπ => ?_
    split_ifs with h
    · rw [hf π hπ, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      split_ifs <;> ring
    · rw [mobius_of_not_refines h]
      simp
  rw [h1, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun ρ hρ => by rw [sum_refines_mobius hρ hσ]]
  simp [hσ]

open scoped Classical in
/-- **Lemma 4.60 (2)** (equation (4.140)). Let
`g : 𝚷(E) → R` and `f(π) = ∑_{σ ≥ π} g(σ)`. Then `g(σ) = ∑_{π ≥ σ} μ(σ, π) f(π)` for every
`σ ∈ 𝚷(E)`. -/
theorem lemma_4_60_2 {R : Type*} [CommRing R] (E : Finset α) (g f : Finset (Finset α) → R)
    (hf : ∀ π ∈ partitions E, f π = ∑ σ ∈ (partitions E).filter (Refines π ·), g σ) :
    ∀ σ ∈ partitions E,
      g σ = ∑ π ∈ (partitions E).filter (Refines σ ·), (mobius σ π : R) * f π := by
  intro σ hσ
  have h1 : ∑ π ∈ (partitions E).filter (Refines σ ·), (mobius σ π : R) * f π =
      ∑ π ∈ partitions E, ∑ ρ ∈ partitions E,
        g ρ * ((mobius σ π : R) * (if Refines π ρ then 1 else 0)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun π hπ => ?_
    split_ifs with h
    · rw [hf π hπ, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      split_ifs <;> ring
    · rw [mobius_of_not_refines h]
      simp
  rw [h1, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun ρ hρ => by rw [sum_mobius_refines hσ hρ]]
  simp [hσ]

end Mobius

end SetPartition

end MultipoleBKT

end
