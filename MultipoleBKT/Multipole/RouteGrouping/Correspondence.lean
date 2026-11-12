/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Mobius

/-!
# The correspondence for grouping the two expanded edge families

See the paper, equation (4.36),
and the marked expansion in Step 5 of the proof of Lemma 5.16.
The first partition records the Mayer components, including unused singleton blocks.
Partitioning these components by the separation edges gives the components of their
union. The inverse restricts the first partition to each union component.
-/

@[expose] public section

namespace MultipoleBKT.Multipole.RouteGrouping

open Finset SetPartition
open scoped Classical

variable {α : Type*} [DecidableEq α] {U : Finset α} {σ : Finset (Finset α)}

/-- Grouping the first components, with inverse given by restriction to union components.
No component is discarded, so the correspondence includes singleton and empty cases. -/
noncomputable def componentGroupingEquiv (hσ : σ ∈ partitions U) :
    {τ // τ ∈ partitions σ} ≃ {ρ // ρ ∈ (partitions U).filter (Refines σ ·)} where
  toFun τ := ⟨τ.1.image (fun Y => Y.biUnion id),
    Finset.mem_filter.2 ⟨image_biUnion_mem_partitions hσ τ.2, refines_image_biUnion τ.2⟩⟩
  invFun ρ := ⟨ρ.1.image (fun D => σ.filter (· ⊆ D)),
    image_filter_mem_partitions hσ (Finset.mem_filter.1 ρ.2).1 (Finset.mem_filter.1 ρ.2).2⟩
  left_inv τ := by
    apply Subtype.ext
    simp only [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := τ.1)]
    exact Finset.image_congr fun Y hY =>
      filter_subset_biUnion_eq (mem_partitions.1 hσ).1 (subset_of_mem_partitions τ.2 hY)
  right_inv ρ := by
    apply Subtype.ext
    simp only [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := ρ.1)]
    exact Finset.image_congr fun D hD => biUnion_filter_subset_eq hσ
      (Finset.mem_filter.1 ρ.2).1 (Finset.mem_filter.1 ρ.2).2 hD

/-- Reindexing by union components using the explicit correspondence. -/
theorem sum_componentGrouping {R : Type*} [AddCommMonoid R]
    (hσ : σ ∈ partitions U) (H : Finset (Finset (Finset α)) → R) :
    ∑ τ ∈ partitions σ, H τ =
      ∑ ρ ∈ (partitions U).filter (Refines σ ·), H (ρ.image fun D => σ.filter (· ⊆ D)) := by
  have h := (componentGroupingEquiv hσ).symm.sum_comp (fun τ => H τ.1)
  change (∑ ρ : {ρ // ρ ∈ (partitions U).filter (Refines σ ·)},
    H (ρ.1.image fun D => σ.filter (· ⊆ D))) = ∑ τ : {τ // τ ∈ partitions σ}, H τ.1 at h
  calc
    _ = ∑ τ : partitions σ, H τ.1 := (Finset.sum_coe_sort (partitions σ) H).symm
    _ = ∑ ρ : (partitions U).filter (Refines σ ·),
        H (ρ.1.image fun D => σ.filter (· ⊆ D)) := h.symm
    _ = _ := Finset.sum_coe_sort ((partitions U).filter (Refines σ ·))
      (fun ρ => H (ρ.image fun D => σ.filter (· ⊆ D)))

/-- Direct grouping of nested component weights. First reindex by the union components,
then choose the first components independently inside each union component. -/
theorem sum_nested_component_weights {R : Type*} [CommSemiring R]
    (U : Finset α) (G : Finset (Finset α) → R) :
    ∑ σ ∈ partitions U, partitionSum G σ =
      partitionSum (fun D => ∑ Y ∈ partitions D, G Y) U := by
  have h1 : ∀ σ ∈ partitions U, partitionSum G σ =
      ∑ ρ ∈ (partitions U).filter (Refines σ ·), ∏ D ∈ ρ, G (σ.filter (· ⊆ D)) := by
    intro σ hσ
    rw [partitionSum, sum_componentGrouping hσ]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hr := Finset.mem_filter.1 hρ
    have hinj : Set.InjOn (fun D => σ.filter (· ⊆ D)) ρ := by
      intro D hD D' hD' heq
      have hd := biUnion_filter_subset_eq hσ hr.1 hr.2 hD
      have hd' := biUnion_filter_subset_eq hσ hr.1 hr.2 hD'
      dsimp only at heq
      rw [← hd, ← hd', heq]
    exact Finset.prod_image hinj
  rw [Finset.sum_congr rfl h1, partitionSum]
  rw [Finset.sum_comm' (t' := partitions U)
    (s' := fun ρ => (partitions U).filter (Refines · ρ)) (fun σ ρ => by
      simp only [Finset.mem_filter]
      tauto)]
  exact Finset.sum_congr rfl fun ρ hρ => sum_partitions_refines hρ (fun _ σ => G σ)

end MultipoleBKT.Multipole.RouteGrouping
