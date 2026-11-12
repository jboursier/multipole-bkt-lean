/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Multipole.RouteGrouping.Integral

/-!
# Marks on union components and unused multipoles

See the paper, Step 5 of the proof of Lemma 5.16. The marks are retained while the edge families are grouped.
Marks outside the nontrivial components remain on the unused multipoles.
-/

public section

namespace MultipoleBKT.Multipole.RouteGrouping

open MeasureTheory Finset SetPartition Hierarchical
open scoped Classical

/-- Summing the marks on unused multipoles gives their external factors.
The groups are disjoint and have at least two blocks, as in the marked expansion. -/
theorem unused_marks {D : Finset (Finset ℕ)} (hD : IsSubpartition D)
    {𝒱 : Finset (Finset (Finset ℕ))}
    (m : ℕ → ℝ) :
    ∑ U ∈ ((D \ 𝒱.biUnion id).biUnion id).powerset, ∏ i ∈ U, m i =
      ∏ S ∈ D \ 𝒱.biUnion id, ∏ i ∈ S, (1 + m i) := by
  rw [← Finset.prod_one_add]
  exact Finset.prod_biUnion (isSubpartition_mono hD Finset.sdiff_subset).2

/-- Marks distribute over the components of the union graph, including singletons. -/
theorem marks_partition {D : Finset (Finset ℕ)} (hD : IsSubpartition D)
    {π : Finset (Finset (Finset ℕ))} (hπ : π ∈ partitions D) (m : ℕ → ℝ) :
    ∏ Y ∈ π, ∏ i ∈ Y.biUnion id, (1 + m i) = ∏ i ∈ D.biUnion id, (1 + m i) := by
  rw [Finset.prod_congr rfl fun Y hY => Finset.prod_biUnion
    (isSubpartition_mono hD (subset_of_mem_partitions hπ hY)).2]
  have hp := Finset.prod_biUnion (f := fun B => ∏ i ∈ B, (1 + m i)) (mem_partitions.1 hπ).1.2
  rw [(mem_partitions.1 hπ).2] at hp
  dsimp only [id_eq] at hp ⊢
  rw [← hp]
  exact (Finset.prod_biUnion hD.2).symm

/-- The marked counterpart of (4.36), with the unused marks displayed
explicitly as in Lemma 5.16. Only the nontrivial union
components carry `𝒰(X)`. Every remaining multipole retains all its marks. -/
theorem marked_components_with_unused (f b : ℕ × ℕ → ℝ) (m : ℕ → ℝ)
    {D : Finset (Finset ℕ)} (hD : IsSubpartition D) :
    (∏ p ∈ interPairs D, ((1 + f p) * (1 - b p))) *
        ∏ i ∈ D.biUnion id, (1 + m i) =
      ∑ 𝒱 ∈ disjointFamilies D (fun Y => 2 ≤ Y.card),
        (∏ Y ∈ 𝒱, groupWeight f b Y * ∏ i ∈ Y.biUnion id, (1 + m i)) *
          ∑ U ∈ ((D \ 𝒱.biUnion id).biUnion id).powerset, ∏ i ∈ U, m i := by
  rw [prod_eq_partitionSum_groupWeight hD, partitionSum, Finset.sum_mul]
  have hmarked : ∀ π ∈ partitions D,
      (∏ Y ∈ π, groupWeight f b Y) * (∏ i ∈ D.biUnion id, (1 + m i)) =
        ∏ Y ∈ π, groupWeight f b Y * ∏ i ∈ Y.biUnion id, (1 + m i) := by
    intro π hπ
    rw [Finset.prod_mul_distrib, marks_partition hD hπ]
  rw [Finset.sum_congr rfl hmarked]
  symm
  refine Finset.sum_nbij' (complete D) (fun π => π.filter (fun Y => 2 ≤ Y.card))
    (fun 𝒱 h𝒱 => complete_mem_partitions (fun _ h => h) h𝒱) (fun π hπ => ?_)
    (fun 𝒱 h𝒱 => filter_complete (fun _ h => h) h𝒱) (fun π hπ => ?_) (fun 𝒱 h𝒱 => ?_)
  · have hπs := (mem_partitions.1 hπ).1
    exact mem_disjointFamilies.2
      ⟨fun Y hY => subset_of_mem_partitions hπ (Finset.mem_filter.1 hY).1,
        hπs.2.subset (Finset.coe_subset.2 (Finset.filter_subset _ _)),
        fun Y hY => (Finset.mem_filter.1 hY).2⟩
  · refine complete_filter hπ fun Y hY => ?_
    have := Finset.card_pos.2 ((mem_partitions.1 hπ).1.1 Y hY)
    by_cases h : 2 ≤ Y.card
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rw [unused_marks hD, complete, Finset.prod_union]
    · congr 1
      rw [Finset.prod_image (fun _ _ _ _ h => Finset.singleton_injective h)]
      exact Finset.prod_congr rfl fun S hS => by
        rw [groupWeight_singleton (hD.1 S (Finset.mem_sdiff.1 hS).1), one_mul,
          Finset.singleton_biUnion, id_eq]
    · rw [Finset.disjoint_left]
      intro Y hY hY'
      obtain ⟨S, _, rfl⟩ := Finset.mem_image.1 hY'
      have h2 := (mem_disjointFamilies.1 h𝒱).2.2 _ hY
      simp at h2

variable {ρ : Measure (ℂ × ℂ)} [IsProbabilityMeasure ρ]
variable {f b : ℂ × ℂ → ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)}

/-- The integral carried by a union component with its retained external marks. -/
@[expose] noncomputable def markedComponentIntegral (ρ : Measure (ℂ × ℂ))
    (bw : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ) (f b : ℂ × ℂ → ℂ × ℂ → ℝ)
    (m : ℂ × ℂ → ℝ) (Y : Finset (Finset ℕ)) : ℝ :=
  ∫ c, ((∏ B ∈ Y, bw B c) *
    groupWeight (fun p => f (c p.1) (c p.2)) (fun p => b (c p.1) (c p.2)) Y) *
      ∏ i ∈ Y.biUnion id, (1 + m (c i)) ∂labelField ρ

/-- Direct marked component expansion followed by independent integration.
The singleton factors are retained and become the unused external normalizations. -/
theorem marked_grouping_integral
    (bw : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ) (m : ℂ × ℂ → ℝ)
    (hK : ∀ᵐ d ∂ρ, d ∈ K)
    (hwm : ∀ B, Measurable (bw B)) (hwb : ∀ B, BoundedOn K (bw B))
    (hwd : ∀ B, DependsOn (bw B) (B : Set ℕ))
    (hfm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => f q.1 q.2)
    (hbm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => b q.1 q.2)
    (hfb : ∀ i j, BoundedOn K fun c => f (c i) (c j))
    (hbb : ∀ i j, BoundedOn K fun c => b (c i) (c j))
    (hmm : Measurable m) (hmb : ∃ B, ∀ d ∈ K, |m d| ≤ B)
    {D : Finset (Finset ℕ)} (hD : IsSubpartition D) :
    (∫ c, ((∏ B ∈ D, bw B c) *
      ∏ p ∈ interPairs D, ((1 + f (c p.1) (c p.2)) * (1 - b (c p.1) (c p.2)))) *
        ∏ i ∈ D.biUnion id, (1 + m (c i)) ∂labelField ρ) =
    partitionSum (fun Y => ∫ c, ((∏ B ∈ Y, bw B c) *
      groupWeight (fun p => f (c p.1) (c p.2)) (fun p => b (c p.1) (c p.2)) Y) *
        ∏ i ∈ Y.biUnion id, (1 + m (c i)) ∂labelField ρ) D := by
  let Φ := fun Y c => ((∏ B ∈ Y, bw B c) *
    groupWeight (fun p => f (c p.1) (c p.2)) (fun p => b (c p.1) (c p.2)) Y) *
      ∏ i ∈ Y.biUnion id, (1 + m (c i))
  have hm : ∀ Y, Measurable (Φ Y) := fun Y =>
    ((Finset.measurable_prod _ fun B _ => hwm B).mul (measurable_groupWeight hfm hbm Y)).mul
      (Finset.measurable_prod _ fun i _ => measurable_const.add (hmm.comp (measurable_pi_apply i)))
  have hb : ∀ Y, BoundedOn K (Φ Y) := fun Y =>
    ((BoundedOn.prod _ fun B _ => hwb B).mul (boundedOn_groupWeight hfb hbb Y)).mul
      (BoundedOn.prod _ fun i _ => (BoundedOn.const K 1).add (BoundedOn.single hmb i))
  have hd : ∀ Y, DependsOn (Φ Y) (Y.biUnion id : Set ℕ) := by
    intro Y c c' hcc'
    dsimp only [Φ]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_
      (dependsOn_groupWeight (f := f) (b := b) Y hcc')) ?_
    · exact Finset.prod_congr rfl fun B hB => hwd B fun i hi =>
        hcc' i (subset_biUnion_of_mem hB hi)
    · exact Finset.prod_congr rfl fun i hi => congrArg (fun d => 1 + m d) (hcc' i hi)
  calc
    _ = ∫ c, partitionSum (fun Y => Φ Y c) D ∂labelField ρ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
      dsimp only
      rw [prod_eq_partitionSum_groupWeight (f := fun p => f (c p.1) (c p.2))
        (b := fun p => b (c p.1) (c p.2)) hD, partitionSum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun π hπ => ?_
      dsimp only [Φ]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, marks_partition hD hπ]
      congr 2
      have hp := Finset.prod_biUnion (f := fun B => bw B c) (mem_partitions.1 hπ).1.2
      rw [(mem_partitions.1 hπ).2] at hp
      exact hp
    _ = _ := integral_partitionSum D (fun Y => Y.biUnion id) Φ hm
      (fun π _ => integrable_of_boundedOn hK
        (Finset.measurable_prod _ fun Y _ => hm Y) (BoundedOn.prod _ fun Y _ => hb Y)) hd
      (fun π hπ Y hY Y' hY' hne => disjoint_biUnion_of_disjoint hD
        (subset_of_mem_partitions hπ hY) (subset_of_mem_partitions hπ hY')
        ((mem_partitions.1 hπ).1.2 hY hY' hne))

end MultipoleBKT.Multipole.RouteGrouping
