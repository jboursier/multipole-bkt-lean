/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Field
public import MultipoleBKT.Multipole.RouteGrouping.Pairs

/-!
# Integrating the directly grouped expansion

See the paper, equation (4.36).
The groups are the components of the union of the two expanded edge families.
Integration factors over their disjoint label sets, including singleton components.
-/

public section

namespace MultipoleBKT.Multipole.RouteGrouping

open MeasureTheory Finset SetPartition Hierarchical
open scoped Classical

variable {ρ : Measure (ℂ × ℂ)} [IsProbabilityMeasure ρ]

/-- Independence of all the components of a subpartition under the product measure. -/
theorem integral_prod_components {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (U : ι → Finset ℕ) (Φ : ι → (ℕ → ℂ × ℂ) → ℝ)
    (hd : (s : Set ι).PairwiseDisjoint U)
    (hm : ∀ i ∈ s, Measurable (Φ i))
    (hdep : ∀ i ∈ s, DependsOn (Φ i) (U i : Set ℕ)) :
    ∫ c, ∏ i ∈ s, Φ i c ∂labelField ρ = ∏ i ∈ s, ∫ c, Φ i c ∂labelField ρ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    rw [integral_mul_of_dependsOn' (C := U i) (D := s.biUnion U) ?_
      (hm i (Finset.mem_insert_self _ _))
      (Finset.measurable_prod _ fun j hj => hm j (Finset.mem_insert_of_mem hj))
      (hdep i (Finset.mem_insert_self _ _)) ?_]
    · rw [ih (hd.subset (by intro j hj; exact Finset.mem_insert_of_mem hj))
        (fun j hj => hm j (Finset.mem_insert_of_mem hj))
        (fun j hj => hdep j (Finset.mem_insert_of_mem hj))]
    · rw [Finset.disjoint_left]
      intro a hai has
      obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.1 has
      exact Finset.disjoint_left.1
        (hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
          (fun h => hi (h ▸ hj))) hai haj
    · intro c c' hcc'
      exact Finset.prod_congr rfl fun j hj => hdep j (Finset.mem_insert_of_mem hj)
        fun a ha => hcc' a (Finset.mem_biUnion.2 ⟨j, hj, ha⟩)

/-- Finite partition sums commute with integration and factor over components. -/
theorem integral_partitionSum {α : Type*} [DecidableEq α] (D : Finset α)
    (U : Finset α → Finset ℕ) (Φ : Finset α → (ℕ → ℂ × ℂ) → ℝ)
    (hm : ∀ Y, Measurable (Φ Y))
    (hi : ∀ π ∈ partitions D, Integrable (fun c => ∏ Y ∈ π, Φ Y c) (labelField ρ))
    (hdep : ∀ Y, DependsOn (Φ Y) (U Y : Set ℕ))
    (hd : ∀ π ∈ partitions D, (π : Set (Finset α)).PairwiseDisjoint U) :
    ∫ c, partitionSum (fun Y => Φ Y c) D ∂labelField ρ =
      partitionSum (fun Y => ∫ c, Φ Y c ∂labelField ρ) D := by
  unfold partitionSum
  rw [integral_finsetSum _ hi]
  exact Finset.sum_congr rfl fun π hπ =>
    integral_prod_components π U Φ (hd π hπ) (fun Y _ => hm Y) (fun Y _ => hdep Y)

variable {f b : ℂ × ℂ → ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)}

/-- Regularity of the finite connected edge sum, before any compact identification. -/
theorem measurable_relConnSum
    (hf : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => f q.1 q.2)
    (D : Finset (Finset ℕ)) :
    Measurable fun c : ℕ → ℂ × ℂ => relConnSum (fun p => f (c p.1) (c p.2)) D :=
  Finset.measurable_sum _ fun _ _ => Finset.measurable_prod _ fun p _ => measurable_pairWeight hf p

/-- The connected edge sum is bounded on configurations in `K`. -/
theorem boundedOn_relConnSum
    (hf : ∀ i j, BoundedOn K fun c => f (c i) (c j)) (D : Finset (Finset ℕ)) :
    BoundedOn K fun c => relConnSum (fun p => f (c p.1) (c p.2)) D :=
  BoundedOn.sum _ fun _ _ => BoundedOn.prod _ fun p _ => hf p.1 p.2

/-- Connected edge sums only depend on the labels of their component. -/
theorem dependsOn_relConnSum (D : Finset (Finset ℕ)) :
    DependsOn (fun c : ℕ → ℂ × ℂ => relConnSum (fun p => f (c p.1) (c p.2)) D)
      (D.biUnion id : Set ℕ) := by
  intro c c' hcc'
  have h := dependsOn_connWeight (h := fun _ _ => 1) (φ := f)
    (fun _ _ _ _ => rfl) D hcc'
  simpa only [connWeight, Finset.prod_const_one, one_mul] using h

/-- The two component families in the grouped expansion have measurable weights. -/
theorem measurable_groupWeight
    (hf : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => f q.1 q.2)
    (hb : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => b q.1 q.2)
    (D : Finset (Finset ℕ)) :
    Measurable fun c : ℕ → ℂ × ℂ =>
      groupWeight (fun p => f (c p.1) (c p.2)) (fun p => b (c p.1) (c p.2)) D := by
  unfold groupWeight groupFactor
  dsimp only
  exact Finset.measurable_sum _ fun σ _ =>
    (Finset.measurable_prod _ fun T _ => (measurable_relConnSum hf T).mul
      (Finset.measurable_prod _ fun p _ => measurable_const.sub (measurable_pairWeight hb p))).mul
      (measurable_relConnSum (f := fun d e => -b d e) hb.neg (merge σ))

/-- The grouped weight is bounded because all its sums are finite. -/
theorem boundedOn_groupWeight
    (hf : ∀ i j, BoundedOn K fun c => f (c i) (c j))
    (hb : ∀ i j, BoundedOn K fun c => b (c i) (c j)) (D : Finset (Finset ℕ)) :
    BoundedOn K fun c =>
      groupWeight (fun p => f (c p.1) (c p.2)) (fun p => b (c p.1) (c p.2)) D := by
  unfold groupWeight groupFactor
  dsimp only
  exact BoundedOn.sum _ fun σ _ =>
    (BoundedOn.prod _ fun T _ => (boundedOn_relConnSum hf T).mul
      (BoundedOn.prod _ fun p _ => (BoundedOn.const K 1).sub (hb p.1 p.2))).mul
      (boundedOn_relConnSum (f := fun d e => -b d e) (fun i j => (hb i j).neg) (merge σ))

/-- The grouped weight only uses labels in its union component. -/
theorem dependsOn_groupWeight (D : Finset (Finset ℕ)) :
    DependsOn (fun c : ℕ → ℂ × ℂ =>
      groupWeight (fun p => f (c p.1) (c p.2)) (fun p => b (c p.1) (c p.2)) D)
      (D.biUnion id : Set ℕ) := by
  intro c c' hcc'
  unfold groupWeight groupFactor
  refine Finset.sum_congr rfl fun σ hσ => congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl fun T hT => congrArg₂ (· * ·) ?_ ?_
    · exact dependsOn_relConnSum T fun i hi => hcc' i
        (Finset.biUnion_subset_biUnion_of_subset_left id (subset_of_mem_partitions hσ hT) hi)
    · refine Finset.prod_congr rfl fun p hp => ?_
      have hsub := Finset.biUnion_subset_biUnion_of_subset_left id (subset_of_mem_partitions hσ hT)
      have hpair := mem_pairsOn.1 (interPairs_subset_pairsOn hp)
      dsimp only
      rw [hcc' _ (hsub hpair.1), hcc' _ (hsub hpair.2.1)]
  · apply dependsOn_relConnSum (f := fun d e => -b d e) (merge σ)
    intro i hi
    apply hcc' i
    have hU : (merge σ).biUnion id = D.biUnion id := by
      ext a
      simp only [merge, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨S, ⟨T, hT, rfl⟩, ha⟩
        exact mem_biUnion_id.1 (Finset.biUnion_subset_biUnion_of_subset_left id
          (subset_of_mem_partitions hσ hT) ha)
      · intro ha
        obtain ⟨B, hB, haB⟩ := ha
        obtain ⟨T, hT, hBT⟩ := exists_mem_of_mem_partitions hσ hB
        exact ⟨T.biUnion id, ⟨T, hT, rfl⟩, mem_biUnion_id.2 ⟨B, hBT, haB⟩⟩
    rwa [hU] at hi

/-- Integrating (4.36) directly. First group the two expanded edge families,
then integrate independently on the label sets of their union components. -/
theorem weighted_grouping_integral
    (bw : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ)
    (hK : ∀ᵐ d ∂ρ, d ∈ K)
    (hwm : ∀ B, Measurable (bw B))
    (hwb : ∀ B, BoundedOn K (bw B))
    (hwd : ∀ B, DependsOn (bw B) (B : Set ℕ))
    (hfm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => f q.1 q.2)
    (hbm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => b q.1 q.2)
    (hfb : ∀ i j, BoundedOn K fun c => f (c i) (c j))
    (hbb : ∀ i j, BoundedOn K fun c => b (c i) (c j))
    {D : Finset (Finset ℕ)} (hD : IsSubpartition D) :
    (∫ c, (∏ B ∈ D, bw B c) *
      ∏ p ∈ interPairs D, ((1 + f (c p.1) (c p.2)) * (1 - b (c p.1) (c p.2)))
      ∂labelField ρ) =
    partitionSum (fun Y => ∫ c, (∏ B ∈ Y, bw B c) *
      groupWeight (fun p => f (c p.1) (c p.2)) (fun p => b (c p.1) (c p.2)) Y
      ∂labelField ρ) D := by
  let Φ := fun Y c => (∏ B ∈ Y, bw B c) *
    groupWeight (fun p => f (c p.1) (c p.2)) (fun p => b (c p.1) (c p.2)) Y
  have hm : ∀ Y, Measurable (Φ Y) := fun Y =>
    (Finset.measurable_prod _ fun B _ => hwm B).mul (measurable_groupWeight hfm hbm Y)
  have hb : ∀ Y, BoundedOn K (Φ Y) := fun Y =>
    (BoundedOn.prod _ fun B _ => hwb B).mul (boundedOn_groupWeight hfb hbb Y)
  have hd : ∀ Y, DependsOn (Φ Y) (Y.biUnion id : Set ℕ) := by
    intro Y c c' hcc'
    dsimp only [Φ]
    exact congrArg₂ (· * ·)
      (Finset.prod_congr rfl fun B hB => hwd B fun i hi =>
        hcc' i (subset_biUnion_of_mem hB hi))
      (dependsOn_groupWeight (f := f) (b := b) Y hcc')
  calc
    _ = ∫ c, partitionSum (fun Y => Φ Y c) D ∂labelField ρ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
      dsimp only
      rw [prod_eq_partitionSum_groupWeight (f := fun p => f (c p.1) (c p.2))
        (b := fun p => b (c p.1) (c p.2)) hD, partitionSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun π hπ => ?_
      dsimp only [Φ]
      rw [Finset.prod_mul_distrib]
      congr 1
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
