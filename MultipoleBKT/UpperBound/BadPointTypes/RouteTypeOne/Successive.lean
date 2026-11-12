/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeOne.Summation

/-!
# The successive sums (5.125), (5.126) and (5.127)

The paper: Lemma 5.40.
These identities apply to any weight on the unscaled data, including the integrated
majorant and the pointwise geometric integrand before the dyadic scales are integrated.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeOne

open Finset

variable {n : ℕ} {R : Type*} [AddCommMonoid R]

open scoped Classical in
/-- Data with the positive and negative bad-charge sets fixed. -/
noncomputable def setBases (q : ℕ) (A B : Finset (Charge n)) : Finset (Base n) :=
  (bases q).filter fun S => badSet (unscaled S) true = A ∧ badSet (unscaled S) false = B

open scoped Classical in
/-- Data with the two partner injections fixed after their bad sets. -/
noncomputable def partnerBases (q : ℕ) (A B : Finset (Charge n))
    (f g : Charge n → Charge n) : Finset (Base n) :=
  (setBases q A B).filter fun S => partner (unscaled S) false = f ∧ partner (unscaled S) true = g

open scoped Classical in
/-- Data with both same-sign partitions and their block counts fixed. -/
noncomputable def partitionBases (q : ℕ) (A B : Finset (Charge n))
    (f g : Charge n → Charge n) (k l : ℕ) (p r : Charge n → Charge n) : Finset (Base n) :=
  (partnerBases q A B f g).filter fun S => blocks S true = k ∧ blocks S false = l ∧
    partition (unscaled S) true = p ∧ partition (unscaled S) false = r

/-- (5.125): split first by both bad-charge counts and then by their sets. -/
theorem sum_bases_by_sets (q : ℕ) (F : Base n → R) :
    ∑ S ∈ bases q, F S =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
        ∑ A ∈ (charges true).powersetCard a, ∑ B ∈ (charges false).powersetCard b,
          ∑ S ∈ setBases q A B, F S := by
  classical
  have hA : ∀ S ∈ bases (n := n) q, badSet (unscaled S) true ∈ (charges true).powerset :=
    fun S _ => mem_powerset.2 (badSet_subset _ _)
  rw [← sum_fiberwise_of_maps_to hA]
  have he : ∀ A, ∑ S ∈ ((bases q).filter fun S => badSet (unscaled S) true = A), F S =
      ∑ B ∈ (charges false).powerset, ∑ S ∈ setBases q A B, F S := by
    intro A
    have hB : ∀ S ∈ ((bases (n := n) q).filter fun S => badSet (unscaled S) true = A),
        badSet (unscaled S) false ∈ (charges false).powerset :=
      fun S _ => mem_powerset.2 (badSet_subset _ _)
    rw [← sum_fiberwise_of_maps_to hB]
    apply sum_congr rfl
    intro B _
    apply sum_congr
    · ext S
      simp only [setBases, mem_filter, and_assoc]
    · intro _ _
      rfl
  simp_rw [he]
  rw [sum_badSets_by_counts true]
  simp_rw [sum_badSets_by_counts false]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]

/-- (5.126): assign the injective maps from good charges to opposite bad charges. -/
theorem sum_setBases_by_partners (q : ℕ) (A B : Finset (Charge n)) (F : Base n → R) :
    ∑ S ∈ setBases q A B, F S =
      ∑ f ∈ injections (charges false \ B) A, ∑ g ∈ injections (charges true \ A) B,
        ∑ S ∈ partnerBases q A B f g, F S := by
  classical
  have hmap : ∀ S ∈ setBases q A B,
      (partner (unscaled S) false, partner (unscaled S) true) ∈
        injections (charges false \ B) A ×ˢ injections (charges true \ A) B := by
    intro S hS
    obtain ⟨hS, hA, hB⟩ := mem_filter.1 hS
    obtain ⟨hV, hC⟩ := (mem_filter.1 hS).2
    refine mem_product.2 ⟨?_, ?_⟩
    · simpa only [hA, hB, Bool.not_false] using partner_mem_injections hV hC false
    · simpa only [hA, hB, Bool.not_true] using partner_mem_injections hV hC true
  rw [← sum_fiberwise_of_maps_to hmap, sum_product]
  apply sum_congr rfl
  intro f _
  apply sum_congr rfl
  intro g _
  apply sum_congr
  · ext S
    simp only [partnerBases, mem_filter, Prod.mk.injEq]
  · intro _ _
    rfl

/-- (5.127): split by positive and negative block counts and same-sign partitions. -/
theorem sum_partnerBases_by_partitions (q : ℕ) (A B : Finset (Charge n))
    (f g : Charge n → Charge n) (F : Base n → R) :
    ∑ S ∈ partnerBases q A B f g, F S =
      ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
        ∑ p ∈ partitions q A k, ∑ r ∈ partitions q B l,
          ∑ S ∈ partitionBases q A B f g k l p r, F S := by
  classical
  have hmap : ∀ S ∈ partnerBases q A B f g, (blocks S true, blocks S false) ∈
      range (n + 1) ×ˢ range (n + 1) := by
    intro S hS
    have hS := (mem_filter.1 (mem_filter.1 hS).1).1
    exact mem_product.2 ⟨mem_range.2 (Nat.lt_succ_of_le (blocks_le hS true)),
      mem_range.2 (Nat.lt_succ_of_le (blocks_le hS false))⟩
  rw [← sum_fiberwise_of_maps_to hmap, sum_product]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro l _
  let T := (partnerBases q A B f g).filter fun S => (blocks S true, blocks S false) = (k,l)
  have hp : ∀ S ∈ T, (partition (unscaled S) true, partition (unscaled S) false) ∈
      partitions q A k ×ˢ partitions q B l := by
    intro S hS
    obtain ⟨hS, he⟩ := mem_filter.1 hS
    obtain ⟨hk, hl⟩ := Prod.mk.inj he
    obtain ⟨hS, -⟩ := mem_filter.1 hS
    obtain ⟨hS, hA, hB⟩ := mem_filter.1 hS
    obtain ⟨hV, hC⟩ := (mem_filter.1 hS).2
    refine mem_product.2 ⟨?_, ?_⟩
    · exact mem_filter.2 ⟨mem_univ _, hA ▸ partition_isPartition hV hC true, by
        simpa only [blocks, hA] using hk⟩
    · exact mem_filter.2 ⟨mem_univ _, hB ▸ partition_isPartition hV hC false, by
        simpa only [blocks, hB] using hl⟩
  rw [← sum_fiberwise_of_maps_to hp, sum_product]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  apply sum_congr
  · ext S
    simp only [T, partitionBases, mem_filter, Prod.mk.injEq]
    tauto
  · intro _ _
    rfl

open scoped Classical in
/-- The successive sums of the paper, in their written order. -/
noncomputable def successiveSum (q : ℕ) (F : Base n → R) : R :=
  ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
    ∑ A ∈ (charges true).powersetCard a, ∑ B ∈ (charges false).powersetCard b,
      ∑ f ∈ injections (charges false \ B) A, ∑ g ∈ injections (charges true \ A) B,
        ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
          ∑ p ∈ partitions q A k, ∑ r ∈ partitions q B l,
            ∑ S ∈ partitionBases q A B f g k l p r, F S

/-- All three successive splittings preserve an arbitrary weight exactly. -/
theorem sum_bases_eq_successive (q : ℕ) (F : Base n → R) :
    ∑ S ∈ bases q, F S = successiveSum q F := by
  classical
  rw [sum_bases_by_sets]
  simp_rw [sum_setBases_by_partners, sum_partnerBases_by_partitions]
  rfl

end MultipoleBKT.BadPointTypes.RouteTypeOne

end
