/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeOne.Enumeration

/-!
# Counting the successive choices

The paper: Lemma 5.40,
(5.125), (5.126), (5.127), and Step 6. The two block counts in the final double sum count positive
and negative blocks, including singleton blocks.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeOne

open Finset

variable {n : ℕ}

/-- Data before assigning dyadic scales. -/
abbrev Base (n : ℕ) := (Charge n → Fin 4) × (Charge n → Charge n)

/-- Forgetting all scales retains exactly the combinatorial choices. -/
def unscaled (B : Base n) : TOData n := (B.1, B.2, fun _ => 0)

open scoped Classical in
/-- Admissible combinatorial data for the successive enumeration. -/
noncomputable def bases (q : ℕ) : Finset (Base n) :=
  univ.filter fun B => TypeOneValid q (unscaled B) ∧ Compatible (unscaled B)

/-- The positive or negative number of same-sign blocks. -/
noncomputable def blocks (B : Base n) (s : Bool) : ℕ :=
  (roots (badSet (unscaled B) s) (partition (unscaled B) s)).card

open scoped Classical in
/-- Fixed bad sets and fixed positive and negative block counts. -/
noncomputable def baseFiber (q : ℕ) (A B : Finset (Charge n)) (k l : ℕ) : Finset (Base n) :=
  (bases q).filter fun S => badSet (unscaled S) true = A ∧ badSet (unscaled S) false = B ∧
    blocks S true = k ∧ blocks S false = l

/-- The successive choices determine the parent of each charge. -/
theorem parents_unique {D E : TOData n}
    (hA : badSet D true = badSet E true) (hB : badSet D false = badSet E false)
    (hf : partner D true = partner E true) (hg : partner D false = partner E false)
    (hp : partition D true = partition E true) (hr : partition D false = partition E false) :
    D.2.1 = E.2.1 := by
  classical
  funext v
  have hsets : ∀ s, badSet D s = badSet E s := by
    intro s
    cases s
    · exact hB
    · exact hA
  have hpartners : ∀ s, partner D s = partner E s := by
    intro s
    cases s
    · exact hg
    · exact hf
  have hparts : ∀ s, partition D s = partition E s := by
    intro s
    cases s
    · exact hr
    · exact hp
  have hgood : D.1 v = 3 ↔ E.1 v = 3 := by
    have he := congrArg (fun A : Finset (Charge n) => v ∈ A) (hsets (positive v))
    have hn : D.1 v ≠ 3 ↔ E.1 v ≠ 3 := by simpa [badSet] using he.to_iff
    exact not_iff_not.1 hn
  by_cases hv : D.1 v = 3
  · have he := congrFun (hpartners (positive v)) v
    simpa [partner, hv, (hgood.1 hv)] using he
  · have hev : E.1 v ≠ 3 := fun h => hv (hgood.2 h)
    have he := congrFun (hparts (positive v)) v
    simpa [partition, badSet, hv, hev] using he

/-- Bad sets, partner injections and same-sign partitions determine the unscaled data. -/
theorem base_key_injective {q : ℕ} (hq : 1 ≤ q) {S T : Base n}
    (hS : S ∈ bases q) (hT : T ∈ bases q)
    (hkey : ((badSet (unscaled S) true, badSet (unscaled S) false),
        ((partner (unscaled S) false, partner (unscaled S) true),
          (partition (unscaled S) true, partition (unscaled S) false))) =
      ((badSet (unscaled T) true, badSet (unscaled T) false),
        ((partner (unscaled T) false, partner (unscaled T) true),
          (partition (unscaled T) true, partition (unscaled T) false)))) : S = T := by
  classical
  obtain ⟨hA, hB, hf, hg, hp, hr⟩ := by
    simpa only [Prod.mk.injEq, and_assoc] using hkey
  have hpar := parents_unique hA hB hg hf hp hr
  have hgood : ∀ v, (unscaled S).1 v = 3 ↔ (unscaled T).1 v = 3 := by
    intro v
    have hsets : ∀ s, badSet (unscaled S) s = badSet (unscaled T) s := by
      intro s
      cases s
      · exact hB
      · exact hA
    have he := congrArg (fun A : Finset (Charge n) => v ∈ A) (hsets (positive v))
    have hn : (unscaled S).1 v ≠ 3 ↔ (unscaled T).1 v ≠ 3 := by
      simpa [badSet] using he.to_iff
    exact not_iff_not.1 hn
  have hkind := kinds_unique hq (mem_filter.1 hS).2.1 (mem_filter.1 hT).2.1 hgood hpar
  exact Prod.ext hkind hpar

/-- Counting fixed sets and fixed block counts by the successive choices of the paper. -/
theorem card_baseFiber_le {q : ℕ} (hq : 1 ≤ q) (A B : Finset (Charge n)) (k l : ℕ) :
    (baseFiber q A B k l).card ≤
      (injections (charges false \ B) A).card * (injections (charges true \ A) B).card *
        (partitions q A k).card * (partitions q B l).card := by
  classical
  let key : Base n → ((Charge n → Charge n) × (Charge n → Charge n)) ×
      ((Charge n → Charge n) × (Charge n → Charge n)) := fun S =>
    ((partner (unscaled S) false, partner (unscaled S) true),
      (partition (unscaled S) true, partition (unscaled S) false))
  let target := ((injections (charges false \ B) A) ×ˢ (injections (charges true \ A) B)) ×ˢ
    ((partitions q A k) ×ˢ (partitions q B l))
  have hmap : Set.MapsTo key (baseFiber q A B k l) target := by
    intro S hS
    obtain ⟨hS, hA, hB, hk, hl⟩ := mem_filter.1 hS
    obtain ⟨hV, hC⟩ := (mem_filter.1 hS).2
    refine mem_product.2 ⟨mem_product.2 ⟨?_, ?_⟩, mem_product.2 ⟨?_, ?_⟩⟩
    · simpa only [hA, hB, Bool.not_false] using partner_mem_injections hV hC false
    · simpa only [hA, hB, Bool.not_true] using partner_mem_injections hV hC true
    · exact mem_filter.2 ⟨mem_univ _, hA ▸ partition_isPartition hV hC true, by
        simpa only [blocks, hA] using hk⟩
    · exact mem_filter.2 ⟨mem_univ _, hB ▸ partition_isPartition hV hC false, by
        simpa only [blocks, hB] using hl⟩
  have hinj : Set.InjOn key (baseFiber q A B k l) := by
    intro S hS T hT he
    obtain ⟨hS, hSA, hSB, -⟩ := mem_filter.1 hS
    obtain ⟨hT, hTA, hTB, -⟩ := mem_filter.1 hT
    apply base_key_injective hq hS hT
    exact Prod.ext (Prod.ext (hSA.trans hTA.symm) (hSB.trans hTB.symm)) he
  have hc := card_le_card_of_injOn key hmap hinj
  simpa only [target, card_product, mul_assoc] using hc

/-- After counting injections and partitions, the exponent of `n` is `2n`:
`(n-|A|)+(n-|B|)+|A|+|B|=2n`. -/
theorem card_baseFiber_mul_factorials_le {q : ℕ} (hq : 1 ≤ q)
    {A B : Finset (Charge n)} (hA : A ⊆ charges true) (hB : B ⊆ charges false) (k l : ℕ) :
    (baseFiber q A B k l).card * k.factorial * l.factorial ≤ n ^ (2 * n) := by
  have hAn : A.card ≤ n := (card_le_card hA).trans_eq (card_charges true)
  have hBn : B.card ≤ n := (card_le_card hB).trans_eq (card_charges false)
  have hf := card_injections_le (charges false \ B) A
  have hg := card_injections_le (charges true \ A) B
  rw [card_sdiff_of_subset hB, card_charges] at hf
  rw [card_sdiff_of_subset hA, card_charges] at hg
  calc (baseFiber q A B k l).card * k.factorial * l.factorial
      ≤ ((injections (charges false \ B) A).card * (injections (charges true \ A) B).card *
        (partitions q A k).card * (partitions q B l).card) * k.factorial * l.factorial := by
          gcongr
          exact card_baseFiber_le hq A B k l
    _ = ((injections (charges false \ B) A).card * (injections (charges true \ A) B).card) *
        ((partitions q A k).card * k.factorial) * ((partitions q B l).card * l.factorial) := by ring
    _ ≤ (A.card ^ (n - B.card) * B.card ^ (n - A.card)) * A.card ^ A.card * B.card ^ B.card :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hf hg)
        (card_partitions_mul_factorial_le q A k)) (card_partitions_mul_factorial_le q B l)
    _ ≤ (n ^ (n - B.card) * n ^ (n - A.card)) * n ^ A.card * n ^ B.card := by
      gcongr
    _ = n ^ (2 * n) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega

open scoped Classical in
/-- Fixed positive and negative block counts, before choosing the bad sets. -/
noncomputable def blockFiber (q k l : ℕ) : Finset (Base n) :=
  (bases q).filter fun S => blocks S true = k ∧ blocks S false = l

/-- The finite sums over the bad positive and negative sets are taken after their counts.
This is the combinatorial form of (5.125) used by the bound. -/
theorem card_blockFiber_eq_successive (q k l : ℕ) :
    (blockFiber (n := n) q k l).card =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
        ∑ A ∈ (charges (n := n) true).powersetCard a, ∑ B ∈ (charges (n := n) false).powersetCard b,
          (baseFiber q A B k l).card := by
  classical
  have hA : ∀ S ∈ blockFiber (n := n) q k l,
      badSet (unscaled S) true ∈ (charges true).powerset :=
    fun S _ => mem_powerset.2 (badSet_subset _ _)
  rw [card_eq_sum_card_fiberwise hA]
  have he : ∀ A, ((blockFiber (n := n) q k l).filter
      (fun S => badSet (unscaled S) true = A)).card =
      ∑ B ∈ (charges false).powerset, (baseFiber q A B k l).card := by
    intro A
    have hB : ∀ S ∈ ((blockFiber (n := n) q k l).filter
        (fun S => badSet (unscaled S) true = A)),
        badSet (unscaled S) false ∈ (charges false).powerset :=
      fun S _ => mem_powerset.2 (badSet_subset _ _)
    rw [card_eq_sum_card_fiberwise hB]
    apply sum_congr rfl
    intro B _
    congr 1
    ext S
    simp only [baseFiber, blockFiber, mem_filter]
    tauto
  simp_rw [he]
  rw [sum_badSets_by_counts true]
  simp_rw [sum_badSets_by_counts false]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]

/-- The bad-set choices cost at most `4^n`. The factorials come from the positive and
negative partition counts, after the partner maps have been counted. -/
theorem card_blockFiber_mul_factorials_le {q : ℕ} (hq : 1 ≤ q) (k l : ℕ) :
    (blockFiber (n := n) q k l).card * k.factorial * l.factorial ≤ 4 ^ n * n ^ (2 * n) := by
  classical
  rw [card_blockFiber_eq_successive]
  simp_rw [sum_mul]
  calc ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
        ∑ A ∈ (charges (n := n) true).powersetCard a, ∑ B ∈ (charges (n := n) false).powersetCard b,
          (baseFiber q A B k l).card * k.factorial * l.factorial
      ≤ ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
        ∑ _A ∈ (charges (n := n) true).powersetCard a,
          ∑ _B ∈ (charges (n := n) false).powersetCard b, n ^ (2 * n) := by
        apply sum_le_sum
        intro a _
        apply sum_le_sum
        intro b _
        apply sum_le_sum
        intro A hA
        apply sum_le_sum
        intro B hB
        exact card_baseFiber_mul_factorials_le hq (mem_powersetCard.1 hA).1
          (mem_powersetCard.1 hB).1 k l
    _ = ∑ _A ∈ (charges (n := n) true).powerset,
        ∑ _B ∈ (charges (n := n) false).powerset, n ^ (2 * n) := by
      rw [sum_badSets_by_counts true]
      simp_rw [sum_badSets_by_counts false]
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
    _ = 4 ^ n * n ^ (2 * n) := by
      simp only [sum_const, nsmul_eq_mul, card_powerset, card_charges, Nat.cast_id]
      rw [← mul_assoc, ← mul_pow]
      norm_num

end MultipoleBKT.BadPointTypes.RouteTypeOne

end
