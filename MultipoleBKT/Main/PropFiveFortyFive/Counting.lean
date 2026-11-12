/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Mobius
public import MultipoleBKT.Frozen.BoundedBlockPartitions
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proposition 5.45: counting by block profile

Counting facts used in the proof of Proposition 5.45 and in the hypertree calculation (4.155). For a family `σ` of finite sets, `blockCount p σ i` is the number of
members of `σ` of cardinality `i + 1` (`i < p`).

* `card_boundedBlockPartitions_mul` (eq. (4.27)): the number of partitions of
  `[N]` with `m_k` blocks of size `k` (`1 ≤ k ≤ p`) is `N! / ∏ₖ ((k!)^{m_k} m_k!)`, stated without
  division as `#{π} · ∏ₖ (k!)^{m_k} m_k! = N!`. The proof groups the partitions by the block of a
  fixed point (`MultipoleBKT.SetPartition.sum_partitions_root`) and uses induction on the ground
  set.
* `card_powerset_filter_blockCount`: a family `A` with `n_k` members of size `k`
  has `∏ₖ C(n_k, m_k)` subfamilies with `m_k` members of size `k`.
* `abs_choose_div_pow_sub_le`: `|C(n, k)/N^k - (n/N)^k/k!| ≤ k²/N` for `n ≤ N`.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace PropFiveFortyFive

section BlockCount

variable {α : Type*} [DecidableEq α]

/-- The block counts `(#{S ∈ σ : |S| = i + 1})_{i < p}` of a family of finite sets. -/
def blockCount (p : ℕ) (σ : Finset (Finset α)) : Fin p → ℕ :=
  fun i => (σ.filter fun S => S.card = (i : ℕ) + 1).card

/-- The weight `∏_{i < p} ((i + 1)!)^{m_i} m_i!` of a block profile `m`. -/
def profileWeight {p : ℕ} (m : Fin p → ℕ) : ℕ :=
  ∏ i : Fin p, ((i : ℕ) + 1).factorial ^ m i * (m i).factorial

theorem profileWeight_pos {p : ℕ} (m : Fin p → ℕ) : 0 < profileWeight m :=
  prod_pos fun _ _ => mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)

/-- A family whose members have sizes in `[1, p]` is the disjoint union of its size classes. -/
theorem eq_biUnion_filter_card {p : ℕ} {σ : Finset (Finset α)}
    (hσ : ∀ S ∈ σ, 1 ≤ S.card ∧ S.card ≤ p) :
    σ = univ.biUnion fun i : Fin p => σ.filter fun S => S.card = (i : ℕ) + 1 := by
  ext S
  simp only [mem_biUnion, mem_univ, true_and, mem_filter]
  constructor
  · intro hS
    obtain ⟨h1, h2⟩ := hσ S hS
    exact ⟨⟨S.card - 1, by omega⟩, hS, by simp only; omega⟩
  · rintro ⟨_, hS, _⟩
    exact hS

omit [DecidableEq α] in
theorem pairwiseDisjoint_filter_card (σ : Finset (Finset α)) (p : ℕ) :
    ((univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint
      fun i : Fin p => σ.filter fun S => S.card = (i : ℕ) + 1 := by
  intro i _ j _ hij
  rw [Function.onFun, disjoint_left]
  intro S hSi hSj
  rw [mem_filter] at hSi hSj
  exact hij (Fin.ext (by omega))

/-- `∑_{S ∈ σ} f(|S|) = ∑_{i < p} #_{i+1} σ · f(i + 1)`. -/
theorem sum_card_eq_sum_blockCount {M : Type*} [AddCommMonoid M] {p : ℕ}
    {σ : Finset (Finset α)} (hσ : ∀ S ∈ σ, 1 ≤ S.card ∧ S.card ≤ p) (f : ℕ → M) :
    ∑ S ∈ σ, f S.card = ∑ i : Fin p, blockCount p σ i • f ((i : ℕ) + 1) := by
  conv_lhs => rw [eq_biUnion_filter_card hσ]
  rw [sum_biUnion (pairwiseDisjoint_filter_card σ p)]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_congr rfl fun S hS => by rw [(mem_filter.1 hS).2], sum_const]
  rfl

/-- `∏_{S ∈ σ} f(|S|) = ∏_{i < p} f(i + 1)^{#_{i+1} σ}`. -/
theorem prod_card_eq_prod_blockCount {M : Type*} [CommMonoid M] {p : ℕ}
    {σ : Finset (Finset α)} (hσ : ∀ S ∈ σ, 1 ≤ S.card ∧ S.card ≤ p) (f : ℕ → M) :
    ∏ S ∈ σ, f S.card = ∏ i : Fin p, f ((i : ℕ) + 1) ^ blockCount p σ i := by
  conv_lhs => rw [eq_biUnion_filter_card hσ]
  rw [prod_biUnion (pairwiseDisjoint_filter_card σ p)]
  refine prod_congr rfl fun i _ => ?_
  rw [prod_congr rfl fun S hS => by rw [(mem_filter.1 hS).2], prod_const]
  rfl

/-- `∑_{i < p} (i + 1) #_{i+1} σ = ∑_{S ∈ σ} |S|`. -/
theorem sum_mul_blockCount {p : ℕ} {σ : Finset (Finset α)}
    (hσ : ∀ S ∈ σ, 1 ≤ S.card ∧ S.card ≤ p) :
    ∑ i : Fin p, ((i : ℕ) + 1) * blockCount p σ i = ∑ S ∈ σ, S.card := by
  rw [sum_card_eq_sum_blockCount hσ (fun k => k)]
  simp only [smul_eq_mul, mul_comm]

/-- `∑_{i < p} #_{i+1} σ = |σ|`. -/
theorem sum_blockCount {p : ℕ} {σ : Finset (Finset α)}
    (hσ : ∀ S ∈ σ, 1 ≤ S.card ∧ S.card ≤ p) : ∑ i : Fin p, blockCount p σ i = σ.card := by
  have h := sum_card_eq_sum_blockCount hσ (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one] at h
  rw [← h, card_eq_sum_ones]

omit [DecidableEq α] in
theorem blockCount_le_card (p : ℕ) (σ : Finset (Finset α)) (i : Fin p) :
    blockCount p σ i ≤ σ.card :=
  card_filter_le _ _

/-- The size-class indicator `e_d(i) = 𝟙_{d = i + 1}`. -/
def sizeIndicator (p d : ℕ) : Fin p → ℕ := fun i => if d = (i : ℕ) + 1 then 1 else 0

theorem blockCount_insert {p : ℕ} {σ : Finset (Finset α)} {D : Finset α} (hD : D ∉ σ) :
    blockCount p (insert D σ) = blockCount p σ + sizeIndicator p D.card := by
  funext i
  simp only [blockCount, Pi.add_apply, sizeIndicator, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem fun h' => hD (mem_filter.1 h').1]
  · rw [add_zero]

end BlockCount

/-! ### The profile weight -/

section ProfileWeight

variable {p : ℕ}

theorem sum_sizeIndicator_mul (d : ℕ) (x : Fin p → ℕ) :
    ∑ i, sizeIndicator p d i * x i = if h : 1 ≤ d ∧ d ≤ p then x ⟨d - 1, by omega⟩ else 0 := by
  split_ifs with h
  · rw [sum_eq_single (⟨d - 1, by omega⟩ : Fin p)]
    · simp only [sizeIndicator]
      rw [ite_eq_left (show d = (d - 1) + 1 by omega), one_mul]
    · intro i _ hi
      simp only [sizeIndicator]
      rw [ite_eq_right, zero_mul]
      intro h'
      exact hi (Fin.ext (show (i : ℕ) = d - 1 by omega))
    · simp
  · refine sum_eq_zero fun i _ => ?_
    simp only [sizeIndicator]
    rw [ite_eq_right, zero_mul]
    intro h'
    exact h ⟨by omega, by have := i.2; omega⟩

/-- Removing one block of size `d` from a profile. -/
theorem profileWeight_eq_mul {d : ℕ} (hd1 : 1 ≤ d) (hdp : d ≤ p) {m : Fin p → ℕ}
    (hm : sizeIndicator p d ≤ m) :
    profileWeight m =
      profileWeight (m - sizeIndicator p d) *
        ∑ i, sizeIndicator p d i * (((i : ℕ) + 1).factorial * m i) := by
  set k : Fin p := ⟨d - 1, by omega⟩
  rw [sum_sizeIndicator_mul, dite_eq_left ⟨hd1, hdp⟩]
  have hk : ∀ i, sizeIndicator p d i = if i = k then 1 else 0 := fun i => by
    simp only [sizeIndicator, k, Fin.ext_iff]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩
  have hmk : 1 ≤ m k := by
    have := hm k
    rw [hk, ite_eq_left rfl] at this
    exact this
  unfold profileWeight
  rw [← mul_prod_erase _ _ (mem_univ k), ← mul_prod_erase _ _ (mem_univ k)]
  have hrest : ∏ x ∈ univ.erase k, ((x : ℕ) + 1).factorial ^ m x * (m x).factorial =
      ∏ x ∈ univ.erase k, ((x : ℕ) + 1).factorial ^ (m - sizeIndicator p d) x *
        ((m - sizeIndicator p d) x).factorial := by
    refine prod_congr rfl fun i hi => ?_
    rw [Pi.sub_apply, hk, ite_eq_right (ne_of_mem_erase hi), Nat.sub_zero]
  rw [hrest, Pi.sub_apply, hk, ite_eq_left rfl]
  obtain ⟨j, hj⟩ : ∃ j, m k = j + 1 := ⟨m k - 1, by omega⟩
  rw [hj, Nat.add_sub_cancel, pow_succ, Nat.factorial_succ j]
  ring

end ProfileWeight

/-! ### Counting partitions by profile (eq. (4.27)) -/

section Partitions

variable {α : Type*} [DecidableEq α]

/-- `#{D ⊆ U : a ∈ D, |D| = k + 1} = C(|U| - 1, k)`. -/
theorem card_powerset_filter_mem_card {U : Finset α} {a : α} (ha : a ∈ U) (k : ℕ) :
    ((U.powerset.filter (a ∈ ·)).filter fun D => D.card = k + 1).card =
      (U.card - 1).choose k := by
  rw [← card_erase_of_mem ha, ← card_powersetCard]
  refine card_nbij' (fun D => D.erase a) (fun E => insert a E) ?_ ?_ ?_ ?_
  · intro D hD
    rw [mem_coe, mem_filter, mem_filter, mem_powerset] at hD
    rw [mem_coe, mem_powersetCard]
    refine ⟨erase_subset_erase a hD.1.1, ?_⟩
    rw [card_erase_of_mem hD.1.2, hD.2, Nat.add_sub_cancel]
  · intro E hE
    rw [mem_coe, mem_powersetCard] at hE
    rw [mem_coe, mem_filter, mem_filter, mem_powerset]
    have haE : a ∉ E := fun h => by simpa using hE.1 h
    refine ⟨⟨insert_subset ha (hE.1.trans (erase_subset a U)), mem_insert_self a E⟩, ?_⟩
    rw [card_insert_of_notMem haE, hE.2]
  · intro D hD
    rw [mem_coe, mem_filter, mem_filter] at hD
    exact insert_erase hD.1.2
  · intro E hE
    rw [mem_coe, mem_powersetCard] at hE
    have haE : a ∉ E := fun h => by simpa using hE.1 h
    exact erase_insert haE

open SetPartition in
/-- The number of partitions of `U` into blocks of sizes at most `p`, with `m_i` blocks of size
`i + 1`, times `∏ᵢ ((i+1)!)^{m_i} m_i!`, is `|U|!` (eq. (4.27)). -/
theorem card_partitions_filter_mul (p : ℕ) :
    ∀ (U : Finset α) (m : Fin p → ℕ), ∑ i : Fin p, ((i : ℕ) + 1) * m i = U.card →
      ((partitions U).filter fun σ => (∀ S ∈ σ, S.card ≤ p) ∧ blockCount p σ = m).card *
        profileWeight m = U.card.factorial := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
  intro m hm
  rcases U.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · have hm0 : m = 0 := by
      funext i
      have h := (sum_eq_zero_iff.1 (by rw [hm, card_empty])) i (mem_univ i)
      simpa using h
    subst hm0
    have hfilt : ((partitions (∅ : Finset α)).filter fun σ =>
        (∀ S ∈ σ, S.card ≤ p) ∧ blockCount p σ = 0) = {∅} := by
      rw [partitions_empty]
      ext σ
      simp only [mem_filter, mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro rfl
        refine ⟨rfl, by simp, ?_⟩
        funext i
        simp [blockCount]
    rw [hfilt, card_singleton, one_mul, card_empty]
    simp [profileWeight]
  · set N := U.card with hN
    have hN1 : 1 ≤ N := card_pos.2 ⟨a, ha⟩
    -- the root recursion
    have hroot : ((partitions U).filter fun σ =>
          (∀ S ∈ σ, S.card ≤ p) ∧ blockCount p σ = m).card =
        ∑ D ∈ U.powerset.filter (a ∈ ·), if D.card ≤ p ∧ sizeIndicator p D.card ≤ m then
          ((partitions (U \ D)).filter fun σ =>
            (∀ S ∈ σ, S.card ≤ p) ∧ blockCount p σ = m - sizeIndicator p D.card).card
        else 0 := by
      rw [card_eq_sum_ones, sum_filter, sum_partitions_root ha]
      refine sum_congr rfl fun D hD => ?_
      have hDne : D.Nonempty := ⟨a, (mem_filter.1 hD).2⟩
      split_ifs with hc
      · rw [card_eq_sum_ones, sum_filter]
        refine sum_congr rfl fun σ hσ => ?_
        have hDσ := notMem_of_mem_partitions_sdiff hDne hσ
        rw [blockCount_insert hDσ]
        have hiff : ((∀ S ∈ insert D σ, S.card ≤ p) ∧
            blockCount p σ + sizeIndicator p D.card = m) ↔
            ((∀ S ∈ σ, S.card ≤ p) ∧ blockCount p σ = m - sizeIndicator p D.card) := by
          rw [forall_mem_insert]
          constructor
          · rintro ⟨⟨-, h1⟩, h2⟩
            refine ⟨h1, ?_⟩
            funext i
            rw [← h2, Pi.sub_apply, Pi.add_apply, Nat.add_sub_cancel]
          · rintro ⟨h1, h2⟩
            refine ⟨⟨hc.1, h1⟩, ?_⟩
            funext i
            rw [Pi.add_apply, h2, Pi.sub_apply, Nat.sub_add_cancel (hc.2 i)]
        simp only [hiff]
      · refine sum_eq_zero fun σ hσ => ?_
        have hDσ := notMem_of_mem_partitions_sdiff hDne hσ
        rw [blockCount_insert hDσ, ite_eq_right]
        rintro ⟨h1, h2⟩
        refine hc ⟨h1 D (mem_insert_self D σ), ?_⟩
        rw [← h2]
        exact le_add_self
    rw [hroot, sum_mul]
    -- each term, by the induction hypothesis
    have hterm : ∀ D ∈ U.powerset.filter (a ∈ ·),
        (if D.card ≤ p ∧ sizeIndicator p D.card ≤ m then
          ((partitions (U \ D)).filter fun σ =>
            (∀ S ∈ σ, S.card ≤ p) ∧ blockCount p σ = m - sizeIndicator p D.card).card
        else 0) * profileWeight m =
        (N - D.card).factorial *
          ∑ i, sizeIndicator p D.card i * (((i : ℕ) + 1).factorial * m i) := by
      intro D hD
      rw [mem_filter, mem_powerset] at hD
      have hD1 : 1 ≤ D.card := card_pos.2 ⟨a, hD.2⟩
      split_ifs with hc
      · rw [profileWeight_eq_mul hD1 hc.1 hc.2, ← mul_assoc]
        congr 1
        have hsub : U \ D ⊂ U := sdiff_ssubset hD.1 ⟨a, hD.2⟩
        rw [ih (U \ D) hsub, card_sdiff_of_subset hD.1]
        -- the size equation for `m - e`
        have he : ∑ i : Fin p, ((i : ℕ) + 1) * sizeIndicator p D.card i = D.card := by
          rw [sum_congr rfl fun i _ => mul_comm _ _, sum_sizeIndicator_mul,
            dite_eq_left ⟨hD1, hc.1⟩]
          simp only
          omega
        have hle : ∀ i : Fin p, ((i : ℕ) + 1) * sizeIndicator p D.card i ≤ ((i : ℕ) + 1) * m i :=
          fun i => Nat.mul_le_mul_left _ (hc.2 i)
        have : ∑ i : Fin p, ((i : ℕ) + 1) * (m - sizeIndicator p D.card) i =
            ∑ i : Fin p, ((i : ℕ) + 1) * m i -
              ∑ i : Fin p, ((i : ℕ) + 1) * sizeIndicator p D.card i := by
          rw [eq_tsub_iff_add_eq_of_le (sum_le_sum fun i _ => hle i), ← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          rw [Pi.sub_apply, Nat.mul_sub, Nat.sub_add_cancel (hle i)]
        rw [this, he, hm, card_sdiff_of_subset hD.1]
      · rw [zero_mul]
        symm
        refine mul_eq_zero_of_right _ ?_
        rw [sum_sizeIndicator_mul (x := fun i => ((i : ℕ) + 1).factorial * m i)]
        split_ifs with h
        · simp only
          have hm0 : m ⟨D.card - 1, by omega⟩ = 0 := by
            by_contra hne
            refine hc ⟨h.2, fun i => ?_⟩
            simp only [sizeIndicator]
            split_ifs with hi
            · have : i = ⟨D.card - 1, by omega⟩ := Fin.ext (by simp only; omega)
              rw [this]
              omega
            · exact Nat.zero_le _
          rw [hm0, mul_zero]
        · rfl
    rw [sum_congr rfl hterm]
    -- exchange the sums and count the blocks of each size containing `a`
    simp_rw [mul_sum]
    rw [sum_comm]
    have hcount : ∀ i : Fin p, ∑ D ∈ U.powerset.filter (a ∈ ·),
        (N - D.card).factorial * (sizeIndicator p D.card i * (((i : ℕ) + 1).factorial * m i)) =
        (N - 1).factorial * (((i : ℕ) + 1) * m i) := by
      intro i
      rw [← sum_filter_add_sum_filter_not _ (fun D => D.card = (i : ℕ) + 1)]
      have h0 : ∑ D ∈ (U.powerset.filter (a ∈ ·)).filter (fun D => ¬ D.card = (i : ℕ) + 1),
          (N - D.card).factorial * (sizeIndicator p D.card i * (((i : ℕ) + 1).factorial * m i)) =
          0 := by
        refine sum_eq_zero fun D hD => ?_
        simp only [sizeIndicator, ite_eq_right (mem_filter.1 hD).2, zero_mul, mul_zero]
      rw [h0, add_zero]
      rw [sum_congr rfl fun D hD => (show (N - D.card).factorial *
          (sizeIndicator p D.card i * (((i : ℕ) + 1).factorial * m i)) =
          (N - ((i : ℕ) + 1)).factorial * (((i : ℕ) + 1).factorial * m i) by
        rw [(mem_filter.1 hD).2]
        simp [sizeIndicator])]
      rw [sum_const, card_powerset_filter_mem_card ha, smul_eq_mul]
      by_cases hmi : m i = 0
      · rw [hmi]
        simp
      · have hiN : (i : ℕ) + 1 ≤ N := by
          rw [← hm]
          calc (i : ℕ) + 1 ≤ ((i : ℕ) + 1) * m i := Nat.le_mul_of_pos_right _ (by omega)
            _ ≤ _ := single_le_sum (f := fun j : Fin p => ((j : ℕ) + 1) * m j)
                (fun _ _ => Nat.zero_le _) (mem_univ i)
        have hc := Nat.choose_mul_factorial_mul_factorial (n := N - 1) (k := (i : ℕ))
          (by omega)
        rw [show N - ((i : ℕ) + 1) = N - 1 - (i : ℕ) by omega, Nat.factorial_succ]
        rw [← hc]
        ring
    rw [sum_congr rfl fun i _ => hcount i, ← mul_sum, hm]
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hM, Nat.add_sub_cancel, Nat.factorial_succ]
    ring

open SetPartition in
theorem boundedBlockPartitions_eq (N p : ℕ) :
    boundedBlockPartitions N p =
      (partitions (Finset.range N)).filter fun σ => ∀ S ∈ σ, S.card ≤ p := by
  ext σ
  simp only [boundedBlockPartitions, mem_filter, mem_partitions]
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    rw [mem_powerset]
    intro S hS
    rw [mem_powerset, ← h2]
    exact SetPartition.subset_biUnion_of_mem hS

/-- **(4.27)**: `#{π ∈ 𝚷_p([N]) : π has m_i blocks of size i + 1} · ∏ᵢ ((i+1)!)^{m_i} m_i!
= N!` when `∑ᵢ (i + 1) m_i = N`. -/
theorem card_boundedBlockPartitions_mul {N p : ℕ} {m : Fin p → ℕ}
    (hm : ∑ i : Fin p, ((i : ℕ) + 1) * m i = N) :
    ((boundedBlockPartitions N p).filter fun σ => blockCount p σ = m).card * profileWeight m =
      N.factorial := by
  have h := card_partitions_filter_mul p (Finset.range N) m (by rw [card_range, hm])
  rw [card_range] at h
  rw [← h, boundedBlockPartitions_eq, filter_filter]

/-- The blocks of a partition in `𝚷_p([N])` have sizes in `[1, p]`. -/
theorem card_mem_Icc_of_mem_boundedBlockPartitions {N p : ℕ} {σ : Finset (Finset ℕ)}
    (hσ : σ ∈ boundedBlockPartitions N p) : ∀ S ∈ σ, 1 ≤ S.card ∧ S.card ≤ p := by
  simp only [boundedBlockPartitions, mem_filter] at hσ
  intro S hS
  exact ⟨card_pos.2 (hσ.2.1.1 S hS), hσ.2.2.2 S hS⟩

theorem isSubpartition_of_mem_boundedBlockPartitions {N p : ℕ} {σ : Finset (Finset ℕ)}
    (hσ : σ ∈ boundedBlockPartitions N p) : IsSubpartition σ := by
  simp only [boundedBlockPartitions, mem_filter] at hσ
  exact hσ.2.1

theorem biUnion_of_mem_boundedBlockPartitions {N p : ℕ} {σ : Finset (Finset ℕ)}
    (hσ : σ ∈ boundedBlockPartitions N p) : σ.biUnion id = Finset.range N := by
  simp only [boundedBlockPartitions, mem_filter] at hσ
  exact hσ.2.2.1

/-- A partition in `𝚷_p([N])` has profile `m` with `∑ᵢ (i + 1) m_i = N`. -/
theorem sum_mul_blockCount_of_mem_boundedBlockPartitions {N p : ℕ} {σ : Finset (Finset ℕ)}
    (hσ : σ ∈ boundedBlockPartitions N p) :
    ∑ i : Fin p, ((i : ℕ) + 1) * blockCount p σ i = N := by
  rw [sum_mul_blockCount (card_mem_Icc_of_mem_boundedBlockPartitions hσ)]
  have h := biUnion_of_mem_boundedBlockPartitions hσ
  have hc : (σ.biUnion id).card = ∑ S ∈ σ, S.card :=
    card_biUnion fun S hS T hT hST => (isSubpartition_of_mem_boundedBlockPartitions hσ).2 hS hT hST
  rw [← hc, h, card_range]

end Partitions

/-! ### Counting subfamilies by profile -/

section Subfamilies

variable {α : Type*} [DecidableEq α]

theorem filter_card_biUnion {p : ℕ} {Z : Fin p → Finset (Finset α)}
    (hZ : ∀ i, ∀ S ∈ Z i, S.card = (i : ℕ) + 1) (i : Fin p) :
    (univ.biUnion Z).filter (fun S => S.card = (i : ℕ) + 1) = Z i := by
  ext S
  simp only [mem_filter, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨⟨j, hj⟩, hS⟩
    have := hZ j S hj
    have hij : j = i := Fin.ext (by omega)
    rwa [← hij]
  · intro hS
    exact ⟨⟨i, hS⟩, hZ i S hS⟩

/-- A family `A` with `n_i` members of size `i + 1` has `∏ᵢ C(n_i, m_i)` subfamilies with `m_i`
members of size `i + 1`. -/
theorem card_powerset_filter_blockCount {p : ℕ} {A : Finset (Finset α)}
    (hA : ∀ S ∈ A, 1 ≤ S.card ∧ S.card ≤ p) (m : Fin p → ℕ) :
    (A.powerset.filter fun Y => blockCount p Y = m).card =
      ∏ i, (blockCount p A i).choose (m i) := by
  have hrhs : ∏ i, (blockCount p A i).choose (m i) =
      (Fintype.piFinset fun i : Fin p =>
        powersetCard (m i) (A.filter fun S => S.card = (i : ℕ) + 1)).card := by
    rw [Fintype.card_piFinset]
    refine prod_congr rfl fun i _ => ?_
    rw [card_powersetCard]
    rfl
  rw [hrhs]
  refine card_nbij' (fun Y i => Y.filter fun S => S.card = (i : ℕ) + 1)
    (fun Z => univ.biUnion Z) ?_ ?_ ?_ ?_
  · intro Y hY
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq] at hY
    simp only [Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ, mem_coe, mem_powersetCard,
      forall_const]
    intro i
    exact ⟨filter_subset_filter _ hY.1, by rw [← hY.2]; rfl⟩
  · intro Z hZ
    simp only [Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ, mem_coe, mem_powersetCard,
      forall_const] at hZ
    have hZc : ∀ i, ∀ S ∈ Z i, S.card = (i : ℕ) + 1 := fun i S hS => (mem_filter.1 ((hZ i).1 hS)).2
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq]
    refine ⟨biUnion_subset.2 fun i _ => (hZ i).1.trans (filter_subset _ _), ?_⟩
    funext i
    simp only [blockCount]
    rw [filter_card_biUnion hZc, (hZ i).2]
  · intro Y hY
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq] at hY
    exact (eq_biUnion_filter_card fun S hS => hA S (hY.1 hS)).symm
  · intro Z hZ
    simp only [Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ, mem_coe, mem_powersetCard,
      forall_const] at hZ
    have hZc : ∀ i, ∀ S ∈ Z i, S.card = (i : ℕ) + 1 := fun i S hS => (mem_filter.1 ((hZ i).1 hS)).2
    funext i
    exact filter_card_biUnion hZc i

end Subfamilies

/-! ### Binomial coefficients -/

section Binomial

/-- `0 ≤ n^k - n(n-1)⋯(n-k+1) ≤ k² n^{k-1}`. -/
theorem pow_sub_descFactorial_le (n k : ℕ) :
    0 ≤ (n : ℝ) ^ k - (n.descFactorial k : ℝ) ∧
      (n : ℝ) ^ k - (n.descFactorial k : ℝ) ≤ (k : ℝ) ^ 2 * (n : ℝ) ^ (k - 1) := by
  constructor
  · rw [sub_nonneg]
    exact_mod_cast Nat.descFactorial_le_pow n k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.add_sub_cancel]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : 0 ≤ (n : ℝ) ^ k := by positivity
    by_cases hkn : k ≤ n
    · rw [Nat.cast_mul, Nat.cast_sub hkn]
      have hD : (n.descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by
        exact_mod_cast Nat.descFactorial_le_pow n k
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have e : (n : ℝ) ^ (k + 1) - ((n : ℝ) - k) * n.descFactorial k =
          (n : ℝ) * ((n : ℝ) ^ k - n.descFactorial k) + k * n.descFactorial k := by ring
      rw [e]
      have h1 : (n : ℝ) * ((n : ℝ) ^ k - n.descFactorial k) ≤ (k : ℝ) ^ 2 * (n : ℝ) ^ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp
        · calc (n : ℝ) * ((n : ℝ) ^ k - n.descFactorial k)
              ≤ (n : ℝ) * ((k : ℝ) ^ 2 * (n : ℝ) ^ (k - 1)) := mul_le_mul_of_nonneg_left ih hn0
            _ = (k : ℝ) ^ 2 * ((n : ℝ) ^ (k - 1) * n) := by ring
            _ = (k : ℝ) ^ 2 * (n : ℝ) ^ k := by rw [← pow_succ, Nat.sub_add_cancel hk]
      have h2 : (k : ℝ) * n.descFactorial k ≤ k * (n : ℝ) ^ k := mul_le_mul_of_nonneg_left hD hk0
      have h3 : (k : ℝ) ^ 2 * (n : ℝ) ^ k + k * (n : ℝ) ^ k ≤
          ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ k := by
        push_cast
        nlinarith
      linarith
    · push Not at hkn
      have hz : n - k = 0 := by omega
      rw [hz, zero_mul, Nat.cast_zero, sub_zero]
      have hnk : (n : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (by omega : n ≤ k + 1)
      have h1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      calc (n : ℝ) ^ (k + 1) = (n : ℝ) * (n : ℝ) ^ k := by ring
        _ ≤ ((k + 1 : ℕ) : ℝ) * (n : ℝ) ^ k := mul_le_mul_of_nonneg_right hnk hp
        _ ≤ ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ k := by
            rw [sq]
            exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) h1) hp

/-- `0 ≤ (n/N)^k/k! - C(n, k)/N^k ≤ k²/N` for `n ≤ N` and `N ≥ 1`. -/
theorem choose_div_pow_le {n N k : ℕ} (hnN : n ≤ N) (hN : 1 ≤ N) :
    (n.choose k : ℝ) / (N : ℝ) ^ k ≤ ((n : ℝ) / N) ^ k / k.factorial ∧
      ((n : ℝ) / N) ^ k / k.factorial - (n.choose k : ℝ) / (N : ℝ) ^ k ≤ (k : ℝ) ^ 2 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hdesc : (n.choose k : ℝ) = (n.descFactorial k : ℝ) / k.factorial := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  have heq : ((n : ℝ) / N) ^ k / k.factorial - (n.choose k : ℝ) / (N : ℝ) ^ k =
      ((n : ℝ) ^ k - n.descFactorial k) / (k.factorial * (N : ℝ) ^ k) := by
    rw [hdesc, div_pow]
    field_simp
  obtain ⟨h0, h1⟩ := pow_sub_descFactorial_le n k
  constructor
  · have : 0 ≤ ((n : ℝ) / N) ^ k / k.factorial - (n.choose k : ℝ) / (N : ℝ) ^ k := by
      rw [heq]
      positivity
    linarith
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    rw [heq]
    have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
    rw [div_le_div_iff₀ (by positivity) hN0]
    have hnN' : (n : ℝ) ^ (k - 1) ≤ (N : ℝ) ^ (k - 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast hnN) _
    have hf1 : (1 : ℝ) ≤ k.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
    have hNkk : (N : ℝ) ^ (k - 1) * N = (N : ℝ) ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    calc ((n : ℝ) ^ k - n.descFactorial k) * N ≤ (k : ℝ) ^ 2 * (n : ℝ) ^ (k - 1) * N :=
          mul_le_mul_of_nonneg_right h1 hN0.le
      _ ≤ (k : ℝ) ^ 2 * (N : ℝ) ^ (k - 1) * N := by gcongr
      _ = (k : ℝ) ^ 2 * (N : ℝ) ^ k := by rw [mul_assoc, hNkk]
      _ ≤ (k : ℝ) ^ 2 * (k.factorial * (N : ℝ) ^ k) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_mul_of_one_le_left hNk.le hf1

/-- For `0 ≤ aᵢ ≤ bᵢ ≤ 1`: `0 ≤ ∏ bᵢ - ∏ aᵢ ≤ ∑ (bᵢ - aᵢ)`. -/
theorem prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i) (hb : ∀ i ∈ s, b i ≤ 1) :
    0 ≤ ∏ i ∈ s, b i - ∏ i ∈ s, a i ∧ ∏ i ∈ s, b i - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (b i - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have ha' : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha i (mem_insert_of_mem hi)
    have hab' : ∀ i ∈ s, a i ≤ b i := fun i hi => hab i (mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, b i ≤ 1 := fun i hi => hb i (mem_insert_of_mem hi)
    obtain ⟨ih0, ih1⟩ := ih ha' hab' hb'
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have haj := ha j (mem_insert_self j s)
    have habj := hab j (mem_insert_self j s)
    have hbj := hb j (mem_insert_self j s)
    have hPa : 0 ≤ ∏ i ∈ s, a i := prod_nonneg ha'
    have hPa1 : ∏ i ∈ s, a i ≤ 1 := prod_le_one₀ ha' fun i hi => (hab' i hi).trans (hb' i hi)
    have e : b j * ∏ i ∈ s, b i - a j * ∏ i ∈ s, a i =
        b j * (∏ i ∈ s, b i - ∏ i ∈ s, a i) + (b j - a j) * ∏ i ∈ s, a i := by ring
    rw [e]
    have hbj0 : 0 ≤ b j := haj.trans habj
    constructor
    · exact add_nonneg (mul_nonneg hbj0 ih0) (mul_nonneg (by linarith) hPa)
    · have h1 : b j * (∏ i ∈ s, b i - ∏ i ∈ s, a i) ≤ ∑ i ∈ s, (b i - a i) :=
        (mul_le_of_le_one_left ih0 hbj).trans ih1
      have h2 : (b j - a j) * ∏ i ∈ s, a i ≤ b j - a j :=
        mul_le_of_le_one_right (by linarith) hPa1
      linarith

end Binomial

end PropFiveFortyFive

end MultipoleBKT

end
