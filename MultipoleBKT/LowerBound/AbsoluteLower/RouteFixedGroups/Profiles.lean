/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.Enumeration

/-!
# Reindexing ordered groups by their size profiles

(4.124) in the proof of Lemma 4.59. The selected union has size `s`, and the ordered
positive sizes `m₁,…,mₙ` have total `s`.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open Finset
open scoped Classical

/-- Ordered, disjoint, nonempty subfamilies of a finite set. -/
noncomputable def nonemptyGroups {α : Type*} (U : Finset α) (n : ℕ) :
    Finset (Fin n → Finset α) :=
  (Fintype.piFinset fun _ : Fin n => U.powerset).filter fun G =>
    (∀ i j, i ≠ j → Disjoint (G i) (G j)) ∧ ∀ i, (G i).Nonempty

theorem mem_nonemptyGroups {α : Type*} {U : Finset α} {n : ℕ} {G : Fin n → Finset α} :
    G ∈ nonemptyGroups U n ↔ (∀ i, G i ⊆ U) ∧
      (∀ i j, i ≠ j → Disjoint (G i) (G j)) ∧ ∀ i, (G i).Nonempty := by
  simp only [nonemptyGroups, mem_filter, Fintype.mem_piFinset, mem_powerset]

theorem sum_group_sizes_le {α : Type*} {U : Finset α} {n : ℕ} {G : Fin n → Finset α}
    (hG : G ∈ nonemptyGroups U n) : ∑ i, (G i).card ≤ U.card := by
  obtain ⟨hGU, hGd, _⟩ := mem_nonemptyGroups.mp hG
  rw [← card_biUnion fun i _ j _ hij => hGd i j hij]
  exact card_le_card (biUnion_subset.mpr fun i _ => hGU i)

/-- Exact group enumeration with both the binomial and multinomial visible. -/
theorem sum_nonemptyGroups {α R : Type*} [AddCommMonoid R] (U : Finset α) (n : ℕ)
    (F : (Fin n → ℕ) → R) :
    (∑ G ∈ nonemptyGroups U n, F (fun i => (G i).card)) =
      ∑ s ∈ range (U.card + 1), ∑ m ∈ positiveProfiles n s,
        (U.card.choose s * Nat.multinomial univ m) • F m := by
  have hsum : ∀ G ∈ nonemptyGroups U n, (∑ i, (G i).card) ∈ range (U.card + 1) :=
    fun G hG => mem_range.mpr (by have := sum_group_sizes_le hG; omega)
  rw [← sum_fiberwise_of_maps_to hsum]
  apply sum_congr rfl
  intro s hs
  have hprofile : ∀ G ∈ (nonemptyGroups U n).filter (fun G => ∑ i, (G i).card = s),
      (fun i => (G i).card) ∈ positiveProfiles n s := by
    intro G hG
    obtain ⟨hG, he⟩ := mem_filter.mp hG
    exact mem_positiveProfiles.mpr ⟨he, fun i => card_pos.mpr ((mem_nonemptyGroups.mp hG).2.2 i)⟩
  rw [← sum_fiberwise_of_maps_to hprofile]
  apply sum_congr rfl
  intro m hm
  have hm' := mem_positiveProfiles.mp hm
  have hset : ((nonemptyGroups U n).filter (fun G => ∑ i, (G i).card = s)).filter
      (fun G => (fun i => (G i).card) = m) = orderedGroups U m := by
    ext G
    simp only [mem_filter, mem_nonemptyGroups, mem_orderedGroups]
    constructor
    · rintro ⟨⟨⟨hGU, hGd, _⟩, _⟩, he⟩
      exact ⟨hGU, fun i => congrFun he i, hGd⟩
    · rintro ⟨hGU, hGc, hGd⟩
      have he : (fun i => (G i).card) = m := funext hGc
      exact ⟨⟨⟨hGU, hGd, fun i => card_pos.mp (by rw [hGc i]; exact hm'.2 i)⟩,
        by simpa only [hGc] using hm'.1⟩, he⟩
  rw [hset]
  have hF : ∀ G ∈ orderedGroups U m, F (fun i => (G i).card) = F m := fun G hG =>
    congrArg F (funext (mem_orderedGroups.mp hG).2.1)
  rw [sum_congr rfl hF, sum_const, card_orderedGroups U m
    (by rw [hm'.1]; have := mem_range.mp hs; omega), hm'.1]

/-- Positive groups cannot outnumber their total size. -/
theorem positiveProfiles_eq_empty_of_lt {n s : ℕ} (hsn : s < n) : positiveProfiles n s = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro m hm
  obtain ⟨he, hp⟩ := mem_positiveProfiles.mp hm
  have : n ≤ ∑ i, m i := by
    calc n = ∑ _i : Fin n, 1 := by simp
      _ ≤ _ := sum_le_sum fun i _ => hp i
  omega

/-- The stars-and-bars count is bounded by `2^s`, uniformly in the group number. -/
theorem card_positiveProfiles_le (n s : ℕ) : (positiveProfiles n s).card ≤ 2 ^ s := by
  by_cases hn : n = 0
  · subst n
    rw [positiveProfiles_zero]
    split_ifs <;> simp_all
  · by_cases hns : n ≤ s
    · rw [card_positiveProfiles (by omega) hns]
      exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le s 1))
    · have he : positiveProfiles n s = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro m hm
        obtain ⟨hm, hp⟩ := mem_positiveProfiles.mp hm
        have : n ≤ ∑ i, m i := by
          calc n = ∑ _i : Fin n, 1 := by simp
            _ ≤ _ := sum_le_sum fun i _ => hp i
        omega
      simp [he]

/-- Stirling absorbs the product of the powers of the group sizes. -/
theorem prod_size_powers_le {n s : ℕ} (m : Fin n → ℕ) (hm : ∑ i, m i = s) :
    (∏ i, (m i : ℝ) ^ m i) ≤ (∏ i, ((m i).factorial : ℝ)) * Real.exp s := by
  calc
    _ ≤ ∏ i, ((m i).factorial : ℝ) * Real.exp (m i) :=
      prod_le_prod₀ (fun i _ => by positivity) (fun i _ => pow_self_le_factorial_mul_exp _)
    _ = _ := by
      rw [prod_mul_distrib, ← Real.exp_sum]
      have he : (∑ i, (m i : ℝ)) = s := by exact_mod_cast hm
      rw [he]

/-- The precise stars-and-bars and Stirling estimate printed in Step 2. -/
theorem positiveProfiles_stirling {n s : ℕ} (hn : 1 ≤ n) (hns : n ≤ s) :
    ((positiveProfiles n s).card : ℝ) ≤ Real.exp s * (s : ℝ) ^ n / (n : ℝ) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hc : (s - 1).choose (n - 1) ≤ s.choose n := by
    have he := Nat.choose_succ_succ (s - 1) (n - 1)
    rw [show (s - 1).succ = s by omega, show (n - 1).succ = n by omega] at he
    omega
  have hi : 1 / (n.factorial : ℝ) ≤ Real.exp n / (n : ℝ) ^ n := by
    rw [div_le_div_iff₀ hf (pow_pos hnR _), one_mul]
    simpa only [mul_comm] using pow_self_le_factorial_mul_exp n
  rw [card_positiveProfiles hn hns]
  calc
    _ ≤ (s.choose n : ℝ) := by exact_mod_cast hc
    _ ≤ (s : ℝ) ^ n / n.factorial := Nat.choose_le_pow_div n s
    _ = (s : ℝ) ^ n * (1 / n.factorial) := by ring
    _ ≤ (s : ℝ) ^ n * (Real.exp s / (n : ℝ) ^ n) := by
      apply mul_le_mul_of_nonneg_left (hi.trans ?_) (by positivity)
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by exact_mod_cast hns)) (by positivity)
    _ = _ := by ring

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
