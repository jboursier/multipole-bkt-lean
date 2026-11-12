/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.Profiles

/-!
# Bounding the enumerated group-size series

(4.125) in the proof of Lemma 4.59. Multinomial cancellation, stars and bars, and Stirling
leave a coefficient exponential in the total number of blocks.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open Finset
open scoped Classical

/-- Cancellation of the factorials in one multinomial term. -/
theorem profile_factorial_cancellation {n s q : ℕ} (hsq : s ≤ q)
    (m : Fin n → ℕ) (hm : ∑ i, m i = s) :
    (1 / (n.factorial : ℝ)) * (q.choose s * Nat.multinomial univ m : ℕ) *
        (∏ i, ((m i).factorial : ℝ)) * ((q - s + n).factorial : ℝ) =
      (q.factorial : ℝ) * ((q - s + n).choose n : ℝ) := by
  have hM : (Nat.multinomial univ m : ℝ) * (∏ i, ((m i).factorial : ℝ)) = s.factorial := by
    have h := Nat.multinomial_spec univ m
    rw [hm] at h
    exact_mod_cast (by simpa only [mul_comm] using h : Nat.multinomial univ m *
      (∏ i, (m i).factorial) = s.factorial)
  have hQ : (q.choose s : ℝ) * s.factorial * (q - s).factorial = q.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hsq
  have hR : ((q - s + n).choose n : ℝ) * n.factorial * (q - s).factorial =
      (q - s + n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ q - s + n by omega)
    rw [show q - s + n - n = q - s by omega] at h
    exact_mod_cast h
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  calc
    _ = (q.choose s : ℝ) * ((Nat.multinomial univ m : ℝ) * ∏ i, ((m i).factorial : ℝ)) *
        ((q - s + n).factorial : ℝ) / n.factorial := by ring
    _ = (q.choose s : ℝ) * s.factorial *
        (((q - s + n).choose n : ℝ) * n.factorial * (q - s).factorial) / n.factorial := by
      rw [hM, hR]
    _ = ((q.choose s : ℝ) * s.factorial * (q - s).factorial) *
        ((q - s + n).choose n : ℝ) := by field_simp
    _ = _ := by rw [hQ]

/-- Each fixed number of groups contributes at most `4^q q!`.
The profile count is the stars-and-bars count proved in `card_positiveProfiles`. -/
theorem sum_profiles_factorials_le {q n s : ℕ} (_hnq : n ≤ q) (hsq : s ≤ q) :
    (1 / (n.factorial : ℝ)) * ∑ m ∈ positiveProfiles n s,
      (q.choose s * Nat.multinomial univ m : ℕ) * (∏ i, ((m i).factorial : ℝ)) *
        ((q - s + n).factorial : ℝ) ≤ (4 : ℝ) ^ q * q.factorial := by
  rw [mul_sum]
  have hterm : ∀ m ∈ positiveProfiles n s,
      1 / (n.factorial : ℝ) * ((q.choose s * Nat.multinomial univ m : ℕ) *
        (∏ i, ((m i).factorial : ℝ)) * ((q - s + n).factorial : ℝ)) ≤
          (q.factorial : ℝ) * (2 : ℝ) ^ q := by
    intro m hm
    have hms := (mem_positiveProfiles.mp hm).1
    have hns : n ≤ s := by
      have hp := (mem_positiveProfiles.mp hm).2
      calc n = ∑ _i : Fin n, 1 := by simp
        _ ≤ s := hms ▸ sum_le_sum fun i _ => hp i
    have he := profile_factorial_cancellation hsq m hms
    rw [show 1 / (n.factorial : ℝ) * ((q.choose s * Nat.multinomial univ m : ℕ) *
        (∏ i, ((m i).factorial : ℝ)) * ((q - s + n).factorial : ℝ)) =
        1 / (n.factorial : ℝ) * (q.choose s * Nat.multinomial univ m : ℕ) *
          (∏ i, ((m i).factorial : ℝ)) * ((q - s + n).factorial : ℝ) by ring, he]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact_mod_cast (Nat.choose_le_two_pow (q - s + n) n).trans
      (Nat.pow_le_pow_right (by omega) (by omega : q - s + n ≤ q))
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hc : ((positiveProfiles n s).card : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast (card_positiveProfiles_le n s).trans (Nat.pow_le_pow_right (by omega) hsq)
  calc
    _ ≤ (2 : ℝ) ^ q * ((q.factorial : ℝ) * 2 ^ q) := by gcongr
    _ = _ := by rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring

/-- The group enumeration with factorial weights.
This form also gives the summed bound. -/
theorem sum_groups_factorials_le {α : Type*} (U : Finset α) :
    (∑ n ∈ range (U.card + 1), 1 / (n.factorial : ℝ) *
      ∑ G ∈ nonemptyGroups U n, (∏ i, ((G i).card.factorial : ℝ)) *
        ((U.card - ∑ i, (G i).card + n).factorial : ℝ)) ≤
      (16 : ℝ) ^ U.card * U.card.factorial := by
  let q := U.card
  have hterm : ∀ n ∈ range (q + 1), 1 / (n.factorial : ℝ) *
      ∑ G ∈ nonemptyGroups U n, (∏ i, ((G i).card.factorial : ℝ)) *
        ((q - ∑ i, (G i).card + n).factorial : ℝ) ≤
      (q + 1 : ℕ) * ((4 : ℝ) ^ q * q.factorial) := by
    intro n hn
    rw [sum_nonemptyGroups U n (fun m => (∏ i, ((m i).factorial : ℝ)) *
      ((q - ∑ i, m i + n).factorial : ℝ))]
    simp only [nsmul_eq_mul]
    rw [mul_sum]
    calc
      _ ≤ ∑ _s ∈ range (q + 1), (4 : ℝ) ^ q * q.factorial := by
        apply sum_le_sum
        intro s hs
        have hb := sum_profiles_factorials_le (by have := mem_range.mp hn; omega : n ≤ q)
          (by have := mem_range.mp hs; omega : s ≤ q)
        convert hb using 1
        congr 1
        apply sum_congr rfl
        intro m hm
        rw [(mem_positiveProfiles.mp hm).1]
        ring
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  have hq : (q + 1 : ℝ) ≤ (2 : ℝ) ^ q := by
    have hnat : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
    exact_mod_cast hnat
  calc
    _ = (q + 1 : ℝ) ^ 2 * ((4 : ℝ) ^ q * q.factorial) := by push_cast; ring
    _ ≤ ((2 : ℝ) ^ q) ^ 2 * ((4 : ℝ) ^ q * q.factorial) := by gcongr
    _ = _ := by
      rw [← pow_mul, mul_comm q 2, pow_mul, ← mul_assoc, ← mul_pow]
      norm_num
      rfl

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
