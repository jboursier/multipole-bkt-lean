/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.Profiles

/-!
# The numerical series in the written group enumeration

(4.124) through
(4.125) in the proof of Lemma 4.59. The powers `n^(-2n)` are retained until
the sum over the number of groups. The zero-group term is separated.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open Finset
open scoped Classical

/-- The size-profile summand after Stirling and stars and bars.
This is the displayed `n^(-2n) q^(q+2n)` bound in the paper. -/
theorem source_profile_inner_le {q s n : ℕ} (hn : 1 ≤ n) (hns : n ≤ s) (hsq : s ≤ q) :
    1 / (n.factorial : ℝ) * ∑ m ∈ positiveProfiles n s,
      (Nat.multinomial univ m : ℝ) * (∏ i, (m i : ℝ) ^ m i) *
        ((q - s + n : ℕ) : ℝ) ^ (q - s + n) ≤
      Real.exp (3 * q) * (q : ℝ) ^ (q + 2 * n) / (n : ℝ) ^ (2 * n) := by
  let r := q - s + n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrq : r ≤ q := by dsimp only [r]; omega
  have hcount := positiveProfiles_stirling hn hns
  have hfac : (s.factorial : ℝ) ≤ (q : ℝ) ^ s :=
    (by exact_mod_cast Nat.factorial_le_pow s : (s.factorial : ℝ) ≤ (s : ℝ) ^ s).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsq) _)
  have hpow : (r : ℝ) ^ r ≤ (q : ℝ) ^ r :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hrq) _
  have hsn : (s : ℝ) ^ n ≤ (q : ℝ) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsq) _
  have hi : 1 / (n.factorial : ℝ) ≤ Real.exp n / (n : ℝ) ^ n := by
    rw [div_le_div_iff₀ (by positivity) (pow_pos hnR _), one_mul]
    simpa only [mul_comm] using pow_self_le_factorial_mul_exp n
  have hterm : ∀ m ∈ positiveProfiles n s,
      (Nat.multinomial univ m : ℝ) * (∏ i, (m i : ℝ) ^ m i) ≤ s.factorial * Real.exp s := by
    intro m hm
    have hms := (mem_positiveProfiles.mp hm).1
    have hp := mul_le_mul_of_nonneg_left (prod_size_powers_le m hms)
      (Nat.cast_nonneg (Nat.multinomial univ m) : (0 : ℝ) ≤ Nat.multinomial univ m)
    have he : (Nat.multinomial univ m : ℝ) * (∏ i, ((m i).factorial : ℝ)) = s.factorial := by
      have h := Nat.multinomial_spec univ m
      rw [hms] at h
      exact_mod_cast (by simpa only [mul_comm] using h : Nat.multinomial univ m *
        (∏ i, (m i).factorial) = s.factorial)
    simpa only [← mul_assoc, he] using hp
  calc
    _ ≤ 1 / (n.factorial : ℝ) *
        (((positiveProfiles n s).card : ℝ) * ((s.factorial : ℝ) * Real.exp s * (r : ℝ) ^ r)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ ∑ _m ∈ positiveProfiles n s, (s.factorial : ℝ) * Real.exp s * (r : ℝ) ^ r :=
          sum_le_sum fun m hm => mul_le_mul_of_nonneg_right (hterm m hm) (by positivity)
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Real.exp n / (n : ℝ) ^ n) *
        ((Real.exp s * (q : ℝ) ^ n / (n : ℝ) ^ n) * ((q : ℝ) ^ s * Real.exp s * (q : ℝ) ^ r)) := by
      gcongr
      exact hcount.trans (by gcongr)
    _ = Real.exp ((n : ℝ) + s + s) * (q : ℝ) ^ (n + s + r) / (n : ℝ) ^ (n + n) := by
      rw [pow_add, pow_add, pow_add, Real.exp_add, Real.exp_add]
      field_simp
      ring
    _ ≤ _ := by
      rw [show n + s + r = q + 2 * n by dsimp only [r]; omega, show n + n = 2 * n by omega]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hsR : (s : ℝ) ≤ q := by exact_mod_cast hsq
      have hnR' : (n : ℝ) ≤ s := by exact_mod_cast hns
      linarith

/-- The last sum over `n` is exponential in `q`, with `q^q` retained. -/
theorem source_profile_inner_uniform {q s n : ℕ} (hsq : s ≤ q) :
    1 / (n.factorial : ℝ) * ∑ m ∈ positiveProfiles n s,
      (Nat.multinomial univ m : ℝ) * (∏ i, (m i : ℝ) ^ m i) *
        ((q - s + n : ℕ) : ℝ) ^ (q - s + n) ≤ Real.exp (5 * q) * (q : ℝ) ^ q := by
  by_cases hn : n = 0
  · subst n
    rw [positiveProfiles_zero]
    by_cases hs : s = 0
    · simp only [hs, ite_true, sum_singleton]
      simp only [Nat.factorial_zero, Nat.cast_one, one_div]
      have he : (Nat.multinomial univ (Fin.elim0 : Fin 0 → ℕ) : ℝ) *
          (∏ i : Fin 0, ((Fin.elim0 i : ℕ) : ℝ) ^ (Fin.elim0 i : ℕ)) *
          ((q - 0 + 0 : ℕ) : ℝ) ^ (q - 0 + 0) = (q : ℝ) ^ q := by
        simp [Nat.multinomial]
      rw [he]
      have hexp : 1 ≤ Real.exp (5 * (q : ℝ)) := Real.one_le_exp (by positivity)
      simpa only [inv_one, one_mul] using
        le_mul_of_one_le_left (pow_nonneg (Nat.cast_nonneg q) q) hexp
    · simp only [hs, ite_false, sum_empty, mul_zero]
      positivity
  · by_cases hns : n ≤ s
    · have hn1 : 1 ≤ n := by omega
      refine (source_profile_inner_le hn1 hns hsq).trans ?_
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
      have hi : (q : ℝ) ^ n / (n : ℝ) ^ n ≤ Real.exp q := by
        calc
          _ ≤ (q : ℝ) ^ n / n.factorial := div_le_div_of_nonneg_left (by positivity)
            (by positivity) (by exact_mod_cast Nat.factorial_le_pow n)
          _ ≤ _ := Real.pow_div_factorial_le_exp q (by positivity) n
      have he : (q : ℝ) ^ (q + 2 * n) / (n : ℝ) ^ (2 * n) =
          (q : ℝ) ^ q * ((q : ℝ) ^ n / (n : ℝ) ^ n) ^ 2 := by
        rw [pow_add, pow_mul, pow_mul, div_pow]
        ring
      rw [div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv, he]
      calc
        _ ≤ Real.exp (3 * q) * ((q : ℝ) ^ q * Real.exp q ^ 2) := by gcongr
        _ = _ := by
          rw [← Real.exp_nat_mul]
          calc
            Real.exp (3 * q) * ((q : ℝ) ^ q * Real.exp ((2 : ℕ) * (q : ℝ))) =
                (Real.exp (3 * q) * Real.exp ((2 : ℕ) * (q : ℝ))) * (q : ℝ) ^ q := by ring
            _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; push_cast; ring
    · have hemp : positiveProfiles n s = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro m hm
        obtain ⟨he, hp⟩ := mem_positiveProfiles.mp hm
        have : n ≤ ∑ i, m i := by
          calc n = ∑ _i : Fin n, 1 := by simp
            _ ≤ _ := sum_le_sum fun i _ => hp i
        omega
      simp only [hemp, sum_empty, mul_zero]
      positivity

/-- The literal numerical series in (4.125). -/
theorem source_size_series_le (q : ℕ) :
    (∑ s ∈ range (q + 1), (q.choose s : ℝ) *
      ∑ n ∈ range (s + 1), 1 / (n.factorial : ℝ) * ∑ m ∈ positiveProfiles n s,
        (Nat.multinomial univ m : ℝ) * (∏ i, (m i : ℝ) ^ m i) *
          ((q - s + n : ℕ) : ℝ) ^ (q - s + n)) ≤
      (4 * Real.exp 5) ^ q * (q : ℝ) ^ q := by
  have hq : (q + 1 : ℝ) ≤ (2 : ℝ) ^ q := by
    have h : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
    exact_mod_cast h
  calc
    _ ≤ ∑ s ∈ range (q + 1), (q.choose s : ℝ) * ((2 : ℝ) ^ q * (Real.exp (5 * q) * (q : ℝ) ^ q)) := by
      apply sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ ∑ _n ∈ range (s + 1), Real.exp (5 * q) * (q : ℝ) ^ q :=
          sum_le_sum fun n _ => source_profile_inner_uniform (by have := mem_range.mp hs; omega)
        _ = (s + 1 : ℕ) * (Real.exp (5 * q) * (q : ℝ) ^ q) := by rw [sum_const, card_range, nsmul_eq_mul]
        _ ≤ _ := by
          have hsR : ((s + 1 : ℕ) : ℝ) ≤ (q : ℝ) + 1 := by
            have := mem_range.mp hs
            exact_mod_cast (by omega : s + 1 ≤ q + 1)
          exact mul_le_mul_of_nonneg_right (hsR.trans hq) (by positivity)
    _ = (2 : ℝ) ^ q * ((2 : ℝ) ^ q * (Real.exp (5 * q) * (q : ℝ) ^ q)) := by
      rw [← sum_mul]
      have h : (∑ s ∈ range (q + 1), (q.choose s : ℝ)) = (2 : ℝ) ^ q := by
        exact_mod_cast Nat.sum_range_choose q
      rw [h]
    _ = _ := by
      have he : Real.exp (5 * q) = Real.exp 5 ^ q := by rw [← Real.exp_nat_mul]; congr 1; ring
      rw [he, mul_pow]
      have h4 : (4 : ℝ) ^ q = 2 ^ q * 2 ^ q := by rw [← mul_pow]; norm_num
      rw [h4]
      ring

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
