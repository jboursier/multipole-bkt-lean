/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Count
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Entropy of a fixed multipole profile

Lemma 4.59,
(4.121) and Step 3, proof of Lemma 4.59. Zero coordinates
contribute `0 log 0 = 0` and `0 ^ 0 = 1`, including the empty profile.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteProfiles

open Finset

/-- The binomial and Stirling estimate, with denominators cleared. -/
theorem choose_mul_pow_self_le (n m : ℕ) :
    (n.choose m : ℝ) * (m : ℝ) ^ m ≤ Real.exp m * (n : ℝ) ^ m := by
  have h := Nat.choose_le_pow_div (α := ℝ) m n
  have hf : (0 : ℝ) < m.factorial := by positivity
  have hs := pow_self_le_factorial_mul_exp m
  calc (n.choose m : ℝ) * (m : ℝ) ^ m
      ≤ ((n : ℝ) ^ m / m.factorial) * ((m.factorial : ℝ) * Real.exp m) :=
        mul_le_mul h hs (by positivity) (by positivity)
    _ = Real.exp m * (n : ℝ) ^ m := by field_simp

/-- Jensen's inequality for `x log x`, before exponentiating. -/
theorem profile_log_entropy {p : ℕ} (hp : 0 < p) (m : Fin p → ℕ) :
    (∑ i, (m i : ℝ)) * Real.log (∑ i, (m i : ℝ)) -
        ∑ i, (m i : ℝ) * Real.log (m i) ≤
      (∑ i, (m i : ℝ)) * Real.log p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set a : ℝ := ∑ i, (m i : ℝ)
  have ha : 0 ≤ a := sum_nonneg fun _ _ => by positivity
  by_cases haz : a = 0
  · have hm : ∀ i, m i = 0 := by
      intro i
      have hi : (m i : ℝ) ≤ a := single_le_sum (f := fun i => (m i : ℝ)) (fun _ _ => by positivity) (mem_univ i)
      have : (m i : ℝ) = 0 := by linarith
      exact_mod_cast this
    simp [haz, hm]
  have haR : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hj := Real.convexOn_mul_log.map_sum_le (t := (univ : Finset (Fin p)))
    (w := fun _ => (p : ℝ)⁻¹) (p := fun i => (m i : ℝ))
    (fun _ _ => inv_nonneg.mpr hpR.le)
    (by simp [hpR.ne']) (fun _ _ => Nat.cast_nonneg _)
  have hsum : ∑ i : Fin p, (p : ℝ)⁻¹ * (m i : ℝ) = a / p := by
    rw [← mul_sum]
    simp [a, div_eq_mul_inv, mul_comm]
  simp only [smul_eq_mul] at hj
  rw [hsum, Real.log_div haR.ne' hpR.ne'] at hj
  have hr : (∑ i : Fin p, (p : ℝ)⁻¹ * ((m i : ℝ) * Real.log (m i))) =
      (∑ i, (m i : ℝ) * Real.log (m i)) / p := by
    rw [← mul_sum]
    ring
  rw [hr] at hj
  have hj' := (div_le_div_iff_of_pos_right hpR).mp
    (show (a * (Real.log a - Real.log p)) / p ≤
      (∑ i, (m i : ℝ) * Real.log (m i)) / p by simpa only [div_mul_eq_mul_div] using hj)
  dsimp [a] at hj'
  nlinarith

/-- Exponentiating `m log m`, also at the zero coordinate. -/
theorem exp_nat_mul_log (m : ℕ) : Real.exp ((m : ℝ) * Real.log m) = (m : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rw [Real.exp_nat_mul, Real.exp_log hmR]

/-- The entropy bound `k₀^k₀ / ∏ mᵢ^mᵢ ≤ p^k₀` used in Step 3. -/
theorem profile_entropy {p : ℕ} (m : Fin p → ℕ) :
    ((∑ i, m i : ℕ) : ℝ) ^ (∑ i, m i) ≤
      (p : ℝ) ^ (∑ i, m i) * ∏ i, (m i : ℝ) ^ m i := by
  by_cases hp : p = 0
  · subst p
    simp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.pos_of_ne_zero hp)
  have h := profile_log_entropy (Nat.pos_of_ne_zero hp) m
  have he := Real.exp_le_exp.mpr (show
      ((∑ i, m i : ℕ) : ℝ) * Real.log (∑ i, m i : ℕ) ≤
        ((∑ i, m i : ℕ) : ℝ) * Real.log p + ∑ i, (m i : ℝ) * Real.log (m i) by
      push_cast
      linarith)
  rw [Real.exp_add, Real.exp_sum, exp_nat_mul_log] at he
  simp only [exp_nat_mul_log] at he
  rw [Real.exp_nat_mul, Real.exp_log hpR] at he
  exact he

/-- Fix a profile, multiply the binomial estimates, then use its entropy. -/
theorem binomial_profile_entropy {p : ℕ} (n m : Fin p → ℕ) (v : Fin p → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    ((∑ i, m i : ℕ) : ℝ) ^ (∑ i, m i) *
        ∏ i, (n i |>.choose (m i) : ℝ) * v i ^ m i ≤
      (Real.exp 1 * p) ^ (∑ i, m i) * ∏ i, ((n i : ℝ) * v i) ^ m i := by
  have hb : (∏ i, (n i |>.choose (m i) : ℝ) * v i ^ m i) *
        (∏ i, (m i : ℝ) ^ m i) ≤
      Real.exp (∑ i, m i : ℕ) * ∏ i, ((n i : ℝ) * v i) ^ m i := by
    rw [← prod_mul_distrib]
    calc ∏ i, ((n i |>.choose (m i) : ℝ) * v i ^ m i) * (m i : ℝ) ^ m i
        ≤ ∏ i, Real.exp (m i) * ((n i : ℝ) * v i) ^ m i := by
          apply prod_le_prod₀ (fun i _ => mul_nonneg (mul_nonneg (by positivity)
            (pow_nonneg (hv i) _)) (by positivity))
          intro i _
          have h := mul_le_mul_of_nonneg_right (choose_mul_pow_self_le (n i) (m i))
            (pow_nonneg (hv i) (m i))
          simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by rw [prod_mul_distrib, ← Real.exp_sum]; push_cast; rfl
  have he := mul_le_mul_of_nonneg_right (profile_entropy m)
    (show 0 ≤ ∏ i, (n i |>.choose (m i) : ℝ) * v i ^ m i from
      prod_nonneg fun i _ => mul_nonneg (by positivity) (pow_nonneg (hv i) _))
  calc _ ≤ (p : ℝ) ^ (∑ i, m i) *
        ((∏ i, (n i |>.choose (m i) : ℝ) * v i ^ m i) * ∏ i, (m i : ℝ) ^ m i) := by
          convert he using 1; ring
    _ ≤ (p : ℝ) ^ (∑ i, m i) *
        (Real.exp (∑ i, m i : ℕ) * ∏ i, ((n i : ℝ) * v i) ^ m i) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [mul_pow, ← Real.exp_one_pow]; ring

/-- Stirling after prescribing one block. The factor for that block is
kept outside the product, so entropy is applied to the remaining profile. -/
theorem shifted_binomial_profile_entropy {p : ℕ} (n m : Fin p → ℕ) (v : Fin p → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    (((∑ i, m i) + 1 : ℕ) : ℝ) ^ ((∑ i, m i) + 1) *
        ∏ i, ((n i).choose (m i) : ℝ) * v i ^ m i ≤
      Real.exp 1 * (((∑ i, m i) + 1 : ℕ) : ℝ) *
        (Real.exp 2 * p) ^ (∑ i, m i) * ∏ i, ((n i : ℝ) * v i) ^ m i := by
  set a := ∑ i, m i
  have hs := pow_self_le_factorial_mul_exp (a + 1)
  have hf : (a.factorial : ℝ) ≤ (a : ℝ) ^ a := by exact_mod_cast Nat.factorial_le_pow a
  have hs' : ((a + 1 : ℕ) : ℝ) ^ (a + 1) ≤
      Real.exp (a + 1 : ℕ) * (a + 1 : ℕ) * (a : ℝ) ^ a := by
    rw [Nat.factorial_succ, Nat.cast_mul] at hs
    refine hs.trans ?_
    have hh := mul_le_mul_of_nonneg_left hf
      (show 0 ≤ Real.exp (a + 1 : ℕ) * (a + 1 : ℕ) from by positivity)
    nlinarith [hh]
  have he := binomial_profile_entropy n m v hv
  have hp : 0 ≤ ∏ i, ((n i).choose (m i) : ℝ) * v i ^ m i :=
    prod_nonneg fun i _ => mul_nonneg (by positivity) (pow_nonneg (hv i) _)
  calc _ ≤ (Real.exp (a + 1 : ℕ) * (a + 1 : ℕ)) *
        ((a : ℝ) ^ a * ∏ i, ((n i).choose (m i) : ℝ) * v i ^ m i) := by
          convert mul_le_mul_of_nonneg_right hs' hp using 1; ring
    _ ≤ (Real.exp (a + 1 : ℕ) * (a + 1 : ℕ)) *
        ((Real.exp 1 * p) ^ a * ∏ i, ((n i : ℝ) * v i) ^ m i) :=
          mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [Nat.cast_add, Nat.cast_one, Real.exp_add, he2]
      simp only [mul_pow, Real.exp_one_pow]
      ring

end MultipoleBKT.AbsoluteLower.RouteProfiles

end
