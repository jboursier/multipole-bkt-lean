/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteProfiles.Counting

/-!
# Fixed-profile and fixed-size entropy estimates

Lemma 4.59,
(4.129), (4.130) and (4.131) in the proof of Lemma 4.59.
The factor for a prescribed block stays outside the entropy estimate.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteProfiles

open Finset PropFiveFortyFive
open scoped Classical

/-- An explicit exponential constant absorbing entropy and the number of profiles. -/
noncomputable def entropyConstant (p : ℕ) : ℝ := Real.exp 2 * (p + 1) * 2 ^ p

theorem entropy_base_one_le (p : ℕ) : 1 ≤ Real.exp 2 * (p + 1) := by
  have he : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hp : (1 : ℝ) ≤ p + 1 := by have := Nat.cast_nonneg (α := ℝ) p; linarith
  nlinarith

theorem entropyConstant_pos (p : ℕ) : 0 < entropyConstant p := by
  unfold entropyConstant
  positivity

/-- Insert the ambient profile bounds in the binomial/Stirling/entropy estimate. -/
theorem fixed_profile_le {p : ℕ} (n m : Fin p → ℕ) (v : Fin p → ℝ)
    (hv : ∀ i, 0 ≤ v i) {z : ℝ} (hz : 0 ≤ z)
    (hn : ∀ i, (n i : ℝ) * v i ≤ z ^ ((i : ℕ) + 1)) :
    ((∑ i, m i : ℕ) : ℝ) ^ (∑ i, m i) *
        ∏ i, ((n i).choose (m i) : ℝ) * v i ^ m i ≤
      (Real.exp 2 * (p + 1) * z) ^ degree m := by
  have hp : Real.exp 1 * p ≤ Real.exp 2 * (p + 1) := by
    have he : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    have he0 := (Real.exp_pos 2).le
    have hp0 : (0 : ℝ) ≤ p := by positivity
    nlinarith
  calc _ ≤ (Real.exp 1 * p) ^ (∑ i, m i) * ∏ i, ((n i : ℝ) * v i) ^ m i :=
      binomial_profile_entropy n m v hv
    _ ≤ (Real.exp 2 * (p + 1)) ^ (∑ i, m i) *
        ∏ i : Fin p, (z ^ ((i : ℕ) + 1)) ^ m i := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ (by positivity) hp _
          · exact prod_le_prod₀ (fun i _ => pow_nonneg (mul_nonneg (by positivity) (hv i)) _)
              fun i _ => pow_le_pow_left₀ (mul_nonneg (by positivity) (hv i)) (hn i) _
          · exact prod_nonneg fun i _ => pow_nonneg (mul_nonneg (by positivity) (hv i)) _
          · positivity
    _ ≤ (Real.exp 2 * (p + 1)) ^ degree m * z ^ degree m := by
          rw [show (∏ i : Fin p, (z ^ ((i : ℕ) + 1)) ^ m i) = z ^ degree m by
            simp only [← pow_mul, prod_pow_eq_pow_sum, degree]]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (entropy_base_one_le p) (sum_le_degree m)) (pow_nonneg hz _)
    _ = _ := by simp only [mul_pow]

/-- The analogous estimate with one prescribed block removed. -/
theorem fixed_anchored_profile_le {p : ℕ} (n m : Fin p → ℕ) (v : Fin p → ℝ)
    (hv : ∀ i, 0 ≤ v i) {z : ℝ} (_hz : 0 ≤ z)
    (hn : ∀ i, (n i : ℝ) * v i ≤ z ^ ((i : ℕ) + 1)) :
    (((∑ i, m i) + 1 : ℕ) : ℝ) ^ ((∑ i, m i) + 1) *
        ∏ i, ((n i).choose (m i) : ℝ) * v i ^ m i ≤
      Real.exp 1 * (degree m + 1) * (Real.exp 2 * (p + 1) * z) ^ degree m := by
  have hs := shifted_binomial_profile_entropy n m v hv
  have hprod : ∏ i, ((n i : ℝ) * v i) ^ m i ≤ z ^ degree m := by
    calc _ ≤ ∏ i : Fin p, (z ^ ((i : ℕ) + 1)) ^ m i :=
        prod_le_prod₀ (fun i _ => pow_nonneg (mul_nonneg (by positivity) (hv i)) _)
          fun i _ => pow_le_pow_left₀ (mul_nonneg (by positivity) (hv i)) (hn i) _
      _ = _ := by simp only [← pow_mul, prod_pow_eq_pow_sum, degree]
  have hpow : (Real.exp 2 * p) ^ (∑ i, m i) ≤ (Real.exp 2 * (p + 1)) ^ degree m := by
    calc _ ≤ (Real.exp 2 * (p + 1)) ^ (∑ i, m i) := by gcongr; linarith [Real.exp_pos 2]
      _ ≤ _ := pow_le_pow_right₀ (entropy_base_one_le p) (sum_le_degree m)
  have ha : (((∑ i, m i) + 1 : ℕ) : ℝ) ≤ degree m + 1 := by
    exact_mod_cast Nat.add_le_add_right (sum_le_degree m) 1
  refine hs.trans ?_
  conv_rhs => rw [mul_pow (Real.exp 2 * (p + 1)) z, ← mul_assoc]
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le) hpow
    (by positivity) (by positivity)) hprod
    (prod_nonneg fun i _ => pow_nonneg (mul_nonneg (by positivity) (hv i)) _) (by positivity)

/-- Sum the entropy estimates over all profiles with total size `k`. -/
theorem size_sum_le {p k : ℕ} {π : Finset (Finset ℕ)} (hπ : IsSubpartition π)
    (hp : ∀ S ∈ π, S.card ≤ p) (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) {z : ℝ} (hz : 0 ≤ z)
    (hn : ∀ i : Fin p, (blockCount p π i : ℝ) * v ((i : ℕ) + 1) ≤ z ^ ((i : ℕ) + 1)) :
    ∑ X ∈ π.powerset.filter (fun X => (X.biUnion id).card = k),
        (X.card : ℝ) ^ X.card * ∏ S ∈ X, v S.card ≤ (entropyConstant p * z) ^ k := by
  rw [sum_by_profile hπ hp]
  have hs : ∀ m ∈ profiles p k,
      ∑ X ∈ π.powerset.filter (fun X => blockCount p X = m),
        (X.card : ℝ) ^ X.card * ∏ S ∈ X, v S.card ≤ (Real.exp 2 * (p + 1) * z) ^ k := by
    intro m hm
    rw [sum_fixed_profile (fun S hS => ⟨(hπ.1 S hS).card_pos, hp S hS⟩)]
    simpa only [mem_profiles.mp hm] using
      fixed_profile_le (blockCount p π) m (fun i => v ((i : ℕ) + 1)) (fun i => hv _) hz hn
  calc _ ≤ ∑ _m ∈ profiles p k, (Real.exp 2 * (p + 1) * z) ^ k := sum_le_sum hs
    _ = ((profiles p k).card : ℝ) * (Real.exp 2 * (p + 1) * z) ^ k := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ p : ℝ) ^ k) * (Real.exp 2 * (p + 1) * z) ^ k := by
      gcongr
      exact_mod_cast card_profiles_le p k
    _ = _ := by unfold entropyConstant; rw [← mul_pow]; congr 1; ring

/-- Fix the total size after removing the prescribed block. -/
theorem shifted_size_sum_le {p k : ℕ} {π : Finset (Finset ℕ)} (hπ : IsSubpartition π)
    (hp : ∀ S ∈ π, S.card ≤ p) (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) {z : ℝ} (hz : 0 ≤ z)
    (hn : ∀ i : Fin p, (blockCount p π i : ℝ) * v ((i : ℕ) + 1) ≤ z ^ ((i : ℕ) + 1)) :
    ∑ X ∈ π.powerset.filter (fun X => (X.biUnion id).card = k),
        ((X.card + 1 : ℕ) : ℝ) ^ (X.card + 1) * ∏ S ∈ X, v S.card ≤
      Real.exp 1 * (k + 1) * (entropyConstant p * z) ^ k := by
  rw [sum_by_profile hπ hp]
  have hs : ∀ m ∈ profiles p k,
      ∑ X ∈ π.powerset.filter (fun X => blockCount p X = m),
        ((X.card + 1 : ℕ) : ℝ) ^ (X.card + 1) * ∏ S ∈ X, v S.card ≤
      Real.exp 1 * (k + 1) * (Real.exp 2 * (p + 1) * z) ^ k := by
    intro m hm
    have he : ∀ X ∈ π.powerset.filter (fun X => blockCount p X = m),
        ((X.card + 1 : ℕ) : ℝ) ^ (X.card + 1) * ∏ S ∈ X, v S.card =
          (((∑ i, m i) + 1 : ℕ) : ℝ) ^ ((∑ i, m i) + 1) *
            ∏ i : Fin p, v ((i : ℕ) + 1) ^ m i := by
      intro X hX
      obtain ⟨hsub, he⟩ := mem_filter.mp hX
      have hpX : ∀ S ∈ X, 1 ≤ S.card ∧ S.card ≤ p := fun S hS => ⟨(hπ.1 S (mem_powerset.mp hsub hS)).card_pos,
        hp S (mem_powerset.mp hsub hS)⟩
      rw [← sum_blockCount hpX, prod_card_eq_prod_blockCount hpX, he]
    rw [sum_congr rfl he, sum_const, nsmul_eq_mul,
      card_powerset_filter_blockCount (fun S hS => ⟨(hπ.1 S hS).card_pos, hp S hS⟩), Nat.cast_prod]
    have hh := fixed_anchored_profile_le (blockCount p π) m
      (fun i => v ((i : ℕ) + 1)) (fun i => hv _) hz hn
    rw [mem_profiles.mp hm] at hh
    convert hh using 1; rw [prod_mul_distrib]; ring
  calc _ ≤ ∑ _m ∈ profiles p k,
        Real.exp 1 * (k + 1) * (Real.exp 2 * (p + 1) * z) ^ k := sum_le_sum hs
    _ ≤ ((2 ^ p : ℝ) ^ k) *
        (Real.exp 1 * (k + 1) * (Real.exp 2 * (p + 1) * z) ^ k) := by
      rw [sum_const, nsmul_eq_mul]
      gcongr
      exact_mod_cast card_profiles_le p k
    _ = _ := by unfold entropyConstant; simp only [mul_pow]; ring

end MultipoleBKT.AbsoluteLower.RouteProfiles

end
