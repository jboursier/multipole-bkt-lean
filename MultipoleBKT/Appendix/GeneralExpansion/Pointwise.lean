/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Lemma A.6, Step 1: the algebra of the expansion

See the proof of Lemma A.6, Step 1: the expansion (A.31) of
`∏_{i<j} e^{-β w_ij} 𝟙_{𝒜_ij} ∏_i e^{L r_i²/τ_i²}` around `∏_{i<j} e^{-β v_ij} 𝟙_{𝒜_ij}` and the
bounds (A.32) and (A.35) on its terms, in the form of a telescoping estimate: if every
pair factor moves by at most `K₁ (ρ_i + ρ_j)` and every one-body factor by at most `K₂ ρ_i`, the
product moves by at most `W^{k²} Ψ^k (2k K₁ + K₂) ∑_i ρ_i` (eq. (A.36), with
`ρ_i = r_i²/τ_i²`).

* `abs_prod_sub_prod_le`: `|∏ f - ∏ g| ≤ B^{|s|} ∑ |f_i - g_i|` for `0 ≤ f, g ≤ B`, `B ≥ 1`;
* `abs_exp_sub_exp_le`: `|e^a - e^b| ≤ e^{max(a, b)} |a - b|`;
* `abs_pairs_mul_sub_le`: the expansion bound.
-/

@[expose] public section

namespace MultipoleBKT

namespace GeneralExpansion

open Finset

/-- **Telescoping**: for `0 ≤ f_i, g_i ≤ B` with `B ≥ 1`,
`|∏_{i ∈ s} f_i - ∏_{i ∈ s} g_i| ≤ B^{|s|} ∑_{i ∈ s} |f_i - g_i|`. -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) {f g : ι → ℝ} {B : ℝ}
    (hB : 1 ≤ B) (hf0 : ∀ i ∈ s, 0 ≤ f i) (hfB : ∀ i ∈ s, f i ≤ B) (hg0 : ∀ i ∈ s, 0 ≤ g i)
    (hgB : ∀ i ∈ s, g i ≤ B) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ B ^ s.card * ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hf0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf0 i (mem_insert_of_mem hi)
    have hfB' : ∀ i ∈ s, f i ≤ B := fun i hi => hfB i (mem_insert_of_mem hi)
    have hg0' : ∀ i ∈ s, 0 ≤ g i := fun i hi => hg0 i (mem_insert_of_mem hi)
    have hgB' : ∀ i ∈ s, g i ≤ B := fun i hi => hgB i (mem_insert_of_mem hi)
    have ih' := ih hf0' hfB' hg0' hgB'
    rw [prod_insert ha, prod_insert ha, sum_insert ha, card_insert_of_notMem ha]
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    have hPf0 : 0 ≤ ∏ i ∈ s, f i := prod_nonneg hf0'
    have hPf : ∏ i ∈ s, f i ≤ B ^ s.card := by
      calc ∏ i ∈ s, f i ≤ ∏ _i ∈ s, B := prod_le_prod₀ hf0' hfB'
        _ = B ^ s.card := prod_const B
    have hga0 : 0 ≤ g a := hg0 a (mem_insert_self a s)
    have hgaB : g a ≤ B := hgB a (mem_insert_self a s)
    have hsplit : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    have hpow : B ^ s.card ≤ B ^ (s.card + 1) := pow_le_pow_right₀ hB (Nat.le_succ _)
    have hS0 : 0 ≤ ∑ i ∈ s, |f i - g i| := sum_nonneg fun i _ => abs_nonneg _
    rw [hsplit]
    calc |(f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)|
        ≤ |f a - g a| * ∏ i ∈ s, f i + g a * |∏ i ∈ s, f i - ∏ i ∈ s, g i| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hPf0, abs_of_nonneg hga0]
      _ ≤ |f a - g a| * B ^ (s.card + 1) + B * (B ^ s.card * ∑ i ∈ s, |f i - g i|) := by
          gcongr
          exact hPf.trans hpow
      _ = B ^ (s.card + 1) * (|f a - g a| + ∑ i ∈ s, |f i - g i|) := by ring

/-- `|e^a - e^b| ≤ e^{max(a, b)} |a - b|`. -/
theorem abs_exp_sub_exp_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ Real.exp (max a b) * |a - b| := by
  rcases le_total a b with hab | hab
  · have h1 : Real.exp b - Real.exp a ≤ Real.exp b * (b - a) := by
      have := Real.add_one_le_exp (a - b)
      have h2 : Real.exp a = Real.exp b * Real.exp (a - b) := by
        rw [← Real.exp_add]; ring_nf
      rw [h2]
      nlinarith [Real.exp_pos b]
    have h3 : Real.exp a ≤ Real.exp b := Real.exp_le_exp.2 hab
    rw [max_eq_right hab, abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp b -
      Real.exp a), abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)]
    exact h1
  · have h1 : Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := by
      have := Real.add_one_le_exp (b - a)
      have h2 : Real.exp b = Real.exp a * Real.exp (b - a) := by
        rw [← Real.exp_add]; ring_nf
      rw [h2]
      nlinarith [Real.exp_pos a]
    have h3 : Real.exp b ≤ Real.exp a := Real.exp_le_exp.2 hab
    rw [max_eq_left hab, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp a - Real.exp b),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)]
    exact h1

/-- **The expansion bound** (eqs. (A.31)–(A.35), (A.36)): let `a, b` be pair factors and
`ψ` one-body factors on a set of `k` labels with `0 ≤ a_ij, b_ij ≤ W`, `0 ≤ ψ_i ≤ Ψ`
(`W, Ψ ≥ 1`), `|a_ij - b_ij| ≤ K₁ (ρ_i + ρ_j)` and `|ψ_i - 1| ≤ K₂ ρ_i` with `ρ ≥ 0`. Then
`|(∏∏ a)(∏ ψ) - ∏∏ b| ≤ W^{k²} Ψ^k (2k K₁ + K₂) ∑_i ρ_i`. -/
theorem abs_pairs_mul_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → ι → ℝ}
    {ψ ρ : ι → ℝ} {W Ψ K₁ K₂ : ℝ} (hW : 1 ≤ W) (hΨ : 1 ≤ Ψ) (hK₁ : 0 ≤ K₁)
    (ha0 : ∀ i j, 0 ≤ a i j) (haW : ∀ i j, a i j ≤ W) (hb0 : ∀ i j, 0 ≤ b i j)
    (hbW : ∀ i j, b i j ≤ W) (hψ0 : ∀ i, 0 ≤ ψ i) (hψΨ : ∀ i, ψ i ≤ Ψ) (hρ : ∀ i, 0 ≤ ρ i)
    (hab : ∀ i j, |a i j - b i j| ≤ K₁ * (ρ i + ρ j)) (hψ : ∀ i, |ψ i - 1| ≤ K₂ * ρ i) :
    |(∏ i, ∏ j, a i j) * ∏ i, ψ i - ∏ i, ∏ j, b i j| ≤
      W ^ (Fintype.card ι * Fintype.card ι) * Ψ ^ Fintype.card ι *
        (2 * Fintype.card ι * K₁ + K₂) * ∑ i, ρ i := by
  set k := Fintype.card ι
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hΨ0 : 0 ≤ Ψ := zero_le_one.trans hΨ
  -- the pair products as products over `ι × ι`
  have hA : ∏ i, ∏ j, a i j = ∏ p ∈ (univ : Finset (ι × ι)), a p.1 p.2 := by
    rw [← univ_product_univ, prod_product]
  have hB : ∏ i, ∏ j, b i j = ∏ p ∈ (univ : Finset (ι × ι)), b p.1 p.2 := by
    rw [← univ_product_univ, prod_product]
  have hcard : (univ : Finset (ι × ι)).card = k * k := by
    rw [card_univ, Fintype.card_prod]
  have hpairs : |∏ i, ∏ j, a i j - ∏ i, ∏ j, b i j| ≤
      W ^ (k * k) * ∑ p ∈ (univ : Finset (ι × ι)), |a p.1 p.2 - b p.1 p.2| := by
    rw [hA, hB, ← hcard]
    exact abs_prod_sub_prod_le _ hW (fun p _ => ha0 _ _) (fun p _ => haW _ _)
      (fun p _ => hb0 _ _) (fun p _ => hbW _ _)
  have hsum_pairs : ∑ p ∈ (univ : Finset (ι × ι)), |a p.1 p.2 - b p.1 p.2| ≤
      2 * k * K₁ * ∑ i, ρ i := by
    calc ∑ p ∈ (univ : Finset (ι × ι)), |a p.1 p.2 - b p.1 p.2|
        ≤ ∑ p ∈ (univ : Finset (ι × ι)), K₁ * (ρ p.1 + ρ p.2) :=
          sum_le_sum fun p _ => hab _ _
      _ = 2 * k * K₁ * ∑ i, ρ i := by
          rw [← univ_product_univ, sum_product]
          simp only [mul_add, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
          rw [show (k : ℝ) = Fintype.card ι from rfl]
          ring
  have hψprod : |∏ i, ψ i - ∏ _i : ι, (1 : ℝ)| ≤ Ψ ^ k * ∑ i, |ψ i - 1| :=
    abs_prod_sub_prod_le _ hΨ (fun i _ => hψ0 i) (fun i _ => hψΨ i) (fun _ _ => zero_le_one)
      (fun _ _ => hΨ)
  rw [prod_const_one] at hψprod
  have hψsum : ∑ i, |ψ i - 1| ≤ K₂ * ∑ i, ρ i := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => hψ i
  have hPa0 : 0 ≤ ∏ i, ∏ j, a i j := prod_nonneg fun i _ => prod_nonneg fun j _ => ha0 i j
  have hPb0 : 0 ≤ ∏ i, ∏ j, b i j := prod_nonneg fun i _ => prod_nonneg fun j _ => hb0 i j
  have hPb : ∏ i, ∏ j, b i j ≤ W ^ (k * k) := by
    rw [hB, ← hcard]
    calc ∏ p ∈ (univ : Finset (ι × ι)), b p.1 p.2 ≤ ∏ _p ∈ (univ : Finset (ι × ι)), W :=
          prod_le_prod₀ (fun p _ => hb0 _ _) fun p _ => hbW _ _
      _ = W ^ (univ : Finset (ι × ι)).card := prod_const W
  have hPψ0 : 0 ≤ ∏ i, ψ i := prod_nonneg fun i _ => hψ0 i
  have hPψ : ∏ i, ψ i ≤ Ψ ^ k := by
    calc ∏ i, ψ i ≤ ∏ _i : ι, Ψ := prod_le_prod₀ (fun i _ => hψ0 i) fun i _ => hψΨ i
      _ = Ψ ^ k := by rw [prod_const, card_univ]
  have hρ0 : 0 ≤ ∑ i, ρ i := sum_nonneg fun i _ => hρ i
  have hsplit : (∏ i, ∏ j, a i j) * ∏ i, ψ i - ∏ i, ∏ j, b i j =
      (∏ i, ∏ j, a i j - ∏ i, ∏ j, b i j) * ∏ i, ψ i +
        (∏ i, ∏ j, b i j) * (∏ i, ψ i - 1) := by ring
  have hWk : 1 ≤ W ^ (k * k) := one_le_pow₀ hW
  have hΨk : 1 ≤ Ψ ^ k := one_le_pow₀ hΨ
  rw [hsplit]
  calc |(∏ i, ∏ j, a i j - ∏ i, ∏ j, b i j) * ∏ i, ψ i + (∏ i, ∏ j, b i j) * (∏ i, ψ i - 1)|
      ≤ |∏ i, ∏ j, a i j - ∏ i, ∏ j, b i j| * ∏ i, ψ i +
          (∏ i, ∏ j, b i j) * |∏ i, ψ i - 1| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hPψ0, abs_of_nonneg hPb0]
    _ ≤ (W ^ (k * k) * (2 * k * K₁ * ∑ i, ρ i)) * Ψ ^ k +
          W ^ (k * k) * (Ψ ^ k * (K₂ * ∑ i, ρ i)) := by
        gcongr
        · exact hpairs.trans (mul_le_mul_of_nonneg_left hsum_pairs (by positivity))
        · exact hψprod.trans (mul_le_mul_of_nonneg_left hψsum (by positivity))
    _ = W ^ (k * k) * Ψ ^ k * (2 * k * K₁ + K₂) * ∑ i, ρ i := by ring

end GeneralExpansion

end MultipoleBKT

end
