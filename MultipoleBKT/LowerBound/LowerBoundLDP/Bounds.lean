/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.Counting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proposition 4.62: elementary estimates

Elementary estimates of the proof of Proposition 4.62 (Section 4.20), stated for arbitrary real data:

* the block weights `u(S) = λ^{-2(|S|-1)}/N` (`blockWeight`): under the assumption (4.22) on the
  block profile of `π`, `∑_{S ∈ π} u(S) ≤ p (1 + ε₀^{-α})` (`sum_blockWeight_le`), and
  `∑_{Y ⊂ π} ∏_{S ∈ Y} u(S) ≤ exp ∑_{S ∈ π} u(S)` (`sum_powerset_prod_le_exp`). This is the paper's
  "counting block profiles with (4.22)" (proof of Proposition 4.62): for a cluster `X` with `m` blocks and
  `|V_X| = k`, `N ∏_{S ∈ X} u(S) = λ^{-2(k-m)} N^{1-m}` (`mul_prod_blockWeight_mul_pow`);
* `log (1 - a) ≥ -2a` for `0 ≤ a ≤ 1/2` (`neg_two_mul_le_log_one_sub`);
* the product of the block partition functions (eq. (4.143), proof of Proposition 4.62): from
  `|𝖬^-(S) - 𝖬(S)| ≤ C N^{1-|S|} R̄^{-2}` and `𝖬(S) ≥ λ^{2(|S|-1)}/(C' N^{|S|-1})`,
  `log ∏ 𝖬^-(S) ≥ log ∏ 𝖬(S) - 2 C C' R̄^{-2} N ∑_{S ∈ π} u(S)` (`log_prod_ge_of_abs_sub_le`);
* the normalization (eq. (4.11), proof of Proposition 4.62): from
  `|C_{β,λ,ε₀} - λ^{2-β} 𝒵_β| ≤ λ^{2-β} η`, `log C_{β,λ,ε₀} ≥ (2-β) log λ + log 𝒵_β - 2η/𝒵_β`
  (`log_ge_of_abs_sub_le`).
-/

@[expose] public section

namespace MultipoleBKT

namespace LowerBoundLDP

open Finset PropFiveFortyFive

/-! ### Block weights -/

/-- The block weight `u(S) = λ^{-2(|S|-1)} / N`. -/
noncomputable def blockWeight (lam : ℝ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ((lam ^ 2) ^ (S.card - 1))⁻¹ / N

theorem blockWeight_nonneg {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (S : Finset ℕ) :
    0 ≤ blockWeight lam N S := by
  unfold blockWeight
  positivity

/-- `∑_{Y ⊂ π} ∏_{S ∈ Y} u(S) = ∏_{S ∈ π} (1 + u(S)) ≤ exp ∑_{S ∈ π} u(S)` for `u ≥ 0`. -/
theorem sum_powerset_prod_le_exp {α : Type*} (π : Finset α) {u : α → ℝ} (hu : ∀ S, 0 ≤ u S) :
    ∑ Y ∈ π.powerset, ∏ S ∈ Y, u S ≤ Real.exp (∑ S ∈ π, u S) := by
  rw [← prod_one_add, Real.exp_sum]
  exact prod_le_prod₀ (fun S _ => by linarith [hu S]) fun S _ => by
    linarith [Real.add_one_le_exp (u S)]

/-- **Counting with (4.22)**: if `#_k π ≤ A N λ^{2(k-1)}` for `2 ≤ k ≤ p`, then
`∑_{S ∈ π} u(S) ≤ p (1 + A)` for `π ∈ 𝚷_p([N])`. -/
theorem sum_blockWeight_le {N p : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ : π ∈ boundedBlockPartitions N p) {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A)
    (hn : ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ((π.filter fun S => S.card = k).card : ℝ) ≤ A * N * lam ^ (2 * (k - 1))) :
    ∑ S ∈ π, blockWeight lam N S ≤ p * (1 + A) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ1 := card_mem_Icc_of_mem_boundedBlockPartitions hπ
  have hsum := sum_card_eq_sum_blockCount hπ1 (fun k => ((lam ^ 2) ^ (k - 1))⁻¹ / (N : ℝ))
  have hπN : (π.card : ℝ) ≤ N := by
    have h := sum_mul_blockCount_of_mem_boundedBlockPartitions hπ
    rw [← sum_blockCount hπ1]
    have : ∑ i : Fin p, blockCount p π i ≤ N := by
      rw [← h]
      exact sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact_mod_cast this
  unfold blockWeight
  rw [hsum]
  calc ∑ i : Fin p, blockCount p π i • (((lam ^ 2) ^ ((i : ℕ) + 1 - 1))⁻¹ / (N : ℝ))
      ≤ ∑ _i : Fin p, (1 + A) := by
        refine sum_le_sum fun i _ => ?_
        rw [nsmul_eq_mul, Nat.add_sub_cancel]
        rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
        · rw [h0, pow_zero, inv_one]
          have hb : (blockCount p π i : ℝ) ≤ N :=
            (by exact_mod_cast blockCount_le_card p π i : (blockCount p π i : ℝ) ≤ π.card).trans hπN
          calc (blockCount p π i : ℝ) * (1 / N) ≤ N * (1 / N) :=
                mul_le_mul_of_nonneg_right hb (by positivity)
            _ = 1 := by field_simp
            _ ≤ 1 + A := by linarith
        · have hk := hn ((i : ℕ) + 1) (by omega) (by omega)
          rw [Nat.add_sub_cancel, pow_mul] at hk
          have hb : (blockCount p π i : ℝ) ≤ A * N * (lam ^ 2) ^ (i : ℕ) := hk
          have hl : (0 : ℝ) < (lam ^ 2) ^ (i : ℕ) := by positivity
          calc (blockCount p π i : ℝ) * (((lam ^ 2) ^ (i : ℕ))⁻¹ / N)
              ≤ A * N * (lam ^ 2) ^ (i : ℕ) * (((lam ^ 2) ^ (i : ℕ))⁻¹ / N) :=
                mul_le_mul_of_nonneg_right hb (by positivity)
            _ = A := by field_simp
            _ ≤ 1 + A := by linarith
    _ = p * (1 + A) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- For a subpartition `X` with `m ≥ 1` blocks and `|V_X| = k`,
`N ∏_{S ∈ X} u(S) · λ^{2(k-1)} = (λ²/N)^{m-1}`. -/
theorem mul_prod_blockWeight_mul_pow {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (hX1 : 1 ≤ X.card) {lam : ℝ} (hlam : 0 < lam) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * (∏ S ∈ X, blockWeight lam N S) * (lam ^ 2) ^ ((X.biUnion id).card - 1) =
      (lam ^ 2 / N) ^ (X.card - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ S ∈ X, (S.card - 1) + X.card = (X.biUnion id).card := by
    rw [card_biUnion fun S hS T hT hST => hX.2 hS hT hST, card_eq_sum_ones X, ← sum_add_distrib]
    refine sum_congr rfl fun S hS => ?_
    have := card_pos.2 (hX.1 S hS)
    simp only [id]
    omega
  set k := (X.biUnion id).card
  set m := X.card
  have hprod : ∏ S ∈ X, blockWeight lam N S =
      ((lam ^ 2) ^ (∑ S ∈ X, (S.card - 1)))⁻¹ / (N : ℝ) ^ m := by
    unfold blockWeight
    rw [prod_div_distrib, prod_inv_distrib, prod_pow_eq_pow_sum, prod_const]
  rw [hprod]
  have hk : k - 1 = ∑ S ∈ X, (S.card - 1) + (m - 1) := by omega
  rw [hk, pow_add, div_pow]
  have hm : (N : ℝ) ^ m = N * N ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hm]
  have h1 : (0 : ℝ) < (lam ^ 2) ^ (∑ S ∈ X, (S.card - 1)) := by positivity
  field_simp

/-- A lower bound on a product of block partition functions:
if `𝖬(S) ≥ λ^{2(|S|-1)}/(C N^{|S|-1})` with `C ≥ 1`, then
`1/(∏_{S ∈ X} 𝖬(S) N^{k-1}) ≤ C^p N ∏_{S ∈ X} u(S)` for a subpartition `X` with at most `p`
blocks and `|V_X| = k`. -/
theorem inv_prod_mul_pow_le {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (hX1 : 1 ≤ X.card)
    {p : ℕ} (hXp : X.card ≤ p) {lam C : ℝ} (hlam : 0 < lam) (hC : 1 ≤ C) {N : ℕ} (hN : 1 ≤ N)
    {Mz : Finset ℕ → ℝ}
    (hlow : ∀ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (C * (N : ℝ) ^ (S.card - 1)) ≤ Mz S) :
    1 / ((∏ S ∈ X, Mz S) * (N : ℝ) ^ ((X.biUnion id).card - 1)) ≤
      C ^ p * (N * ∏ S ∈ X, blockWeight lam N S) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hC0 : 0 < C := by linarith
  have hlowpos : ∀ S ∈ X, 0 < (lam ^ 2) ^ (S.card - 1) / (C * (N : ℝ) ^ (S.card - 1)) :=
    fun S _ => by positivity
  have hP : ∏ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (C * (N : ℝ) ^ (S.card - 1)) ≤ ∏ S ∈ X, Mz S :=
    prod_le_prod₀ (fun S hS => (hlowpos S hS).le) hlow
  have hPpos : 0 < ∏ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (C * (N : ℝ) ^ (S.card - 1)) :=
    prod_pos hlowpos
  -- the product of the lower bounds
  have hS : ∀ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (C * (N : ℝ) ^ (S.card - 1)) =
      (C * N * (N : ℝ) ^ (S.card - 1) * blockWeight lam N S)⁻¹ := by
    intro S _
    unfold blockWeight
    have : (0 : ℝ) < (lam ^ 2) ^ (S.card - 1) := by positivity
    field_simp
  have hlowprod : ∏ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (C * (N : ℝ) ^ (S.card - 1)) =
      (C ^ X.card * (N : ℝ) ^ X.card * (N : ℝ) ^ (∑ S ∈ X, (S.card - 1)) *
        ∏ S ∈ X, blockWeight lam N S)⁻¹ := by
    rw [prod_congr rfl hS, prod_inv_distrib, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib,
      prod_const, prod_const, prod_pow_eq_pow_sum]
  have hsum : ∑ S ∈ X, (S.card - 1) + X.card = (X.biUnion id).card := by
    rw [card_biUnion fun S hS T hT hST => hX.2 hS hT hST, card_eq_sum_ones X, ← sum_add_distrib]
    refine sum_congr rfl fun S hS => ?_
    have := card_pos.2 (hX.1 S hS)
    simp only [id]
    omega
  have hk : (X.biUnion id).card - 1 = ∑ S ∈ X, (S.card - 1) + (X.card - 1) := by omega
  have hB : 0 < ∏ S ∈ X, blockWeight lam N S := by
    refine prod_pos fun S _ => ?_
    unfold blockWeight
    positivity
  have hCp : C ^ X.card ≤ C ^ p := pow_le_pow_right₀ hC hXp
  calc 1 / ((∏ S ∈ X, Mz S) * (N : ℝ) ^ ((X.biUnion id).card - 1))
      ≤ 1 / ((∏ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (C * (N : ℝ) ^ (S.card - 1))) *
          (N : ℝ) ^ ((X.biUnion id).card - 1)) :=
        one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hP (by positivity))
    _ = C ^ X.card * (N * ∏ S ∈ X, blockWeight lam N S) := by
        rw [hlowprod, hk, pow_add]
        have hm : (N : ℝ) ^ X.card = N * N ^ (X.card - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hm]
        field_simp
    _ ≤ C ^ p * (N * ∏ S ∈ X, blockWeight lam N S) :=
        mul_le_mul_of_nonneg_right hCp (by positivity)

/-! ### Logarithms -/

/-- `log (1 - a) ≥ -2a` for `0 ≤ a ≤ 1/2`. -/
theorem neg_two_mul_le_log_one_sub {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) :
    -2 * a ≤ Real.log (1 - a) := by
  have h1 : 0 < 1 - a := by linarith
  have h := Real.one_sub_inv_le_log_of_pos h1
  have h2 : -2 * a ≤ 1 - (1 - a)⁻¹ := by
    rw [show 1 - (1 - a)⁻¹ = -(a / (1 - a)) by field_simp; ring]
    rw [neg_mul, neg_le_neg_iff, div_le_iff₀ h1]
    nlinarith
  linarith

/-- **The product of the block partition functions** (eq. (4.143), proof of Proposition 4.62): if
`|𝖬^-(S) - 𝖬(S)| ≤ C_M N^{1-|S|} R`, `𝖬(S) ≥ λ^{2(|S|-1)}/(C N^{|S|-1})` and
`C_M C R ≤ λ^{2(p-1)}/2`, then `∏ 𝖬^-(S) > 0` and
`log ∏_{S ∈ π} 𝖬(S) - 2 C_M C R N ∑_{S ∈ π} u(S) ≤ log ∏_{S ∈ π} 𝖬^-(S)`. -/
theorem log_prod_ge_of_abs_sub_le {π : Finset (Finset ℕ)} {p N : ℕ} (hN : 1 ≤ N)
    (hπ : ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ p) {lam CM C R : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hC : 0 < C) (hCM : 0 ≤ CM) (hR : 0 ≤ R) {Mm Mz : Finset ℕ → ℝ}
    (hdiff : ∀ S ∈ π, |Mm S - Mz S| ≤ CM / (N : ℝ) ^ (S.card - 1) * R)
    (hlow : ∀ S ∈ π, (lam ^ 2) ^ (S.card - 1) / (C * (N : ℝ) ^ (S.card - 1)) ≤ Mz S)
    (hsmall : CM * C * R ≤ (lam ^ 2) ^ (p - 1) / 2) :
    0 < ∏ S ∈ π, Mm S ∧
      Real.log (∏ S ∈ π, Mz S) - 2 * (CM * C * R) * N * ∑ S ∈ π, blockWeight lam N S ≤
        Real.log (∏ S ∈ π, Mm S) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hl2 : 0 < lam ^ 2 := by positivity
  have hl21 : lam ^ 2 ≤ 1 := pow_le_one₀ hlam.le hlam1
  -- `a_S = C_M C R λ^{-2(|S|-1)} = C_M C R N u(S) ≤ 1/2`
  set a : Finset ℕ → ℝ := fun S => CM * C * R * ((lam ^ 2) ^ (S.card - 1))⁻¹ with ha_def
  have ha0 : ∀ S, 0 ≤ a S := fun S => by simp only [ha_def]; positivity
  have ha : ∀ S ∈ π, a S ≤ 1 / 2 := by
    intro S hS
    have hpow : (lam ^ 2) ^ (p - 1) ≤ (lam ^ 2) ^ (S.card - 1) :=
      pow_le_pow_of_le_one hl2.le hl21 (by have := (hπ S hS).2; omega)
    have hpos : 0 < (lam ^ 2) ^ (S.card - 1) := by positivity
    simp only [ha_def]
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  have hMz : ∀ S ∈ π, 0 < Mz S := fun S hS =>
    lt_of_lt_of_le (by positivity) (hlow S hS)
  have hMm : ∀ S ∈ π, Mz S * (1 - a S) ≤ Mm S := by
    intro S hS
    have h1 := hdiff S hS
    have h2 := hlow S hS
    have hpos : 0 < (lam ^ 2) ^ (S.card - 1) := by positivity
    have hNk : (0 : ℝ) < (N : ℝ) ^ (S.card - 1) := by positivity
    have key : CM / (N : ℝ) ^ (S.card - 1) * R ≤ a S * Mz S := by
      calc CM / (N : ℝ) ^ (S.card - 1) * R
          = a S * ((lam ^ 2) ^ (S.card - 1) / (C * (N : ℝ) ^ (S.card - 1))) := by
            simp only [ha_def]
            field_simp
        _ ≤ a S * Mz S := mul_le_mul_of_nonneg_left h2 (ha0 S)
    rw [abs_le] at h1
    nlinarith [h1.1]
  have hMmpos : ∀ S ∈ π, 0 < Mm S := fun S hS =>
    lt_of_lt_of_le (mul_pos (hMz S hS) (by linarith [ha S hS])) (hMm S hS)
  refine ⟨prod_pos hMmpos, ?_⟩
  rw [Real.log_prod (fun S hS => (hMz S hS).ne'), Real.log_prod (fun S hS => (hMmpos S hS).ne')]
  have hterm : ∀ S ∈ π, Real.log (Mz S) - 2 * a S ≤ Real.log (Mm S) := by
    intro S hS
    have h1 : Real.log (Mz S * (1 - a S)) ≤ Real.log (Mm S) :=
      Real.log_le_log (mul_pos (hMz S hS) (by linarith [ha S hS])) (hMm S hS)
    rw [Real.log_mul (hMz S hS).ne' (by linarith [ha S hS])] at h1
    have h2 := neg_two_mul_le_log_one_sub (ha0 S) (ha S hS)
    linarith
  have hsum : ∑ S ∈ π, a S = CM * C * R * N * ∑ S ∈ π, blockWeight lam N S := by
    rw [mul_sum]
    refine sum_congr rfl fun S _ => ?_
    simp only [ha_def, blockWeight]
    field_simp
  calc ∑ S ∈ π, Real.log (Mz S) - 2 * (CM * C * R) * N * ∑ S ∈ π, blockWeight lam N S
      = ∑ S ∈ π, (Real.log (Mz S) - 2 * a S) := by
        rw [sum_sub_distrib, ← mul_sum, hsum]
        ring
    _ ≤ ∑ S ∈ π, Real.log (Mm S) := sum_le_sum hterm

/-- **The normalization** (eq. (4.11)): if `|C - λ^{2-β} 𝒵| ≤ λ^{2-β} η` with `𝒵 > 0`,
`0 ≤ η ≤ 𝒵/2`, then `C > 0` and `(2-β) log λ + log 𝒵 - 2η/𝒵 ≤ log C`. -/
theorem log_ge_of_abs_sub_le {Cn lam β Z η : ℝ} (hlam : 0 < lam) (hZ : 0 < Z) (hη : 0 ≤ η)
    (hηZ : η ≤ Z / 2) (h : |Cn - lam ^ (2 - β) * Z| ≤ lam ^ (2 - β) * η) :
    0 < Cn ∧ (2 - β) * Real.log lam + Real.log Z - 2 * η / Z ≤ Real.log Cn := by
  have hl : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  set a := η / Z with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha : a ≤ 1 / 2 := by rw [ha_def, div_le_iff₀ hZ]; linarith
  have hlow : lam ^ (2 - β) * Z * (1 - a) ≤ Cn := by
    rw [abs_le] at h
    have : lam ^ (2 - β) * Z * (1 - a) = lam ^ (2 - β) * Z - lam ^ (2 - β) * η := by
      rw [ha_def]
      field_simp
    linarith [h.1]
  have hpos : 0 < lam ^ (2 - β) * Z * (1 - a) := by
    have : 0 < 1 - a := by linarith
    positivity
  refine ⟨hpos.trans_le hlow, ?_⟩
  have h1 := Real.log_le_log hpos hlow
  rw [Real.log_mul (by positivity) (by linarith), Real.log_mul hl.ne' hZ.ne',
    Real.log_rpow hlam] at h1
  have h2 := neg_two_mul_le_log_one_sub ha0 ha
  have h3 : 2 * η / Z = 2 * a := by rw [ha_def]; ring
  linarith

end LowerBoundLDP

end MultipoleBKT

end
