/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.BoundedLowerEps.Bonds

/-!
# Block weights in the grouped lower reduction

Proposition 4.23, (4.73). Bound the stable interaction and
one-body weights while retaining the connected-block indicators.
-/

@[expose] public section

namespace MultipoleBKT

namespace BoundedLowerEps

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits SmallIntegral Hierarchical Parity

variable {β lam M : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ} {X : Finset (Finset ℕ)}

/-- `∑_{S ∈ X} |S| = |V_X|` for a subpartition. -/
theorem sum_card_eq (hX : IsSubpartition X) : ∑ S ∈ X, S.card = (X.biUnion id).card := by
  rw [card_biUnion fun S hS T hT hST => hX.2 hS hT hST]
  rfl

/-- `∑_{S ∈ X} |S|² ≤ |V_X|²` for a subpartition. -/
theorem sum_card_sq_le (hX : IsSubpartition X) : ∑ S ∈ X, S.card ^ 2 ≤ (X.biUnion id).card ^ 2 := by
  rw [← sum_card_eq hX, sq, sum_mul]
  refine sum_le_sum fun S hS => ?_
  rw [sq]
  exact Nat.mul_le_mul_left _ (single_le_sum (f := fun S => S.card) (fun _ _ => Nat.zero_le _) hS)

open scoped Classical in
/-- The block weights on the support: `∏_{B ∈ X} bw_B ≤ W_b^{|V_X|²} Ψ^{|V_X|}`, and the product
vanishes unless every block is near-connected. -/
theorem prod_blockWeightOf_le (hX : IsSubpartition X) {K : Set (ℂ × ℂ)} (hψ0 : ∀ d, 0 ≤ ψ d)
    {Wb Ψ : ℝ} (hWb : 1 ≤ Wb) (hΨ : 1 ≤ Ψ)
    (hstab : ∀ d ∈ K, ∀ e ∈ K, stableWeight β w d e ≤ Wb) (hψb : ∀ d ∈ K, ψ d ≤ Ψ)
    (c : ℕ → ℂ × ℂ) (hc : ∀ i ∈ X.biUnion id, c i ∈ K) :
    ∏ B ∈ X, blockWeightOf β w ψ M lam B c ≤
      Wb ^ ((X.biUnion id).card ^ 2) * Ψ ^ (X.biUnion id).card := by
  have hB : ∀ B ∈ X, blockWeightOf β w ψ M lam B c ≤ Wb ^ (B.card ^ 2) * Ψ ^ B.card := by
    intro B hB
    have hBV : ∀ i ∈ B, c i ∈ K := fun i hi => hc i (mem_biUnion.2 ⟨B, hB, hi⟩)
    unfold blockWeightOf
    have hp : ∏ p ∈ pairsOn B, stableWeight β w (c p.1) (c p.2) ≤ Wb ^ (B.card ^ 2) := by
      calc ∏ p ∈ pairsOn B, stableWeight β w (c p.1) (c p.2) ≤ ∏ _p ∈ pairsOn B, Wb :=
            prod_le_prod₀ (fun p _ => stableWeight_nonneg β w _ _) fun p hp =>
              hstab _ (hBV _ (mem_pairsOn.1 hp).1) _ (hBV _ (mem_pairsOn.1 hp).2.1)
        _ = Wb ^ (pairsOn B).card := prod_const _
        _ ≤ Wb ^ (B.card ^ 2) := by
            refine pow_le_pow_right₀ hWb ?_
            calc (pairsOn B).card ≤ (B ×ˢ B).card := card_filter_le _ _
              _ = B.card ^ 2 := by rw [card_product, sq]
    have hq : ∏ i ∈ B, ψ (c i) ≤ Ψ ^ B.card := by
      calc ∏ i ∈ B, ψ (c i) ≤ ∏ _i ∈ B, Ψ := prod_le_prod₀ (fun i _ => hψ0 _) fun i hi =>
            hψb _ (hBV i hi)
        _ = Ψ ^ B.card := prod_const _
    have hind : (if ConnOn B (linkedPairs M lam c B) then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have hind0 : (0 : ℝ) ≤ if ConnOn B (linkedPairs M lam c B) then 1 else 0 := by
      split_ifs <;> norm_num
    calc (if ConnOn B (linkedPairs M lam c B) then (1 : ℝ) else 0) *
          (∏ p ∈ pairsOn B, stableWeight β w (c p.1) (c p.2)) * ∏ i ∈ B, ψ (c i)
        ≤ 1 * Wb ^ (B.card ^ 2) * Ψ ^ B.card :=
          mul_le_mul (mul_le_mul hind hp (prod_nonneg fun p _ => stableWeight_nonneg β w _ _)
            zero_le_one) hq (prod_nonneg fun i _ => hψ0 _)
            (mul_nonneg zero_le_one (pow_nonneg (zero_le_one.trans hWb) _))
      _ = Wb ^ (B.card ^ 2) * Ψ ^ B.card := by ring
  calc ∏ B ∈ X, blockWeightOf β w ψ M lam B c ≤ ∏ B ∈ X, (Wb ^ (B.card ^ 2) * Ψ ^ B.card) :=
        prod_le_prod₀ (fun B _ => blockWeightOf_nonneg M lam hψ0 B c) hB
    _ = Wb ^ (∑ B ∈ X, B.card ^ 2) * Ψ ^ (∑ B ∈ X, B.card) := by
        rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum]
    _ ≤ _ := by
        rw [sum_card_eq hX]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hWb (sum_card_sq_le hX))
          (pow_nonneg (zero_le_one.trans hΨ) _)

end BoundedLowerEps

end MultipoleBKT

end
