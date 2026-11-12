/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.Weighted
public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Levels

/-!
# The two logarithmic tree sums

(A.65) and
(A.66) in the proof of Lemma 4.58. The power of each group cardinality remains
visible. All other coefficients grow exponentially in the number of blocks.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open Finset Multipole SetPartition
open scoped Classical

/-- Absorb the logarithmic moment after weighted Cayley and arithmetic-geometric mean.
This is the last inequality of the display preceding (A.65). -/
theorem cayley_moment_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) {q : ℕ} (hq : 2 ≤ q) :
    x ^ (2 * q - 2) / (q : ℝ) ^ q ≤
      max (4 / a ^ 2) 1 ^ q * (q : ℝ) ^ q * Real.exp (a * x) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqpos : (0 : ℝ) < q := by linarith
  have hf : ((q - 1).factorial : ℝ) ≤ (q : ℝ) ^ q := by
    calc
      _ ≤ ((q - 1 : ℕ) : ℝ) ^ (q - 1) := by exact_mod_cast Nat.factorial_le_pow (q - 1)
      _ ≤ (q : ℝ) ^ (q - 1) := pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.sub_le q 1) _
      _ ≤ _ := pow_le_pow_right₀ hqr (Nat.sub_le _ _)
  have hD : (4 / a ^ 2) ^ (q - 1) ≤ max (4 / a ^ 2) 1 ^ q :=
    (pow_le_pow_left₀ (by positivity) (le_max_left _ _) _).trans
      (pow_le_pow_right₀ (le_max_right _ _) (Nat.sub_le _ _))
  have hp := pow_two_mul_le_exp ha hx (q - 1)
  rw [show 2 * (q - 1) = 2 * q - 2 by omega] at hp
  rw [div_le_iff₀ (pow_pos hqpos _)]
  calc
    _ ≤ (4 / a ^ 2) ^ (q - 1) * ((q - 1).factorial : ℝ) ^ 2 * Real.exp (a * x) := hp
    _ ≤ max (4 / a ^ 2) 1 ^ q * ((q : ℝ) ^ q) ^ 2 * Real.exp (a * x) := by gcongr
    _ = _ := by ring

/-- The weighted tree bound with the literal cardinality factor `q^q`.
Apply it separately to each odd group and to the coarse even partition. -/
theorem sum_tree_weights_le {Q : Finset (Finset ℕ)} (hQ : IsSubpartition Q)
    (𝒯 : Finset (Finset (ℕ × ℕ))) (h𝒯 : 𝒯 ⊆ relTreePairs₀ Q)
    (L : ℕ → ℝ) (hL : ∀ i, 0 ≤ L i) (w : ℕ × ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p ∈ interPairs Q, w p ≤ L p.1 * L p.2) {a : ℝ} (ha : 0 < a) :
    (∑ T ∈ 𝒯, ∏ p ∈ T, w p) ≤
      max (4 / a ^ 2) 1 ^ Q.card * (Q.card : ℝ) ^ Q.card *
        Real.exp (a * ∑ i ∈ Q.biUnion id, L i) := by
  have hS : 0 ≤ ∑ i ∈ Q.biUnion id, L i := sum_nonneg fun i _ => hL i
  by_cases hq : 2 ≤ Q.card
  · calc
      _ ≤ ∑ T ∈ relTreePairs₀ Q, ∏ p ∈ T, L p.1 * L p.2 := by
        refine (sum_le_sum fun T hT => prod_le_prod₀ (fun p _ => hw0 p)
          (fun p hp => hw p (subset_interPairs_of_mem_relTreePairs₀ hQ (h𝒯 hT) hp))).trans ?_
        exact sum_le_sum_of_subset_of_nonneg h𝒯 fun T _ _ =>
          prod_nonneg fun p _ => mul_nonneg (hL _) (hL _)
      _ ≤ (∑ i ∈ Q.biUnion id, L i) ^ (2 * Q.card - 2) / (Q.card : ℝ) ^ Q.card :=
        relative_weighted_amgm hQ hq L hL
      _ ≤ _ := cayley_moment_le ha hS hq
  · have hT0 : ∀ T ∈ 𝒯, T = ∅ := by
      intro T hT
      have := card_add_one_of_mem_relTreePairs₀ hQ (h𝒯 hT)
      exact card_eq_zero.mp (by omega)
    have hle : (∑ T ∈ 𝒯, ∏ p ∈ T, w p) ≤ 1 := by
      calc
        _ ≤ ∑ T ∈ ({∅} : Finset (Finset (ℕ × ℕ))), ∏ p ∈ T, w p :=
          sum_le_sum_of_subset_of_nonneg (fun T hT => mem_singleton.mpr (hT0 T hT))
            (fun T _ _ => prod_nonneg fun p _ => hw0 p)
        _ = 1 := by simp
    refine hle.trans ?_
    have hqq : (1 : ℝ) ≤ (Q.card : ℝ) ^ Q.card := by
      rcases Nat.eq_zero_or_pos Q.card with h | h
      · simp [h]
      · exact one_le_pow₀ (by exact_mod_cast h)
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_right _ _)) hqq)
      (Real.one_le_exp (mul_nonneg ha.le hS))

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
