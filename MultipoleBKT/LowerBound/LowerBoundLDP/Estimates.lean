/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.LowerBoundLDP.Bounds
public import MultipoleBKT.LowerBound.LowerBoundLDP.ClusterLog
public import MultipoleBKT.LowerBound.LowerBoundLDP.Inputs
public import MultipoleBKT.Limits.MultipoleLimit

/-!
# Proposition 4.62: the estimates at fixed `N`

The estimates of the proof of Proposition 4.62 at a fixed `N` and a fixed
partition `π ∈ 𝚷_p([N])` satisfying (4.22) (`#_k π ≤ A N λ^{2(k-1)}`, `A = ε₀^{-α(β)}`), from the bounds of Propositions 4.23 and 4.24
taken as hypotheses:

* `log_minusPartitionFunction_ge` ((4.143), proof of Proposition 4.62): from the direct singleton
  estimate in the display after (4.142), (4.42) for sizes at least two and (4.38),
  `log 𝖬^-_{ε₀}(π) ≥ log ∏_{S ∈ π} 𝖬_{β,λ}(S) - 2 C_M C' p (1 + A) R̄^{-2} N`;
* `abs_minusActivity_sub_le` (the blue paragraph, proof of Proposition 4.62): from (4.44) and (4.38),
  `|𝖪^-_{ε₀}(X) - 𝖪^mult(X)| ≤ C_K C'^p R̄^{-2} N ∏_{S ∈ X} u(S)`, `u(S) = λ^{-2(|S|-1)}/N`;
* `sum_retained_diff_le` (proof of Proposition 4.62, `D ≤ C N R̄^{-2}`): summing over the retained
  subfamilies with (4.22);
* `abs_minusActivity_le` (proof of Proposition 4.62, `w(X) ≤ C (λ²/N)^{|X|-1}`): from `R̄^{-2} ≤ λ^{2(p-1)}`.
-/

@[expose] public section

namespace MultipoleBKT

namespace LowerBoundLDP

open Finset Hierarchical PropFiveFortyFive

variable {χ : ℂ → ℝ} {p₀ N p : ℕ} {β lam M ε₀ L : ℝ}

/-- `𝖬^-_{ε₀}(π) = ∏_{S ∈ π} 𝖬^-_{ε₀}({S})`. -/
theorem minusPartitionFunction_eq_prod (π : Finset (Finset ℕ)) :
    minusPartitionFunction χ N p₀ β lam M ε₀ L π =
      ∏ S ∈ π, minusPartitionFunction χ N p₀ β lam M ε₀ L {S} := by
  unfold minusPartitionFunction
  exact prod_congr rfl fun S _ => (prod_singleton _ S).symm

/-- **The product of the block partition functions** ((4.143), proof of Proposition 4.62) at fixed
`N`: combine the direct singleton estimate with (4.42) for sizes at least two into
`|𝖬^-_{ε₀}(S) - 𝖬(S)| ≤ C_M N^{1-|S|} R`, then use (4.38)
`𝖬(S) ≥ λ^{2(|S|-1)}/(C' N^{|S|-1})` for `1 ≤ |S| ≤ p`, the assumption (4.22) and
`C_M C' R ≤ λ^{2(p-1)}/2`: `𝖬^-_{ε₀}(π) > 0`, `∏_{S ∈ π} 𝖬([|S|]) > 0` and
`log ∏_{S ∈ π} 𝖬([|S|]) - 2 C_M C' p (1 + A) R N ≤ log 𝖬^-_{ε₀}(π)`. -/
theorem log_minusPartitionFunction_ge (hχ : IsMollifier χ) (hN : 1 ≤ N)
    {π : Finset (Finset ℕ)} (hπ : π ∈ boundedBlockPartitions N p) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) {CM C' R A : ℝ} (hC' : 0 < C') (hCM : 0 ≤ CM) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hn : ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ((π.filter fun S => S.card = k).card : ℝ) ≤ A * N * lam ^ (2 * (k - 1)))
    (hdiff : ∀ s, 1 ≤ s → s ≤ p → ∀ S : Finset ℕ, S.card = s →
      |minusPartitionFunction χ N p₀ β lam M ε₀ L {S} - multipolePartitionFunction χ N β lam M S| ≤
        CM / (N : ℝ) ^ (s - 1) * R)
    (hlow : ∀ S : Finset ℕ, S ⊆ Finset.range N → 1 ≤ S.card → S.card ≤ p →
      lam ^ (2 * (S.card - 1)) / (C' * (N : ℝ) ^ (S.card - 1)) ≤
        multipolePartitionFunction χ N β lam M S)
    (hsmall : CM * C' * R ≤ (lam ^ 2) ^ (p - 1) / 2) :
    0 < minusPartitionFunction χ N p₀ β lam M ε₀ L π ∧
      0 < ∏ S ∈ π, multipolePartitionFunction χ N β lam M (Finset.range S.card) ∧
      Real.log (∏ S ∈ π, multipolePartitionFunction χ N β lam M (Finset.range S.card)) -
          2 * CM * C' * (p * (1 + A)) * R * N ≤
        Real.log (minusPartitionFunction χ N p₀ β lam M ε₀ L π) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨-, -, -, hπ1⟩ := facts_of_mem_boundedBlockPartitions hN hπ
  have hsubN : ∀ S ∈ π, S ⊆ Finset.range N := fun S hS => by
    rw [← biUnion_of_mem_boundedBlockPartitions hπ]
    exact subset_biUnion_of_mem id hS
  have hcongr : ∀ S ∈ π, multipolePartitionFunction χ N β lam M (Finset.range S.card) =
      multipolePartitionFunction χ N β lam M S := fun S _ =>
    Limits.multipolePartitionFunction_congr_card hχ hlam hN (card_range _)
  have hlow' : ∀ S ∈ π, (lam ^ 2) ^ (S.card - 1) / (C' * (N : ℝ) ^ (S.card - 1)) ≤
      multipolePartitionFunction χ N β lam M S := fun S hS => by
    rw [← pow_mul]
    exact hlow S (hsubN S hS) (hπ1 S hS).1 (hπ1 S hS).2
  obtain ⟨hpos, hlog⟩ := log_prod_ge_of_abs_sub_le hN hπ1 hlam hlam1 hC' hCM hR
    (Mm := fun S => minusPartitionFunction χ N p₀ β lam M ε₀ L {S})
    (Mz := fun S => multipolePartitionFunction χ N β lam M S)
    (fun S hS => hdiff S.card (hπ1 S hS).1 (hπ1 S hS).2 S rfl) hlow' hsmall
  have hMz : 0 < ∏ S ∈ π, multipolePartitionFunction χ N β lam M S :=
    prod_pos fun S hS => lt_of_lt_of_le (by have := (hπ1 S hS).1; positivity) (hlow' S hS)
  rw [minusPartitionFunction_eq_prod, prod_congr rfl hcongr]
  refine ⟨hpos, hMz, le_trans ?_ hlog⟩
  have hU := sum_blockWeight_le hN hπ hlam hA hn
  have h0 : 0 ≤ 2 * (CM * C' * R) * N := by positivity
  have := mul_le_mul_of_nonneg_left hU h0
  linarith

/-- **The activity difference** (the blue paragraph, proof of Proposition 4.62): from (4.44)
`|𝖪^-(X) - 𝖪^0_∞(X)| ≤ C_K R / (𝖬^0_∞(X) N^{k-1})`, (4.38) with `C' ≥ 1` and
`𝖪^0_∞ = 𝖪^mult`, `|𝖪^-(X) - 𝖪^mult(X)| ≤ C_K C'^p R N ∏_{S ∈ X} u(S)` for a subpartition `X` with
at most `p` blocks. -/
theorem abs_sub_le_of_kdiff {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (hX1 : 1 ≤ X.card)
    (hXp : X.card ≤ p) (hlam : 0 < lam) (hN : 1 ≤ N) {CK C' R : ℝ} (hCK : 0 ≤ CK) (hR : 0 ≤ R)
    (hC' : 1 ≤ C') {K₁ K₂ : ℝ}
    (hdiff : |K₁ - K₂| ≤ CK * R / ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) *
      (N : ℝ) ^ ((X.biUnion id).card - 1)))
    (hlow : ∀ S ∈ X, lam ^ (2 * (S.card - 1)) / (C' * (N : ℝ) ^ (S.card - 1)) ≤
      multipolePartitionFunction χ N β lam M S) :
    |K₁ - K₂| ≤ CK * C' ^ p * R * (N * ∏ S ∈ X, blockWeight lam N S) := by
  have hlow' : ∀ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (C' * (N : ℝ) ^ (S.card - 1)) ≤
      multipolePartitionFunction χ N β lam M S := fun S hS => by
    rw [← pow_mul]
    exact hlow S hS
  have h := inv_prod_mul_pow_le hX hX1 hXp hlam hC' hN hlow'
  refine hdiff.trans ?_
  rw [div_eq_mul_one_div (CK * R)]
  calc CK * R * (1 / ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) *
        (N : ℝ) ^ ((X.biUnion id).card - 1)))
      ≤ CK * R * (C' ^ p * (N * ∏ S ∈ X, blockWeight lam N S)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = CK * C' ^ p * R * (N * ∏ S ∈ X, blockWeight lam N S) := by ring

/-- **`D ≤ C N R̄^{-2}`** (proof of Proposition 4.62): if `|K₁(X) - K₂(X)| ≤ C_d R N ∏_{S ∈ X} u(S)` on the
retained clusters and (4.22) holds, then
`∑_{X ⊂ π retained} |K₁(X) - K₂(X)| ≤ C_d R N e^{p (1 + A)}`. -/
theorem sum_retained_diff_le (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ : π ∈ boundedBlockPartitions N p) (hlam : 0 < lam) {A Cd R : ℝ} (hA : 0 ≤ A)
    (hCd : 0 ≤ Cd) (hR : 0 ≤ R)
    (hn : ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ((π.filter fun S => S.card = k).card : ℝ) ≤ A * N * lam ^ (2 * (k - 1)))
    {K₁ K₂ : Finset (Finset ℕ) → ℝ}
    (hd : ∀ X ⊆ π, Retained p X →
      |K₁ X - K₂ X| ≤ Cd * R * (N * ∏ S ∈ X, blockWeight lam N S)) :
    (∑ Y ∈ π.powerset, if Retained p Y then |K₁ Y - K₂ Y| else 0) ≤
      Cd * R * N * Real.exp (p * (1 + A)) := by
  have hu : ∀ S, 0 ≤ blockWeight lam N S := blockWeight_nonneg hlam N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc (∑ Y ∈ π.powerset, if Retained p Y then |K₁ Y - K₂ Y| else 0)
      ≤ ∑ Y ∈ π.powerset, Cd * R * N * ∏ S ∈ Y, blockWeight lam N S := by
        refine sum_le_sum fun Y hY => ?_
        split_ifs with hr
        · exact (hd Y (mem_powerset.mp hY) hr).trans (le_of_eq (by ring))
        · exact mul_nonneg (by positivity) (prod_nonneg fun S _ => hu S)
    _ = Cd * R * N * ∑ Y ∈ π.powerset, ∏ S ∈ Y, blockWeight lam N S := (mul_sum _ _ _).symm
    _ ≤ Cd * R * N * Real.exp (∑ S ∈ π, blockWeight lam N S) :=
        mul_le_mul_of_nonneg_left (sum_powerset_prod_le_exp π hu) (by positivity)
    _ ≤ Cd * R * N * Real.exp (p * (1 + A)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sum_blockWeight_le hN hπ hlam hA hn))
          (by positivity)

/-- **The retained activities** (proof of Proposition 4.62): if `|K₂(X)| ≤ C (λ²/N)^{|X|-1}`,
`|K₁(X) - K₂(X)| ≤ C_d R N ∏_{S ∈ X} u(S)` and `R ≤ λ^{2(p-1)}`, then
`|K₁(X)| ≤ (C + C_d) (λ²/N)^{|X|-1}` for a retained subpartition `X`. -/
theorem abs_le_of_abs_sub_le {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (hr : Retained p X)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hN : 1 ≤ N) {C Cd R : ℝ} (hCd : 0 ≤ Cd)
    (hR : R ≤ (lam ^ 2) ^ (p - 1)) {K₁ K₂ : ℝ}
    (h₂ : |K₂| ≤ C * (lam ^ 2 / N) ^ (X.card - 1))
    (hd : |K₁ - K₂| ≤ Cd * R * (N * ∏ S ∈ X, blockWeight lam N S)) :
    |K₁| ≤ (C + Cd) * (lam ^ 2 / N) ^ (X.card - 1) := by
  have hX1 : 1 ≤ X.card := by have := hr.1; omega
  have hkey := mul_prod_blockWeight_mul_pow hX hX1 hlam hN
  have hl2 : 0 ≤ lam ^ 2 := by positivity
  have hl21 : lam ^ 2 ≤ 1 := pow_le_one₀ hlam.le hlam1
  have hpow : (lam ^ 2) ^ (p - 1) ≤ (lam ^ 2) ^ ((X.biUnion id).card - 1) :=
    pow_le_pow_of_le_one hl2 hl21 (by have := hr.2; omega)
  have hB : 0 ≤ (N : ℝ) * ∏ S ∈ X, blockWeight lam N S :=
    mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun S _ => blockWeight_nonneg hlam N S)
  have hd' : |K₁ - K₂| ≤ Cd * (lam ^ 2 / N) ^ (X.card - 1) := by
    refine hd.trans ?_
    rw [← hkey, mul_assoc Cd]
    refine mul_le_mul_of_nonneg_left ?_ hCd
    rw [mul_comm R]
    exact mul_le_mul_of_nonneg_left (hR.trans hpow) hB
  calc |K₁| = |(K₁ - K₂) + K₂| := by ring_nf
    _ ≤ |K₁ - K₂| + |K₂| := abs_add_le _ _
    _ ≤ Cd * (lam ^ 2 / N) ^ (X.card - 1) + C * (lam ^ 2 / N) ^ (X.card - 1) := add_le_add hd' h₂
    _ = (C + Cd) * (lam ^ 2 / N) ^ (X.card - 1) := by ring

end LowerBoundLDP

end MultipoleBKT

end
