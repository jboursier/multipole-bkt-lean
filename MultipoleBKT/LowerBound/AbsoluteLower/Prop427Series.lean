/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Tree
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteProfiles.Sums
public import MultipoleBKT.Frozen.IsSubpartition

/-!
# Lemma 4.59 and the connected series of Proposition 4.27

Lemma 4.59,
(4.120), and proof of Proposition 4.27.

`cvgentseries_of_bounds` fixes the block-size profiles and applies the
binomial/Stirling and entropy estimates from `RouteProfiles`. Their
global and anchored summations give (4.118) and (4.119).
The prescribed block's weight remains explicit.

`series_of_norm_bounds` then performs the connected-series argument:
Rota, rooted leaf removal, weighted Cayley and geometric summation.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset

/-- For a subpartition, `|X| ≤ |V_X|`. -/
theorem card_le_card_biUnion_of_isSubpartition {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    X.card ≤ (X.biUnion id).card :=
  card_le_card_biUnion (fun _S hS _T hT hST => hX.2 hS hT hST) fun S hS => hX.1 S hS

/-- A subfamily of a subpartition is a subpartition. -/
theorem IsSubpartition.subset' {π X : Finset (Finset ℕ)} (hπ : IsSubpartition π) (hX : X ⊆ π) :
    IsSubpartition X :=
  ⟨fun S hS => hπ.1 S (hX hS), hπ.2.subset (by exact_mod_cast hX)⟩

section Series

variable {π : Finset (Finset ℕ)} (K : Finset (Finset ℕ) → ℝ) (p : ℕ)
  {N lam δ Cs Cl : ℝ} (w : Finset ℕ → ℝ)

open scoped Classical in
/-- Internal assembly from global and anchored weight sums. -/
theorem cvgentseries_of_weight_sums (hN : 0 < N)
    (hπN : (π.card : ℝ) ≤ N) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hCs : 0 ≤ Cs) (hCl : 0 ≤ Cl)
    (hδ : 0 ≤ δ) (hw0 : ∀ S, 0 ≤ w S)
    (hsum : ∑ X ∈ π.powerset, (X.card : ℝ) ^ X.card * ∏ S ∈ X, w S ≤ 2)
    (hroot : ∀ S₀ ∈ π, ∑ X ∈ π.powerset,
      (if S₀ ∈ X then (X.card : ℝ) ^ X.card * ∏ S ∈ X, w S else 0) ≤
        4 * Real.exp 1 * w S₀)
    (hK1 : ∀ X ⊆ π, X.card ≤ 1 → K X = 0)
    (hsmall : ∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
      |K X| ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1))
    (hlarge : ∀ X ⊆ π, 2 ≤ X.card → p < (X.biUnion id).card →
      |K X| * 20 ^ (X.biUnion id).card ≤ Cl * N * δ * ((X.card : ℝ) ^ X.card * ∏ S ∈ X, w S)) :
    (∑ X ∈ π.powerset.filter (fun X => p < (X.biUnion id).card),
        |K X| * 20 ^ (X.biUnion id).card ≤ 2 * (Cl * N * δ)) ∧
    ∀ S₀ ∈ π, ∑ X ∈ π.powerset, (if S₀ ∈ X then |K X| * 20 ^ (X.biUnion id).card else 0) ≤
      2 * 20 ^ p * Cs * lam ^ 2 + 4 * Real.exp 1 * (Cl * N * δ) * w S₀ := by
  have hD : 0 ≤ Cl * N * δ := by positivity
  have hP : ∀ X : Finset (Finset ℕ), 0 ≤ (X.card : ℝ) ^ X.card * ∏ S ∈ X, w S :=
    fun X => mul_nonneg (by positivity) (prod_nonneg fun S _ => hw0 S)
  -- the large-cluster bound for every subfamily
  have hlarge' : ∀ X ∈ π.powerset, p < (X.biUnion id).card →
      |K X| * 20 ^ (X.biUnion id).card ≤
        Cl * N * δ * ((X.card : ℝ) ^ X.card * ∏ S ∈ X, w S) := by
    intro X hX hp
    have hX' := mem_powerset.1 hX
    by_cases h2 : 2 ≤ X.card
    · exact hlarge X hX' h2 hp
    · rw [hK1 X hX' (by omega), abs_zero, zero_mul]
      exact mul_nonneg hD (hP X)
  refine ⟨?_, fun S₀ hS₀ => ?_⟩
  · -- (4.118)
    calc ∑ X ∈ π.powerset.filter (fun X => p < (X.biUnion id).card),
          |K X| * 20 ^ (X.biUnion id).card
        ≤ ∑ X ∈ π.powerset.filter (fun X => p < (X.biUnion id).card),
          Cl * N * δ * ((X.card : ℝ) ^ X.card * ∏ S ∈ X, w S) :=
          sum_le_sum fun X hX => hlarge' X (mem_filter.1 hX).1 (mem_filter.1 hX).2
      _ ≤ ∑ X ∈ π.powerset, Cl * N * δ * ((X.card : ℝ) ^ X.card * ∏ S ∈ X, w S) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun X _ _ => mul_nonneg hD (hP X)
      _ = Cl * N * δ * ∑ X ∈ π.powerset, (X.card : ℝ) ^ X.card * ∏ S ∈ X, w S :=
          (mul_sum _ _ _).symm
      _ ≤ Cl * N * δ * 2 :=
          mul_le_mul_of_nonneg_left hsum hD
      _ = 2 * (Cl * N * δ) := by ring
  · -- (4.119)
    have hu : 0 ≤ lam ^ 2 / N := by positivity
    have hsplit : ∀ X ∈ π.powerset,
        (if S₀ ∈ X then |K X| * 20 ^ (X.biUnion id).card else 0) ≤
          20 ^ p * Cs * (if S₀ ∈ X ∧ 2 ≤ X.card then (lam ^ 2 / N) ^ (X.card - 1) else 0) +
          Cl * N * δ * (if S₀ ∈ X then (X.card : ℝ) ^ X.card * ∏ S ∈ X, w S else 0) := by
      intro X hX
      have hX' := mem_powerset.1 hX
      by_cases hS : S₀ ∈ X
      · rw [ite_eq_left hS, ite_eq_left hS]
        by_cases h2 : 2 ≤ X.card
        · rw [ite_eq_left ⟨hS, h2⟩]
          by_cases hp : p < (X.biUnion id).card
          · have := hlarge' X hX hp
            have : 0 ≤ 20 ^ p * Cs * (lam ^ 2 / N) ^ (X.card - 1) := by positivity
            linarith
          · have h1 := hsmall X hX' h2 (by omega)
            have h20 : (20 : ℝ) ^ (X.biUnion id).card ≤ 20 ^ p :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            have := mul_nonneg hD (hP X)
            calc |K X| * 20 ^ (X.biUnion id).card ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1) * 20 ^ p :=
                  mul_le_mul h1 h20 (by positivity) (by positivity)
              _ ≤ 20 ^ p * Cs * (lam ^ 2 / N) ^ (X.card - 1) +
                  Cl * N * δ * ((X.card : ℝ) ^ X.card * ∏ S ∈ X, w S) := by nlinarith
        · rw [hK1 X hX' (by omega), abs_zero, zero_mul, ite_eq_right (fun h => h2 h.2), mul_zero,
            zero_add]
          exact mul_nonneg hD (hP X)
      · rw [ite_eq_right hS, ite_eq_right (fun h => hS h.1), ite_eq_right hS]
        simp
    refine (sum_le_sum hsplit).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have h1 := sum_powerset_mem_pow_le π hu hS₀
    have h2 := hroot S₀ hS₀
    have hexp : Real.exp ((π.card : ℝ) * (lam ^ 2 / N)) - 1 ≤ 2 * lam ^ 2 := by
      have hx0 : 0 ≤ (π.card : ℝ) * (lam ^ 2 / N) := by positivity
      have hx1 : (π.card : ℝ) * (lam ^ 2 / N) ≤ lam ^ 2 := by
        rw [mul_div_assoc', div_le_iff₀ hN]
        nlinarith [sq_nonneg lam]
      have hl1 : lam ^ 2 ≤ 1 := pow_le_one₀ hlam0 hlam1
      have := Real.abs_exp_sub_one_le (x := (π.card : ℝ) * (lam ^ 2 / N))
        (by rw [abs_of_nonneg hx0]; linarith)
      rw [abs_of_nonneg hx0] at this
      have h' := le_abs_self (Real.exp ((π.card : ℝ) * (lam ^ 2 / N)) - 1)
      linarith
    have hc1 : 0 ≤ 20 ^ p * Cs := by positivity
    calc 20 ^ p * Cs * ∑ X ∈ π.powerset,
          (if S₀ ∈ X ∧ 2 ≤ X.card then (lam ^ 2 / N) ^ (X.card - 1) else 0) +
        Cl * N * δ * ∑ X ∈ π.powerset,
          (if S₀ ∈ X then (X.card : ℝ) ^ X.card * ∏ S ∈ X, w S else 0)
        ≤ 20 ^ p * Cs * (2 * lam ^ 2) + Cl * N * δ * (4 * Real.exp 1 * w S₀) :=
          add_le_add (mul_le_mul_of_nonneg_left (h1.trans hexp) hc1)
            (mul_le_mul_of_nonneg_left h2 hD)
      _ = 2 * 20 ^ p * Cs * lam ^ 2 + 4 * Real.exp 1 * (Cl * N * δ) * w S₀ := by ring

open scoped Classical in
/-- **Lemma 4.59 by size profiles**, Steps 1, 3 and 4
(4.120).
Binomial counting and Stirling are applied with the profile fixed, followed
by convexity of `x log x`, the profile sum and the size sum. -/
theorem cvgentseries_of_bounds (hπ : IsSubpartition π) (hp : ∀ S ∈ π, S.card ≤ p)
    (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) {z : ℝ} (hz : 0 ≤ z)
    (hn : ∀ i : Fin p, (PropFiveFortyFive.blockCount p π i : ℝ) * v ((i : ℕ) + 1) ≤
      z ^ ((i : ℕ) + 1)) (hzsmall : RouteProfiles.entropyConstant p * z ≤ 1 / 2)
    (hN : 0 < N) (hπN : (π.card : ℝ) ≤ N) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hCs : 0 ≤ Cs) (hCl : 0 ≤ Cl) (hδ : 0 ≤ δ)
    (hK1 : ∀ X ⊆ π, X.card ≤ 1 → K X = 0)
    (hsmall : ∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
      |K X| ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1))
    (hlarge : ∀ X ⊆ π, 2 ≤ X.card → p < (X.biUnion id).card →
      |K X| * 20 ^ (X.biUnion id).card ≤ Cl * N * δ *
        ((X.card : ℝ) ^ X.card * ∏ S ∈ X, v S.card)) :
    (∑ X ∈ π.powerset.filter (fun X => p < (X.biUnion id).card),
        |K X| * 20 ^ (X.biUnion id).card ≤ 2 * (Cl * N * δ)) ∧
    ∀ S₀ ∈ π, ∑ X ∈ π.powerset,
      (if S₀ ∈ X then |K X| * 20 ^ (X.biUnion id).card else 0) ≤
        2 * 20 ^ p * Cs * lam ^ 2 + 4 * Real.exp 1 * (Cl * N * δ) * v S₀.card := by
  exact cvgentseries_of_weight_sums K p (fun S => v S.card) hN hπN hlam0 hlam1 hCs hCl hδ
    (fun S => hv _) (RouteProfiles.global_sum_le hπ hp v hv hz hn hzsmall)
    (fun _ hS => RouteProfiles.anchored_sum_le hπ hp v hv hz hn hzsmall hS) hK1 hsmall hlarge

open scoped Classical in
/-- A sequence `a ≥ 0` with `a 0 = 0` and `a n ≤ B (1/2)^{n-1}` for `n ≥ 1` is summable, with sum
at most `2B`. -/
theorem summable_and_tsum_le_of_le_geometric {a : ℕ → ℝ} {B : ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (hzero : a 0 = 0) (hle : ∀ n, 1 ≤ n → a n ≤ B * (1 / 2) ^ (n - 1)) :
    Summable a ∧ ∑' n, a n ≤ 4 * B := by
  have hB : 0 ≤ B := by
    have := (ha0 1).trans (hle 1 le_rfl)
    simpa using this
  have hle' : ∀ n, a n ≤ 2 * B * (1 / 2) ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hzero]
      positivity
    · refine (hle n hn).trans (le_of_eq ?_)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
  have hg : Summable fun n : ℕ => 2 * B * (1 / 2 : ℝ) ^ n :=
    summable_geometric_two.mul_left (2 * B)
  have hs : Summable a := Summable.of_nonneg_of_le ha0 hle' hg
  refine ⟨hs, (hs.tsum_le_tsum hle' hg).trans (le_of_eq ?_)⟩
  rw [tsum_mul_left, tsum_geometric_two]
  ring

open scoped Classical in
/-- **Proposition 4.27 from per-subfamily bounds** (internal form): equation (4.55), the
absolute convergence of the full connected series (Proposition 4.27), and equation (4.56), when the anchored norm (4.119) is at most `2`. -/
theorem series_of_norm_bounds (hπ : IsSubpartition π)
    (hK1 : ∀ X ⊆ π, X.card ≤ 1 → K X = 0)
    (hB12 : ∑ X ∈ π.powerset.filter (fun X => p < (X.biUnion id).card),
      |K X| * 20 ^ (X.biUnion id).card ≤ 2 * (Cl * N * δ))
    (hA : ∀ S₀ ∈ π, ∑ X ∈ π.powerset,
      (if S₀ ∈ X then |K X| * 20 ^ (X.biUnion id).card else 0) ≤ 2) :
    (∑ X ∈ π.powerset.filter (fun X => p < (X.biUnion id).card), |K X| ≤ 2 * (Cl * N * δ)) ∧
    (Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected),
        |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)|) ∧
    (∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected ∧ ∃ i, p < ((X i).biUnion id).card),
        |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)| ≤ 8 * (Cl * N * δ)) := by
  have hK0 : K ∅ = 0 := hK1 ∅ (empty_subset π) (by simp)
  have h20 : ∀ X ∈ π.powerset, |K X| * 20 ^ X.card ≤ |K X| * 20 ^ (X.biUnion id).card :=
    fun X hX => mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num)
      (card_le_card_biUnion_of_isSubpartition (IsSubpartition.subset' hπ (mem_powerset.1 hX))))
      (abs_nonneg _)
  -- the anchored norm, with the weight `20^{|X|}`
  have h𝒜 : ∀ a ∈ π, ∑ Y ∈ π.powerset, (if a ∈ Y then |K Y| * 20 ^ Y.card else 0) ≤ 2 := by
    intro a ha
    refine le_trans (sum_le_sum fun Y hY => ?_) (hA a ha)
    split_ifs
    · exact h20 Y hY
    · exact le_rfl
  refine ⟨?_, ?_, ?_⟩
  · -- (4.54)
    refine le_trans (sum_le_sum fun X hX => ?_) hB12
    exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ (by norm_num))
  · -- the full connected series
    set Bf := ∑ Y ∈ π.powerset.filter (fun _ => True), |K Y| * 20 ^ Y.card with hBf
    have hfil : ∀ n : ℕ, (Fintype.piFinset fun _ : Fin n => π.powerset).filter
        (fun X => (connectionGraph X).Connected) =
        (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected ∧ ∃ _i : Fin n, True) := by
      intro n
      refine filter_congr fun X _ => ?_
      constructor
      · intro h
        obtain ⟨i⟩ := h.nonempty
        exact ⟨h, i, trivial⟩
      · exact fun h => h.1
    refine (summable_and_tsum_le_of_le_geometric (B := Bf) (fun n => by positivity) ?_
      fun n hn => ?_).1
    · simp only [hfil]
      simp
    · rw [hfil n]
      have := cluster_tree_bound π K (fun _ => True) zero_le_two hK0 h𝒜 le_rfl hn
      have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
      rw [one_div, inv_mul_le_iff₀ hf]
      convert this using 2 <;> norm_num [hBf]
  · -- (4.55)
    refine (summable_and_tsum_le_of_le_geometric (B := 2 * (Cl * N * δ))
      (fun n => by positivity) ?_ fun n hn => ?_).2.trans (by linarith)
    · simp
    · have h𝒬 : ∑ Y ∈ π.powerset.filter (fun Y => p < (Y.biUnion id).card),
          |K Y| * 20 ^ Y.card ≤ 2 * (Cl * N * δ) :=
        le_trans (sum_le_sum fun Y hY => h20 Y (mem_filter.1 hY).1) hB12
      have := cluster_tree_bound π K (fun Y => p < (Y.biUnion id).card) zero_le_two hK0 h𝒜
        (by convert h𝒬) hn
      have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
      rw [one_div, inv_mul_le_iff₀ hf]
      convert this using 2
      · congr
      · norm_num

end Series

end AbsoluteLower

end MultipoleBKT

end
