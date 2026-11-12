/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteProfiles.Estimates

/-!
# Summing global and anchored profiles

Lemma 4.59,
Steps 3 and 4, proof of Lemma 4.59. Fixed-size profile bounds give a geometric
series. In the anchored series the prescribed block's weight is retained
exactly, before taking a maximum over its possible sizes.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteProfiles

open Finset PropFiveFortyFive
open scoped Classical

/-- Group a finite cluster sum by the number of labels. -/
theorem sum_by_size (π : Finset (Finset ℕ)) (f : Finset (Finset ℕ) → ℝ) :
    ∑ X ∈ π.powerset, f X =
      ∑ k ∈ range ((π.biUnion id).card + 1),
        ∑ X ∈ π.powerset.filter (fun X => (X.biUnion id).card = k), f X := by
  exact (sum_fiberwise_of_maps_to (s := π.powerset) (g := fun X : Finset (Finset ℕ) => (X.biUnion id).card)
    (fun X hX => mem_range.mpr (Nat.lt_succ_of_le
      (card_le_card (biUnion_subset_biUnion_of_subset_left id (mem_powerset.mp hX))))) f).symm

/-- Sum the fixed-size global entropy bounds. -/
theorem global_sum_le {p : ℕ} {π : Finset (Finset ℕ)} (hπ : IsSubpartition π)
    (hp : ∀ S ∈ π, S.card ≤ p) (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) {z : ℝ} (hz : 0 ≤ z)
    (hn : ∀ i : Fin p, (blockCount p π i : ℝ) * v ((i : ℕ) + 1) ≤ z ^ ((i : ℕ) + 1))
    (hsmall : entropyConstant p * z ≤ 1 / 2) :
    ∑ X ∈ π.powerset, (X.card : ℝ) ^ X.card * ∏ S ∈ X, v S.card ≤ 2 := by
  rw [sum_by_size]
  calc _ ≤ ∑ k ∈ range ((π.biUnion id).card + 1), (entropyConstant p * z) ^ k :=
      sum_le_sum fun k _ => size_sum_le hπ hp v hv hz hn
    _ ≤ ∑ k ∈ range ((π.biUnion id).card + 1), (1 / 2 : ℝ) ^ k :=
      sum_le_sum fun k _ => pow_le_pow_left₀ (mul_nonneg (entropyConstant_pos p).le hz) hsmall k
    _ ≤ 2 := by simpa using sum_geometric_two_le ((π.biUnion id).card + 1)

/-- Sum the size bounds after removing the prescribed block. -/
theorem shifted_sum_le {p : ℕ} {π : Finset (Finset ℕ)} (hπ : IsSubpartition π)
    (hp : ∀ S ∈ π, S.card ≤ p) (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) {z : ℝ} (hz : 0 ≤ z)
    (hn : ∀ i : Fin p, (blockCount p π i : ℝ) * v ((i : ℕ) + 1) ≤ z ^ ((i : ℕ) + 1))
    (hsmall : entropyConstant p * z ≤ 1 / 2) :
    ∑ X ∈ π.powerset, ((X.card + 1 : ℕ) : ℝ) ^ (X.card + 1) * ∏ S ∈ X, v S.card ≤
      4 * Real.exp 1 := by
  rw [sum_by_size]
  calc _ ≤ ∑ k ∈ range ((π.biUnion id).card + 1),
        Real.exp 1 * (k + 1) * (entropyConstant p * z) ^ k :=
      sum_le_sum fun k _ => shifted_size_sum_le hπ hp v hv hz hn
    _ ≤ ∑ k ∈ range ((π.biUnion id).card + 1), Real.exp 1 * (k + 1) * (1 / 2 : ℝ) ^ k := by
      apply sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (entropyConstant_pos p).le hz) hsmall k) (by positivity)
    _ = Real.exp 1 * ∑ k ∈ range ((π.biUnion id).card + 1),
        ((k : ℝ) * (1 / 2) ^ k + (1 / 2) ^ k) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ Real.exp 1 * 4 := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [sum_add_distrib]
      have hA : ∑ k ∈ range ((π.biUnion id).card + 1), (k : ℝ) * (1 / 2) ^ k ≤ 2 := by
        have hs : Summable fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n := by
          simpa using summable_pow_mul_geometric_of_norm_lt_one 1
            (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
        refine (hs.sum_le_tsum _ fun _ _ => by positivity).trans (le_of_eq ?_)
        rw [tsum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
        norm_num
      have hB : ∑ k ∈ range ((π.biUnion id).card + 1), (1 / 2 : ℝ) ^ k ≤ 2 := by
        simpa using sum_geometric_two_le ((π.biUnion id).card + 1)
      linarith
    _ = _ := by ring

/-- The anchored sum keeps the exact weight `v |S₀|` of the prescribed block. -/
theorem anchored_sum_le {p : ℕ} {π : Finset (Finset ℕ)} (hπ : IsSubpartition π)
    (hp : ∀ S ∈ π, S.card ≤ p) (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) {z : ℝ} (hz : 0 ≤ z)
    (hn : ∀ i : Fin p, (blockCount p π i : ℝ) * v ((i : ℕ) + 1) ≤ z ^ ((i : ℕ) + 1))
    (hsmall : entropyConstant p * z ≤ 1 / 2) {S₀ : Finset ℕ} (hS₀ : S₀ ∈ π) :
    ∑ X ∈ π.powerset,
        (if S₀ ∈ X then (X.card : ℝ) ^ X.card * ∏ S ∈ X, v S.card else 0) ≤
      4 * Real.exp 1 * v S₀.card := by
  set π' := π.erase S₀
  have hroot : S₀ ∉ π' := notMem_erase S₀ π
  have hsub : π' ⊆ π := erase_subset _ _
  have hπ' : IsSubpartition π' :=
    ⟨fun S hS => hπ.1 S (hsub hS), hπ.2.subset (by exact_mod_cast hsub)⟩
  have hn' : ∀ i : Fin p, (blockCount p π' i : ℝ) * v ((i : ℕ) + 1) ≤ z ^ ((i : ℕ) + 1) := by
    intro i
    refine (mul_le_mul_of_nonneg_right ?_ (hv _)).trans (hn i)
    exact_mod_cast card_le_card (filter_subset_filter _ hsub)
  conv_lhs => rw [← insert_erase hS₀, sum_powerset_insert hroot]
  have hzero : ∑ X ∈ π'.powerset,
      (if S₀ ∈ X then (X.card : ℝ) ^ X.card * ∏ S ∈ X, v S.card else 0) = 0 := by
    apply sum_eq_zero
    intro X hX
    exact ite_eq_right (fun h => hroot (mem_powerset.mp hX h))
  rw [hzero, zero_add]
  have he : ∀ Y ∈ π'.powerset,
      (if S₀ ∈ insert S₀ Y then ((insert S₀ Y).card : ℝ) ^ (insert S₀ Y).card *
        ∏ S ∈ insert S₀ Y, v S.card else 0) =
      v S₀.card * (((Y.card + 1 : ℕ) : ℝ) ^ (Y.card + 1) * ∏ S ∈ Y, v S.card) := by
    intro Y hY
    have hSY : S₀ ∉ Y := fun h => hroot (mem_powerset.mp hY h)
    rw [ite_eq_left (mem_insert_self _ _), card_insert_of_notMem hSY, prod_insert hSY]
    ring
  rw [sum_congr rfl he, ← mul_sum]
  calc _ ≤ v S₀.card * (4 * Real.exp 1) :=
      mul_le_mul_of_nonneg_left
        (shifted_sum_le hπ' (fun S hS => hp S (hsub hS)) v hv hz hn' hsmall) (hv _)
    _ = _ := by ring

end MultipoleBKT.AbsoluteLower.RouteProfiles

end
