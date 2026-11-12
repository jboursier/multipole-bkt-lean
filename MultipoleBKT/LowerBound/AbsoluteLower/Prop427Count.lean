/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Stirling and the bounded anchored sum

The proof of Lemma 4.59, equations (4.121) and (4.134).

`pow_self_le_factorial_mul_exp` supplies the Stirling bound used by the
fixed-profile entropy proof in `RouteProfiles`. `sum_powerset_mem_pow_le`
is the bounded-cluster anchored estimate.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset

section Count

variable {β : Type*} [DecidableEq β]

/-- `m^m / m! ≤ e^m`. -/
theorem pow_self_le_factorial_mul_exp (m : ℕ) :
    (m : ℝ) ^ m ≤ (m.factorial : ℝ) * Real.exp m := by
  have h := Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf] at h
  linarith

/-- **Eq. (4.134)** of Lemma 4.57: for `u ≥ 0` and `S₀ ∈ π`,
`∑_{X ⊆ π, X ∋ S₀, |X| ≥ 2} u^{|X|-1} ≤ e^{|π| u} - 1`. -/
theorem sum_powerset_mem_pow_le (π : Finset β) {u : ℝ} (hu : 0 ≤ u) {S₀ : β} (hS₀ : S₀ ∈ π) :
    ∑ X ∈ π.powerset, (if S₀ ∈ X ∧ 2 ≤ X.card then u ^ (X.card - 1) else 0) ≤
      Real.exp (π.card * u) - 1 := by
  set π' := π.erase S₀ with hπ'
  have hS₀' : S₀ ∉ π' := notMem_erase S₀ π
  conv_lhs => rw [← insert_erase hS₀, sum_powerset_insert hS₀']
  have h1 : ∑ X ∈ π'.powerset, (if S₀ ∈ X ∧ 2 ≤ X.card then u ^ (X.card - 1) else 0) = 0 :=
    sum_eq_zero fun X hX => ite_eq_right fun h => hS₀' (mem_powerset.1 hX h.1)
  rw [h1, zero_add]
  have h2 : ∀ Y ∈ π'.powerset, (if S₀ ∈ insert S₀ Y ∧ 2 ≤ (insert S₀ Y).card then
      u ^ ((insert S₀ Y).card - 1) else 0) = (if Y.Nonempty then ∏ _S ∈ Y, u else 0) := by
    intro Y hY
    have hY' : S₀ ∉ Y := fun h => hS₀' (mem_powerset.1 hY h)
    rw [card_insert_of_notMem hY', prod_const, Nat.add_sub_cancel]
    by_cases hne : Y.Nonempty
    · rw [ite_eq_left ⟨mem_insert_self S₀ Y, by have := hne.card_pos; omega⟩, ite_eq_left hne]
    · rw [not_nonempty_iff_eq_empty] at hne
      subst hne
      simp
  rw [sum_congr rfl h2]
  have h3 : ∑ Y ∈ π'.powerset, (if Y.Nonempty then ∏ _S ∈ Y, u else 0) =
      ∏ _S ∈ π', (1 + u) - 1 := by
    rw [prod_one_add]
    have : ∀ Y ∈ π'.powerset, ∏ _S ∈ Y, u =
        (if Y.Nonempty then ∏ _S ∈ Y, u else 0) + (if ∅ = Y then 1 else 0) := by
      intro Y _
      by_cases hY : Y.Nonempty
      · rw [ite_eq_left hY, ite_eq_right (fun h => hY.ne_empty h.symm), add_zero]
      · rw [not_nonempty_iff_eq_empty] at hY
        subst hY
        simp
    rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq π'.powerset ∅,
      ite_eq_left (empty_mem_powerset π')]
    ring
  rw [h3, prod_const]
  have h4 : (1 + u) ^ π'.card ≤ Real.exp (π.card * u) := by
    calc (1 + u) ^ π'.card ≤ Real.exp u ^ π'.card := by
          refine pow_le_pow_left₀ (by linarith) ?_ _
          linarith [Real.add_one_le_exp u]
      _ = Real.exp (π'.card * u) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (π.card * u) := by
          refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hu)
          exact_mod_cast card_le_card (erase_subset S₀ π)
  linarith

end Count

end AbsoluteLower

end MultipoleBKT

end
