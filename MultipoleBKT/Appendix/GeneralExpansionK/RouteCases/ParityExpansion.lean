/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.Expansion

/-!
# Reversal cancellation followed by the five-subset expansion

See Step 1 of
the proof of Lemma A.7, in particular (A.51).
First retain exactly the cut-even odd subsets. Then expand the five correction
families, remove the all-empty term and apply the triangle inequality.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits

variable {ε ν κ : Type*} [DecidableEq ε] [DecidableEq ν] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ν] in
open scoped Classical in
/-- Exact reversal cancellation. Each retained odd product has coefficient one. -/
theorem avg_product_eq_cutEven (ends : ε → Sym2 κ) (E : Finset ε) (a g : ε → ℝ) :
    (∑ A : Finset κ, ∏ e ∈ E, (a e + signCross ends A e * g e)) / 2 ^ Fintype.card κ =
      ∑ O ∈ E.powerset.filter (CutEven ends), (∏ e ∈ O, g e) * ∏ e ∈ E \ O, a e := by
  have hsign : ∀ O : Finset ε, (∑ A : Finset κ, ∏ e ∈ O, signCross ends A e) =
      if CutEven ends O then (2 : ℝ) ^ Fintype.card κ else 0 := by
    intro O
    split_ifs with ho
    · have hprod : ∀ A : Finset κ, ∏ e ∈ O, signCross ends A e = 1 := by
        intro A
        rw [prod_signCross]
        exact (ho A).neg_one_pow
      simp_rw [hprod]
      rw [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
    · exact sum_prod_signCross_eq_zero ends ho
  have hexp : ∀ A : Finset κ, ∏ e ∈ E, (a e + signCross ends A e * g e) =
      ∑ O ∈ E.powerset, (∏ e ∈ O, signCross ends A e) *
        ((∏ e ∈ O, g e) * ∏ e ∈ E \ O, a e) := by
    intro A
    rw [show (fun e => a e + signCross ends A e * g e) =
      (fun e => signCross ends A e * g e + a e) from funext fun e => add_comm _ _, prod_add]
    apply sum_congr rfl
    intro O _
    rw [prod_mul_distrib, mul_assoc]
  simp_rw [hexp]
  rw [sum_comm]
  simp_rw [← sum_mul, hsign, ite_mul, zero_mul]
  rw [← sum_filter, ← mul_sum, mul_div_cancel_left₀ _ (by positivity)]

open scoped Classical in
/-- The exact odd/even and five-subset error expansion. The common factor `G`
contains the unchanged support, intra-block baseline and dipole density. -/
theorem parity_five_subset_error (ends : ε → Sym2 κ) (E I : Finset ε) (V : Finset ν)
    (a₁ a₀ g₁ g₀ q : ε → ℝ) (u v : ν → ℝ) (G : ℝ) :
    (∑ A : Finset κ,
      (G * (∏ e ∈ I, q e) * (∏ i ∈ V, (1 + u i)) * (∏ i ∈ V, (1 + v i)) *
          (∏ e ∈ E, (a₁ e + signCross ends A e * g₁ e)) -
        G * (∏ e ∈ E, (a₀ e + signCross ends A e * g₀ e)))) / 2 ^ Fintype.card κ =
      ∑ O ∈ E.powerset.filter (CutEven ends),
        ∑ P ∈ (fiveSubsets O (E \ O) I V).erase (∅, ∅, ∅, ∅, ∅),
          G * fiveTerm O (E \ O) I g₁ g₀ a₁ a₀ q u v P := by
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sub_div, mul_div_assoc, mul_div_assoc,
    avg_product_eq_cutEven, avg_product_eq_cutEven, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro O _
  rw [← five_subset_error O (E \ O) I V g₁ g₀ a₁ a₀ q u v G]
  ring

open scoped Classical in
/-- The pointwise triangle bound used before treating cases A–E separately.
No single-bond telescoping replaces the five-subset expansion. -/
theorem abs_parity_five_subset_error_le (ends : ε → Sym2 κ) (E I : Finset ε) (V : Finset ν)
    (a₁ a₀ g₁ g₀ q : ε → ℝ) (u v : ν → ℝ) (G : ℝ) :
    |(∑ A : Finset κ,
      (G * (∏ e ∈ I, q e) * (∏ i ∈ V, (1 + u i)) * (∏ i ∈ V, (1 + v i)) *
          (∏ e ∈ E, (a₁ e + signCross ends A e * g₁ e)) -
        G * (∏ e ∈ E, (a₀ e + signCross ends A e * g₀ e)))) / 2 ^ Fintype.card κ| ≤
      ∑ O ∈ E.powerset.filter (CutEven ends),
        ∑ P ∈ (fiveSubsets O (E \ O) I V).erase (∅, ∅, ∅, ∅, ∅),
          |G * fiveTerm O (E \ O) I g₁ g₀ a₁ a₀ q u v P| := by
  rw [parity_five_subset_error]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun O _ => abs_sum_le_sum_abs _ _)

end MultipoleBKT.ExpansionK.RouteCases

end
