/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ModelExpansion

/-!
# Products in a mixed five-subset summand

See (A.55) through
(A.62). The selected correction replaces exactly one
factor. All other corrections remain controlled in the same product.
These internal inequalities keep the common support and density factor.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset

variable {ε ν : Type*} [DecidableEq ε] [DecidableEq ν]

/-- The bond chosen by an error subset, on its full edge carrier. -/
noncomputable def mixedBond (F : Finset ε) (a₁ a₀ : ε → ℝ) (e : ε) : ℝ :=
  if e ∈ F then a₁ e - a₀ e else a₀ e

/-- Recombine the corrected and uncorrected factors before taking products. -/
theorem prod_mixedBond (O F : Finset ε) (hF : F ⊆ O) (a₁ a₀ : ε → ℝ) :
    ∏ e ∈ O, mixedBond F a₁ a₀ e =
      (∏ e ∈ F, (a₁ e - a₀ e)) * ∏ e ∈ O \ F, a₀ e := by
  rw [← prod_sdiff hF, mul_comm]
  congr 1
  · exact prod_congr rfl fun e he => ite_eq_left he
  · exact prod_congr rfl fun e he => ite_eq_right (mem_sdiff.1 he).2

omit [DecidableEq ν] in
/-- The absolute value of a complete mixed summand is a product of its five
families. The common factor can include all spatial supports and densities. -/
theorem abs_fiveTerm_mul (O B I : Finset ε) (a₁ a₀ b₁ b₀ q : ε → ℝ)
    (u v : ν → ℝ) (P : FiveSubsets ε ν) {V : Finset ν} (hP : P ∈ fiveSubsets O B I V)
    (G : ℝ) :
    |G * fiveTerm O B I a₁ a₀ b₁ b₀ q u v P| =
      |G| * (∏ e ∈ O, |mixedBond P.1 a₁ a₀ e|) *
        (∏ e ∈ B, |mixedBond P.2.1 b₁ b₀ e|) *
        (∏ e ∈ P.2.2.1, |q e - 1|) *
        (∏ i ∈ P.2.2.2.1, |u i|) * ∏ i ∈ P.2.2.2.2, |v i| := by
  have hsets := mem_product.1 hP
  have hF := mem_powerset.1 hsets.1
  have hB := mem_powerset.1 (mem_product.1 hsets.2).1
  rw [← abs_prod, ← abs_prod, prod_mixedBond O P.1 hF,
    prod_mixedBond B P.2.1 hB]
  simp only [fiveTerm, abs_mul, abs_prod, mul_assoc]

omit [DecidableEq ε] in
/-- Internal comparison for an entire product, with the constant counted once
per original factor. -/
theorem internal_prod_bound (S : Finset ε) (f a : ε → ℝ) {K : ℝ}
    (hf : ∀ e ∈ S, |f e| ≤ K * a e) :
    (∏ e ∈ S, |f e|) ≤ K ^ S.card * ∏ e ∈ S, a e := by
  calc _ ≤ ∏ e ∈ S, K * a e := prod_le_prod₀ (fun e _ => abs_nonneg _) hf
       _ = _ := by rw [prod_mul_distrib, prod_const]

end MultipoleBKT.ExpansionK.RouteCases

end
