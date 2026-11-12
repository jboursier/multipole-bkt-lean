/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.MixedProducts

/-!
# Selected factors in a whole mixed product

See (A.55)–(A.58)
and cases D–E. One factor supplies the gain. All other
correction factors are controlled simultaneously, including the common factor.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset

variable {ε ν : Type*} [DecidableEq ε] [DecidableEq ν]

/-- The number of original factors in the five families of a fixed term. -/
def factorCount (O B : Finset ε) (P : FiveSubsets ε ν) : ℕ :=
  O.card + B.card + P.2.2.1.card + P.2.2.2.1.card + P.2.2.2.2.card

/-- The product of geometric majorants for all five families. -/
noncomputable def weightedFive (O B : Finset ε) (P : FiveSubsets ε ν)
    (A B' Q : ε → ℝ) (U V : ν → ℝ) : ℝ :=
  (∏ e ∈ O, A e) * (∏ e ∈ B, B' e) * (∏ e ∈ P.2.2.1, Q e) *
    (∏ i ∈ P.2.2.2.1, U i) * ∏ i ∈ P.2.2.2.2, V i

omit [DecidableEq ν] in
/-- Internal comparison of a complete mixed summand. The majorants may single
out any correction factor without changing the bounds on the other families. -/
theorem internal_fiveTerm_weighted (O B I : Finset ε) (V : Finset ν)
    (a₁ a₀ b₁ b₀ q : ε → ℝ) (u v : ν → ℝ) (P : FiveSubsets ε ν)
    (hP : P ∈ fiveSubsets O B I V) (A B' Q : ε → ℝ) (U W : ν → ℝ)
    {K : ℝ} (_hK : 0 ≤ K)
    (ha : ∀ e ∈ O, |mixedBond P.1 a₁ a₀ e| ≤ K * A e)
    (hb : ∀ e ∈ B, |mixedBond P.2.1 b₁ b₀ e| ≤ K * B' e)
    (hq : ∀ e ∈ P.2.2.1, |q e - 1| ≤ K * Q e)
    (hu : ∀ i ∈ P.2.2.2.1, |u i| ≤ K * U i)
    (hv : ∀ i ∈ P.2.2.2.2, |v i| ≤ K * W i) (G : ℝ) :
    |G * fiveTerm O B I a₁ a₀ b₁ b₀ q u v P| ≤
      |G| * K ^ factorCount O B P * weightedFive O B P A B' Q U W := by
  rw [abs_fiveTerm_mul O B I a₁ a₀ b₁ b₀ q u v P hP G]
  have hA : ∀ e ∈ O, 0 ≤ K * A e := fun e he => (abs_nonneg _).trans (ha e he)
  have hB : ∀ e ∈ B, 0 ≤ K * B' e := fun e he => (abs_nonneg _).trans (hb e he)
  have hQ : ∀ e ∈ P.2.2.1, 0 ≤ K * Q e := fun e he => (abs_nonneg _).trans (hq e he)
  have hU : ∀ i ∈ P.2.2.2.1, 0 ≤ K * U i := fun i hi => (abs_nonneg _).trans (hu i hi)
  calc _ ≤ |G| * (∏ e ∈ O, K * A e) * (∏ e ∈ B, K * B' e) *
      (∏ e ∈ P.2.2.1, K * Q e) * (∏ i ∈ P.2.2.2.1, K * U i) *
      ∏ i ∈ P.2.2.2.2, K * W i := by
        have hpA := prod_nonneg hA
        have hpB := prod_nonneg hB
        have hpQ := prod_nonneg hQ
        have hpU := prod_nonneg hU
        gcongr
        all_goals first | positivity | exact ha _ ‹_› | exact hb _ ‹_› |
          exact hq _ ‹_› | exact hu _ ‹_› | exact hv _ ‹_›
       _ = _ := by
         simp only [prod_mul_distrib, prod_const, factorCount, pow_add, weightedFive]
         ring

/-- A selected factor is replaced before the remaining factors are dropped. -/
theorem internal_selected_product (S : Finset ε) (a : ε → ℝ) {e : ε} (he : e ∈ S)
    (g : ℝ) :
    (∏ x ∈ S, if x = e then g else a x) = g * ∏ x ∈ S.erase e, a x := by
  rw [← mul_prod_erase _ _ he]
  simp only [ite_true]
  congr 1
  exact prod_congr rfl fun x hx => ite_eq_right (mem_erase.1 hx).1

/-- Finite products of unit majorants leave precisely the selected gain. -/
theorem internal_selected_units (S : Finset ε) {e : ε} (he : e ∈ S) (g : ℝ) :
    (∏ x ∈ S, if x = e then g else 1) = g := by
  rw [internal_selected_product S (fun _ => 1) he g, prod_const_one, mul_one]

end MultipoleBKT.ExpansionK.RouteCases

end
