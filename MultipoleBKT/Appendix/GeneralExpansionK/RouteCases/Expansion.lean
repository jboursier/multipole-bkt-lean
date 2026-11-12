/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.GeneralModel

/-!
# The five-subset expansion of an activity error

See (A.51).
Expand the odd bonds, even bonds, intra-block exponential corrections, quadratic
marks and good-label corrections separately. The all-empty term is the unperturbed
integrand. The common support and dipole density multiply every term unchanged.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset

variable {ε ν : Type*} [DecidableEq ε] [DecidableEq ν]

/-- The five sets `(F₁,F₂,F₃,U₁,U₂)` in the written expansion. -/
abbrev FiveSubsets (ε ν : Type*) :=
  Finset ε × Finset ε × Finset ε × Finset ν × Finset ν

/-- The finite domain of all five choices. -/
def fiveSubsets (O B I : Finset ε) (V : Finset ν) : Finset (FiveSubsets ε ν) :=
  O.powerset ×ˢ (B.powerset ×ˢ (I.powerset ×ˢ (V.powerset ×ˢ V.powerset)))

/-- A summand of the five-subset expansion. The functions `u` and `v` are the
quadratic and good-label corrections, so their unperturbed factors are one. -/
noncomputable def fiveTerm (O B _I : Finset ε) (a₁ a₀ b₁ b₀ q : ε → ℝ)
    (u v : ν → ℝ) (P : FiveSubsets ε ν) : ℝ :=
  ((∏ e ∈ P.1, (a₁ e - a₀ e)) * ∏ e ∈ O \ P.1, a₀ e) *
    ((∏ e ∈ P.2.1, (b₁ e - b₀ e)) * ∏ e ∈ B \ P.2.1, b₀ e) *
    (∏ e ∈ P.2.2.1, (q e - 1)) *
    (∏ i ∈ P.2.2.2.1, u i) * ∏ i ∈ P.2.2.2.2, v i

omit [DecidableEq ν] in
/-- The all-empty term is exactly the unperturbed odd/even product. -/
theorem fiveTerm_empty (O B I : Finset ε) (a₁ a₀ b₁ b₀ q : ε → ℝ) (u v : ν → ℝ) :
    fiveTerm O B I a₁ a₀ b₁ b₀ q u v (∅, ∅, ∅, ∅, ∅) =
      (∏ e ∈ O, a₀ e) * ∏ e ∈ B, b₀ e := by
  simp [fiveTerm]

private theorem prod_eq_sum_corrections (S : Finset ε) (f g : ε → ℝ) :
    ∏ e ∈ S, f e = ∑ F ∈ S.powerset,
      (∏ e ∈ F, (f e - g e)) * ∏ e ∈ S \ F, g e := by
  rw [← prod_add]
  exact prod_congr rfl fun e _ => (sub_add_cancel _ _).symm

/-- The exact five-subset identity before removing the all-empty term. -/
theorem five_subset_expansion (O B I : Finset ε) (V : Finset ν)
    (a₁ a₀ b₁ b₀ q : ε → ℝ) (u v : ν → ℝ) :
    (∏ e ∈ O, a₁ e) * (∏ e ∈ B, b₁ e) * (∏ e ∈ I, q e) *
        (∏ i ∈ V, (1 + u i)) * (∏ i ∈ V, (1 + v i)) =
      ∑ P ∈ fiveSubsets O B I V, fiveTerm O B I a₁ a₀ b₁ b₀ q u v P := by
  rw [prod_eq_sum_corrections O a₁ a₀, prod_eq_sum_corrections B b₁ b₀,
    prod_eq_sum_corrections I q (fun _ => 1),
    prod_eq_sum_corrections V (fun i => 1 + u i) (fun _ => 1),
    prod_eq_sum_corrections V (fun i => 1 + v i) (fun _ => 1)]
  simp only [add_sub_cancel_left, prod_const_one, mul_one]
  simp only [fiveSubsets, sum_product, fiveTerm]
  simp_rw [mul_assoc, ← mul_sum, ← sum_mul]
  simp_rw [← mul_assoc, ← sum_mul]
  ring

/-- (A.51) pointwise on the common support: only the nonempty choices remain.
A common indicator, intra-block baseline and dipole density can all be included in `G`. -/
theorem five_subset_error (O B I : Finset ε) (V : Finset ν)
    (a₁ a₀ b₁ b₀ q : ε → ℝ) (u v : ν → ℝ) (G : ℝ) :
    G * ((∏ e ∈ O, a₁ e) * (∏ e ∈ B, b₁ e) * (∏ e ∈ I, q e) *
        (∏ i ∈ V, (1 + u i)) * (∏ i ∈ V, (1 + v i))) -
      G * ((∏ e ∈ O, a₀ e) * ∏ e ∈ B, b₀ e) =
      ∑ P ∈ (fiveSubsets O B I V).erase (∅, ∅, ∅, ∅, ∅),
        G * fiveTerm O B I a₁ a₀ b₁ b₀ q u v P := by
  have hmem : (∅, ∅, ∅, ∅, ∅) ∈ fiveSubsets O B I V := by
    simp [fiveSubsets]
  rw [five_subset_expansion O B I V, ← fiveTerm_empty O B I a₁ a₀ b₁ b₀ q u v,
    ← mul_sub, ← sum_erase_add _ _ hmem, add_sub_cancel_right, mul_sum]

/-- Cases A–E exhaust every nonempty five-subset summand. The skeleton `K` and
even tree `T` can be selected before the error subsets are inspected. -/
theorem five_cases_exhaustive (O B I : Finset ε) (V : Finset ν) (K T : Finset ε)
    {P : FiveSubsets ε ν}
    (hP : P ∈ (fiveSubsets O B I V).erase (∅, ∅, ∅, ∅, ∅)) :
    (P.2.2.1.Nonempty ∨ P.2.2.2.1.Nonempty ∨ P.2.2.2.2.Nonempty) ∨
      ((O \ K) ∩ P.1).Nonempty ∨ ((B \ T) ∩ P.2.1).Nonempty ∨
      (K ∩ P.1).Nonempty ∨ (T ∩ P.2.1).Nonempty := by
  obtain ⟨hne, hP⟩ := mem_erase.1 hP
  simp only [fiveSubsets, mem_product, mem_powerset] at hP
  by_cases hA : P.2.2.1.Nonempty ∨ P.2.2.2.1.Nonempty ∨ P.2.2.2.2.Nonempty
  · exact Or.inl hA
  by_cases hF₁ : P.1.Nonempty
  · obtain ⟨e, he⟩ := hF₁
    by_cases heK : e ∈ K
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, mem_inter.2 ⟨heK, he⟩⟩)))
    · exact Or.inr (Or.inl ⟨e, mem_inter.2 ⟨mem_sdiff.2 ⟨hP.1 he, heK⟩, he⟩⟩)
  by_cases hF₂ : P.2.1.Nonempty
  · obtain ⟨e, he⟩ := hF₂
    by_cases heT : e ∈ T
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e, mem_inter.2 ⟨heT, he⟩⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨e, mem_inter.2 ⟨mem_sdiff.2 ⟨hP.2.1 he, heT⟩, he⟩⟩))
  exfalso
  apply hne
  have h₁ := not_nonempty_iff_eq_empty.1 hF₁
  have h₂ := not_nonempty_iff_eq_empty.1 hF₂
  have h₃ : P.2.2.1 = ∅ := not_nonempty_iff_eq_empty.1 (fun h => hA (Or.inl h))
  have h₄ : P.2.2.2.1 = ∅ := not_nonempty_iff_eq_empty.1 (fun h => hA (Or.inr (Or.inl h)))
  have h₅ : P.2.2.2.2 = ∅ := not_nonempty_iff_eq_empty.1 (fun h => hA (Or.inr (Or.inr h)))
  exact Prod.ext h₁ (Prod.ext h₂ (Prod.ext h₃ (Prod.ext h₄ h₅)))

end MultipoleBKT.ExpansionK.RouteCases

end
