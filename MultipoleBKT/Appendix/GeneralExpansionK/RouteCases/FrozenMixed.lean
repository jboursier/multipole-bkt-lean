/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ExtendedEstimates
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.MixedProducts

/-!
# A whole-summand estimate for the extended frozen expansion

See (A.54). Every mixed correction is bounded on its full carrier before
selecting the factor that supplies the gain. The baseline block weight and
all common support and density factors remain explicit.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Hierarchical SmallIntegral

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

/-- The far odd geometric weight before reduction to component skeletons. -/
noncomputable def mixedOddWeight (M lam : ℝ) (c : ι → ℂ × ℂ) (e : Sym2 ι) : ℝ :=
  ahatE c e * farInd M lam c e

/-- The far even geometric weight before selecting the connecting tree. -/
noncomputable def mixedEvenWeight (M lam : ℝ) (c : ι → ℂ × ℂ) (e : Sym2 ι) : ℝ :=
  ahatE c e ^ 2 * farInd M lam c e

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Internal whole-carrier bond estimate, including the vanishing near branch. -/
theorem internal_bond_parts_geometric {β M lam C : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hlam : 0 < lam) (hM : 1 ≤ M)
    (c : ι → ℂ × ℂ)
    (hw : ∀ i j, ¬ MultipoleLinked M lam (c i) (c j) → |w (c i) (c j)| ≤ C * ahat (c i) (c j)) :
    ∀ e, |gammaW β w M lam c e| ≤ partConst β C * mixedOddWeight M lam c e ∧
      |alphaW β w M lam c e + linkIndE M lam c e| ≤
        partConst β C * mixedEvenWeight M lam c e := by
  classical
  intro e
  by_cases hf : FarE M lam c e
  · have hah : ∀ i j, ¬ MultipoleLinked M lam (c i) (c j) → ahat (c i) (c j) ≤ 1 :=
      fun i j h => (far_facts hlam hM h).2.2
    have hfar : farInd M lam c e = 1 := by
      induction e using Sym2.ind with
      | h i j => exact ite_eq_right hf
    simp only [mixedOddWeight, mixedEvenWeight, hfar, mul_one,
      linkIndE_of_far c hf, add_zero]
    exact ⟨abs_gammaW_le hβ hC c hw hah hf, abs_alphaW_le hβ hC c hw hah hf⟩
  · have hfar : farInd M lam c e = 0 := by
      induction e using Sym2.ind with
      | h i j => exact ite_eq_left (not_not.1 hf)
    simp only [gammaW_of_linked c hf, alphaW_add_linkIndE_of_linked c hf,
      mixedOddWeight, mixedEvenWeight, hfar, mul_zero, abs_zero, le_refl, and_self]

/-- The dipole density and the two support restrictions common to every
five-subset summand in the paper. -/
noncomputable def mixedDensity (χ : ℂ → ℝ) (β lam h : ℝ) (Df : Finset (Sym2 ι))
    (c : ι → ℂ × ℂ) : ℝ :=
  (∏ i, pairDensity χ β lam (c i)) * cutInd h c * shortInd (17 * h) Df c

omit [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ] in
/-- Common densities and cutoff supports are nonnegative. -/
theorem mixedDensity_nonneg (χ : ℂ → ℝ) (β lam h : ℝ) (Df : Finset (Sym2 ι))
    (c : ι → ℂ × ℂ) : 0 ≤ mixedDensity χ β lam h Df c := by
  classical
  unfold mixedDensity shortInd
  apply mul_nonneg (mul_nonneg
    (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le) (cutInd_nonneg h c))
  apply prod_nonneg
  intro e _
  split_ifs <;> norm_num

end MultipoleBKT.ExpansionK.RouteCases

end
