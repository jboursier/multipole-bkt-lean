/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.MinusAssembly

/-!
# Screened pair weights and radial support

See Lemma A.7. The stable pair-weight constant and the radial cutoff identities
are shared by the screened assembly and the omitted baseline estimate.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph
open Hierarchical Multipole Parity Limits SmallIntegral

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Constants -/

/-- The bound `e^{β(C_b + C/64)}` of the pair weights. -/
noncomputable def Wm (hχ : IsMollifier χ) (β : ℝ) : ℝ := Real.exp (β * (cbK hχ + c310 hχ / 64))

theorem one_le_Wm (hχ : IsMollifier χ) (hβ : 0 ≤ β) : 1 ≤ Wm hχ β :=
  Real.one_le_exp (mul_nonneg hβ (add_nonneg (cbK_nonneg hχ) (by have := c310_pos hχ; positivity)))

/-! ### Cut configurations -/

section Cut

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem cutInd_eq_one_or (h : ℝ) (c : ι → ℂ × ℂ) :
    (cutInd h c = 1 ∧ ∀ i, ‖(c i).1 - (c i).2‖ ≤ h) ∨ cutInd h c = 0 := by
  classical
  unfold cutInd
  by_cases hall : ∀ i, ‖(c i).1 - (c i).2‖ ≤ h
  · exact Or.inl ⟨prod_eq_one fun i _ => by rw [ite_eq_left (hall i)], hall⟩
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    exact Or.inr (prod_eq_zero (mem_univ i) (by rw [ite_eq_right (not_le.2 hi)]))

omit [DecidableEq ι] in
theorem maxRad_le_of_cut {h : ℝ} (hlh : lam ≤ h) (c : ι → ℂ × ℂ)
    (hcut : ∀ i, ‖(c i).1 - (c i).2‖ ≤ h) : maxRad lam c ≤ h := by
  unfold maxRad
  rw [Finset.fold_max_le]
  exact ⟨hlh, fun i _ => max_le (hcut i) hlh⟩

end Cut

end ExpansionK

end MultipoleBKT

end
