/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ModelControls

/-!
# The distinguished even kernel throughout the extended expansion

See (A.61) and (A.62). The refinement is valid off the all-good event too.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Limits SmallIntegral

variable {ι : Type*} [LinearOrder ι]

/-- Internal version of the refined even estimate from the two interaction
bounds. It retains the distinguished even kernel, including both endpoint squares. -/
theorem internal_refined_even {χ : ℂ → ℝ} {β C D : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {lam M : ℝ}, 0 < lam → 1 ≤ M →
      ∀ (w : ℂ × ℂ → ℂ × ℂ → ℝ) (τ : ι → ℝ) (c : ι → ℂ × ℂ),
      (∀ i, 0 < τ i) →
      (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
        |w (c i) (c j)| + |dipoleInteraction χ lam (c i) (c j)| ≤ C * ahat (c i) (c j)) →
      (∀ i j, |w (c i) (c j) - dipoleInteraction χ lam (c i) (c j)| ≤
        D * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max (τ i) (τ j) ^ 2) →
      ∀ i j, |(alphaW β w M lam c s(i,j) + linkIndE M lam c s(i,j)) -
        (alphaW β (dipoleInteraction χ lam) M lam c s(i,j) + linkIndE M lam c s(i,j))| ≤
        K * ((τ i ^ 2)⁻¹ * markedEvenKernel (rhoD lam (c i)) (rhoD lam (c j)) (dipoleDist (c i) (c j))) := by
  classical
  let K := β ^ 2 * C * max C D * Real.exp (β * C)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro lam M hlam hM w τ c hτ hw herr i j
  have hkernel : 0 ≤ markedEvenKernel (rhoD lam (c i)) (rhoD lam (c j)) (dipoleDist (c i) (c j)) := by
    unfold markedEvenKernel
    exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (dipoleDist_nonneg _ _) ((dipoleDist_nonneg _ _).trans (le_max_left _ _)))
  by_cases hf : FarE M lam c s(i,j)
  · have hwo : |wOrd w c i j| + |wOrd (dipoleInteraction χ lam) c i j| ≤ C * ahat (c i) (c j) := by
      unfold wOrd
      split_ifs
      · exact hw i j hf
      · simpa only [ahat_comm] using hw j i (fun h => hf (multipoleLinked_comm.1 h))
    have hdord : |wOrd w c i j - wOrd (dipoleInteraction χ lam) c i j| ≤
        D * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max (τ i) (τ j) ^ 2 := by
      unfold wOrd
      split_ifs
      · exact herr i j
      · simpa only [mul_comm ‖(c j).1 - (c j).2‖, max_comm (τ j)] using herr j i
    rw [mul_div_assoc] at hdord
    have hd := hlam.trans (far_facts hlam hM hf).1
    have hQ : dipoleDist (c i) (c j) ^ 2 ≤ dipoleDist (c i) (c j) *
        max (dipoleDist (c i) (c j)) (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖) := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) hd.le
    have hp := internal_marked_cosh_error hβ hC (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      ((hτ i).trans_le (le_max_left _ _)) hd hQ hwo (far_facts hlam hM hf).2.2 hdord
    simp only [alphaW, symmLift_mk, ite_eq_right hf]
    rw [show (Real.cosh (β * wOrd w c i j) - 1 + linkIndE M lam c s(i,j)) -
        (Real.cosh (β * wOrd (dipoleInteraction χ lam) c i j) - 1 + linkIndE M lam c s(i,j)) =
        Real.cosh (β * wOrd w c i j) - Real.cosh (β * wOrd (dipoleInteraction χ lam) c i j) by ring]
    refine hp.trans ?_
    rw [mul_pow]
    have hp' := internal_marked_even_root hK (hτ i) (le_max_left (τ i) (τ j)) hd.le
      (s := ‖(c i).1 - (c i).2‖) (t := ‖(c j).1 - (c j).2‖)
    have hm := markedEvenKernel_mono (norm_nonneg _) (norm_nonneg _)
      (le_max_left ‖(c i).1 - (c i).2‖ lam) (le_max_left ‖(c j).1 - (c j).2‖ lam) hd
    convert hp'.trans (mul_le_mul_of_nonneg_left hm (div_nonneg hK (sq_nonneg (τ i)))) using 1 <;>
      simp only [K, rhoD] <;> ring
  · simp only [alphaW_add_linkIndE_of_linked c hf, sub_self, abs_zero]
    exact mul_nonneg hK (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) hkernel)

end MultipoleBKT.ExpansionK.RouteCases

end
