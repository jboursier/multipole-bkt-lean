/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.AnalyticControls

/-!
# Controls for the two admissible models

See Lemma A.7. Both coefficients precede lambda and all frozen data.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SmallIntegral Hierarchical

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
/-- All ordinary and selected-factor estimates for the actual extended frozen
corrections. There is no all-good hypothesis on individual terms. -/
theorem frozen_controls {χ : ℂ → ℝ} {β L : ℝ} (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {N p₀ : ℕ} {lam M ε₀ : ℝ}
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → 1 ≤ M →
      ∀ c : ι → ℂ × ℂ,
      InternalControls K (fun i => rhoD lam (c i))
        (routeFrozenRadius p₀ β lam ε₀ V Z ∘ c)
        (mixedOddWeight M lam c) (mixedEvenWeight M lam c)
        (gammaW β (routeFrozenInteraction χ p₀ β lam ε₀ V Z) M lam c)
        (gammaW β (dipoleInteraction χ lam) M lam c)
        (fun e => alphaW β (routeFrozenInteraction χ p₀ β lam ε₀ V Z) M lam c e + linkIndE M lam c e)
        (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
        (intraRatio β (routeFrozenInteraction χ p₀ β lam ε₀ V Z) (dipoleInteraction χ lam) c)
        (routeFrozenQuadratic p₀ β lam ε₀ L V Z ∘ c)
        (routeFrozenBad p₀ β lam M ε₀ V Z ∘ c) := by
  obtain ⟨Ce, hCe, he⟩ := routeFrozen_interaction_bounds hχ
  obtain ⟨Cv, hCv, hv⟩ := BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ
  obtain ⟨K, hK, hk⟩ := internal_controls_of_interactions (ι := ι) (L := L) hβ
    (add_nonneg hCe.le hCv) hCe.le
  refine ⟨K, hK, ?_⟩
  intro N p₀ lam M ε₀ V Z hlam hM c
  refine hk hlam hM _ _ c _ (fun i => hlam.trans_le (routeFrozenRadius_lower p₀ β lam ε₀ V Z (c i)).1)
    (fun i => by dsimp only [Function.comp_apply]; linarith [(routeFrozenRadius_lower p₀ β lam ε₀ V Z (c i)).2])
    (fun i => ?_) (fun i j hf => ?_) (fun i j => (he V Z hlam hM (c i) (c j)).1)
  · dsimp only [Function.comp_apply, routeFrozenBad]
    split_ifs <;> norm_num
  · exact ⟨((he V Z hlam hM (c i) (c j)).2 hf).trans
      (mul_le_mul_of_nonneg_right (by linarith) (ahat_nonneg _ _)),
      (hv lam hlam M hM (c i) (c j) hf).trans
      (mul_le_mul_of_nonneg_right (by linarith) (ahat_nonneg _ _))⟩

omit [Fintype ι] in
/-- The screened model has the same controls with its literal Gaussian
correction and cutoff screening radius. The zero bad correction is exact. -/
theorem screened_controls {χ : ℂ → ℝ} {β L : ℝ} (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {lam M ε₀ R : ℝ}, 0 < lam → 1 ≤ M → lam ≤ ε₀ * R →
      ∀ (c : ι → ℂ × ℂ), (∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      InternalControls K (fun i => rhoD lam (c i)) (fun _ => ε₀ * R)
        (mixedOddWeight M lam c) (mixedEvenWeight M lam c)
        (gammaW β (upperBoundInteraction χ lam ε₀ R) M lam c)
        (gammaW β (dipoleInteraction χ lam) M lam c)
        (fun e => alphaW β (upperBoundInteraction χ lam ε₀ R) M lam c e + linkIndE M lam c e)
        (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
        (intraRatio β (upperBoundInteraction χ lam ε₀ R) (dipoleInteraction χ lam) c)
        (fun i => Real.exp (-L * (‖(c i).1 - (c i).2‖ / (ε₀ * R)) ^ 2) - 1) (fun _ => 0) := by
  obtain ⟨K, hK, hk⟩ := internal_controls_of_interactions (ι := ι) (L := -L) hβ
    (cA_nonneg hχ) (c310_pos hχ).le
  refine ⟨K, hK, ?_⟩
  intro lam M ε₀ R hlam hM hlh c hcut
  have hh : 0 < ε₀ * R := hlam.trans_le hlh
  obtain ⟨hw, hv, -, hd⟩ := minus_far_facts hχ hlam hM hlh c hcut
  refine hk hlam hM _ _ c _ (fun _ => hh) (fun i => by linarith [hcut i])
    (fun _ => by norm_num) (fun i j hf => ⟨hw i j hf, hv i j hf⟩) ?_
  intro i j
  have h8i : 8 * max ‖(c i).2 - (c i).1‖ lam ≤ 8 * ε₀ * R := by
    rw [norm_sub_rev, mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le (hcut i) hlh) (by norm_num)
  have h8j : 8 * max ‖(c j).2 - (c j).1‖ lam ≤ 8 * ε₀ * R := by
    rw [norm_sub_rev, mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le (hcut j) hlh) (by norm_num)
  have hp := ((Classical.choose_spec (lemma_3_10 hχ)).2 lam (8 * ε₀ * R) hlam (c i) (c j) h8i h8j).1
  change |upperBoundInteraction χ lam ε₀ R (c i) (c j) - dipoleInteraction χ lam (c i) (c j)| ≤
    c310 hχ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / (8 * ε₀ * R) ^ 2 at hp
  apply hp.trans
  rw [max_self]
  exact div_le_div_of_nonneg_left (mul_nonneg (c310_pos hχ).le (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (pow_pos hh 2)
    (pow_le_pow_left₀ hh.le (by rw [mul_assoc]; linarith) 2)

end MultipoleBKT.ExpansionK.RouteCases

end
