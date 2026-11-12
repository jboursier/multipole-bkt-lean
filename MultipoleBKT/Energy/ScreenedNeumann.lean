/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.Correction

/-!
# The variational Neumann identity for the screened field

The Green representation, zero-mean normalization and finite-energy
uniqueness follow the paper's treatment of (3.16). Testing the represented solution gives the public
weak identity used to paste screened fields in (3.25).
The source equation is superposed in `RouteNeumann.Superposition` before
boundary cutoffs in `RouteNeumann.WeakBase` extend the tests.
-/

public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam τ : ℝ} {d : ℂ × ℂ}

/-- The zero-mean solution of (3.16) is the Green superposition and has
unique finite-energy gradient. -/
theorem screened_neumann_green_solution (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ∃ U : RouteNeumann.EnergyPair (dipoleMidpoint d) τ,
      RouteNeumann.IsWeakSolution (dipoleMidpoint d) τ (RouteNeumann.sourceLp hχ hlam τ d) U ∧
      U.1 =ᵐ[volume.restrict (ball (dipoleMidpoint d) τ)]
        RouteNeumann.normalizedGreenAverage χ lam τ d ∧
      (∫ w in ball (dipoleMidpoint d) τ, U.1 w) = 0 ∧
      U.2 =ᵐ[volume.restrict (ball (dipoleMidpoint d) τ)]
        gradient (RouteNeumann.normalizedGreenAverage χ lam τ d) ∧
      ∀ V, RouteNeumann.IsWeakSolution (dipoleMidpoint d) τ
        (RouteNeumann.sourceLp hχ hlam τ d) V → V.2 = U.2 := by
  obtain ⟨U, hU, hp, _⟩ := RouteNeumann.exists_normalized_green_solution hχ hlam hτ
  refine ⟨U, hU, hp, ?_, RouteNeumann.weakSolution_gradient_eq_greenAverage hχ hlam hτ hU,
    fun V hV => RouteNeumann.gradient_unique hV hU⟩
  rw [integral_congr_ae hp, RouteNeumann.integral_normalizedGreenAverage hχ hlam hτ]

/-- The weak Neumann identity, including tests reaching the boundary.
The solution is the zero-mean Green average in the energy completion. -/
theorem integral_fderiv_apply_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {ρ : ℝ} (hρ : τ < ρ) {φ : ℂ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (ball (dipoleMidpoint d) ρ)) :
    ∫ w in ball (dipoleMidpoint d) τ, fderiv ℝ φ w (screenedField χ lam τ d w) =
      2 * Real.pi *
        ((∫ v, φ v ∂smearedCharge χ d.1 lam) - ∫ v, φ v ∂smearedCharge χ d.2 lam) := by
  have hcφ : ContinuousOn φ (closedBall (dipoleMidpoint d) τ) :=
    hφ.continuousOn.mono (closedBall_subset_ball hρ)
  have hp := RouteNeumann.memLp_of_continuousOn_closedBall hcφ
  have hcG : ContinuousOn (gradient φ) (ball (dipoleMidpoint d) ρ) :=
    (toDual ℝ ℂ).symm.continuous.comp_continuousOn
      (hφ.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)
  have hG := RouteNeumann.memLp_of_continuousOn_closedBall
    (hcG.mono (closedBall_subset_ball hρ))
  let V : RouteNeumann.EnergyPair (dipoleMidpoint d) τ :=
    (hp.toLp φ, hG.toLp (gradient φ))
  have hV : V ∈ RouteNeumann.classicalPairs (dipoleMidpoint d) τ := by
    refine ⟨φ, gradient φ, ρ, hρ, hφ, ?_, hp, hG, rfl⟩
    intro w hw
    exact (hφ.contDiffAt (isOpen_ball.mem_nhds hw)).differentiableAt one_ne_zero |>.hasGradientAt
  obtain ⟨U, hU, _, _, hUG, _⟩ := screened_neumann_green_solution hχ hlam hτ
  have hUF : U.2 =ᵐ[volume.restrict (ball (dipoleMidpoint d) τ)] screenedField χ lam τ d := by
    apply hUG.trans
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (RouteNeumann.hasGradientAt_normalizedGreenAverage hχ hlam hτ hw).gradient
  have htest := hU.test (subset_closure hV)
  have he : inner ℝ U.2 V.2 =
      ∫ w in ball (dipoleMidpoint d) τ, fderiv ℝ φ w (screenedField χ lam τ d w) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hUF, hG.coeFn_toLp] with w hw hgw
    change inner ℝ (U.2 w) ((hG.toLp (gradient φ)) w) = _
    rw [hw, hgw, inner_gradient_right]
    rfl
  rw [he, RouteNeumann.inner_sourceLp_test hχ hlam hτ hp] at htest
  exact htest

end MultipoleBKT
