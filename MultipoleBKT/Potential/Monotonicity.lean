/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.Potential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Monotonicity of the smeared kernels in the radii (Lemma 3.2)

See Lemma 3.2 of the paper. The weak Poisson equation for the difference gives a
nonpositive circle flux by scaling enclosed masses. Radial symmetry gives a
nonpositive radial derivative. Newton's theorem gives the exterior zero value,
so the difference is nonnegative everywhere. The two positive convolutions
then give monotonicity in both smoothing radii.

The same flux formula gives radial decrease of a single smoothed potential.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam α η : ℝ}

/-- The difference of two potentials decreases with the radius, by its flux sign.
See Lemma 3.2 of the paper. -/
theorem antitoneOn_smearedPotential_sub (hχ : IsMollifier χ) (hα : 0 < α) (hαη : α ≤ η) :
    AntitoneOn (fun r : ℝ => smearedPotential χ α (r : ℂ) -
      smearedPotential χ η (r : ℂ)) (Ici 0) := by
  have hη := hα.trans_le hαη
  apply antitoneOn_of_deriv_nonpos (f := fun r : ℝ =>
    smearedPotential χ α (r : ℂ) - smearedPotential χ η (r : ℂ)) (convex_Ici 0)
    (((continuous_smearedPotential hχ hα).comp Complex.continuous_ofReal).sub
      ((continuous_smearedPotential hχ hη).comp Complex.continuous_ofReal)).continuousOn
  · intro r _
    exact ((RouteFlux.hasDerivAt_smearedPotential_real hχ hα r).sub
      (RouteFlux.hasDerivAt_smearedPotential_real hχ hη r)).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ici, mem_Ioi] at hr
    calc
      deriv (fun t : ℝ => smearedPotential χ α (t : ℂ) -
          smearedPotential χ η (t : ℂ)) r = _ :=
        ((RouteFlux.hasDerivAt_smearedPotential_real hχ hα r).sub
          (RouteFlux.hasDerivAt_smearedPotential_real hχ hη r)).deriv
      _ ≤ 0 := RouteFlux.radialComponent_sub_nonpos hχ hα hαη hr

/-- Newton's theorem gives the exterior zero value of the difference.
See Lemma 3.2 of the paper. -/
theorem smearedPotential_sub_eq_zero_of_le_norm (hχ : IsMollifier χ) (hα : 0 < α)
    (hαη : α ≤ η) {x : ℂ} (hx : η ≤ ‖x‖) :
    smearedPotential χ α x - smearedPotential χ η x = 0 := by
  rw [smearedPotential_eq_logKernel hχ hα (hαη.trans hx),
    smearedPotential_eq_logKernel hχ (hα.trans_le hαη) hx, sub_self]

/-- **Equation (3.5)**: for `0 < α ≤ η`, `g * δ₀^{(α)} ≥ g * δ₀^{(η)}` pointwise. -/
theorem smearedPotential_le_of_le (hχ : IsMollifier χ) (hα : 0 < α) (hαη : α ≤ η) (x : ℂ) :
    smearedPotential χ η x ≤ smearedPotential χ α x := by
  have hη := hα.trans_le hαη
  have he (β : ℝ) (hβ : 0 < β) :
      smearedPotential χ β x = smearedPotential χ β (‖x‖ : ℂ) :=
    smearedPotential_eq_of_norm_eq hχ hβ (by simp)
  rw [he α hα, he η hη, ← sub_nonneg]
  by_cases hx : η ≤ ‖x‖
  · rw [← he α hα, ← he η hη, smearedPotential_sub_eq_zero_of_le_norm hχ hα hαη hx]
  · have hzero := smearedPotential_sub_eq_zero_of_le_norm hχ hα hαη
      (x := (η : ℂ)) (by simp [Complex.norm_real, abs_of_pos hη])
    have h := antitoneOn_smearedPotential_sub hχ hα hαη (norm_nonneg x) hη.le
      (le_of_not_ge hx)
    dsimp only at h
    rwa [hzero] at h

/-- Equation (3.5) for charges centred at any `z`: for `0 < α ≤ η`,
`∫ g(x - y) dδ_z^{(η)}(y) ≤ ∫ g(x - y) dδ_z^{(α)}(y)`. -/
theorem integral_logKernel_sub_smearedCharge_le_of_le (hχ : IsMollifier χ) (hα : 0 < α)
    (hαη : α ≤ η) (x z : ℂ) :
    ∫ y, logKernel (x - y) ∂smearedCharge χ z η ≤ ∫ y, logKernel (x - y) ∂smearedCharge χ z α := by
  rw [integral_logKernel_sub_smearedCharge_eq_smearedPotential,
    integral_logKernel_sub_smearedCharge_eq_smearedPotential]
  exact smearedPotential_le_of_le hχ hα hαη (x - z)

/-! ### Equations (3.3) and (3.4) -/

/-- Monotonicity in the second radius: for `0 < η ≤ η'`,
`g * δ₀^{(α)} * δ₀^{(η')} ≤ g * δ₀^{(α)} * δ₀^{(η)}`. -/
theorem twoRadiusKernel_le_of_le_right (hχ : IsMollifier χ) (α : ℝ) {η' : ℝ} (hη : 0 < η)
    (hηη' : η ≤ η') (z : ℂ) : twoRadiusKernel χ α η' z ≤ twoRadiusKernel χ α η z := by
  have hη' : 0 < η' := hη.trans_le hηη'
  rw [twoRadiusKernel_eq_integral_smearedPotential hχ,
    twoRadiusKernel_eq_integral_smearedPotential hχ]
  exact integral_mono
    (integrable_smearedPotential_comp hχ hη' (continuous_const.sub continuous_id) 0 α)
    (integrable_smearedPotential_comp hχ hη (continuous_const.sub continuous_id) 0 α)
    fun a => smearedPotential_le_of_le hχ hη hηη' (z - a)

/-- Monotonicity in the first radius: for `0 < α ≤ α'`,
`g * δ₀^{(α')} * δ₀^{(η)} ≤ g * δ₀^{(α)} * δ₀^{(η)}`. -/
theorem twoRadiusKernel_le_of_le_left (hχ : IsMollifier χ) {α' : ℝ} (hα : 0 < α)
    (hαα' : α ≤ α') (η : ℝ) (z : ℂ) : twoRadiusKernel χ α' η z ≤ twoRadiusKernel χ α η z := by
  rw [twoRadiusKernel_comm hχ α' η, twoRadiusKernel_comm hχ α η]
  exact twoRadiusKernel_le_of_le_right hχ η hα hαα' z

/-- **Lemma 3.2, equation (3.3)**: if `0 < α₁ ≤ η₁` and `0 < α₂ ≤ η₂`, then
`g * δ₀^{(α₁)} * δ₀^{(α₂)} ≥ g * δ₀^{(η₁)} * δ₀^{(η₂)}`. -/
theorem twoRadiusKernel_le_twoRadiusKernel (hχ : IsMollifier χ) {α₁ α₂ η₁ η₂ : ℝ}
    (hα₁ : 0 < α₁) (h₁ : α₁ ≤ η₁) (hα₂ : 0 < α₂) (h₂ : α₂ ≤ η₂) (z : ℂ) :
    twoRadiusKernel χ η₁ η₂ z ≤ twoRadiusKernel χ α₁ α₂ z :=
  (twoRadiusKernel_le_of_le_left hχ hα₁ h₁ η₂ z).trans
    (twoRadiusKernel_le_of_le_right hχ α₁ hα₂ h₂ z)

/-- **Lemma 3.2, equation (3.4)**: if `0 < α ≤ η`, then `g_α ≥ g_η`. -/
theorem smearedKernel_le_smearedKernel (hχ : IsMollifier χ) (hα : 0 < α) (hαη : α ≤ η)
    (z : ℂ) : smearedKernel χ η z ≤ smearedKernel χ α z := by
  rw [← twoRadiusKernel_self, ← twoRadiusKernel_self]
  exact twoRadiusKernel_le_twoRadiusKernel hχ hα hαη hα hαη z

/-! ### Radial monotonicity of the potential -/

/-- `g * δ₀^{(λ)}` is radially nonincreasing: `|x| ≤ |x'|` gives
`(g * δ₀^{(λ)})(x') ≤ (g * δ₀^{(λ)})(x)`. -/
theorem smearedPotential_le_of_norm_le (hχ : IsMollifier χ) (hlam : 0 < lam) {x x' : ℂ}
    (h : ‖x‖ ≤ ‖x'‖) : smearedPotential χ lam x' ≤ smearedPotential χ lam x := by
  have hd := fun r => RouteFlux.hasDerivAt_smearedPotential_real hχ hlam r
  have hanti : AntitoneOn (fun r : ℝ => smearedPotential χ lam (r : ℂ)) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (f := fun r : ℝ => smearedPotential χ lam (r : ℂ))
      (convex_Ici 0)
      ((continuous_smearedPotential hχ hlam).comp Complex.continuous_ofReal).continuousOn
    · exact fun r _ => (hd r).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Ici, mem_Ioi] at hr
      rw [(hd r).deriv, RouteFlux.radialComponent_convolvedField hχ hlam hr]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (RouteFlux.massProfile_nonneg χ lam r)) hr.le
  have he (y : ℂ) : smearedPotential χ lam y = smearedPotential χ lam (‖y‖ : ℂ) :=
    smearedPotential_eq_of_norm_eq hχ hlam (by simp)
  rw [he x, he x']
  exact hanti (norm_nonneg x) (norm_nonneg x') h

end MultipoleBKT

end
