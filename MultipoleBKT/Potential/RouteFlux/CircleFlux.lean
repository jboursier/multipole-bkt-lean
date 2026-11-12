/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.Continuity
public import MultipoleBKT.Potential.RouteFlux.WeakStokes
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle flux from the weak Poisson equation

See Lemmas 3.1 and 3.2 of the paper.

Test each weak Poisson equation against smooth radial cutoffs of the disc.
The source integral converges to enclosed mass. Continuity of the field gives
the boundary flux limit on the other side. Thus the flux identities follow
from the weak equations, as in the paper's application of Stokes's formula.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology Complex
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteFlux

variable {χ : ℂ → ℝ} {α η : ℝ}

/-- Stokes's formula for the weak Poisson solution with a continuous field.
The source density need only be bounded and measurable. -/
theorem circleFlux_convolvedField (hχ : IsMollifier χ) (z : ℂ) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) :
    circleFlux (convolvedField χ z α) r =
      -(2 * Real.pi) * (smearedCharge χ z α).real (ball 0 r) := by
  have := isFiniteMeasure_smearedCharge hχ z α
  have hfield := tendsto_integral_fderiv_fluxCutoff
    (continuous_convolvedField_center hχ z hα) hr
  have hsource := (tendsto_integral_fluxCutoff (smearedCharge χ z α) hr
    (ae_norm_ne_smearedCharge χ z α r)).const_mul (2 * Real.pi)
  have he : (fun h => ∫ x, fderiv ℝ (fluxCutoff r h) x (convolvedField χ z α x)) =ᶠ[𝓝[>] 0]
      fun h => 2 * Real.pi * ∫ y, fluxCutoff r h y ∂smearedCharge χ z α := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact weakPoisson_convolvedField hχ (contDiff_fluxCutoff r h)
      (hasCompactSupport_fluxCutoff hr hh) z hα
  have hlim := tendsto_nhds_unique hfield (hsource.congr' he.symm)
  linarith

private theorem circleFlux_sub {F G : ℂ → ℂ} (hF : Continuous F) (hG : Continuous G) (r : ℝ) :
    circleFlux (F - G) r = circleFlux F r - circleFlux G r := by
  unfold circleFlux
  simp_rw [Pi.sub_apply, inner_sub_left]
  apply integral_sub
  · exact (((hF.comp (continuous_circleMap 0 r)).inner (continuous_circleMap 0 r)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · exact (((hG.comp (continuous_circleMap 0 r)).inner (continuous_circleMap 0 r)).integrableOn_Icc).mono_set Ioo_subset_Icc_self

/-- Stokes's formula applied to the difference equation in Lemma 3.2.
This proof tests `weakPoisson_sub_convolvedField` directly. -/
theorem circleFlux_sub_convolvedField (hχ : IsMollifier χ) (z : ℂ) (hα : 0 < α)
    (hη : 0 < η) {r : ℝ} (hr : 0 < r) :
    circleFlux (convolvedField χ z α) r - circleFlux (convolvedField χ z η) r =
      -(2 * Real.pi) * ((smearedCharge χ z α).real (ball 0 r) -
        (smearedCharge χ z η).real (ball 0 r)) := by
  have := isFiniteMeasure_smearedCharge hχ z α
  have := isFiniteMeasure_smearedCharge hχ z η
  have hαc := continuous_convolvedField_center hχ z hα
  have hηc := continuous_convolvedField_center hχ z hη
  have hfield := tendsto_integral_fderiv_fluxCutoff (hαc.sub hηc) hr
  have hsource := ((tendsto_integral_fluxCutoff (smearedCharge χ z α) hr
    (ae_norm_ne_smearedCharge χ z α r)).sub
      (tendsto_integral_fluxCutoff (smearedCharge χ z η) hr
        (ae_norm_ne_smearedCharge χ z η r))).const_mul (2 * Real.pi)
  have he : (fun h => ∫ x, fderiv ℝ (fluxCutoff r h) x
      (convolvedField χ z α x - convolvedField χ z η x)) =ᶠ[𝓝[>] 0]
      fun h => 2 * Real.pi * ((∫ y, fluxCutoff r h y ∂smearedCharge χ z α) -
        ∫ y, fluxCutoff r h y ∂smearedCharge χ z η) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact weakPoisson_sub_convolvedField hχ (contDiff_fluxCutoff r h)
      (hasCompactSupport_fluxCutoff hr hh) z hα hη
  have hlim := tendsto_nhds_unique hfield (hsource.congr' he.symm)
  rw [circleFlux_sub hαc hηc] at hlim
  linarith

end MultipoleBKT.RouteFlux

end
