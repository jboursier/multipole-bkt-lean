/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.Measurable
import TwoComponentCoulomb.Potential.DiscField
import TwoComponentCoulomb.Potential.DiscPotential

/-!
# Polar Fubini on a punctured disc

See Lemma 3.1 of the paper. These change-of-variables identities retain the inner boundary.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteHessian

/-- Polar Fubini with the radial integration performed first on an annulus. -/
theorem integral_annulus_polar {F : ℂ → ℝ} (hm : Measurable F)
    {ε R : ℝ} (hε : 0 ≤ ε) (hεR : ε ≤ R)
    (hi : IntegrableOn F (ball (0 : ℂ) R)) :
    (∫ x in ball (0 : ℂ) R \ closedBall 0 ε, F x) =
      ∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in ε..R, r * F (circleMap 0 r θ) := by
  let S := ball (0 : ℂ) R \ closedBall 0 ε
  let G := S.indicator F
  have hS : MeasurableSet S := measurableSet_ball.diff measurableSet_closedBall
  have hGm : Measurable G := hm.indicator hS
  have hGi : Integrable G := (integrable_indicator_iff hS).mpr (hi.mono_set sdiff_subset)
  have hP := TwoComponentCoulomb.integrableOn_polarCoord_target_of_integrable hGm hGi
  rw [Complex.polarCoord_target] at hP
  have hP' : Integrable (fun p : ℝ × ℝ => p.1 • G (Complex.polarCoord.symm p))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hP
  rw [← integral_indicator hS, ← Complex.integral_comp_polarCoord_symm G]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • G (Complex.polarCoord.symm p)) = _
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod _ _,
    ← Measure.prod_restrict, integral_prod_symm _ hP']
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  have he : ∀ r ∈ Ioi (0 : ℝ), r • G (Complex.polarCoord.symm (r, θ)) =
      (Ioo ε R).indicator (fun r => r * F (circleMap 0 r θ)) r := by
    intro r hr
    rw [TwoComponentCoulomb.polarCoord_symm_eq_circleMap]
    have hs : circleMap 0 r θ ∈ S ↔ r ∈ Ioo ε R := by
      simp only [S, Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff,
        norm_circleMap_zero, abs_of_pos hr, not_le, mem_Ioo]
      exact and_comm
    by_cases hh : r ∈ Ioo ε R
    · simp [G, indicator_of_mem (hs.mpr hh), hh, smul_eq_mul]
    · simp [G, indicator_of_notMem (hs.not.mpr hh), hh]
  dsimp only
  rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Ioo]
  have hs : Ioi (0 : ℝ) ∩ Ioo ε R = Ioo ε R :=
    inter_eq_right.mpr (fun _ hr => hε.trans_lt hr.1)
  rw [hs, intervalIntegral.integral_of_le hεR, integral_Ioc_eq_integral_Ioo]

end MultipoleBKT.RouteHessian

end
