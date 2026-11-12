/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Weight
import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.API

/-!
# Cutoff weights for the type-two spatial cells

The paper: Lemma 5.41. The cutoff is retained in the actual-tree radial reduction.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open MeasureTheory Finset MultipoleIntegral
open scoped ENNReal Classical
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- The weight of one dipole with the cutoff: `𝟙_{Λ²}(x, y) 𝟙_{|x - y| ≤ h} e^{β g_λ(x - y)}`. -/
noncomputable def cutDipoleWeight (χ : ℂ → ℝ) (β lam h : ℝ) (Nₐ : ℕ) (p : ℂ × ℂ) : ℝ≥0∞ :=
  (box Nₐ ×ˢ box Nₐ).indicator (fun p => (Metric.closedBall (0 : ℂ) h).indicator
    (fun w => ENNReal.ofReal (Real.exp (β * smearedKernel χ lam w))) (p.1 - p.2)) p

/-- The length factor `𝟙_{|w| ≤ h} e^{β g_λ(w)}`. -/
noncomputable def cutFactor (χ : ℂ → ℝ) (β lam h : ℝ) (w : ℂ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : ℂ) h).indicator
    (fun w => ENNReal.ofReal (Real.exp (β * smearedKernel χ lam w))) w

theorem measurable_cutFactor (hχ : IsMollifier χ) (hlam : 0 < lam) (β h : ℝ) :
    Measurable (cutFactor χ β lam h) :=
  Measurable.indicator (ENNReal.measurable_ofReal.comp (measurable_exp_smearedKernel hχ hlam β))
    measurableSet_closedBall

theorem measurable_cutDipoleWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β h : ℝ) (Nₐ : ℕ) :
    Measurable (cutDipoleWeight χ β lam h Nₐ) :=
  Measurable.indicator ((measurable_cutFactor hχ hlam β h).comp (measurable_fst.sub measurable_snd))
    (measurableSet_box_prod Nₐ)

/-- The simultaneous short-radius cutoff. -/
noncomputable def radialCut {ι : Type*} (h : ℝ) (r : ι → ℂ) : ℝ≥0∞ :=
  if ∀ i, ‖r i‖ ≤ h then 1 else 0

theorem measurable_radialCut {ι : Type*} [Fintype ι] (h : ℝ) :
    Measurable (radialCut (ι := ι) h) := by
  apply Measurable.ite _ measurable_const measurable_const
  have heq : {r : ι → ℂ | ∀ i, ‖r i‖ ≤ h} = ⋂ i, {r : ι → ℂ | ‖r i‖ ≤ h} := by
    ext r
    simp
  rw [heq]
  exact MeasurableSet.iInter fun i => measurableSet_le
    (measurable_pi_apply i).norm measurable_const

end MultipoleBKT.BadPointTypes

end
