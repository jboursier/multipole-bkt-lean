/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.Radial

/-!
# The cut dipole weight

See (A.36). This is the actual smeared weight restricted to the cutoff disc.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set Metric
open scoped ENNReal

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- The cut dipole weight `e^{β g_λ(w)} 𝟙_{|w| ≤ h}`. -/
noncomputable def cutWeight (χ : ℂ → ℝ) (β lam h : ℝ) (w : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((closedBall (0 : ℂ) h).indicator
    (fun w => Real.exp (β * smearedKernel χ lam w)) w)

theorem measurable_cutWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β h : ℝ) :
    Measurable (cutWeight χ β lam h) :=
  ENNReal.measurable_ofReal.comp
    ((measurable_exp_smearedKernel hχ hlam β).indicator measurableSet_closedBall)


end MultipoleBKT.GeneralExpansion

end
