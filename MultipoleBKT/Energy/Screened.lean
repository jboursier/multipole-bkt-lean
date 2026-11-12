/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.SmearedCorrection

/-!
# The screened correction estimate

The mixed source derivative and translation argument for (3.20) in the paper.
The screened objects and their regularity API are defined in `RouteNeumann.Base`.
-/

public section

open MeasureTheory Metric Set InnerProductSpace

namespace MultipoleBKT

variable {lam τ : ℝ} {d : ℂ × ℂ}

/-- **Lemma 3.5, equation (3.20)**: the correction
bound follows by translating smeared sources. Since the correction is independent
of the mollifier, the uniform unit-disc density supplies the source here. -/
theorem norm_screenedCorrectionField_le (hlam : 0 < lam) (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ)
    {w : ℂ} (hw : ‖w - dipoleMidpoint d‖ ≤ τ) :
    ‖screenedCorrectionField τ d w‖ ≤ 2 * ‖d.2 - d.1‖ / τ ^ 2 := by
  exact RouteNeumann.norm_correction_via_smeared_translation
    RouteNeumann.isMollifier_unitDisc hlam hτ hw

end MultipoleBKT
