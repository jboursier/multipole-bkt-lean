/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Separation
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Indicators

/-!
# Retaining separation in the three marked-gain cases

The paper: (5.106). A raw marked term contains every separation indicator
of each odd component. Multiplying a comparison by that same indicator
keeps it available for the replacement-family estimates.
-/

public section

namespace MultipoleBKT.UpperBound.NonEmptyMarks.RouteGain

/-- Internal arithmetic for carrying an indicator through a comparison. -/
theorem le_mul_indicator {a b f s : ℝ} (ha : a = a * s) (hab : a ≤ f * b)
    (hs : 0 ≤ s) : a ≤ f * (b * s) := by
  calc a = a * s := ha
    _ ≤ (f * b) * s := mul_le_mul_of_nonneg_right hab hs
    _ = f * (b * s) := mul_assoc _ _ _

end MultipoleBKT.UpperBound.NonEmptyMarks.RouteGain

end
