/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.Radial
public import MultipoleBKT.Limits.MultIntegrable

/-!
# Nonnegativity of the dipole distance

See Lemma A.7. The minimum of the four endpoint distances is nonnegative.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset Function
open scoped ENNReal
open Limits

variable {lam M : ℝ}

/-! ### Edge integrals -/

section EdgeIntegrals

theorem dipoleDist_nonneg (d e : ℂ × ℂ) : 0 ≤ dipoleDist d e :=
  le_min (le_min (norm_nonneg _) (norm_nonneg _)) (le_min (norm_nonneg _) (norm_nonneg _))

end EdgeIntegrals

end ExpansionK

end MultipoleBKT

end
