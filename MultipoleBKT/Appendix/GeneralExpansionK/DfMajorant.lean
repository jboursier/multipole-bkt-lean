/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.ParityMajorant
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ComponentBounds

/-!
# Nonnegativity of the absolute bond weight

See Lemma A.7. The absolute bond weight is nonnegative on every unordered label pair.
The component bounds are imported from `RouteCases.ComponentBounds`.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open Finset SimpleGraph
open Limits

variable {M lam : ℝ}

/-! ### The weights -/

section Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem ahatE_nonneg (c : ι → ℂ × ℂ) (e : Sym2 ι) : 0 ≤ ahatE c e := by
  induction e using Sym2.ind with
  | h i j => exact ahat_nonneg _ _

end Weights

end ExpansionK

end MultipoleBKT

end
