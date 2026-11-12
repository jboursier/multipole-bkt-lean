/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.WeightBounds

/-!
# Measurability of the external bond

The paper: Definition 5.14. The external-bond measurability theorem is used by the simplified upper-bound expansion.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Multipole Parity

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

theorem measurable_externalBondZ (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Measurable (externalBondZ χ p₀ β lam ε₀ V Z) := by
  unfold externalBondZ
  exact (Finset.measurable_prod _ fun j _ => Real.measurable_exp.comp (measurable_const.mul
    (measurable_interactionExtZ p₀ β lam ε₀ V Z hχ hlam j))).sub_const 1


end BoundedUpper

end UpperBound

end MultipoleBKT

end
