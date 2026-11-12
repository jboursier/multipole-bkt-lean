/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.ExpE11
public import MultipoleBKT.LowerBound.Hierarchical.ActivityIntegral

/-!
# The unlinked bond identity

The proof of Proposition 4.23. The grouped lower route retains
its separation factors and applies parity before taking absolute values.
This algebraic identity is also used by the upper expansion.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

variable {ρ : Measure (ℂ × ℂ)} {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
  {K : Set (ℂ × ℂ)} {M lam : ℝ}

open scoped Classical in
/-- `u_ij = a^w_ij 𝟙_{𝓑_ij^c} + (b^w_ij 𝟙_{𝓑_ij^c} - 𝟙_{𝓑_ij})`. -/
theorem unlinkedBondOf_eq_add (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (d e : ℂ × ℂ) :
    unlinkedBondOf β w M lam d e = oddBondUnlinked β w M lam d e + evenBondMult β w M lam d e := by
  unfold unlinkedBondOf evenBondMult
  by_cases h : MultipoleLinked M lam d e
  · rw [ite_eq_left h, oddBondUnlinked_of_linked h, evenBondUnlinked_of_linked h, ite_eq_left h]
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    unfold oddBondUnlinked evenBondUnlinked
    rw [ite_eq_right h, ite_eq_right h, sub_zero, ← mayerBondOf_eq_add, mayerBondOf_eq]

end Hierarchical

end MultipoleBKT

end
