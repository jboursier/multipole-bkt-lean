/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MultipoleBKT.Frozen.TransitionBeta
public import MultipoleBKT.Frozen.CriticalScale

/-!
# Frozen: `MultipoleBKT.errorRate`

See the paper, equation (2.37).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- total; the `∑'` has at most one nonzero term.
-- `p₀ : ℕ` explicit.
/-- The error rate `δ_{β,λ}`, Definition 2.9 (eq. (2.37)):
`R_{β,λ}^{-2} 𝟙_{β∈(2,4)} (1 + ∑_{p ≥ 2} |log λ| 𝟙_{β = β_p}) + λ^{2p₀} 𝟙_{β ≥ 4}`. -/
noncomputable def errorRate (p₀ : ℕ) (β lam : ℝ) : ℝ :=
  (if 2 < β ∧ β < 4 then
      (criticalScale β lam).toReal ^ (-2 : ℤ) *
        (1 + ∑' q : ℕ, if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0)
    else 0)
  + if 4 ≤ β then lam ^ (2 * p₀) else 0

end MultipoleBKT

end
