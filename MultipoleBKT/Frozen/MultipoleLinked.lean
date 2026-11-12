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

/-!
# Frozen: `MultipoleBKT.MultipoleLinked`

See the paper, equation (2.11).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- closed `≤`; the distance of two two-point sets is the minimum of
-- the four distances.
/-- The multipole relation between two dipoles `d = (x, y)` and `e = (x', y')` (Definition 2.2; Definition 2.3):
`dist({x, y}, {x', y'}) ≤ M min(max(|x - y|, λ), max(|x' - y'|, λ))`. Applied to
`(x_i, y_{σ_N(i)})` it is `i ↔_{σ_N} j` (event `𝖡_ij`); applied to `(x_i, y_i)` it is
`i ↔ j` (event `𝓑_ij`). -/
def MultipoleLinked (M lam : ℝ) (d e : ℂ × ℂ) : Prop :=
  min (min ‖d.1 - e.1‖ ‖d.1 - e.2‖) (min ‖d.2 - e.1‖ ‖d.2 - e.2‖) ≤
    M * min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam)

end MultipoleBKT

end
