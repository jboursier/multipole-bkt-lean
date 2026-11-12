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
# Frozen: `MultipoleBKT.transitionBeta`

See the paper, equation (1.3).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- total in `q` (`q = 0` gives `4`, never consumed).
/-- `β_q = 4 - 2/q`, eq. (1.3); used for `q ∈ ℕ*`. -/
noncomputable def transitionBeta (q : ℕ) : ℝ := 4 - 2 / q

end MultipoleBKT

end
