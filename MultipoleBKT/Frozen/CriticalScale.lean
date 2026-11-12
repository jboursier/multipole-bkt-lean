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
# Frozen: `MultipoleBKT.criticalScale`

See the paper, equation (1.4).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- total; the value `+∞` lives in `ℝ≥0∞`.
/-- The critical length scale `R_{β,λ}`, eq. (1.4):
`λ^{-(β-2)/(4-β)}` if `β < 4` and `+∞` if `β ≥ 4`. -/
noncomputable def criticalScale (β lam : ℝ) : ℝ≥0∞ :=
  if β < 4 then ENNReal.ofReal (lam ^ (-(β - 2) / (4 - β))) else ⊤

end MultipoleBKT

end
