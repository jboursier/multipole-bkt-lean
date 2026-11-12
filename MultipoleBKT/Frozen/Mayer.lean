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
public import MultipoleBKT.Frozen.MayerTerm

/-!
# Frozen: `MultipoleBKT.mayer`

See the paper, equation (2.36).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- `tsum`s; summability is asserted by the theorems.
-- a function of the coefficient function `kdip : ℕ → ℝ`.
/-- The truncated Mayer series `Mayer_{β,p,λ}`, eq. (2.36):
`∑_{n ≥ 1} ∑_{k ≥ 1}` of `mayerTerm`, evaluated at the coefficients `kdip`. -/
noncomputable def mayer (p : ℕ) (kdip : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, ∑' k : ℕ+, mayerTerm p kdip n k

end MultipoleBKT

end
