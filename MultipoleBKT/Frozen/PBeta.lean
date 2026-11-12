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
public import MultipoleBKT.Frozen.PStar

/-!
# Frozen: `MultipoleBKT.pBeta`

See the paper, Definition 2.8.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- total in `β`; `ENat.toNat` is exact on `(2, 4)`, where `p*(β) < ∞`.
-- `p₀ : ℕ` explicit.
/-- The series truncation parameter `p(β)`, Definition 2.8:
`p*(β)` if `β ∈ (2, 4)` (where `p*(β)` is finite) and `p₀` if `β ≥ 4`. -/
noncomputable def pBeta (p₀ : ℕ) (β : ℝ) : ℕ :=
  if β < 4 then (pStar β).toNat else p₀

end MultipoleBKT

end
