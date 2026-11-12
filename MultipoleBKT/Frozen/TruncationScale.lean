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
public import MultipoleBKT.Frozen.CriticalScale

/-!
# Frozen: `MultipoleBKT.truncationScale`

See the paper, Definition 2.18.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- total in `β`, `λ`; used for `β > 2`, `λ ∈ (0,1)`.
/-- The truncation scale `R̄_{β,λ}`, Definition 2.18: `R_{β,λ}` if `β ∈ (2,4)` and `λ^{-2p₀}` if `β ≥ 4`.
For `β < 4`, `R_{β,λ} < ∞` and `toReal` is exact. -/
noncomputable def truncationScale (p₀ : ℕ) (β lam : ℝ) : ℝ :=
  if β < 4 then (criticalScale β lam).toReal else lam ^ (-(2 * (p₀ : ℤ)))

end MultipoleBKT

end
