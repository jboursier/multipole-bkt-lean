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
# Frozen: `MultipoleBKT.simplex`

See the paper, Definition 2.15.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- `Fin p`, coordinate `i` carrying weight `i + 1`.
/-- `Δ_{p,x} = {(γ_1, …, γ_p) ∈ [0,1]^p : γ_1 + 2γ_2 + ⋯ + pγ_p = 1 - x}`, Definition 2.15, with `γ i = γ_{i+1}`. -/
def simplex (p : ℕ) (x : ℝ) : Set (Fin p → ℝ) :=
  {γ | (∀ i, γ i ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * γ i = 1 - x}

end MultipoleBKT

end
