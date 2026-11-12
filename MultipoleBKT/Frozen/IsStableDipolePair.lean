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
public import MultipoleBKT.Frozen.StableMatching

/-!
# Frozen: `MultipoleBKT.IsStableDipolePair`

See the paper, equation (4.2).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- the pair is passed in increasing label order (`i < j`), so `𝒜_ij`
-- is symmetric in `i, j` by construction.
/-- The event `𝒜_ij` (Definition 4.4, eq. (4.2)), for the dipoles
`d = (x_i, y_i)` and `e = (x_j, y_j)` with `i < j`: the stable matching of `x_i, x_j` with
`y_i, y_j` alone is the identity, `σ₂[(x_i, x_j), (y_i, y_j)] = Id_{i,j}`. -/
def IsStableDipolePair (d e : ℂ × ℂ) : Prop :=
  stableMatching ![d, e] = Equiv.refl (Fin 2)

end MultipoleBKT

end
