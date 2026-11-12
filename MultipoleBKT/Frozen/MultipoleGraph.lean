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
public import MultipoleBKT.Frozen.MultipoleLinked

/-!
# Frozen: `MultipoleBKT.multipoleGraph`

See the paper, Definition 2.2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- vertices `Fin N`, dipoles `(x_i, y_{σ_N(i)})`.
-- the literal relation `MultipoleLinked`.
/-- The multipole graph (Definition 2.2 (1)–(2)): the graph on `[N]` with
`i ~ j` iff `i ≠ j` and `i ↔_{σ_N} j`, computed on the dipoles `(x_i, y_{σ_N(i)})`. Its
connected components are the multipoles. -/
noncomputable def multipoleGraph {N : ℕ} (M lam : ℝ) (c : Fin N → ℂ × ℂ) :
    SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun i j =>
    MultipoleLinked M lam ((c i).1, (c (stableMatching c i)).2)
      ((c j).1, (c (stableMatching c j)).2)

end MultipoleBKT

end
