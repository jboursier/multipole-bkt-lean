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
public import MultipoleBKT.Frozen.MultipoleLinked

/-!
# Frozen: `MultipoleBKT.multipoleClassOn`

See the paper, Section 4.4.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- `Π_mult^U` is "the partition of `U` into multipoles (computed among
-- points in `U` only)"; on dipole
-- configurations this is the partition of `U` into the connected components of the graph that
-- `↔` (Definition 2.3, i.e. `MultipoleLinked` on the dipoles `d i`) induces on `U`.
open scoped Classical in
/-- The class `[i]^{Π_mult^U}` of `i ∈ U` in the multipoles computed among points of `U` only
("We compute multipoles on `U`"): the labels reachable from `i` in the
graph on `[N]` whose edges are the pairs `a ↔ b` (Definition 2.3, with the dipoles `d a`, `d b`)
with `a, b ∈ U`. For `i ∈ U` this is the connected component of `i` in the graph induced on
`U`. -/
noncomputable def multipoleClassOn {N : ℕ} (M lam : ℝ) (d : Fin N → ℂ × ℂ) (U : Finset (Fin N))
    (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun j =>
    (SimpleGraph.fromRel fun a b : Fin N =>
      a ∈ U ∧ b ∈ U ∧ MultipoleLinked M lam (d a) (d b)).Reachable i j

end MultipoleBKT

end
