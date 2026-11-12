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
public import MultipoleBKT.Frozen.IsSubpartition

/-!
# Frozen: `MultipoleBKT.boundedBlockPartitions`

See the paper, Definition 5.44.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- `[N]` as `Finset.range N`; partitions as `Finset (Finset ℕ)`.
open scoped Classical in
/-- `𝚷_p([N])`, the partitions of `[N]` whose blocks have cardinality at most `p` (the
Definition 5.44). -/
noncomputable def boundedBlockPartitions (N p : ℕ) : Finset (Finset (Finset ℕ)) :=
  (Finset.range N).powerset.powerset.filter fun π =>
    IsSubpartition π ∧ π.biUnion id = Finset.range N ∧ ∀ S ∈ π, S.card ≤ p

end MultipoleBKT

end
