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
public import MultipoleBKT.Frozen.GreedyMatching

/-!
# Frozen: `MultipoleBKT.stableMatching`

See the paper, Section 2.2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- configurations `c : Fin N → ℂ × ℂ`.
-- `σ_N` literal, `N` rounds of `greedyMatching`, a permutation.
/-- The stable matching `σ_N` (Definition 2.1; Definition 4.1): `N` rounds of the greedy procedure, starting from all labels. -/
noncomputable def stableMatching {N : ℕ} (c : Fin N → ℂ × ℂ) : Equiv.Perm (Fin N) :=
  (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans
    ((greedyMatching c N Finset.univ Finset.univ (by simp) (by simp)).trans
      (Equiv.subtypeUnivEquiv Finset.mem_univ))

end MultipoleBKT

end
