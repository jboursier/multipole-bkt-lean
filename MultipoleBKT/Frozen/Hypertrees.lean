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
public import MultipoleBKT.Frozen.ConnectionGraph

/-!
# Frozen: `MultipoleBKT.hypertrees`

See the paper, equation (2.35).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

open scoped Classical in
/-- `Htrees_n(A)`, eq. (2.35): the tuples `(X_1, …, X_n)` of subsets
of `A` with `|X_i| ≥ 2` for every `i`, `G(X_1, …, X_n)` connected, and
`|⋃ᵢ X_i| + n - ∑ᵢ |X_i| = 1`. -/
noncomputable def hypertrees {α : Type*} [DecidableEq α] (n : ℕ) (A : Finset α) :
    Finset (Fin n → Finset α) :=
  (Fintype.piFinset fun _ : Fin n => A.powerset).filter fun X =>
    (∀ i, 2 ≤ (X i).card) ∧ (connectionGraph X).Connected ∧
      ((Finset.univ.biUnion X).card : ℤ) + n - ∑ i, ((X i).card : ℤ) = 1

end MultipoleBKT

end
