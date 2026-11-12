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
# Frozen: `MultipoleBKT.ursell`

See the paper, equation (2.29).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

open scoped Classical in
/-- The Ursell function `I(G) = ∑_{H ⊂ G} (-1)^{|E(H)|}`, Definition 2.4 (Definition 2.4,
eq. (2.29)), the sum over connected spanning subgraphs `H` of `G`. -/
noncomputable def ursell {V : Type*} [Fintype V] (G : SimpleGraph V) : ℤ :=
  ∑ H ∈ (Finset.univ : Finset (SimpleGraph V)).filter (fun H => H ≤ G ∧ H.Connected),
    (-1) ^ H.edgeFinset.card

end MultipoleBKT

end
