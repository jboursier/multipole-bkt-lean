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
public import MultipoleBKT.Frozen.MultipoleGraph

/-!
# Frozen: `MultipoleBKT.multipoleCount`

See the paper, Theorem 2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- configurations `c : Fin N → ℂ × ℂ`.
-- `𝒩_k` = number of connected components of size `k`.
/-- `𝒩_k`, the number of multipoles of cardinality `k` (Theorem 2): the number
of connected components of the multipole graph with `k` vertices. -/
noncomputable def multipoleCount {N : ℕ} (M lam : ℝ) (c : Fin N → ℂ × ℂ) (k : ℕ) : ℕ :=
  Nat.card {C : (multipoleGraph M lam c).ConnectedComponent // Nat.card C.supp = k}

end MultipoleBKT

end
