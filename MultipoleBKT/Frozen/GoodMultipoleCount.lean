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
public import MultipoleBKT.Frozen.MultipoleGraph
public import MultipoleBKT.Frozen.GoodPoints

/-!
# Frozen: `MultipoleBKT.goodMultipoleCount`

See the paper, Proposition 5.43.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- the good points of a configuration `c` are those of its matched dipoles
-- `(x_i, y_{σ_N(i)})`, the dipoles of Definition 2.2.
-- "multipoles of cardinality `k` in `I_good`" are the
-- multipoles of Definition 2.2 (components of `multipoleGraph`) contained in `I_good`; by
-- Remark 5.6(1) these are also the `Π_mult^U`-classes contained in `I_good`.
-- counted as connected components with `k` vertices.
/-- `𝒩_k^good`, the number of multipoles of cardinality `k` in `I_good` (Proposition 5.43; proof of Theorem 2): the connected components of the multipole graph
(Definition 2.2) with `k` vertices, all of them good. -/
noncomputable def goodMultipoleCount {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (c : Fin N → ℂ × ℂ)
    (k : ℕ) : ℕ :=
  Nat.card {C : (multipoleGraph M lam c).ConnectedComponent // Nat.card C.supp = k ∧
    C.supp ⊆ ↑(goodPoints p₀ β lam M ε₀ fun i => ((c i).1, (c (stableMatching c i)).2))}

end MultipoleBKT

end
