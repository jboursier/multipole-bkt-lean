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
public import MultipoleBKT.Frozen.TruncationScale
public import MultipoleBKT.Frozen.ClusterThreshold
public import MultipoleBKT.Frozen.SameSignClustering

/-!
# Frozen: `MultipoleBKT.badPointsTypeOne`

See the paper, Definition 5.2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- on a dipole configuration `d` (the paper's event `{σ_N = Id}`).
-- clusters of cardinality exactly `q(β) + 1`, as written; the
-- larger clusters occur only on the null set excluded after Definition 5.1.
open scoped Classical in
/-- Bad points of type 1, Definition 5.2, for the dipoles
`d i = (x_i, y_i)`, `r_i = |x_i - y_i|`:
`J^{1,±} = {i : r_i > ε₀ R̄_{β,λ}} ∪ ⋃_{S ∈ Clus_N^±, |S| = q(β)+1} S`, with `Clus_N^±` the
`q(β)`-clusterings (Definition 5.1, cutoff `ε₀ R̄_{β,λ}`) of the positive and of the negative
charges; `I^1_bad = J^{1,+} ∪ J^{1,-}`. -/
noncomputable def badPointsTypeOne {N : ℕ} (p₀ : ℕ) (β lam ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  -- `J^{1,±}` for the clustering of the charges `z`
  let J : (Fin N → ℂ) → Finset (Fin N) := fun z =>
    Finset.univ.filter (fun i => ε₀ * truncationScale p₀ β lam < ‖(d i).1 - (d i).2‖) ∪
      ((sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
          (fun i => ‖(d i).1 - (d i).2‖) Finset.univ).filter
        (fun Sτ => Sτ.1.card = clusterThreshold p₀ β + 1)).biUnion Prod.fst
  J (fun i => (d i).1) ∪ J (fun i => (d i).2)

end MultipoleBKT

end
