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
public import MultipoleBKT.Frozen.BadPointsTypeOne
public import MultipoleBKT.Frozen.MultipoleClassOn
public import MultipoleBKT.Frozen.BadPointsTypeTwo

/-!
# Frozen: `MultipoleBKT.badPointsTypeThree`

See the paper, Definition 5.4.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- on a dipole configuration `d`.
-- `[i]^{Π_mult^U}` is `multipoleClassOn M lam d U i`, `U = [N] ∖ I^1_bad`.
-- `d_ij` is the minimum of the four distances.
open scoped Classical in
/-- Bad points of type 3, Definition 5.4: `J^3_bad` is the set
of `i ∉ I^1_bad ∪ I^2_bad` such that `d_ij ≤ M max(r_i, λ)` (eq. (5.2)) for some
`j ∈ I^1_bad ∪ I^2_bad`, where `d_ij = dist({x_i, y_i}, {x_j, y_j})`; and
`I^3_bad = {i ∉ I^1_bad ∪ I^2_bad : [i]^{Π_mult^U} ∩ J^3_bad ≠ ∅}`. -/
noncomputable def badPointsTypeThree {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  let I₁₂ := badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d
  let U := Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d
  -- `J^3_bad`
  let J₃ := (Finset.univ \ I₁₂).filter fun i => ∃ j ∈ I₁₂,
    min (min ‖(d i).1 - (d j).1‖ ‖(d i).1 - (d j).2‖) (min ‖(d i).2 - (d j).1‖ ‖(d i).2 - (d j).2‖)
      ≤ M * max ‖(d i).1 - (d i).2‖ lam
  (Finset.univ \ I₁₂).filter fun i => (multipoleClassOn M lam d U i ∩ J₃).Nonempty

end MultipoleBKT

end
