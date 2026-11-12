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
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.AlphaExponent
public import MultipoleBKT.Frozen.BadPointsTypeOne
public import MultipoleBKT.Frozen.MultipoleClassOn

/-!
# Frozen: `MultipoleBKT.badPointsTypeTwo`

See the paper, Definition 5.3.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- on a dipole configuration `d`.
-- `[i]^{Π_mult^U}` is `multipoleClassOn M lam d U i`.
open scoped Classical in
/-- Bad points of type 2, Definition 5.3, with
`U = [N] ∖ I^1_bad` and multipoles computed on `U`: `I^{2,1}_bad` is the set of `i ∈ U` with
`|[i]^{Π_mult^U}| > p(β)`; for `k ∈ [p(β)]`, `I^{2,2,k}_bad` is `{i ∈ U : |[i]^{Π_mult^U}| = k}`
if this set has more than `ε₀^{-α(β)} N λ^{2(k-1)}` elements and `∅` otherwise;
`I^2_bad = I^{2,1}_bad ∪ ⋃_{k ∈ [p(β)]} I^{2,2,k}_bad`. -/
noncomputable def badPointsTypeTwo {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  let U := Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d
  -- `I^{2,1}_bad`
  U.filter (fun i => pBeta p₀ β < (multipoleClassOn M lam d U i).card) ∪
    -- `I^{2,2}_bad = ⋃_{k ∈ [p(β)]} I^{2,2,k}_bad`
    (Finset.Icc 1 (pBeta p₀ β)).biUnion fun k =>
      if ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) <
          ((U.filter fun i => (multipoleClassOn M lam d U i).card = k).card : ℝ)
      then U.filter fun i => (multipoleClassOn M lam d U i).card = k
      else ∅

end MultipoleBKT

end
