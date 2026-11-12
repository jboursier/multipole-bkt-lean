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
public import MultipoleBKT.Frozen.RateSeriesTerm

/-!
# Frozen: `MultipoleBKT.rateFunction`

See the paper, Definition 2.15.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- total on `Fin p → ℝ`; the theorems use it on `Δ_{p,0}` only.
-- `tsum`s; summability is asserted by the theorems.
-- a function of the coefficient functions `msf` and `kmult`.
/-- The multipole rate function `ℐ_{β,p,λ}(γ)`, Definition 2.15, for coefficients `msf` (the paper's `𝗆_{β,λ}`) and `kmult`:
`∑_{i=1}^p γᵢ (log i! - 1 + log γᵢ - log 𝗆(i)) + 1 + ∑_{n ≥ 1} ∑_{m ∈ ℕ^p}` of
`rateSeriesTerm`. The convention `0 log 0 = 0` holds since `Real.log 0 = 0`. -/
noncomputable def rateFunction (p : ℕ) (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ)
    (γ : Fin p → ℝ) : ℝ :=
  ∑ i, γ i * (Real.log ((i : ℕ) + 1).factorial - 1 + Real.log (γ i) - Real.log (msf ((i : ℕ) + 1)))
    + 1 + ∑' n : ℕ+, ∑' m : Fin p → ℕ, rateSeriesTerm p kmult γ n m

end MultipoleBKT

end
