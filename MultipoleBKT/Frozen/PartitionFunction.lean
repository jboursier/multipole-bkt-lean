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
public import TwoComponentCoulomb.Frozen.Box
public import MultipoleBKT.Frozen.Energy

/-!
# Frozen: `MultipoleBKT.partitionFunction`

See the paper, equation (2.9).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

@[expose] public section

namespace MultipoleBKT

-- integration over `(Λ²)^N` as `c : Fin N → ℂ × ℂ`, `c i = (x_i, y_i)`.
-- takes `χ` explicitly. value in `[0, ∞]`.
/-- `Z_{N,β}^λ = ∫_{(Λ²)^N} exp(-β F_λ) dX_N dY_N`, eq. (2.9). -/
noncomputable def partitionFunction (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) : ℝ≥0∞ :=
  ∫⁻ c in Set.univ.pi fun _ : Fin N => box N ×ˢ box N,
    ENNReal.ofReal (Real.exp (-β * energy χ lam c))

end MultipoleBKT

end
