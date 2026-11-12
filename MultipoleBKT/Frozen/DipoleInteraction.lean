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
public import MultipoleBKT.Frozen.SmearedKernel

/-!
# Frozen: `MultipoleBKT.dipoleInteraction`

See the paper, Section 2.6.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- takes `χ` explicitly.
/-- The dipole–dipole interaction `v_ij = g_λ(x_i - x_j) + g_λ(y_i - y_j) - g_λ(x_i - y_j)
- g_λ(x_j - y_i)` of `d = (x_i, y_i)` and `e = (x_j, y_j)`. -/
noncomputable def dipoleInteraction (χ : ℂ → ℝ) (lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  smearedKernel χ lam (d.1 - e.1) + smearedKernel χ lam (d.2 - e.2)
    - smearedKernel χ lam (d.1 - e.2) - smearedKernel χ lam (e.1 - d.2)

end MultipoleBKT

end
