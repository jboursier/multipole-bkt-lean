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
public import TwoComponentCoulomb.Frozen.LogKernel
public import MultipoleBKT.Frozen.SmearedCharge

/-!
# Frozen: `MultipoleBKT.kappa`

See the paper, equation (2.3).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

@[expose] public section

namespace MultipoleBKT

-- takes `χ` explicitly.
/-- `κ = ∬ g(x - y) dδ₀^{(1)}(x) dδ₀^{(1)}(y)`, eq. (2.3). -/
noncomputable def kappa (χ : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge χ 0 1).prod (smearedCharge χ 0 1)

end MultipoleBKT

end
