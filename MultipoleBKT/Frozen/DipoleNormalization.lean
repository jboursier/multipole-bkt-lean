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
public import MultipoleBKT.Frozen.SmearedKernel

/-!
# Frozen: `MultipoleBKT.dipoleNormalization`

See the paper, equation (2.31).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

@[expose] public section

namespace MultipoleBKT

-- total in `N` (`1 / 0 = 0`).
-- takes `χ` explicitly.
/-- `C_{β,λ} = (1/N) ∫_{Λ²} e^{β g_λ(x - y)} dx dy`, eq. (2.31). -/
noncomputable def dipoleNormalization (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) : ℝ :=
  (1 / N) * ∫ p in box N ×ˢ box N, Real.exp (β * smearedKernel χ lam (p.1 - p.2))

end MultipoleBKT

end
