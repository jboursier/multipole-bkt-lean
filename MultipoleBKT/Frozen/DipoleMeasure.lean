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
public import MultipoleBKT.Frozen.DipoleNormalization

/-!
# Frozen: `MultipoleBKT.dipoleMeasure`

See the paper, equation (2.30).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

@[expose] public section

namespace MultipoleBKT

-- total; `(N C)⁻¹ = 0` when `N C = 0`.
-- takes `χ` explicitly.
/-- The dipole measure `dμ_{β,λ}(x, y) = (N C_{β,λ})⁻¹ e^{β g_λ(x - y)} dx dy` on `Λ²`,
eq. (2.30). -/
noncomputable def dipoleMeasure (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) : Measure (ℂ × ℂ) :=
  (volume.restrict (box N ×ˢ box N)).withDensity fun p =>
    ENNReal.ofReal
      ((N * dipoleNormalization χ N β lam)⁻¹ * Real.exp (β * smearedKernel χ lam (p.1 - p.2)))

end MultipoleBKT

end
