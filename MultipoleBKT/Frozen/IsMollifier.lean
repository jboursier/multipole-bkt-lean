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

/-!
# Frozen: `MultipoleBKT.IsMollifier`

See the paper, Section 2.1.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- general mollifier as in the paper.
/-- `χ` is an admissible mollifier: measurable, nonnegative, radial, bounded,
vanishing outside the closed unit ball ("supported in `B(0,1)`"), with `∫ χ = 1`. -/
def IsMollifier (χ : ℂ → ℝ) : Prop :=
  Measurable χ ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x y, ‖x‖ = ‖y‖ → χ x = χ y) ∧ BddAbove (Set.range χ) ∧
    (∀ x, 1 < ‖x‖ → χ x = 0) ∧ ∫ x, χ x = 1

end MultipoleBKT

end
