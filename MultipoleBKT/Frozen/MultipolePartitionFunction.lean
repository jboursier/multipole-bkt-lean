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
public import MultipoleBKT.Frozen.IsStableDipolePair
public import MultipoleBKT.Frozen.DipoleInteraction
public import MultipoleBKT.Frozen.DipoleMeasure
public import MultipoleBKT.Frozen.MultipoleLinked

/-!
# Frozen: `MultipoleBKT.multipolePartitionFunction`

See the paper, equation (2.41).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- takes `χ` explicitly. `S : Finset ℕ`.
-- `𝒜_ij` evaluated with `i < j`.
open scoped Classical in
/-- The multipole partition function `𝖬_{β,λ}(S) = 𝔼_{μ^{⊗|S|}} [𝟙_{𝓑_S} ∏_{i<j ∈ S}
e^{-β v_ij} 𝟙_{𝒜_ij}]`, eq. (2.41), where `𝓑_S` says that the graph
induced on `S` by `↔` (with the pairs `(x_i, y_i)`) is connected (eq. (2.14)). -/
noncomputable def multipolePartitionFunction (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (S : Finset ℕ) : ℝ :=
  ∫ c : S → ℂ × ℂ,
    (if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
      then 1 else 0) *
    ∏ i : S, ∏ j : S,
      if i < j then
        (if IsStableDipolePair (c i) (c j) then
          Real.exp (-β * dipoleInteraction χ lam (c i) (c j)) else 0)
      else 1
    ∂Measure.pi fun _ : S => dipoleMeasure χ N β lam

end MultipoleBKT

end
