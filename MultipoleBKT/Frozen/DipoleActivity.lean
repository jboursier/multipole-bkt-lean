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

/-!
# Frozen: `MultipoleBKT.dipoleActivity`

See the paper, Definition 2.5.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- takes `χ` explicitly.
-- `V : Finset ℕ` (any finite label set), configurations `V → ℂ × ℂ`.
-- `𝒜_ij` evaluated with `i < j`.
open scoped Classical in
/-- The dipole activity `K^dip_{β,λ}(V)`, Definition 2.5: the sum over `E ∈ 𝒢_c(V)` (edge sets on `V`, i.e. simple graphs on `V`, that are
connected and have at least one edge) of `𝔼_{μ^{⊗|V|}} ∏_{ij ∈ E} (e^{-β v_ij} 𝟙_{𝒜_ij} - 1)`. -/
noncomputable def dipoleActivity (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) (V : Finset ℕ) : ℝ :=
  ∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
      (fun E => E.Connected ∧ E.edgeSet.Nonempty),
    ∫ c : V → ℂ × ℂ,
      ∏ i : V, ∏ j : V,
        if i < j ∧ E.Adj i j then
          (if IsStableDipolePair (c i) (c j) then
              Real.exp (-β * dipoleInteraction χ lam (c i) (c j)) else 0) - 1
        else 1
      ∂Measure.pi fun _ : V => dipoleMeasure χ N β lam

end MultipoleBKT

end
