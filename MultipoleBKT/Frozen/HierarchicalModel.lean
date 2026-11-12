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
public import MultipoleBKT.Frozen.MultipolePartitionFunction

/-!
# Frozen: `MultipoleBKT.hierarchicalModel`

See the paper, equation (2.42).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- takes `χ` explicitly.
-- density form, with the normalisation `∏_{S ∈ X} 𝖬(S)` divided
-- out (Mathlib's `x⁻¹ = 0` at `𝖬(S) = 0`, which does not occur for `N ≥ 1`, `λ > 0`, `S ≠ ∅`).
open scoped Classical in
/-- The hierarchical multipole model `𝖯^X_{β,λ} = ⨂_{S ∈ X} 𝖯^S_{β,λ}` on `(Λ²)^{V_X}`
(eq. (2.42) and the line after it), written, as in eq. (4.16)
(with `ε₀ = ∞`), as the measure with density
`∏_{S ∈ X} 𝖬(S)⁻¹ 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij}` with respect to
`μ^{⊗ V_X}`, `V_X = ⋃_{S ∈ X} S`. -/
noncomputable def hierarchicalModel (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (X : Finset (Finset ℕ)) : Measure (X.biUnion id → ℂ × ℂ) :=
  (Measure.pi fun _ : X.biUnion id => dipoleMeasure χ N β lam).withDensity fun c =>
    ∏ S ∈ X, ENNReal.ofReal ((multipolePartitionFunction χ N β lam M S)⁻¹ *
      ((if ((SimpleGraph.fromRel fun i j : X.biUnion id =>
            MultipoleLinked M lam (c i) (c j)).induce {i : X.biUnion id | (i : ℕ) ∈ S}).Connected
          then 1 else 0) *
        ∏ i : X.biUnion id, ∏ j : X.biUnion id,
          if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then
            (if IsStableDipolePair (c i) (c j) then
              Real.exp (-β * dipoleInteraction χ lam (c i) (c j)) else 0)
          else 1))

end MultipoleBKT

end
