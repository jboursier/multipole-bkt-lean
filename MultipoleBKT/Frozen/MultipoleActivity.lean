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
public import MultipoleBKT.Frozen.DipoleInteraction
public import MultipoleBKT.Frozen.MultipoleLinked
public import MultipoleBKT.Frozen.HierarchicalModel

/-!
# Frozen: `MultipoleBKT.multipoleActivity`

See the paper, equation (2.44).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- takes `χ` explicitly.
-- `X : Finset (Finset ℕ)`, configurations `V_X → ℂ × ℂ`.
open scoped Classical in
/-- The multipole activity `𝖪^mult_{β,λ}(X)`, Definition 2.13 (eq. (2.44)): the sum over `E ∈ 𝖤^X` of `𝔼_{𝖯^X} ∏_{ij ∈ E} (e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1)`.
Here `𝖤^X` is the set of edge sets `E ⊂ ℰ^inter(X)` (edges between
distinct blocks) with at least one edge such that `(V_X, E ∪ ℰ^intra(X))` is connected,
`ℰ^intra(X)` being the edges inside the blocks. -/
noncomputable def multipoleActivity (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (X : Finset (Finset ℕ)) : ℝ :=
  ∑ E ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (fun E =>
      (∀ i j : X.biUnion id, E.Adj i j →
          ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
        E.edgeSet.Nonempty ∧
        (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
          ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected),
    ∫ c : X.biUnion id → ℂ × ℂ,
      ∏ i : X.biUnion id, ∏ j : X.biUnion id,
        if i < j ∧ E.Adj i j then
          (if MultipoleLinked M lam (c i) (c j) then 0 else
              Real.exp (-β * dipoleInteraction χ lam (c i) (c j))) - 1
        else 1
      ∂hierarchicalModel χ N β lam M X

end MultipoleBKT

end
