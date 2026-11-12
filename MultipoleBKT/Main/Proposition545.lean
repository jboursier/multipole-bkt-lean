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
public import MultipoleBKT.Frozen.IsMollifier
public import MultipoleBKT.Frozen.Energy
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.ErrorRate
public import MultipoleBKT.Frozen.StableMatching
public import MultipoleBKT.Frozen.BoundedBlockPartitions
public import MultipoleBKT.Frozen.TruncatedPartitionWeight
public import MultipoleBKT.Frozen.Theorem2
public import MultipoleBKT.Main.PropFiveFortyFive.Final

/-!
# Provider for the frozen statement `MultipoleBKT.proposition_5_45`

Registered implementation module of `MultipoleBKT/Frozen/Proposition545.lean`. Its export
`MultipoleBKT.Main.proposition_5_45` states and proves exactly the frozen statement. The proof
applies `PropFiveFortyFive.proposition_5_45_of_theorem_2` (Prop 5.45 from the statement of
Theorem 2) to the frozen statement `MultipoleBKT.theorem_2`. The binders follow the frozen statement's, so that
its body is `by exact MultipoleBKT.Main.proposition_5_45`.

The frozen statement imports this provider; this module never imports the frozen statement.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT.Main

open scoped Classical in
/-- Exactly the frozen statement of `MultipoleBKT.proposition_5_45`. -/
theorem proposition_5_45 {χ : ℂ → ℝ} (hχ : IsMollifier χ := by assumption) {p₀ : ℕ}
    (hp₀ : 1 ≤ p₀ := by assumption) {β : ℝ} (hβ : 2 < β := by assumption) :
    let p := pBeta p₀ β
    -- "For `M` large enough with respect to `β, p`"
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      -- "`λ` small enough and `N` large enough depending on `λ`";
      -- `O_{β,p,M}(Nδ)` as `C`, then `λ₀`, `N₀(λ)`
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          -- `∫_{σ_N = Id}` as `∫⁻` over `(Λ²)^N ∩ {σ_N = Id}`
          let zId : ℝ≥0∞ := ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
              {c | stableMatching c = Equiv.refl (Fin N)},
            ENNReal.ofReal (Real.exp (-β * energy χ lam c))
          let zHat : ℝ := ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π
          -- both logarithms are of positive finite
          -- quantities, asserted; then the two-sided bound
          0 < zId ∧ zId < ∞ ∧ 0 < zHat ∧
            |Real.log zId.toReal - Real.log zHat| ≤ C * N * errorRate p₀ β lam :=
  PropFiveFortyFive.proposition_5_45_of_theorem_2 @MultipoleBKT.theorem_2 χ hχ p₀ hp₀ β hβ

end MultipoleBKT.Main

end
