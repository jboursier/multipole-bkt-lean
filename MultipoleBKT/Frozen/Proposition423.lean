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
public import MultipoleBKT.Frozen.IsMollifier
public import MultipoleBKT.Frozen.PStar
public import MultipoleBKT.Frozen.DipoleActivity
public import MultipoleBKT.Frozen.IsSubpartition
public import MultipoleBKT.Frozen.MultipolePartitionFunction
public import MultipoleBKT.Frozen.MultipoleActivity
import MultipoleBKT.LowerBound.Proposition423

/-!
# Frozen: `MultipoleBKT.proposition_4_23`

See the paper, Proposition 4.23.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

open scoped Classical in
/-- **Proposition 4.23**, restricted to the frozen activities: the bounds (4.38)–(4.39) for `𝖬^0_∞ = 𝖬_{β,λ}`, (4.40) for
`𝖪^0_∞ = 𝖪^mult_{β,λ}` (Corollary 4.61) when `|V_X| ≤ p*(β)`, and (4.41) for
`𝖪^dip_{β,λ}`. The statements about `𝖬^-_{ε₀}`, `𝖬^0_{ε₀}`, `𝖪^-_{ε₀}`, `𝖪^0_{ε₀}` are not
part of this gate. -/
theorem proposition_4_23
    -- `χ` outermost; the gate's objects do not depend on `p₀`
    (χ : ℂ → ℝ) (hχ : IsMollifier χ) (β : ℝ) (hβ : 2 < β) :
    -- (4.38) and (4.39) for `𝖬^0_∞ = 𝖬_{β,λ}`
    -- `M` large, `∃ M₀ > 20, ∀ M ≥ M₀`, `M₀` after `k` (the proof uses
    -- Appendix A, which assumes `M > max(20, 3^{p(β)})`); `C` depends on `β, M, |S|`
    --
    -- `C, λ₀, N₀(λ)` in that order
    -- `S ⊂ [N]` as `S ⊆ Finset.range N`
    (∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ S : Finset ℕ, S ⊆ Finset.range N → S.card = k →
            lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤ multipolePartitionFunction χ N β lam M S ∧
            multipolePartitionFunction χ N β lam M S ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) ∧
    -- (4.40) for `𝖪^0_∞ = 𝖪^mult_{β,λ}`, `|V_X| ≤ p*(β)`, so `γ_{β,λ,|V_X|} = λ^{2(|V_X|-1)}`
    -- `M` large, `∃ M₀ > 20, ∀ M ≥ M₀`, `M₀` after `k`; `C` depends on
    -- `β, M, |V_X|`
    -- `𝖬^0_∞(X) = ∏_{S ∈ X} 𝖬_{β,λ}(S)`, as a quotient
    (∀ k : ℕ, (k : ℕ∞) ≤ pStar β → ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |multipoleActivity χ N β lam M X| ≤
              C * lam ^ (2 * (k - 1)) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1))) ∧
    -- (4.41), for `1 < |V| ≤ p*(β)`
    -- `𝖪^dip` does not depend on `M`, so no `M` is quantified here
    (∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ V : Finset ℕ, V ⊆ Finset.range N → V.card = k →
            |dipoleActivity χ N β lam V| ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) :=
  by exact MultipoleBKT.LowerBound.proposition_4_23

end MultipoleBKT

end
