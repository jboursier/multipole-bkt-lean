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
public import MultipoleBKT.Appendix.MultipoleIntegral.Bounds
public import MultipoleBKT.LowerBound.BoundedLower.MultipoleActivity
public import MultipoleBKT.LowerBound.BoundedLower.DipoleActivity
public import MultipoleBKT.LowerBound.RouteBounded.Normalizer

/-!
# Provider for the frozen Proposition 4.23

The proof of Proposition 4.23. Transfer the lower bound for the untruncated
normalizer from the truncated zero model. For the multipole activity,
retain the grouped expansion through parity and odd-component peeling,
then integrate the separate odd and even trees with the hatted infinite J
bound. The dipole activity uses the separately proved Lemma A.5.

This provider proves the frozen gate. Its frozen statement
imports this module.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound

open scoped Classical in
/-- Proposition 4.23 for the frozen objects. -/
theorem proposition_4_23
    -- `χ` outermost. The gate's objects do not depend on `p₀`
    {χ : ℂ → ℝ} (hχ : IsMollifier χ := by assumption) {β : ℝ} (hβ : 2 < β := by assumption) :
    -- (4.38) and (4.39) for `𝖬^0_∞ = 𝖬_{β,λ}`
    -- `M` large, `∃ M₀ > 20, ∀ M ≥ M₀`, `M₀` after `k` (the proof uses
    -- Appendix A, which assumes `M > max(20, 3^{p(β)})`). `C` depends on `β, M, |S|`
    -- (Proposition 4.23)
    -- `C, λ₀, N₀(λ)` are quantified in that order
    -- `S ⊂ [N]` as `S ⊆ Finset.range N`
    (∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ S : Finset ℕ, S ⊆ Finset.range N → S.card = k →
            lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤ multipolePartitionFunction χ N β lam M S ∧
            multipolePartitionFunction χ N β lam M S ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) ∧
    -- (4.40) for `𝖪^0_∞ = 𝖪^mult_{β,λ}`, `|V_X| ≤ p*(β)`, so `γ_{β,λ,|V_X|} = λ^{2(|V_X|-1)}`
    -- `M` large, `∃ M₀ > 20, ∀ M ≥ M₀`, `M₀` after `k`. `C` depends on
    -- `β, M, |V_X|` (Proposition 4.23)
    -- `𝖬^0_∞(X) = ∏_{S ∈ X} 𝖬_{β,λ}(S)` (4.17), as a quotient
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
  ⟨RouteBounded.multipolePartitionFunction_two_sided χ hχ β hβ,
    BoundedLower.multipoleActivity_bound χ hχ β hβ,
    BoundedLower.dipoleActivity_bound χ hχ β hβ⟩

end MultipoleBKT.LowerBound

end
