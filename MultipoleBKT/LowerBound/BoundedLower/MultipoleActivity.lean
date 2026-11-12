/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.Infinity

/-!
# The bounded multipole activity from the grouped reduction

The proof of Proposition 4.23, (4.40). Keep the grouped expansion, apply parity,
bound its odd components by the ear cover of the proof of (A.30) (proof of Proposition 4.23)
and choose the separate even tree. The hatted
infinite-cutoff integral gives a uniform coefficient before normalization.
-/

@[expose] public section

namespace MultipoleBKT.BoundedLower

open MeasureTheory Finset Filter

/-- Proposition 4.23, (4.40), for the infinite-cutoff zero model.
proof of Proposition 4.23. -/
theorem multipoleActivity_bound (χ : ℂ → ℝ) (hχ : IsMollifier χ) (β : ℝ) (hβ : 2 < β) :
    ∀ k : ℕ, (k : ℕ∞) ≤ pStar β → ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |multipoleActivity χ N β lam M X| ≤
              C * lam ^ (2 * (k - 1)) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  intro k hk
  refine ⟨21, by norm_num, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by linarith
  by_cases hk1 : 1 ≤ k
  swap
  · refine ⟨1, one_pos, 1, one_pos, le_rfl, fun lam _ _ => ⟨0, fun N _ X hX _ h2 hXk => ?_⟩⟩
    have hpos := BoundedLowerEps.nonempty_of_card hX h2
    omega
  obtain ⟨C, hC, hb⟩ := LowerBound.RouteBounded.exists_abs_activity_infinity_le hχ hβ hM1 k hk1 hk
  refine ⟨C, hC, 1, one_pos, le_rfl, fun lam hlam _ => ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_half_le_dipoleNormalization hχ hβ hlam)
  refine ⟨max N₀ 1, fun N hN X hX _ h2 hXk => ?_⟩
  exact hb lam hlam N ((le_max_right _ _).trans hN)
    (hN₀ N ((le_max_left _ _).trans hN)) X hX h2 hXk

end MultipoleBKT.BoundedLower

end
