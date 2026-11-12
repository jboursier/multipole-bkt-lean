/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Theorem1.Definitions
public import MultipoleBKT.Frozen.Theorem1

/-!
# Theorem 1 (free energy expansion): the proof

The challenge's statement, proved from `theorem_1` of the library. The shared
copied definitions unfold to the library's definitions, so Lean checks the direct
application of the library theorem.
-/

-- Compare the recursive definitions by ordinary unfolding.
set_option smartUnfolding false

@[expose] public section

namespace MultipoleBKTAudit.Theorem1

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

open scoped Classical in
/-- **Theorem 1** (free energy expansion). -/
theorem theorem_1
    -- `χ` and `p₀` outermost, before every constant
    (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (β : ℝ) (hβ : 2 < β) :
    -- `kdip λ` is the paper's `𝗄^dip_{β,λ}`, pinned by the limits (2.34)
    ∃ kdip : ℝ → ℕ → ℝ,
      -- (2.34), and the existence part of item (2), for every `λ ∈ (0,1)`
      -- every `2 ≤ k ≤ p*(β)` (every `k ≥ 2` when `β ≥ 4`)
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        kdip lam 0 = 0 ∧ kdip lam 1 = 0 ∧
        ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∀ V : Finset ℕ, V.card = k →
          Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * dipoleActivity χ N β lam V) atTop
            (𝓝 (kdip lam k))) ∧
      -- item (1), eq. (2.38)
      -- own `C, λ₀, N₀(λ)` in that order
      (∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          let cluster : ℕ+ → ℝ := fun n =>
            1 / (n : ℕ).factorial *
              ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
                  (fun V => (connectionGraph V).Connected ∧
                    ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ pBeta p₀ β),
                (∏ i, dipoleActivity χ N β lam (V i)) * (ursell (connectionGraph V) : ℝ)
          -- `0 < Z < ∞`, then `log Z` as `Real.log Z.toReal`
          0 < partitionFunction χ N β lam ∧ partitionFunction χ N β lam < ∞ ∧
          -- absolute summability of the cluster series
          Summable (fun n => ‖cluster n‖) ∧
          |Real.log (partitionFunction χ N β lam).toReal
              - (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant χ β) - 1))
              - ∑' n, cluster n|
            ≤ C * N * errorRate p₀ β lam) ∧
      -- item (2), eq. (2.39)
      -- every `2 ≤ k ≤ p*(β)`
      -- own `C, λ₀` for each `k`
      (∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ → |kdip lam k| ≤ C * lam ^ (2 * (k - 1))) ∧
      -- item (3), eq. (2.40)
      -- own `C, λ₀, N₀(λ)`
      (∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          -- absolute summability of the Mayer double series
          Summable (fun nk : ℕ+ × ℕ+ => ‖mayerTerm (pBeta p₀ β) (kdip lam) nk.1 nk.2‖) ∧
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            let cluster : ℕ+ → ℝ := fun n =>
              1 / (n : ℕ).factorial *
                ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
                    (fun V => (connectionGraph V).Connected ∧
                      ∀ i, (V i).card ≤ pBeta p₀ β),
                  (∏ i, dipoleActivity χ N β lam (V i)) * (ursell (connectionGraph V) : ℝ)
            -- absolute summability of the cluster series
            Summable (fun n => ‖cluster n‖) ∧
            |∑' n, cluster n - (-N * mayer (pBeta p₀ β) (kdip lam))|
              ≤ C * N * errorRate p₀ β lam) :=
  by exact _root_.MultipoleBKT.theorem_1 χ hχ p₀ hp₀ β hβ

end MultipoleBKT

end MultipoleBKTAudit.Theorem1

end
