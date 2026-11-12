/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Theorem1.Definitions

/-!
# Theorem 1 (free energy expansion): the statement

Mathlib-only statement of Theorem 1 of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, revised version 2026).

For every admissible mollifier `χ`, `p₀ ≥ 1` and `β > 2`, the dipole coefficients
`kdip λ k` exist as the limits (2.34) for every `λ ∈ (0,1)` and `2 ≤ k ≤ p*(β)`.
They have size `O(λ^{2(k-1)})`. The logarithm of the partition function equals
`2N log N + N ((2-β) log λ + log C_β - 1)` plus the connected dipole cluster series,
up to `O(N δ_{β,λ})`, as in (2.38). The cluster series equals `-N Mayer` up to the
same error, as in (2.40). Positivity and finiteness of the partition function and
absolute convergence of the cluster and Mayer series are conclusions.

## How the objects are specified

`IsMollifier` gives the radial, nonnegative, bounded unit-disc mollifier with integral one.
`energy`, `partitionFunction`, `smearedCharge` and `smearedKernel` specify the smeared
Coulomb model on the square `box N` of the companion paper. `dipoleConstant` is the
one-dipole constant. `dipoleActivity` is the connected-graph expectation of Definition 2.5
under the normalized `dipoleMeasure`, with the pair-stability event `IsStableDipolePair`.
`stableMatching` uses the greedy rule with lexicographic tie breaking. `connectionGraph`
and `ursell` specify the connected cluster sum. `hypertrees`, `hypertreeWeight`,
`mayerTerm` and `mayer` specify the series (2.36).
`transitionBeta`, `pStar`, `pBeta`, `criticalScale` and `errorRate` specify the temperature
thresholds, truncation and error of Definitions 2.8 and 2.9. The coefficients are
existentially quantified, with their limits imposed before their bounds.

Configurations are `Fin N → ℂ × ℂ`, with the paper's labels shifted to start at zero.
All definitions are total; the theorem imposes the admissible parameter ranges.
The theorem below uses the definitions shared by the challenge and solution, which
import Mathlib only. Its final proof is the only `sorry`.
-/

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
  sorry

end MultipoleBKT

end MultipoleBKTAudit.Theorem1

end
