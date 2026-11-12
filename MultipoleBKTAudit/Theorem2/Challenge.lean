/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Theorem2.Definitions

/-!
# Theorem 2 (multipole distribution): the statement

Mathlib-only statement of Theorem 2 of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, revised version 2026).

For every admissible mollifier `χ`, `p₀ ≥ 1` and `β > 2`, for all sufficiently large
`M`, the multipole coefficients exist as the limits (2.45) and (2.46) for every
`λ ∈ (0,1)`. The six conclusions give their bounds (2.47) and (2.48), the free energy
through the minimum of the rate function (2.49), exponential control of large multipoles
and long dipoles (2.50) and (2.51), the two-sided large deviations estimate (2.52),
the unique minimizer and its size (2.53), and the typical counts (2.54).
The partition function is positive and finite, and the series defining the rate function
converges absolutely on its simplex, as asserted in the statement.

## How the objects are specified

`energy`, `partitionFunction` and `gibbsMeasure` give the smeared Coulomb model and its
normalized measure on the companion square `box N`. `IsMollifier` specifies the allowed
mollifiers. `stableMatching` is the greedy matching with lexicographic tie breaking;
`MultipoleLinked` and `multipoleGraph` use the minimum of the four endpoint distances
and closed inequalities. `multipoleCount` counts connected components by their number
of dipoles. `multipolePartitionFunction`, `hierarchicalModel` and `multipoleActivity`
are the integrals and graph sums of Definitions 2.12 and 2.13. `blockProfile` records
block sizes, and `IsSubpartition` requires nonempty disjoint blocks.
`simplex`, `canonicalPartition`, `hypertrees`, `hypertreeWeight`, `rateSeriesTerm` and
`rateFunction` give Definition 2.15. The rate function depends on the coefficient
families whose existence and limits are concluded. Its infima are infima of images.
`pStar`, `pBeta`, `criticalScale` and `errorRate` specify the cutoffs and errors.
In Theorem 2(4), the closed count window and closed norm ball use the same `C₀`, and
`N₀(λ)` is uniform in `γ`. In Theorem 2(6), `λ₀` and `N₀(λ)` follow the choice of large `C₀`.

Configurations are `Fin N → ℂ × ℂ`, with the paper's labels shifted to start at zero.
All definitions are total; the theorem imposes the admissible parameter ranges.
The theorem below uses the definitions shared by the challenge and solution, which
import Mathlib only. Its final proof is the only `sorry`.
-/

@[expose] public section

namespace MultipoleBKTAudit.Theorem2

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

open scoped Classical in
/-- **Theorem 2** (multipole distribution). -/
theorem theorem_2
    -- `χ` and `p₀` outermost, before every constant
    (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (β : ℝ) (hβ : 2 < β) :
    let p := pBeta p₀ β
    -- `∃ M₀ > 20, ∀ M ≥ M₀`, every `M`-dependent object at that `M`
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    -- `msf λ`, `kmult λ` are the paper's `𝗆_{β,λ}`, `𝗄^mult_{β,λ}`,
    -- pinned by the limits (2.45), (2.46)
    ∃ msf : ℝ → ℕ → ℝ, ∃ kmult : ℝ → (ℕ →₀ ℕ) → ℝ,
      -- item (1), existence: the limits (2.45) and (2.46), for every `λ ∈ (0,1)`
      -- sizes `≤ p*(β)`
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        (∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
            (𝓝 (msf lam S.card))) ∧
        (∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
            (𝓝 (kmult lam (blockProfile X))))) ∧
      -- item (1), eq. (2.47)
      -- own `C, λ₀` for each `k`
      (∀ k : ℕ, 2 ≤ k → k ≤ p →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            C⁻¹ * lam ^ (2 * (k - 1)) ≤ msf lam k ∧ msf lam k ≤ C * lam ^ (2 * (k - 1))) ∧
      -- item (1), eq. (2.48)
      -- own `C, λ₀` for each `X`
      (∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ p →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            |kmult lam (blockProfile X)| ≤ C * lam ^ (2 * ((X.card : ℤ) - 1))) ∧
      -- item (2), eq. (2.49)
      -- own `C, λ₀, N₀(λ)`
      (∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          -- absolute summability of the series in `ℐ` on `Δ_{p,0}`
          (∀ γ ∈ simplex p 0, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
            ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            -- `0 < Z < ∞`, then `log Z` as `Real.log Z.toReal`
            0 < partitionFunction χ N β lam ∧ partitionFunction χ N β lam < ∞ ∧
            -- `inf_{Δ_{p,0}} ℐ` as `sInf (ℐ '' Δ_{p,0})`
            |Real.log (partitionFunction χ N β lam).toReal
                - (2 * N * Real.log N
                  + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant χ β) - 1)
                  - N * sInf (rateFunction p (msf lam) (kmult lam) '' simplex p 0))|
              ≤ C * N * errorRate p₀ β lam) ∧
      -- item (3), eqs. (2.50) and (2.51)
      -- own `C, λ₀, N₀(λ)`, uniform in `n`
      -- `log ℙ(E) ≤ X` as `ℙ(E) ≤ e^X`
      (∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, 1 ≤ n →
          gibbsMeasure χ N β lam {c | (n : ℤ) ≤
              |(∑ k ∈ Finset.Icc 1 p, (k : ℤ) * multipoleCount M lam c k) - N|}
            ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * n + C * N * errorRate p₀ β lam)) ∧
          gibbsMeasure χ N β lam {c | n ≤ {i : Fin N | criticalScale β lam ≤
              ENNReal.ofReal ‖(c i).1 - (c (stableMatching c i)).2‖}.ncard}
            ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * n + C * N * errorRate p₀ β lam))) ∧
      -- item (4), eq. (2.52); `γ i = γ_{i+1}`
      -- `∀ C₀`, then `C, λ₀, N₀(λ)`, then `∀ γ` (uniform `N₀`); the
      -- same `C₀` in the hypothesis and the window; closed window and closed `ℓ^∞` ball
      -- the two-sided `log ℙ(E) = X + O(Nδ)` as two bounds on `ℙ(E)`
      (∀ C₀ : ℝ, 0 < C₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            -- absolute summability of the series in `ℐ` on `Δ_{p,0}`
            (∀ γ ∈ simplex p 0, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ γ ∈ simplex p 0,
              (∀ i : Fin p, 1 ≤ (i : ℕ) → γ i ≤ C₀ * lam ^ (2 * (i : ℕ))) →
              -- both infima as `sInf (ℐ '' _)`
              let rate : ℝ :=
                sInf (rateFunction p (msf lam) (kmult lam) ''
                    {γ' | γ' ∈ simplex p 0 ∧ ‖γ' - γ‖ ≤ C₀ * errorRate p₀ β lam})
                  - sInf (rateFunction p (msf lam) (kmult lam) '' simplex p 0)
              let event : Set (Fin N → ℂ × ℂ) := {c | ∀ i : Fin p,
                |(multipoleCount M lam c ((i : ℕ) + 1) : ℝ) - N * γ i|
                  ≤ C₀ * N * errorRate p₀ β lam}
              ENNReal.ofReal (Real.exp (-N * rate - C * N * errorRate p₀ β lam))
                  ≤ gibbsMeasure χ N β lam event ∧
                gibbsMeasure χ N β lam event
                  ≤ ENNReal.ofReal (Real.exp (-N * rate + C * N * errorRate p₀ β lam))) ∧
      -- item (5), eq. (2.53); `γstar i = γ*_{i+1}`
      -- attainment and uniqueness, which pin the `sInf` values above
      ((∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          -- absolute summability of the series in `ℐ` on `Δ_{p,0}`
          (∀ γ ∈ simplex p 0, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
            ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
          ∃! γstar : Fin p → ℝ, γstar ∈ simplex p 0 ∧
            IsMinOn (rateFunction p (msf lam) (kmult lam)) (simplex p 0) γstar) ∧
        -- own `C, λ₀` for each `k = i + 1`
        ∀ i : Fin p, 1 ≤ (i : ℕ) →
          ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
            ∀ lam : ℝ, 0 < lam → lam < lam₀ →
              ∃ γstar ∈ simplex p 0,
                IsMinOn (rateFunction p (msf lam) (kmult lam)) (simplex p 0) γstar ∧
                C⁻¹ * lam ^ (2 * (i : ℕ)) ≤ γstar i ∧ γstar i ≤ C * lam ^ (2 * (i : ℕ))) ∧
      -- item (6), eq. (2.54)
      -- `∀ k`, `C, C'`, then "for `C₀` large enough", then `λ₀, N₀(λ)`
      -- `log ℙ(E) ≤ X` as `ℙ(E) ≤ e^X`
      (∀ k : ℕ, 2 ≤ k → k ≤ p →
        ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ C₀min : ℝ, 0 < C₀min ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
          ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
              gibbsMeasure χ N β lam {c | (multipoleCount M lam c k : ℝ) ∉
                  Set.Ioo (C₀⁻¹ * N * lam ^ (2 * (k - 1))) (C₀ * N * lam ^ (2 * (k - 1)))}
                ≤ ENNReal.ofReal (Real.exp
                    (-C * N * lam ^ (2 * (k - 1)) + C' * N * errorRate p₀ β lam))) :=
  sorry

end MultipoleBKT

end MultipoleBKTAudit.Theorem2

end
