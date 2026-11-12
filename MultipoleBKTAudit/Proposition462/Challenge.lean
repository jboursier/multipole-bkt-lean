/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Proposition462.Definitions

/-!
# Proposition 4.62 (large deviations lower bound): the statement

Mathlib-only statement of Proposition 4.62 of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, revised version 2026).

For every admissible mollifier `χ`, `p₀ ≥ 1` and `β > 2`, for all sufficiently large
`M` and sufficiently small `ε₀ > 0`, the integral over the event (4.24) has the lower
bound (4.141). This event prescribes `n_k` multipoles of size `k` and requires all
matched dipoles to have length at most `ε₀ R̄_{β,λ}`. The profile satisfies
`∑ k n_k = N` and the bounds (4.22). The logarithm of the lower bound is
`N log N + log N! + (2-β) N log λ + N log C_β - N I(n/N) - C N δ_{β,λ}`.
The conclusion holds for every coefficient family satisfying (2.45) and (2.46),
and includes absolute convergence of the rate series on the full simplex.

## How the objects are specified

`energy` is the smeared Coulomb energy with `IsMollifier χ`; integration is a lower
Lebesgue integral over the companion square `box N` for each endpoint.
`stableMatching` uses the greedy rule with lexicographic tie breaking.
`multipoleCount` counts connected components of `multipoleGraph`, using the closed
relation `MultipoleLinked`. `multipolePartitionFunction`, `hierarchicalModel` and
`multipoleActivity` specify the coefficient limits, with `blockProfile` recording
sizes and `IsSubpartition` requiring nonempty disjoint blocks.
`rateSeriesTerm` and `rateFunction` give Definition 2.15 using canonical partitions
and weighted hypertrees. `simplex p 0` is the normalized profile domain.
`pBeta`, `errorRate`, `truncationScale` and `alphaExponent` specify the cutoffs and
profile bounds. After `ε₀`, the constants are chosen as `C`, `λ₀`, then `N₀(λ)`;
`N₀(λ)` is uniform over the profiles.

Configurations are `Fin N → ℂ × ℂ`, with the paper's labels shifted to start at zero.
All definitions are total; the theorem imposes the admissible parameter ranges.
The theorem below uses the definitions shared by the challenge and solution, which
import Mathlib only. Its final proof is the only `sorry`.
-/

@[expose] public section

namespace MultipoleBKTAudit.Proposition462

open MeasureTheory Filter Topology
open scoped ENNReal
open _root_.MultipoleBKTAudit.Proposition462.TwoComponentCoulomb (box)

namespace MultipoleBKT

open scoped Classical in
/-- **Proposition 4.62** (large deviations lower bound), eq. (4.141), for a profile `n` (`n i = n_{i+1}`) with
`n_1 + 2n_2 + ⋯ + p n_p = N` satisfying (4.22), and the event (4.24)
`𝒜 = {𝒩_1 = n_1, …, 𝒩_p = n_p} ∩ ⋂ᵢ {|x_i - y_{σ_N(i)}| ≤ ε₀ R̄_{β,λ}}`. -/
theorem proposition_4_62
    -- `χ` and `p₀` outermost
    (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (β : ℝ) (hβ : 2 < β) :
    let p := pBeta p₀ β
    -- `M` large (Proposition 4.27)
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    -- `ℐ_{β,p,λ}` is evaluated at any
    -- coefficient families `msf λ`, `kmult λ` pinned by the limits (2.45), (2.46) (Lemma 4.26)
    ∀ msf : ℝ → ℕ → ℝ, ∀ kmult : ℝ → (ℕ →₀ ℕ) → ℝ,
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
            (𝓝 (msf lam S.card))) →
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
            (𝓝 (kmult lam (blockProfile X)))) →
      -- every `ε₀ ∈ (0, ε₁)`, `ε₁` depending on `β, M, p`
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        -- `O_{β,M,p,ε₀}(Nδ)` as `C`, then `λ₀`, `N₀(λ)`
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            -- absolute summability of the series in `ℐ` on `Δ_{p,0}`
            (∀ γ ∈ simplex p 0, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            -- `N₀` uniform in the profile
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin p → ℕ,
              ∑ i : Fin p, ((i : ℕ) + 1) * n i = N →
              -- (4.22) for `k = i + 1 ∈ {2, …, p}`
              (∀ i : Fin p, 1 ≤ (i : ℕ) →
                (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
              -- `log ∫_𝒜 ≥ X` as `e^X ≤ ∫_𝒜`
              -- `∫_𝒜 e^{-βF_λ} dX_N dY_N` as `∫⁻` over `(Λ²)^N ∩ 𝒜`
              ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
                  + (2 - β) * N * Real.log lam + N * Real.log (dipoleConstant χ β)
                  - N * rateFunction p (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
                  - C * N * errorRate p₀ β lam))
                ≤ ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
                    {c | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
                      ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
                        ε₀ * truncationScale p₀ β lam},
                  ENNReal.ofReal (Real.exp (-β * energy χ lam c)) :=
  sorry

end MultipoleBKT

end MultipoleBKTAudit.Proposition462

end
