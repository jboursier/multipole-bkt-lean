/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Proposition543.Definitions

/-!
# Proposition 5.43 (large deviations upper bound): the statement

Mathlib-only statement of Proposition 5.43 of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, revised version 2026).

For every admissible mollifier `χ`, `p₀ ≥ 1` and `β > 2`, for all sufficiently large
`M`, every fixed `t ≥ 1` and all sufficiently small `ε₀ > 0`, the integral over a
prescribed good-multipole profile, weighted by `exp(t |I_bad|)`, has the upper bound
of Proposition 5.43. The profile satisfies `∑ k n_k ≤ N` and (5.56).
The logarithm of the upper bound is
`N log N + log N! + (2-β) N log λ + N log C_β - N I(n/N) + C N δ_{β,λ}`.
The conclusion holds for every coefficient family satisfying (2.45) and (2.46).
The rate series converges absolutely on every `simplex p x`, `0 ≤ x ≤ 1`.

## How the objects are specified

`energy` gives the smeared Coulomb model with `IsMollifier χ`; each endpoint is
integrated over the companion square `box N` by a lower Lebesgue integral.
`stableMatching` is greedy with lexicographic tie breaking. Bad and good points are
computed on these matched dipoles. `sameSignClustering` implements Definition 5.1,
with closed balls and ties broken by smallest label. `badPointsTypeOne`,
`badPointsTypeTwo`, `badPointsTypeThree`, `badPoints` and `goodPoints` implement
Definitions 5.2–5.5. `goodMultipoleCount` counts components of `multipoleGraph`
whose vertices are all good. `multipoleClassOn` restricts the multipole relation
to the designated labels.
`multipolePartitionFunction`, `hierarchicalModel`, `multipoleActivity` and
`blockProfile` specify the coefficient limits. `rateSeriesTerm` and `rateFunction`
give Definition 2.15; `simplex p x` allows the missing mass `x` of the good profile.
`pBeta`, `errorRate`, `truncationScale`, `clusterThreshold` and `alphaExponent`
specify the cutoffs. The choices follow `t`, then `ε₀`, then `C`, `λ₀`, `N₀(λ)`;
`N₀(λ)` is uniform over the profiles.

Configurations are `Fin N → ℂ × ℂ`, with the paper's labels shifted to start at zero.
All definitions are total; the theorem imposes the admissible parameter ranges.
The theorem below uses the definitions shared by the challenge and solution, which
import Mathlib only. Its final proof is the only `sorry`.
-/

@[expose] public section

namespace MultipoleBKTAudit.Proposition543

open MeasureTheory Filter Topology
open scoped ENNReal
open _root_.MultipoleBKTAudit.Proposition543.TwoComponentCoulomb (box)

namespace MultipoleBKT

open scoped Classical in
/-- **Proposition 5.43**, for a
profile `n` (`n i = n_{i+1}`) with `n_1 + 2n_2 + ⋯ + p n_p ≤ N` satisfying (5.56), the event
`𝒜 = {𝒩_1^good = n_1, …, 𝒩_p^good = n_p}` and the weight `e^{t|I_bad|}`. -/
theorem proposition_5_43
    -- `χ` and `p₀` outermost
    (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (β : ℝ) (hβ : 2 < β) :
    let p := pBeta p₀ β
    -- `M` large (`M > max(20, 3^p)`; Proposition 5.20)
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    -- coefficient families pinned by the limits (2.45), (2.46)
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
      -- "for every fixed `t ≥ 1` and for `ε₀, λ` small enough depending on `β, M, p, t`"
      -- `∀ t`, then every `ε₀ ∈ (0, ε₁(t))`, then `C`, `λ₀(ε₀)`, `N₀(λ)`
      ∀ t : ℝ, 1 ≤ t →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        -- `O_{β,M,p,ε₀,t}(Nδ)` as `C`, then `λ₀`, `N₀(λ)`
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            -- absolute summability of the series in `ℐ`;
            -- on `⋃_{x ∈ [0,1]} Δ_{p,x}`, the domain on which this gate evaluates
            -- `ℐ` (`n/N ∈ Δ_{p,x}`, `x = 1 - ∑ k n_k/N`)
            (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ simplex p x, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            -- `N₀` uniform in the profile
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin p → ℕ,
              ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N →
              -- (5.56) for `k = i + 1 ∈ {2, …, p}`
              (∀ i : Fin p, 1 ≤ (i : ℕ) →
                (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
              -- `I_bad` of `c` computed on its matched dipoles
              -- `log ∫ ≤ X` as `∫ ≤ e^X`
              -- the integral as `∫⁻` over `(Λ²)^N ∩ 𝒜`
              -- `ℐ` evaluated at `n/N ∈ Δ_{p,x}` by the formula of Definition 2.15
              ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
                  {c | ∀ i : Fin p, goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
                ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀
                    fun i => ((c i).1, (c (stableMatching c i)).2)).card)) *
                  ENNReal.ofReal (Real.exp (-β * energy χ lam c))
                ≤ ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
                    + N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)
                    - N * rateFunction p (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
                    + C * N * errorRate p₀ β lam)) :=
  sorry

end MultipoleBKT

end MultipoleBKTAudit.Proposition543

end
