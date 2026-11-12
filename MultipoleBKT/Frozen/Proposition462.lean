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
public import MultipoleBKT.Frozen.DipoleConstant
public import MultipoleBKT.Frozen.PStar
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.ErrorRate
public import MultipoleBKT.Frozen.StableMatching
public import MultipoleBKT.Frozen.MultipoleCount
public import MultipoleBKT.Frozen.IsSubpartition
public import MultipoleBKT.Frozen.MultipolePartitionFunction
public import MultipoleBKT.Frozen.MultipoleActivity
public import MultipoleBKT.Frozen.BlockProfile
public import MultipoleBKT.Frozen.Simplex
public import MultipoleBKT.Frozen.RateSeriesTerm
public import MultipoleBKT.Frozen.RateFunction
public import MultipoleBKT.Frozen.TruncationScale
public import MultipoleBKT.Frozen.AlphaExponent
import MultipoleBKT.LowerBound.Proposition462

/-!
# Frozen: `MultipoleBKT.proposition_4_62`

See the paper, Proposition 4.62.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

@[expose] public section

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
  by exact MultipoleBKT.LowerBound.proposition_4_62

end MultipoleBKT

end
