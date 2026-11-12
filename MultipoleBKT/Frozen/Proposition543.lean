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
public import MultipoleBKT.Frozen.IsSubpartition
public import MultipoleBKT.Frozen.MultipolePartitionFunction
public import MultipoleBKT.Frozen.MultipoleActivity
public import MultipoleBKT.Frozen.BlockProfile
public import MultipoleBKT.Frozen.Simplex
public import MultipoleBKT.Frozen.RateSeriesTerm
public import MultipoleBKT.Frozen.RateFunction
public import MultipoleBKT.Frozen.AlphaExponent
public import MultipoleBKT.Frozen.BadPoints
public import MultipoleBKT.Frozen.GoodMultipoleCount
import MultipoleBKT.UpperBound.Proposition543

/-!
# Frozen: `MultipoleBKT.proposition_5_43`

See the paper, Proposition 5.43.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

@[expose] public section

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
  by exact MultipoleBKT.UpperBound.proposition_5_43

end MultipoleBKT

end
