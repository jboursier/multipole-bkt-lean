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
public import MultipoleBKT.Frozen.PartitionFunction
public import MultipoleBKT.Frozen.GibbsMeasure
public import MultipoleBKT.Frozen.DipoleConstant
public import MultipoleBKT.Frozen.PStar
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.CriticalScale
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
import MultipoleBKT.Main.Theorem2

/-!
# Frozen: `MultipoleBKT.theorem_2`

See the paper, Theorem 2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

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
  by exact MultipoleBKT.Main.theorem_2

end MultipoleBKT

end
