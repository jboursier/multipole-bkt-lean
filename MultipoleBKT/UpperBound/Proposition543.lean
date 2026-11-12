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
public import MultipoleBKT.UpperBound.UpperBoundLDP.Assembly

/-!
# Provider for the frozen statement `MultipoleBKT.proposition_5_43`

Registered implementation module of `MultipoleBKT/Frozen/Proposition543.lean`. Its export
`MultipoleBKT.UpperBound.proposition_5_43` states exactly the frozen statement (Proposition 5.43,
the large deviations upper bound). The proof is `MultipoleBKT.UpperBoundLDP.proposition_5_43_upper`
(`MultipoleBKT.UpperBound.UpperBoundLDP.Assembly`), which has no further hypotheses: the inputs of
Propositions 5.19 and 5.20 are discharged there, namely Lemma A.7 for `(v^Z, τ^Z)`
(`ExpansionK.lemmaA8Plus_holds`), Lemma A.7 (A.50) (`ExpansionK.lemmaA8Bis_holds`),
the claim (5.106) (`UpperBound.NonEmptyMarks.nonEmptyMarks_holds`), Lemma 5.37
(`UpperBound.SimplifiedUpper.simplifiedBoundUpper_holds`) and the transfer of Lemma 4.59 /
Proposition 4.27 (`AbsoluteLower.absoluteConvergenceTransfer`).

The binders follow the frozen statement's: `χ`, `p₀`, `β` are implicit and the hypotheses are
auto-parameters, so that the frozen statement's body is `by exact MultipoleBKT.UpperBound.proposition_5_43`.

The frozen statement imports this provider; this module does not import the frozen statement.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT.UpperBound

open scoped Classical in
/-- **Proposition 5.43**, exactly
the frozen statement of `MultipoleBKT.proposition_5_43`: for a profile `n` (`n i = n_{i+1}`) with
`n_1 + 2n_2 + ⋯ + p n_p ≤ N` satisfying (5.56), the event
`𝒜 = {𝒩_1^good = n_1, …, 𝒩_p^good = n_p}` and the weight `e^{t|I_bad|}`. -/
theorem proposition_5_43
    -- `χ` and `p₀` are quantified outermost, before `N` and `λ`.
    {χ : ℂ → ℝ} (hχ : IsMollifier χ := by assumption) {p₀ : ℕ} (hp₀ : 1 ≤ p₀ := by assumption)
    {β : ℝ} (hβ : 2 < β := by assumption) :
    let p := pBeta p₀ β
    -- `M` is sufficiently large: `M > max(20, 3^p)` (Proposition 5.20).
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
      -- "for every fixed `t ≥ 1` and for `ε₀, λ` small enough depending on `β, M, p, t`" (Proposition 5.43)
      -- `∀ t`, then every `ε₀ ∈ (0, ε₁(t))`, then `C`, `λ₀(ε₀)`, `N₀(λ)`
      ∀ t : ℝ, 1 ≤ t →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        -- `O_{β,M,p,ε₀,t}(Nδ)` as `C`, then `λ₀`, `N₀(λ)`
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            -- absolute summability of the series in `ℐ`;
            -- on `⋃_{x ∈ [0,1]} Δ_{p,x}`, the domain on which this gate evaluates
            -- `ℐ` (`n/N ∈ Δ_{p,x}`, `x = 1 - ∑ k n_k/N`; cf. proof of Theorem 2)
            (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ simplex p x, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            -- `N₀` uniform in the profile (proof of Theorem 2)
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
  UpperBoundLDP.proposition_5_43_upper hχ hp₀ hβ

end MultipoleBKT.UpperBound

end
