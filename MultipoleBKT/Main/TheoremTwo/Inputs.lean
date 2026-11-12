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
public import MultipoleBKT.Frozen.PartitionFunction
public import MultipoleBKT.Frozen.GibbsMeasure
public import MultipoleBKT.Frozen.DipoleConstant
public import MultipoleBKT.Frozen.DipoleActivity
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
public import MultipoleBKT.Frozen.TruncationScale
public import MultipoleBKT.Frozen.AlphaExponent
public import MultipoleBKT.Frozen.BadPoints
public import MultipoleBKT.Frozen.GoodMultipoleCount

/-!
# Theorem 2 from the gates: the inputs

The proof of Theorem 2
uses the gates Proposition 4.23, Proposition 4.62
and Proposition 5.43, together with the existence of the limiting
activities `𝗆`, `𝗄^mult` (eqs. (2.45), (2.46); Lemma 4.26).

The types of the frozen statements are restated here to avoid import cycles:

* `MultipoleBKT.TheoremTwo.Prop423Statement`, `Prop462Statement`, `Prop543Statement` are the
 types of `MultipoleBKT.proposition_4_23`, `proposition_4_62`, `proposition_5_43`;
* `MultipoleBKT.TheoremTwo.Theorem2Statement` is the type of `MultipoleBKT.theorem_2`;
* `MultipoleBKT.TheoremTwo.LimitingActivitiesExist` is the existence of coefficient families
 with the `Tendsto` clauses of Theorem 2 item (1), for every `λ ∈ (0,1)`, at every `M ≥ M₀`.
 Lemma 4.26 supplies this input in `MultipoleBKT.TheoremTwo.limitingActivitiesExist`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

@[expose] public section

namespace MultipoleBKT

namespace TheoremTwo

open scoped Classical in
/-- The type of the frozen statement `MultipoleBKT.proposition_4_23` (verbatim). -/
def Prop423Statement : Prop :=
    ∀ (χ : ℂ → ℝ), IsMollifier χ → ∀ (β : ℝ), 2 < β →
    (∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ S : Finset ℕ, S ⊆ Finset.range N → S.card = k →
            lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤ multipolePartitionFunction χ N β lam M S ∧
            multipolePartitionFunction χ N β lam M S ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) ∧
    (∀ k : ℕ, (k : ℕ∞) ≤ pStar β → ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |multipoleActivity χ N β lam M X| ≤
              C * lam ^ (2 * (k - 1)) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1))) ∧
    (∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ V : Finset ℕ, V ⊆ Finset.range N → V.card = k →
            |dipoleActivity χ N β lam V| ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1))

open scoped Classical in
/-- The type of the frozen statement `MultipoleBKT.proposition_4_62` (verbatim). -/
def Prop462Statement : Prop :=
    ∀ (χ : ℂ → ℝ), IsMollifier χ → ∀ (p₀ : ℕ), 1 ≤ p₀ → ∀ (β : ℝ), 2 < β →
    let p := pBeta p₀ β
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
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
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            (∀ γ ∈ simplex p 0, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin p → ℕ,
              ∑ i : Fin p, ((i : ℕ) + 1) * n i = N →
              (∀ i : Fin p, 1 ≤ (i : ℕ) →
                (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
              ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
                  + (2 - β) * N * Real.log lam + N * Real.log (dipoleConstant χ β)
                  - N * rateFunction p (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
                  - C * N * errorRate p₀ β lam))
                ≤ ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
                    {c | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
                      ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
                        ε₀ * truncationScale p₀ β lam},
                  ENNReal.ofReal (Real.exp (-β * energy χ lam c))

open scoped Classical in
/-- The type of the frozen statement `MultipoleBKT.proposition_5_43` (verbatim). -/
def Prop543Statement : Prop :=
    ∀ (χ : ℂ → ℝ), IsMollifier χ → ∀ (p₀ : ℕ), 1 ≤ p₀ → ∀ (β : ℝ), 2 < β →
    let p := pBeta p₀ β
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
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
      ∀ t : ℝ, 1 ≤ t →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ simplex p x, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin p → ℕ,
              ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N →
              (∀ i : Fin p, 1 ≤ (i : ℕ) →
                (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
              ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
                  {c | ∀ i : Fin p, goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
                ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀
                    fun i => ((c i).1, (c (stableMatching c i)).2)).card)) *
                  ENNReal.ofReal (Real.exp (-β * energy χ lam c))
                ≤ ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
                    + N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)
                    - N * rateFunction p (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
                    + C * N * errorRate p₀ β lam))

open scoped Classical in
/-- The type of the frozen statement `MultipoleBKT.theorem_2` (verbatim). -/
def Theorem2Statement : Prop :=
    ∀ (χ : ℂ → ℝ), IsMollifier χ → ∀ (p₀ : ℕ), 1 ≤ p₀ → ∀ (β : ℝ), 2 < β →
    let p := pBeta p₀ β
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    ∃ msf : ℝ → ℕ → ℝ, ∃ kmult : ℝ → (ℕ →₀ ℕ) → ℝ,
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        (∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
            (𝓝 (msf lam S.card))) ∧
        (∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
            (𝓝 (kmult lam (blockProfile X))))) ∧
      (∀ k : ℕ, 2 ≤ k → k ≤ p →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            C⁻¹ * lam ^ (2 * (k - 1)) ≤ msf lam k ∧ msf lam k ≤ C * lam ^ (2 * (k - 1))) ∧
      (∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ p →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            |kmult lam (blockProfile X)| ≤ C * lam ^ (2 * ((X.card : ℤ) - 1))) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          (∀ γ ∈ simplex p 0, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
            ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            0 < partitionFunction χ N β lam ∧ partitionFunction χ N β lam < ∞ ∧
            |Real.log (partitionFunction χ N β lam).toReal
                - (2 * N * Real.log N
                  + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant χ β) - 1)
                  - N * sInf (rateFunction p (msf lam) (kmult lam) '' simplex p 0))|
              ≤ C * N * errorRate p₀ β lam) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, 1 ≤ n →
          gibbsMeasure χ N β lam {c | (n : ℤ) ≤
              |(∑ k ∈ Finset.Icc 1 p, (k : ℤ) * multipoleCount M lam c k) - N|}
            ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * n + C * N * errorRate p₀ β lam)) ∧
          gibbsMeasure χ N β lam {c | n ≤ {i : Fin N | criticalScale β lam ≤
              ENNReal.ofReal ‖(c i).1 - (c (stableMatching c i)).2‖}.ncard}
            ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * n + C * N * errorRate p₀ β lam))) ∧
      (∀ C₀ : ℝ, 0 < C₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            (∀ γ ∈ simplex p 0, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ γ ∈ simplex p 0,
              (∀ i : Fin p, 1 ≤ (i : ℕ) → γ i ≤ C₀ * lam ^ (2 * (i : ℕ))) →
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
      ((∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          (∀ γ ∈ simplex p 0, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
            ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
          ∃! γstar : Fin p → ℝ, γstar ∈ simplex p 0 ∧
            IsMinOn (rateFunction p (msf lam) (kmult lam)) (simplex p 0) γstar) ∧
        ∀ i : Fin p, 1 ≤ (i : ℕ) →
          ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
            ∀ lam : ℝ, 0 < lam → lam < lam₀ →
              ∃ γstar ∈ simplex p 0,
                IsMinOn (rateFunction p (msf lam) (kmult lam)) (simplex p 0) γstar ∧
                C⁻¹ * lam ^ (2 * (i : ℕ)) ≤ γstar i ∧ γstar i ≤ C * lam ^ (2 * (i : ℕ))) ∧
      (∀ k : ℕ, 2 ≤ k → k ≤ p →
        ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ C₀min : ℝ, 0 < C₀min ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
          ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
              gibbsMeasure χ N β lam {c | (multipoleCount M lam c k : ℝ) ∉
                  Set.Ioo (C₀⁻¹ * N * lam ^ (2 * (k - 1))) (C₀ * N * lam ^ (2 * (k - 1)))}
                ≤ ENNReal.ofReal (Real.exp
                    (-C * N * lam ^ (2 * (k - 1)) + C' * N * errorRate p₀ β lam)))

open scoped Classical in
/-- **Existence of the limiting activities** (eqs. (2.45), (2.46); Lemma 4.26, for every `λ ∈ (0,1)`): for every mollifier `χ` and `β > 2`, for every `M` large enough there are
coefficient families `msf`, `kmult` with exactly the `Tendsto` clauses of Theorem 2 item (1).
This is an input of the conditional assembly `theorem_2_of_gates`, not a gate. -/
def LimitingActivitiesExist : Prop :=
  ∀ (χ : ℂ → ℝ), IsMollifier χ → ∀ (β : ℝ), 2 < β →
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
    ∃ msf : ℝ → ℕ → ℝ, ∃ kmult : ℝ → (ℕ →₀ ℕ) → ℝ,
      ∀ lam : ℝ, 0 < lam → lam < 1 →
        (∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
            (𝓝 (msf lam S.card))) ∧
        (∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
            (𝓝 (kmult lam (blockProfile X))))

end TheoremTwo

end MultipoleBKT

end
