/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.PlusModel
public import MultipoleBKT.LowerBound.AbsoluteLower.SumEuler
public import MultipoleBKT.Appendix.SmallIntegral.TreeTerm
public import MultipoleBKT.Appendix.RadialIntegral
public import MultipoleBKT.Limits.BoxAverage
public import MultipoleBKT.Frozen.ErrorRate
public import MultipoleBKT.Frozen.AlphaExponent
public import MultipoleBKT.Frozen.Ursell
public import MultipoleBKT.Frozen.ConnectionGraph

/-!
# The objects of Proposition 5.20 and of Lemma 5.37

The paper: Proposition 5.20 and
Lemma 5.37, whose right-hand side is that of Lemma 4.57
(Lemma 4.57, with `J_{large,C₀}` of eq. (4.113)).

* `IsFrozenConfig p₀ β λ M ε₀ V Z`: the convention for frozen configurations of bad points
  : `I_bad^V(Z) = V` (bad sets computed from `Z` on the labels of `V`, keeping `N` in the
  count thresholds; `MultipoleBKT.UpperBound.badPointsOn`) and `Z ∈ ⋂_{i<j ∈ V} 𝒜_ij`.
* `ProfileBound p₀ β λ ε₀ N π`: eq. (5.56) for the block profile of `π`,
  `n_k = |{S ∈ π : |S| = k}| ≤ ε₀^{-α(β)} λ^{2(k-1)} N` for `k ∈ {2, …, p(β)}`.
* `jLargeIntegrand`, `jLarge`: `J_{large,C₀}(∪ₗ Tₗ^a, T^b)` of eq. (4.113),
  the Lebesgue integral over `(Λ²)^{V_X}` (values in `[0, ∞]`) of
  `∏_{ij ∈ T^b} b^abs_ij ∏ₗ ∏_{S ∈ Xₗ, S ≠ Ŝₗ} r_S² ∏ₗ ∏_{ij ∈ Tₗ^a} d_ij^{-2} 𝟙_{d_ij ≤ 17 ε₀ R̄} 𝟙_{𝓑_ij^c}
∏_{S ∈ X} 𝟙_{𝓑_S} ∏_{i ∈ V_X} (ε₀ R̄ / r_i)^{C₀/M} e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R̄}`. The factor `∏_{S ∈ Xₗ, S ≠ Ŝₗ} r_S²`, `Ŝₗ` a block of maximal radius,
  is `MultipoleBKT.AbsoluteLower.prodExceptMax` (it does not depend on the choice of `Ŝₗ`); the
  edge weights are `MultipoleBKT.AbsoluteLower.keptPair` and `MultipoleBKT.Parity.absEvenWeight`
  (the objects of Lemma 4.55, `MultipoleBKT.AbsoluteLower.eulerTreeMajorant`); the dipole
  density `e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ ε₀ R̄}` is `MultipoleBKT.SmallIntegral.cutDens` (that of
  Lemma A.4). At `r_i = 0` (a null set) Lean's conventions give the factor `0`.
* `simplifiedMajorant C C₀ X`: the right-hand side of Lemmas 4.57 and 5.37,
  `e^{C|V_X|} / ((N λ^{2-β})^{|V_X|} 𝖬^0_{ε₀}(X)) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint}
  ∑_{Tₗ^a ∈ 𝖳^{Xₗ}} ∑_{T^b ∈ 𝖳_0^{Coarse_X(X₁, …, Xₙ)}} J_{large,C₀}(∪ₗ Tₗ^a, T^b)`, in `[0, ∞]`
  (the iterated reading of the paper's `∏ₗ ∑_{Tₗ^a} ∑_{T^b}`). The prefactor is `∞` if `𝖬^0_{ε₀}(X) = 0`.
* `bigClusterTerm K p π n`, `connectedTerm K π n`: the `n`-th terms of the series of
  eq. (5.71) and of the full connected series of eq. (4.4)
  (`|∏ᵢ K(Xᵢ) I(G(X₁, …, Xₙ))|`, summed over the connected `X₁, …, Xₙ ∈ 𝒫(π)`, divided by `n!`).
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace MultipoleBKT

namespace UpperBound

namespace AbsoluteUpper

open Hierarchical Multipole SetPartition Parity AbsoluteLower

/-! ### Frozen configurations and block profiles -/

section Conventions

variable {N : ℕ}

/-- **The convention for frozen configurations of bad points** (Section 5.3): the bad points
computed from `Z` on the labels of `V` are exactly `V` (`I_bad^V(Z) = V`), and the bad dipoles
satisfy `𝒜_ij` for `i < j` in `V`. -/
def IsFrozenConfig (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) : Prop :=
  badPointsOn p₀ β lam M ε₀ V Z = V ∧ ∀ i ∈ V, ∀ j ∈ V, i < j → IsStableDipolePair (Z i) (Z j)

/-- **Eq. (5.56)** for the block profile of `π`: for every
`k ∈ {2, …, p(β)}`, `n_k = |{S ∈ π : |S| = k}| ≤ ε₀^{-α(β)} λ^{2(k-1)} N`. -/
def ProfileBound (p₀ : ℕ) (β lam ε₀ : ℝ) (N : ℕ) (π : Finset (Finset ℕ)) : Prop :=
  ∀ k : ℕ, 2 ≤ k → k ≤ pBeta p₀ β →
    ((π.filter fun S => S.card = k).card : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (k - 1)) * N

end Conventions

/-! ### `J_{large,C₀}` and the right-hand side of Lemmas 4.57 and 5.37 -/

section Majorant

variable (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ C₀ : ℝ)

open scoped Classical in
/-- **The integrand of `J_{large,C₀}(∪ₗ Tₗ^a, T^b)`** (eq. (4.113)) at a
configuration `c` of all labels, for the groups `Xs`, the trees `Ta l ∈ 𝖳^{Xs l}` and
`Tb ∈ 𝖳_0^{Coarse_X(Xs)}` (as edge sets of pairs):
`∏_{ij ∈ T^b} b^abs_ij ∏ₗ ∏_{S ∈ Xₗ, S ≠ Ŝₗ} r_S² ∏ₗ ∏_{ij ∈ Tₗ^a} d_ij^{-2} 𝟙_{d_ij ≤ 17 ε₀ R̄} 𝟙_{𝓑_ij^c}
∏_{S ∈ X} 𝟙_{𝓑_S} ∏_{i ∈ V_X} (ε₀ R̄ / r_i)^{C₀/M} e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R̄}`. -/
noncomputable def jLargeIntegrand (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ p ∈ Tb, absEvenWeight M lam ε₀ (truncationScale p₀ β lam) (c p.1) (c p.2)) *
    (∏ l, prodExceptMax c (Xs l)) *
    (∏ l, ∏ p ∈ Ta l, keptPair M lam ε₀ (truncationScale p₀ β lam) c p) *
    (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
    ∏ i ∈ X.biUnion id,
      (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) *
        SmallIntegral.cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (c i)

/-- **`J_{large,C₀}(∪ₗ Tₗ^a, T^b)`** (eq. (4.113)): the integral of
`jLargeIntegrand` over `(Λ²)^{V_X}`, `Λ = Λ_N`, with respect to Lebesgue measure, in `[0, ∞]`. -/
noncomputable def jLarge (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ)) : ℝ≥0∞ :=
  ∫⁻ y in Limits.boxConfig (X.biUnion id) N,
    ENNReal.ofReal (jLargeIntegrand χ p₀ β lam M ε₀ C₀ X Xs Ta Tb (extendConfig (X.biUnion id) y))

open scoped Classical in
/-- **The right-hand side of Lemmas 4.57 and 5.37** (Lemma 4.57,
Lemma 5.37), in `[0, ∞]`:
`e^{C|V_X|} / ((N λ^{2-β})^{|V_X|} 𝖬^0_{ε₀}(X)) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint}
∑_{(Tₗ^a)ₗ, Tₗ^a ∈ 𝖳^{Xₗ}} ∑_{T^b ∈ 𝖳_0^{Coarse_X(X₁, …, Xₙ)}} J_{large,C₀}(∪ₗ Tₗ^a, T^b)`. -/
noncomputable def simplifiedMajorant (C : ℝ) (X : Finset (Finset ℕ)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (C * (X.biUnion id).card)) /
      ENNReal.ofReal (((N : ℝ) * lam ^ (2 - β)) ^ (X.biUnion id).card *
        zeroPartitionFunction χ N p₀ β lam M ε₀ X) *
    ∑' n : ℕ, ((n.factorial : ℝ≥0∞))⁻¹ *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
            jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb

end Majorant

/-! ### The terms of the connected series -/

section Series

variable (K : Finset (Finset ℕ) → ℝ) (π : Finset (Finset ℕ))

open scoped Classical in
/-- The `n`-th term of the full connected series of eq. (4.4) in absolute value,
`(1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) connected} |K(X₁) ⋯ K(Xₙ) I(G(X₁, …, Xₙ))|`. -/
noncomputable def connectedTerm (n : ℕ) : ℝ :=
  1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
        (fun Xs => (connectionGraph Xs).Connected),
      |(∏ i, K (Xs i)) * (ursell (connectionGraph Xs) : ℝ)|

open scoped Classical in
/-- The `n`-th term of the series of eq. (5.71),
`(1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) connected} |K(X₁) ⋯ K(Xₙ) I(G(X₁, …, Xₙ))| 𝟙_{∃ i, |V_{Xᵢ}| > p}`. -/
noncomputable def bigClusterTerm (p : ℕ) (n : ℕ) : ℝ :=
  1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
        (fun Xs => (connectionGraph Xs).Connected ∧ ∃ i, p < ((Xs i).biUnion id).card),
      |(∏ i, K (Xs i)) * (ursell (connectionGraph Xs) : ℝ)|

open scoped Classical in
/-- The full connected series of eq. (4.4),
`∑_{n ≥ 1} (1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) connected} K(X₁) ⋯ K(Xₙ) I(G(X₁, …, Xₙ))`. -/
noncomputable def connectedSeries : ℝ :=
  ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
        (fun Xs => (connectionGraph Xs).Connected),
      (∏ i, K (Xs i)) * (ursell (connectionGraph Xs) : ℝ)

/-- **The conclusions of Proposition 5.20 for an activity `K`** with bound `B` (`= C N δ_{β,λ}`):
eq. (5.70), the absolute convergence of the full connected series, and
eq. (5.71), whose series converges. -/
def AbsoluteUpperBounds (p : ℕ) (B : ℝ) : Prop :=
  (∑ X ∈ π.powerset.filter (fun X => p < (X.biUnion id).card), |K X| ≤ B) ∧
    Summable (connectedTerm K π) ∧ Summable (bigClusterTerm K π p) ∧
    ∑' n, bigClusterTerm K π p n ≤ B

theorem connectedTerm_nonneg (n : ℕ) : 0 ≤ connectedTerm K π n :=
  mul_nonneg (by positivity) (sum_nonneg fun _ _ => abs_nonneg _)

theorem bigClusterTerm_nonneg (p n : ℕ) : 0 ≤ bigClusterTerm K π p n :=
  mul_nonneg (by positivity) (sum_nonneg fun _ _ => abs_nonneg _)

end Series

end AbsoluteUpper

end UpperBound

end MultipoleBKT

end
