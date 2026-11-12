/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.ExpansionPlus.Blocks

/-!
# The inputs of eq. (5.69)

The paper: proof of Proposition 5.19. The proof of (5.69) uses, besides the results proved in
`MultipoleBKT.UpperBound.ExpansionPlus` and the inputs Lemma A.6, Lemma A.3, Prop 4.23 and
Prop 5.18, three statements. The internal theorems
`MultipoleBKT.UpperBound.ExpansionPlus.eq_K_plus_diff_of_inputs` and
`MultipoleBKT.UpperBound.ExpansionPlus.prop_5_19_of_inputs` take them as hypotheses; all three are
proved:

* `LemmaA8PlusStatement` (this file): **Lemma A.7, eq. (A.49)** for `(w, τ) = (v^Z, τ^Z)`; proved by `MultipoleBKT.ExpansionK.lemmaA8Plus_holds`;
* `MultipoleBKT.ExpansionErrors.LemmaA8BisStatement`: **Lemma A.7,
  eq. (A.50)**, shared with Proposition 4.24; proved by
  `MultipoleBKT.ExpansionK.lemmaA8Bis_holds`;
* `NonEmptyMarksStatement` (this file): **the claim (5.106)** of the proof of
  Proposition 5.19, whose proof is a pointwise reduction of the marked terms of
  `𝖪^{+,Z}_{ε₀}` to the integral `J_ext` and **Lemma A.4, eq. (A.20)** (proof); proved by `MultipoleBKT.UpperBound.NonEmptyMarks.nonEmptyMarks_holds`.

The three are discharged where Proposition 5.19 is used, in `prop_5_19_uniform`
(module `MultipoleBKT.UpperBound.UpperBoundLDP.Uniform`).

`plusClusterIntegral` is `I^{+,Z}_{cl,ε₀}(X; 𝐗, 𝐄, F)` (eq. (A.48)),
in the notation of `MultipoleBKT.ExpansionErrors.clusterIntegral`.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace ExpansionPlus

open MeasureTheory Finset
open Hierarchical BoundedUpper ExpansionErrors Multipole SetPartition

/-- **`I^{+,Z}_{cl,ε₀}(X; 𝐗, 𝐄, F)`** (eq. (A.48), for
`(w, τ, L, Z) = (v^Z, τ^Z, L, Z)`):
`∫_{(Λ²)^{V_X}} ∏_{i ∈ V_X} 𝟙_{i ∈ I_good^Z} ∏_{ij ∈ ∪ Eₗ} f^{v^Z}_ij ∏_{ij ∈ F} (-𝟙_{𝓑_ij})
∏_{ij ∈ ∪ ℰ^inter(Xₗ)} 𝟙_{𝓑_ij^c} (∏_{S ∈ X} 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v^Z_ij} 𝟙_{𝒜_ij})
∏_{i ∈ V_X} e^{L r_i²/(τ_i^Z)²} e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R̄} dx_i dy_i`. -/
noncomputable def plusClusterIntegral (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ L : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) : ℝ :=
  clusterIntegral N β (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z)
    (cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam)) M lam X Xs Es F

open scoped Classical in
/-- **Lemma A.7, eq. (A.49), for the model with frozen bad points**
(with `(w, τ) = (v^Z, τ^Z)`), for fixed `β, M, L, p₀`
and `k = |V_X|` (the paper assumes `k ≤ p*(β)`): there is `C > 0` (depending on `β, M, L, k`, not
on `ε₀`) such that for every `ε₀ ∈ (0, 1)` there are `C_{ε₀} > 0` and `λ₀ > 0` such that for every
`λ ∈ (0, λ₀)` there is `N₀` with, for `N ≥ N₀` (when `3^{p(β)} ≤ M`), every frozen configuration
`(V, Z)` (`I_bad^V(Z) = V`), every subpartition `X` of `[N] ∖ V` with `|X| ≥ 2` and `|V_X| = k`,
and all `X₁, …, Xₙ ⊂ X` disjoint, `Eₗ ∈ 𝖤^{Xₗ}`, `F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}`,
`|I^{+,Z}_{cl,ε₀}(X; 𝐗, 𝐄, F) - I^0_{cl,ε₀}(X; 𝐗, 𝐄, F)| ≤
λ^{(2-β)k} (C_{ε₀} N R̄^{-2} + C ε₀^{α(β)k} |V_bad|)`.
The paper has every `N`; asking it only for `N` large makes the statement weaker. -/
def LemmaA8PlusStatement (χ : ℂ → ℝ) (β M L : ℝ) (p₀ k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (3 : ℝ) ^ pBeta p₀ β ≤ M →
    ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
    ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ goodLabels V →
      2 ≤ X.card → (X.biUnion id).card = k →
      ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
        (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) →
        ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
        ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          |plusClusterIntegral χ N p₀ β lam M ε₀ L V Z X Xs Es F -
              zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F| ≤
            lam ^ ((2 - β) * k) * (Cε * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
              C * ε₀ ^ (alphaExponent β * k) * V.card)

open scoped Classical in
/-- **The claim (5.106)** of the proof of Proposition 5.19 (proved there
from the pointwise reduction and Lemma A.4, eq. (A.20)), for fixed `β, M, L, p₀`
and `k = |V_X|`: there is `C > 0` (not depending on `ε₀`) such that for every `ε₀ ∈ (0, 1)` there
are `C_{ε₀} > 0` and `λ₀ > 0` such that for every `λ ∈ (0, λ₀)` there is `N₀` with, for `N ≥ N₀`
(when `3^{p(β)} ≤ M`), every frozen configuration `(V, Z)`, every subpartition `X` of `[N] ∖ V`
with `|X| ≥ 2` and `|V_X| = k`, every nonempty set of marks `V^∞ ⊆ V_X` and all data `(𝐗, 𝐄, F)`
of Definition 5.15,
`|𝔼_{𝖯^{+,ε₀,Z}_X}[∏_{ij ∈ ∪ Eₗ} f^{v^Z}_ij ∏_{ij ∈ ∪ ℰ^inter(Xₗ)} 𝟙_{𝓑_ij^c}
∏_{ij ∈ F} (-𝟙_{𝓑_ij}) ∏_{i ∈ V^∞} f^{v^Z}_{i∞}]| ≤ θ_k / (𝖬^{+,Z}_{ε₀}(X) N^{k-1})`,
`θ_k = C_{ε₀} R̄^{-2} + C ε₀^{α(β)k} |V_bad|/N`. -/
def NonEmptyMarksStatement (χ : ℂ → ℝ) (β M L : ℝ) (p₀ k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (3 : ℝ) ^ pBeta p₀ β ≤ M →
    ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
    ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ goodLabels V →
      2 ≤ X.card → (X.biUnion id).card = k →
      ∀ U ⊆ X.biUnion id, U.Nonempty →
      ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
        (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) →
        ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
        ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          |∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
                (extendConfig (X.biUnion id) y) *
              ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
            ∂plusModel χ N p₀ β lam M ε₀ L V Z X| ≤
            (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
              ((∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) * (N : ℝ) ^ (k - 1))

end ExpansionPlus

end UpperBound

end MultipoleBKT

end
