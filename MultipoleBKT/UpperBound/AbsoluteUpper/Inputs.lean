/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.AbsoluteUpper.Majorant

/-!
# The inputs of Proposition 5.20

Proposition 5.20 is
proved in `MultipoleBKT.UpperBound.AbsoluteUpper.Assembly` from the statements below, which enter
the internal theorem `MultipoleBKT.UpperBound.AbsoluteUpper.prop_5_20_of_inputs` as hypotheses.
All of them are proved elsewhere in the library (see the end of this docstring).
Each is a statement of the paper, for fixed `χ`, `p₀`, `β` and the constant `L` of
eq. (5.50) (`L = β L₀` in Lemma 5.16), with the paper's implicit "`λ` small enough" and
"`N` large enough" (Section 2.4) made explicit. Good labels are the labels of
`[N] ∖ V_bad`, read in `ℕ`, as in `MultipoleBKT.UpperBound.lemma_5_16`.

* `KPlusBoundInput`: **eq. (5.67)** of Proposition 5.18, for every frozen configuration and every nonempty subpartition `X`
  of the good labels with blocks of size at most `p(β)`:
  `|𝖪^{+,Z}_{ε₀}(X)| ≤ C γ_{β,λ,|V_X|} / (𝖬^0_{ε₀}(X) N^{|V_X|-1})`, `C` depending on `β, M, ε₀`
  and `|V_X|`, as in (5.104); the constant in Proposition 5.20 may also depend on `ε₀`.
* `ExternalPositivityInput`: **eq. (5.101)** of the proof of Proposition 5.18, the lower half `1 ≤ g^Z_{ε₀}(S)`, in the form of
  `MultipoleBKT.UpperBound.BoundedUpper.one_le_externalNormalization`.
* `AbsoluteConvergenceTransfer`: **Lemma 4.59 and Proposition 4.27 for an abstract activity**.
  The proof of Proposition 5.20 is: "the activity `𝖪^{+,Z}_{ε₀}(X)`
  satisfies the exact same bound as `𝖪^-_{ε₀}(X)` in Lemma 4.57. Therefore, since the proofs of
  Lemma 4.59 and Proposition 4.27 only depend on this final bound and on the estimate on bounded
  clusters already established in Proposition 5.18, the same bounds give (5.70) and
  (5.71)". In this form, for every activity `K` on the subfamilies of `π`,
  vanishing on families of at most one block, bounded by the right-hand side of Lemma 4.57
  (`simplifiedMajorant`) and, on clusters of at most `q` dipoles, by the bounded-cluster
  estimate `C_b γ_{β,λ,|V_X|} / (𝖬^0_{ε₀}(X) N^{|V_X|-1})`, eqs. (4.55) and (4.56) of
  Proposition 4.27 hold. The quantifiers are those of Lemma 4.59 and Proposition 4.27: `C₀`
  (Lemma 4.57, depending on `β`) first, then `M` large, then the constant `C` of Lemma 4.57
  (depending on `β`, `M`), then `ε₀` small, a size `q` (the `q₀` of eq. (4.120)) up to which
  the bounded-cluster estimate is used, the bounded-cluster constant `C_b` (which may depend on
  `ε₀`), and finally `C'`, `λ₀`, `N₀`.

All inputs are proved. The first two are proved by
`MultipoleBKT.UpperBound.AbsoluteUpper.kPlusBoundInput_holds` and `externalPositivityInput_holds`
(module `MultipoleBKT.UpperBound.AbsoluteUpper.Discharge`). `AbsoluteConvergenceTransfer` is
proved by `MultipoleBKT.AbsoluteLower.absoluteConvergenceTransfer` (module
`MultipoleBKT.LowerBound.AbsoluteLower.Prop427Transfer`). The statement of Lemma 5.37, `SimplifiedBoundUpper`, is proved by
`MultipoleBKT.UpperBound.SimplifiedUpper.simplifiedBoundUpper_holds` (from Lemmas 5.35–5.36;
module `MultipoleBKT.UpperBound.SimplifiedUpper.Assembly`). These are consumed by
`MultipoleBKT.UpperBound.AbsoluteUpper.prop_5_20_of_simplified` and, through it, by the provider
of Proposition 5.43 (module `MultipoleBKT.UpperBound.UpperBoundLDP.Assembly`).
-/

@[expose] public section

open Finset
open scoped ENNReal

namespace MultipoleBKT

namespace UpperBound

namespace AbsoluteUpper

open Hierarchical

/-- **Eq. (5.67)** of Proposition 5.18: for
`M > max(20, 3^{p(β)})`, `ε₀ ∈ (0, 1)` and `k ≥ 1` there is `C > 0` such
that for `λ` small and `N` large, for every frozen configuration `(V, Z)` and every nonempty
subpartition `X` of the good labels with blocks of size at most `p(β)` and `|V_X| = k`,
`|𝖪^{+,Z}_{ε₀}(X)| ≤ C γ_{β,λ,k} / (𝖬^0_{ε₀}(X) N^{k-1})`. -/
def KPlusBoundInput (χ : ℂ → ℝ) (p₀ : ℕ) (β L : ℝ) : Prop :=
  ∀ M : ℝ, 20 < M → (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∀ k : ℕ, 1 ≤ k →
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
        IsFrozenConfig p₀ β lam M ε₀ V Z →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.Nonempty →
          (∀ S ∈ X, S ⊆ (Finset.univ \ V).map Fin.valEmbedding) →
          (∀ S ∈ X, S.card ≤ pBeta p₀ β) → (X.biUnion id).card = k →
          |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
            C * Appendix.gammaBeta p₀ β lam k /
              (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1))

/-- **Eq. (5.101), lower half** (proof of Proposition 5.18):
`1 ≤ g^Z_{ε₀}(S)` whenever `𝖬^{+,Z}_{ε₀}(S) > 0`, for `0 < λ ≤ ε₀ R̄`, `N ≥ 1`,
`M ≥ max(3, 3^{p(β)})` and `V ⊆ I_bad^V(Z)`. -/
def ExternalPositivityInput (χ : ℂ → ℝ) (p₀ : ℕ) (β L : ℝ) : Prop :=
  ∀ {N : ℕ} (lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → 0 < ε₀ →
    1 ≤ N → lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M → 3 ≤ M →
    V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ S : Finset ℕ, S.Nonempty →
    0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S →
    1 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S

/-- **Lemma 4.59 and Proposition 4.27 for an abstract activity** (the transfer claimed in the
proof of Proposition 5.20): eqs. (4.55) and (4.56) ((5.70),
(5.71) in §5) for every activity `K` on the subfamilies of `π` vanishing on families of at
most one block and satisfying the final bound of Lemma 4.57 (`simplifiedMajorant` with the
constants `C₀`, `C`) and, on clusters of at most `q` dipoles, the bounded-cluster estimate with
constant `C_b`. The series of (4.56) is asserted to converge. -/
def AbsoluteConvergenceTransfer (χ : ℂ → ℝ) (p₀ : ℕ) (β : ℝ) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ C : ℝ, 0 ≤ C →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∃ q : ℕ, ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ → ∀ Cb : ℝ, 0 ≤ Cb →
      ∃ C' : ℝ, 0 < C' ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ π : Finset (Finset ℕ), IsSubpartition π → (∀ S ∈ π, S ⊆ Finset.range N) →
          (∀ S ∈ π, S.card ≤ pBeta p₀ β) → ProfileBound p₀ β lam ε₀ N π →
        ∀ K : Finset (Finset ℕ) → ℝ, (∀ X ⊆ π, X.card ≤ 1 → K X = 0) →
          (∀ X ⊆ π, 2 ≤ X.card →
            ENNReal.ofReal |K X| ≤ simplifiedMajorant χ N p₀ β lam M ε₀ C₀ C X) →
          (∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ q →
            |K X| ≤ Cb * Appendix.gammaBeta p₀ β lam (X.biUnion id).card /
              (zeroPartitionFunction χ N p₀ β lam M ε₀ X *
                (N : ℝ) ^ ((X.biUnion id).card - 1))) →
          (∑ X ∈ π.powerset.filter (fun X => pBeta p₀ β < (X.biUnion id).card), |K X| ≤
              C' * N * errorRate p₀ β lam) ∧
            Summable (bigClusterTerm K π (pBeta p₀ β)) ∧
            ∑' n, bigClusterTerm K π (pBeta p₀ β) n ≤ C' * N * errorRate p₀ β lam

/-- **The statement of Lemma 5.37**: there are `C₀ > 0`
(depending only on `β`) and, for `M > max(20, 3^{p(β)})`, `C ≥ 0` (depending only on `β` and
`M`) such that for every `ε₀ ∈ (0, 1)`, `λ` small and `N` large, every frozen configuration
`(V, Z)` and every subpartition `X` of the good labels with blocks of size at most `p(β)`,
`|𝖪^{+,Z}_{ε₀}(X)| ≤ simplifiedMajorant C C₀ X` (the right-hand side of Lemma 4.57). -/
def SimplifiedBoundUpper (χ : ℂ → ℝ) (p₀ : ℕ) (β L : ℝ) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ M : ℝ, 20 < M → (3 : ℝ) ^ pBeta p₀ β ≤ M → ∃ C : ℝ, 0 ≤ C ∧
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
        IsFrozenConfig p₀ β lam M ε₀ V Z →
        ∀ X : Finset (Finset ℕ), IsSubpartition X →
          (∀ S ∈ X, S ⊆ (Finset.univ \ V).map Fin.valEmbedding) →
          (∀ S ∈ X, S.card ≤ pBeta p₀ β) →
          ENNReal.ofReal |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
            simplifiedMajorant χ N p₀ β lam M ε₀ C₀ C X

end AbsoluteUpper

end UpperBound

end MultipoleBKT

end
