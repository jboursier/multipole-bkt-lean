/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.ActivityDiff
public import MultipoleBKT.Frozen.BoundedBlockPartitions
public import MultipoleBKT.Frozen.ErrorRate
public import MultipoleBKT.Frozen.AlphaExponent
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.Ursell
public import MultipoleBKT.Frozen.ConnectionGraph

/-!
# Proposition 4.62: the inputs

The proof of Proposition 4.62 uses two results, proved elsewhere in the library. Their statements, in the
paper's form, are the only hypotheses of the internal theorem
`MultipoleBKT.LowerBoundLDP.proposition_4_62_of_inputs`:

* `Prop427Statement` — **Proposition 4.27**: for `M` large
  (with respect to `β`, `p(β)`), `ε₀` small (with respect to `β`, `p(β)`, `M`) and `λ` small, there
  is `C` depending on `β, M, p(β), ε₀` such that for every partition `π` of `[N]` into blocks of
  size at most `p(β)` satisfying (4.22) (`#_k π ≤ ε₀^{-α(β)} N λ^{2(k-1)}` for
  `2 ≤ k ≤ p(β)`), eq. (4.55) holds, the full connected series of `𝖪^-_{ε₀}` converges absolutely
  (the blue clause, Proposition 4.27), and eq. (4.56) holds. Here `𝖪^-_{ε₀}` is
  `MultipoleBKT.Hierarchical.minusActivity` with the damping constant `L` of (3.53). The
  statement asks the bounds only for `N` large at fixed `λ`, which is weaker than the paper's
  every `N`. It is proved, for every mollifier, `p₀ ≥ 1`, `β > 2` and every `L` (in
  particular `L = β / 64`), by `MultipoleBKT.AbsoluteLower.prop427Statement_holds`.
* `LemmaA8Inputs` — the two estimates (A.49) and (A.50) of **Lemma A.7**, in the form `LemmaA8MinusStatement`,
  `LemmaA8BisStatement` consumed by Proposition 4.24 (eq. (4.44)), for every `M` large and every
  cluster size `2 ≤ k ≤ p(β)`. It is proved (with `M₁ = 1`, for the damping constant `L = β / 64`)
  by `MultipoleBKT.ExpansionK.lemmaA8Inputs_holds`, from `ExpansionK.lemmaA8Minus_holds` and
  `ExpansionK.lemmaA8Bis_holds`.

Lemma A.8 is not needed: it enters Proposition 4.24 only through (4.43), which
the proof of Proposition 4.62 does not use.
-/

@[expose] public section

namespace MultipoleBKT

namespace LowerBoundLDP

open Hierarchical

open scoped Classical in
/-- **Proposition 4.27**, in the paper's form, for
the activity `𝖪^-_{ε₀}` with damping constant `L` and `p = p(β)`: there is `M₀` such that for
`M ≥ M₀` there is `ε₁ > 0` such that for `ε₀ ∈ (0, ε₁)` there are `C > 0` and `λ₀ > 0` such that
for `λ ∈ (0, λ₀)` and `N` large, for every partition `π ∈ 𝚷_p([N])` with
`#_k π ≤ ε₀^{-α(β)} N λ^{2(k-1)}` for `2 ≤ k ≤ p` (eq. (4.22)):

* (4.55) `∑_{X ⊂ π, |V_X| > p} |𝖪^-_{ε₀}(X)| ≤ C N δ_{β,λ}`;
* the full connected series `∑_n (1/n!) ∑_{X₁, …, Xₙ ⊂ π connected} |𝖪^-_{ε₀}(X₁) ⋯ 𝖪^-_{ε₀}(Xₙ)
  I(G(X))|` converges;
* (4.56) its part over the tuples with some `|V_{X_i}| > p` is at most `C N δ_{β,λ}`. -/
def Prop427Statement (χ : ℂ → ℝ) (p₀ : ℕ) (β L : ℝ) : Prop :=
  ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ π ∈ boundedBlockPartitions N (pBeta p₀ β),
          (∀ k : ℕ, 2 ≤ k → k ≤ pBeta p₀ β →
            ((π.filter fun S => S.card = k).card : ℝ) ≤
              ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1))) →
          (∑ X ∈ π.powerset.filter (fun X => pBeta p₀ β < (X.biUnion id).card),
              |minusActivity χ N p₀ β lam M ε₀ L X| ≤ C * N * errorRate p₀ β lam) ∧
          (Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
            ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
                (fun X => (connectionGraph X).Connected),
              |(∏ i, minusActivity χ N p₀ β lam M ε₀ L (X i)) *
                (ursell (connectionGraph X) : ℝ)|) ∧
          ∑' n : ℕ, 1 / (n.factorial : ℝ) *
            ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
                (fun X => (connectionGraph X).Connected ∧
                  ∃ i, pBeta p₀ β < ((X i).biUnion id).card),
              |(∏ i, minusActivity χ N p₀ β lam M ε₀ L (X i)) *
                (ursell (connectionGraph X) : ℝ)| ≤ C * N * errorRate p₀ β lam

/-- **Lemma A.7**, both estimates, in the form used by
Proposition 4.24 (`MultipoleBKT.ExpansionErrors.LemmaA8MinusStatement`,
`MultipoleBKT.ExpansionErrors.LemmaA8BisStatement`): for every `M` large enough and every cluster
size `2 ≤ k ≤ p(β)`. -/
def LemmaA8Inputs (χ : ℂ → ℝ) (p₀ : ℕ) (β L : ℝ) : Prop :=
  ∃ M₁ : ℝ, ∀ M : ℝ, M₁ ≤ M → ∀ k : ℕ, 2 ≤ k → k ≤ pBeta p₀ β →
    ExpansionErrors.LemmaA8MinusStatement χ β M L p₀ k ∧
      ExpansionErrors.LemmaA8BisStatement χ β M p₀ k

end LowerBoundLDP

end MultipoleBKT

end
