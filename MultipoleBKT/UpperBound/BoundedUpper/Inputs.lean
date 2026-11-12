/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Model
public import MultipoleBKT.Frozen.PStar

/-!
# The inputs of Proposition 5.18 from Proposition 4.23 and Lemma A.4

Proposition 5.18 uses,
besides the results proved in `MultipoleBKT.UpperBound.BoundedUpper` and Lemma A.3 for the model
with frozen bad points (`MultipoleBKT.plusPartitionFunction_two_sided`), the multipole and integral bounds below. The internal theorem `MultipoleBKT.UpperBound.BoundedUpper.prop_5_18_of_inputs` takes
them as hypotheses in the form below (each for fixed `p₀`, `β`, `M`, `ε₀`, with the paper's
implicit "`λ` small enough" and "`N` large enough", explicit); they are discharged by
`mxZeroBounds_holds` and `RouteRaw.lemmaA6J_source_holds`, giving the unconditional
`MultipoleBKT.UpperBound.BoundedUpper.prop_5_18`. Labels: `S`, `X` are finite sets of labels of
`ℕ`; the good labels of a set `V : Finset (Fin N)` of bad labels are `goodLabels V = [N] ∖ V`, read
in `ℕ`.

* `MXZeroBounds`: **eqs. (4.38) and (4.39)** of Proposition 4.23 for `𝖬 = 𝖬^0_{ε₀}`: for `1 < |S| ≤ p*(β)`,
  `λ^{2(|S|-1)} / (C N^{|S|-1}) ≤ 𝖬^0_{ε₀}(S) ≤ C λ^{2(|S|-1)} / N^{|S|-1}`.

The second input, Lemma A.4 (eq. (A.19)), is stated in
`MultipoleBKT.UpperBound.BoundedUpper.JIntegral` (`LemmaA6J`).
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical

/-- The good labels `[N] ∖ V` of a set `V` of bad labels, read in `ℕ`. -/
def goodLabels {N : ℕ} (V : Finset (Fin N)) : Finset ℕ :=
  (Finset.univ \ V).map Fin.valEmbedding

theorem mem_goodLabels {N : ℕ} {V : Finset (Fin N)} {n : ℕ} :
    n ∈ goodLabels V ↔ ∃ h : n < N, (⟨n, h⟩ : Fin N) ∉ V := by
  simp only [goodLabels, Finset.mem_map, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, hi⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨n, h⟩, h', rfl⟩

/-- **Eqs. (4.38) and (4.39) for `𝖬^0_{ε₀}`** (Proposition 4.23,
eqs. (4.38)–(4.39)), for fixed `p₀`, `β`, `M`, `ε₀`: for
`1 < k ≤ p*(β)` there is `C > 0` such that for `λ` small and `N` large,
`λ^{2(k-1)} / (C N^{k-1}) ≤ 𝖬^0_{ε₀}(S) ≤ C λ^{2(k-1)} / N^{k-1}` for every `S` with `|S| = k`. -/
def MXZeroBounds (χ : ℂ → ℝ) (p₀ : ℕ) (β M ε₀ : ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S.card = k →
        lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤ zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
          zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)

end BoundedUpper

end UpperBound

end MultipoleBKT

end
