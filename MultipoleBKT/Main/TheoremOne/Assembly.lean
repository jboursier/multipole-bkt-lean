/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremOne.ItemOne
public import MultipoleBKT.Main.TheoremOne.ItemThree

/-!
# Theorem 1 from the gates: the assembly

The proof of Theorem 1 as an internal conditional theorem: `theorem_1_of_gates` proves the type of the
frozen statement `MultipoleBKT.theorem_1` (restated verbatim as
`MultipoleBKT.TheoremOne.Theorem1Statement`) from

* the frozen statement of Proposition 4.23 (`MultipoleBKT.TheoremTwo.Prop423Statement`), of
 which only (4.41) is used;
* the frozen statement of Proposition 5.45 (`MultipoleBKT.TheoremOne.Prop545Statement`);
* the existence of the limits `𝗄^dip` (eq. (2.34); Lemma 4.26), `DipoleLimitsExist`.

Lemma 5.46 is used directly (`MultipoleBKT.lemma_5_46`). The provider of Theorem 1 applies
this assembly to Propositions 4.23 and 5.45 and Lemma 4.26.

The witness `𝗄^dip` is the coefficient family of `DipoleLimitsExist`, set to `0` at `k = 0, 1`
(the limit clause of the frozen statement prescribes these values; they are not limits).
-/

@[expose] public section

open MeasureTheory Filter Topology Finset

namespace MultipoleBKT

namespace TheoremOne

open scoped Classical in
/-- **Theorem 1 from the gates**: the frozen statements of Propositions 4.23 and 5.45 and the existence of the limits
(2.34) imply the frozen statement of Theorem 1. -/
theorem theorem_1_of_gates (h423 : TheoremTwo.Prop423Statement) (h545 : Prop545Statement)
    (hlim : DipoleLimitsExist) : Theorem1Statement := by
  unfold Theorem1Statement
  intro χ hχ p₀ hp₀ β hβ
  obtain ⟨-, -, h439⟩ := h423 χ hχ β hβ
  obtain ⟨kdip₀, hk₀⟩ := hlim χ hχ β hβ
  have hpS : (pBeta p₀ β : ℕ∞) ≤ pStar β := TheoremTwo.pBeta_le_pStar hp₀ hβ
  -- the limits (2.34) for the normalized family
  have hlim' : ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∀ V : Finset ℕ, V.card = k →
        Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * dipoleActivity χ N β lam V) atTop
          (𝓝 ((fun lam k => if k ≤ 1 then 0 else kdip₀ lam k) lam k)) := by
    intro lam hlam hlam1 k hk2 hkS V hV
    simp only [show ¬ k ≤ 1 by omega, ite_false]
    exact hk₀ lam hlam hlam1 k hk2 hkS V hV
  have hlimr : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ j : ℕ, 2 ≤ j → j ≤ pBeta p₀ β →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (j - 1) * dipoleActivity χ N β lam (range j)) atTop
        (𝓝 ((fun lam k => if k ≤ 1 then 0 else kdip₀ lam k) lam j)) :=
    fun lam hlam hlam1 j hj2 hjp => hlim' lam hlam hlam1 j hj2
      ((Nat.cast_le.mpr hjp).trans hpS) (range j) (card_range j)
  obtain ⟨C₀, hC₀, lam₁, hlam₁, hlam₁1, hb⟩ := exists_uniform_dipoleActivity_bound h439 hpS
  refine ⟨fun lam k => if k ≤ 1 then 0 else kdip₀ lam k, ?_, ?_, ?_, ?_⟩
  -- the limit clause (2.34)
  · intro lam hlam hlam1
    exact ⟨by simp, by simp, hlim' lam hlam hlam1⟩
  -- item (1), eq. (2.38)
  · exact item_one hχ hp₀ hβ h545 hlam₁1 hlam₁ hb
  -- item (2), eq. (2.39)
  · exact item_two h439 hlim'
  -- item (3), eq. (2.40)
  · exact item_three hχ hβ hlimr hC₀ hlam₁ hlam₁1 hb
      (fun lam hlam hlaml => exists_uniform_coefficient_bound hlam₁1 hb hlimr hlam hlaml)

end TheoremOne

end MultipoleBKT

end
