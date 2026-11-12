/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.LemmaA8Minus
public import MultipoleBKT.Appendix.GeneralExpansionK.LemmaA8Bis
public import MultipoleBKT.LowerBound.LowerBoundLDP.Inputs

/-!
# Lemma A.7 in the form used by Proposition 4.62

See Lemma A.7, both
estimates (A.49) for the model `(ṽ, τ̃)` and (A.50), as consumed by
Proposition 4.62 through `MultipoleBKT.LowerBoundLDP.LemmaA8Inputs` (with `M₁ = 1`, every `L`,
every `2 ≤ k ≤ p(β)`):

* `le_pStar_of_le_pBeta`: `k ≤ p(β)` gives `k ≤ p*(β)`;
* `lemmaA8Inputs_holds`.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open Appendix

/-- A cluster size `1 ≤ k ≤ p(β)` is at most `p*(β)`. -/
theorem le_pStar_of_le_pBeta {p₀ : ℕ} {β : ℝ} {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ pBeta p₀ β) :
    (k : ℕ∞) ≤ pStar β := by
  unfold pBeta at hk
  split_ifs at hk with h4
  · by_cases htop : pStar β = ⊤
    · rw [htop]; exact le_top
    · rw [← ENat.natCast_toNat htop]
      exact_mod_cast hk
  · push Not at h4
    refine (le_pStar_iff hk1).2 ((transitionBeta_lt_iff hk1 β).2 ?_)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith

/-- **Lemma A.7** in the form `MultipoleBKT.LowerBoundLDP.LemmaA8Inputs` used by
Proposition 4.62 (here with `M₁ = 1` and any damping constant `L`). -/
theorem lemmaA8Inputs_holds {χ : ℂ → ℝ} {p₀ : ℕ} {β : ℝ} (hχ : IsMollifier χ) (_hp₀ : 1 ≤ p₀)
    (hβ : 2 < β) : LowerBoundLDP.LemmaA8Inputs χ p₀ β (β / 64) :=
  ⟨1, fun _M hM k hk2 hkp =>
    ⟨lemmaA8Minus_holds hχ hβ hM (β / 64) p₀ (le_pStar_of_le_pBeta (by omega) hkp),
      lemmaA8Bis_holds hχ hβ hM p₀ (le_pStar_of_le_pBeta (by omega) hkp)⟩⟩

end ExpansionK

end MultipoleBKT

end
