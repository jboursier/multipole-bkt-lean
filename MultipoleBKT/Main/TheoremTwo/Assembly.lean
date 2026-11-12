/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.ItemsFourSix
public import MultipoleBKT.Main.TheoremTwo.MeasurableBadPoints

/-!
# Theorem 2 from the gates: the assembly

`MultipoleBKT.TheoremTwo.theorem_2_of_gates` proves the statement of the frozen Theorem 2
(`MultipoleBKT.TheoremTwo.Theorem2Statement`, the type of the frozen statement `MultipoleBKT.theorem_2`)
from the frozen statements of Propositions 4.23, 4.62, 5.43 (`Prop423Statement`,
`Prop462Statement`, `Prop543Statement`) and the existence of the limiting activities
(`LimitingActivitiesExist`). No other hypothesis: the measurability of `c ↦ |I_bad(c)|` that the
use of Proposition 5.43 needs is proved (`MultipoleBKT.TheoremTwo.measurable_card_badPoints`).
The provider of Theorem 2 is
`theorem_2_of_gates proposition_4_23 proposition_4_62 proposition_5_43 _`.

The proof follows the paper: `M₀` is the largest
of the thresholds of the gates and of the limits, and at each `M ≥ M₀` the coefficient families
are those given by the limits; item (1) is `MultipoleBKT.TheoremTwo.msf_bound`,
`MultipoleBKT.TheoremTwo.kmult_bound`, items (2)–(6) are `item_two`, …, `item_six`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MultipoleBKT

namespace TheoremTwo

/-- Theorem 2 from the frozen gate statements, the existence of the limiting activities and the
measurability of the number of bad points. -/
theorem theorem_2_of_gates_of_measurable (h423 : Prop423Statement) (h462 : Prop462Statement)
    (h543 : Prop543Statement) (hlim : LimitingActivitiesExist)
    (hmeas : ∀ (p₀ : ℕ) (β M lam ε₀ : ℝ) (N : ℕ), Measurable fun c : Fin N → ℂ × ℂ =>
      (badPoints p₀ β lam M ε₀ (matched c)).card) :
    Theorem2Statement := by
  intro χ hχ p₀ hp₀ β hβ p
  have hp1 : 1 ≤ pBeta p₀ β := one_le_pBeta' hp₀ hβ
  have hpS : (pBeta p₀ β : ℕ∞) ≤ pStar β := pBeta_le_pStar hp₀ hβ
  obtain ⟨P1, P2, -⟩ := h423 χ hχ β hβ
  obtain ⟨Ma, -, Ha⟩ := h462 χ hχ p₀ hp₀ β hβ
  obtain ⟨Mb, -, Hb⟩ := h543 χ hχ p₀ hp₀ β hβ
  obtain ⟨Mc, Hc⟩ := hlim χ hχ β hβ
  -- the thresholds of (4.38)–(4.40) for the finitely many sizes `k ≤ p`
  have E1 : ∀ᶠ M in atTop, ∀ k ∈ Finset.Icc 2 (pBeta p₀ β), MsfGateAt χ β M k :=
    (Filter.eventually_all_finset _).mpr fun k hk => by
      obtain ⟨hk2, hkp⟩ := Finset.mem_Icc.mp hk
      obtain ⟨M₀, -, hM₀⟩ := P1 k hk2 (natCast_le_pStar_of_le_pBeta hp₀ hβ hkp)
      exact eventually_atTop.mpr ⟨M₀, hM₀⟩
  have E2 : ∀ᶠ M in atTop, ∀ k ∈ Finset.range (pBeta p₀ β + 1), KmultGateAt χ β M k :=
    (Filter.eventually_all_finset _).mpr fun k hk => by
      have hkp : k ≤ pBeta p₀ β := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      obtain ⟨M₀, -, hM₀⟩ := P2 k (natCast_le_pStar_of_le_pBeta hp₀ hβ hkp)
      exact eventually_atTop.mpr ⟨M₀, hM₀⟩
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (E1.and (E2.and ((eventually_ge_atTop Ma).and
    ((eventually_ge_atTop Mb).and ((eventually_ge_atTop Mc).and (eventually_ge_atTop 21))))))
  refine ⟨max M₀ 21, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun M hM => ?_⟩
  obtain ⟨hG1, hG2, hMa, hMb, hMc, hM21⟩ := hM₀ M ((le_max_left _ _).trans hM)
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨msf, kmult, hlims⟩ := Hc M hMc
  have hS : MsfLimits χ β M msf := fun lam h0 h1 => (hlims lam h0 h1).1
  have hX : KmultLimits χ β M kmult := fun lam h0 h1 => (hlims lam h0 h1).2
  have hG2' : ∀ k, k ≤ pBeta p₀ β → KmultGateAt χ β M k :=
    fun k hk => hG2 k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hlow : LowerGateAt χ p₀ β M msf kmult := Ha M hMa msf kmult hS hX
  have hup : UpperGateAt χ p₀ β M msf kmult := Hb M hMb msf kmult hS hX
  obtain ⟨C₁, C'', l₀, hset⟩ :=
    exists_setupAt hp1 (coefficient_bounds_uniform hχ hβ hpS hG1 hG2' hS hX)
  have hmeasM := fun N lam ε₀ => hmeas p₀ β M lam ε₀ N
  refine ⟨msf, kmult, hlims, fun k hk2 hkp => ?_, fun X hX' hV => ?_,
    item_two hχ hβ hM0 hset hlow hup hmeasM, item_three hχ hβ hM0 hset hlow hup hmeasM,
    item_four hχ hp₀ hβ hM0 hset hlow hup hmeasM, item_five hset,
    item_six hχ hβ hM0 hset hlow hup hmeasM⟩
  · exact msf_bound hk2 (natCast_le_pStar_of_le_pBeta hp₀ hβ hkp)
      (hG1 k (Finset.mem_Icc.mpr ⟨hk2, hkp⟩)) hS
  · exact kmult_bound hχ hpS hG1 hG2' hX hX' hV

/-- **Theorem 2**, conditional on the
frozen statements of the gates Propositions 4.23, 4.62, 5.43 and on the existence of the
limiting activities (Lemma 4.26). The conclusion is the type of the frozen statement
`MultipoleBKT.theorem_2`. -/
theorem theorem_2_of_gates (h423 : Prop423Statement) (h462 : Prop462Statement)
    (h543 : Prop543Statement) (hlim : LimitingActivitiesExist) : Theorem2Statement :=
  theorem_2_of_gates_of_measurable h423 h462 h543 hlim fun p₀ β M lam ε₀ N =>
    measurable_card_badPoints p₀ β M lam ε₀ N

end TheoremTwo

end MultipoleBKT

end
