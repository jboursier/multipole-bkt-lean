/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.LowerBound
public import MultipoleBKT.Limits.MultipoleLimit

/-!
# Chain positivity for the integral with one fixed dipole

See Lemma 4.26. The quantitative chain lower bound in a sufficiently large box
implies positivity of the integral with one fixed dipole.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral.RouteChain

open MeasureTheory Set Finset Limits
open scoped ENNReal

/-- Positivity of the actual `G_S` integral with one fixed dipole from the scale-`λ` chain. -/
theorem anchored_integral_pos_of_chain {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam M : ℝ}
    (hβ : 2 < β) (hlam : 0 < lam) (hM : 9 ≤ M) {S : Finset ℕ}
    (hkp : (S.card : ℕ∞) ≤ pStar β) (root : S) :
    0 < ∫ c, anchorR root c * multipoleBox χ β lam M c := by
  let : Nonempty S := ⟨root⟩
  have hk : 1 ≤ S.card := Finset.card_pos.mpr ⟨root, root.2⟩
  obtain ⟨C, hC, hlow⟩ := le_multipoleIntegral hχ hβ hk hM
  obtain ⟨N₀, hN₀⟩ := hlow lam hlam
  let N := max N₀ 1
  have hN : 0 < (N : ℝ) := by
    have : 1 ≤ N := le_max_right _ _
    exact_mod_cast this
  have hpos : 0 < multipoleIntegral χ N β lam M S :=
    lt_of_lt_of_le (by positivity) (hN₀ N (le_max_left _ _) S rfl)
  have heq : multipoleIntegral χ N β lam M S =
      ∫ c in boxConfig S N, multipoleBox χ β lam M c := by
    unfold multipoleIntegral boxConfig
    congr 1
  rw [heq] at hpos
  have hk' : (Fintype.card S : ℕ∞) ≤ pStar β := by simpa only [Fintype.card_coe] using hkp
  have hint := integrable_anchor_multipoleBox hχ hβ hlam (by linarith : 0 ≤ M) hk' root
  obtain ⟨_, hJ⟩ := integral_boxConfig_eq N root (measurable_multipoleBox hχ hlam β M)
    translationInvariant_multipoleBox hint
  have hle : ∫ c in boxConfig S N, multipoleBox χ β lam M c ≤
      (N : ℝ) * ∫ c, anchorR root c * multipoleBox χ β lam M c := by
    rw [hJ, ← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun c => mul_nonneg
        (mul_nonneg (anchorR_nonneg root c) (multipoleBox_nonneg χ β lam M c)) ENNReal.toReal_nonneg
    · exact hint.const_mul _
    · apply Filter.Eventually.of_forall
      intro c
      have ho : (overlap N c).toReal ≤ N :=
        ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg N) (by simpa using overlap_le N c)
      have hn := mul_nonneg (anchorR_nonneg root c) (multipoleBox_nonneg χ β lam M c)
      calc _ ≤ (anchorR root c * multipoleBox χ β lam M c) * N := mul_le_mul_of_nonneg_left ho hn
        _ = _ := by ring
  by_contra hh
  have hz := mul_nonpos_of_nonneg_of_nonpos hN.le (le_of_not_gt hh)
  linarith

end MultipoleBKT.MultipoleIntegral.RouteChain

end
