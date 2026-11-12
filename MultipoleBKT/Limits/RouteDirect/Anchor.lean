/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.Average

/-!
# Reversal of a translation-invariant integral with a chosen root

See Lemma 4.26 of the paper. Changing which endpoint is chosen as root leaves the integral
on the translation quotient unchanged. This justifies taking the original
reversal average after the merged-part average, including at the root.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Any measurable choice of origin that translates with the configuration
has the same unit-area rooted integral. -/
theorem lintegral_reanchor (root : ι) {p : (ι → ℂ × ℂ) → ℂ} (hp : Measurable p)
    (hpt : ∀ a c, p (translate a c) = p c + a)
    {F : (ι → ℂ × ℂ) → ℝ≥0∞} (hF : Measurable F) (hinv : TranslationInvariant F) :
    ∫⁻ c, (box 1).indicator 1 (p c) * F c = ∫⁻ c, anchor root c * F c := by
  let g : ℂ → ℝ≥0∞ := (box 1).indicator 1
  have hg : Measurable g := measurable_one.indicator (TwoComponentCoulomb.measurableSet_box 1)
  have hx : Measurable fun c : ι → ℂ × ℂ => (c root).1 :=
    measurable_fst.comp (measurable_pi_apply root)
  have h1 : ∫⁻ c, g (p c) * F c =
      ∫⁻ c, ∫⁻ a : ℂ, g ((c root).1 - a) * (g (p c) * F c) := by
    apply lintegral_congr
    intro c
    have hmc : Measurable (fun a : ℂ => g ((c root).1 - a)) :=
      hg.comp (measurable_const.sub measurable_id)
    rw [lintegral_mul_const _ hmc,
      lintegral_indicator_box_one_sub, one_mul]
  have hm : Measurable (Function.uncurry fun (c : ι → ℂ × ℂ) (a : ℂ) =>
      g ((c root).1 - a) * (g (p c) * F c)) :=
    (hg.comp ((hx.comp measurable_fst).sub measurable_snd)).mul
      ((hg.comp (hp.comp measurable_fst)).mul (hF.comp measurable_fst))
  change ∫⁻ c, g (p c) * F c = _
  rw [h1, lintegral_lintegral_swap hm.aemeasurable]
  have h2 (a : ℂ) : ∫⁻ c, g ((c root).1 - a) * (g (p c) * F c) =
      ∫⁻ c, anchor root c * F c * g (p c + a) := by
    have hmc : Measurable (fun c : ι → ℂ × ℂ =>
        g ((c root).1 - a) * (g (p c) * F c)) :=
      (hg.comp (hx.sub_const a)).mul ((hg.comp hp).mul hF)
    rw [← (measurePreserving_translate (ι := ι) a).lintegral_comp hmc]
    apply lintegral_congr
    intro c
    simp only [translate, Prod.fst_add, add_sub_cancel_right, hinv a c, hpt a c]
    unfold anchor
    change g (c root).1 * (g (p c + a) * F c) = g (c root).1 * F c * g (p c + a)
    ring
  simp_rw [h2]
  have hm2 : Measurable (Function.uncurry fun (a : ℂ) (c : ι → ℂ × ℂ) =>
      anchor root c * F c * g (p c + a)) :=
    (((measurable_anchor root).comp measurable_snd).mul (hF.comp measurable_snd)).mul
      (hg.comp ((hp.comp measurable_snd).add measurable_fst))
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  apply lintegral_congr
  intro c
  have hmc : Measurable (fun a : ℂ => g (p c + a)) :=
    hg.comp (measurable_const.add measurable_id)
  rw [lintegral_const_mul _ hmc,
    lintegral_add_left_eq_self g (p c)]
  have hgint : ∫⁻ a, g a = 1 := by
    rw [lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box 1),
      TwoComponentCoulomb.volume_box]
    simp
  rw [hgint, mul_one]

/-- Endpoint reversal preserves the rooted nonnegative integral. -/
theorem lintegral_anchor_flip (root : ι) (A : Finset ι)
    {F : (ι → ℂ × ℂ) → ℝ≥0∞} (hF : Measurable F) (hinv : TranslationInvariant F) :
    ∫⁻ c, anchor root c * F (flipCfg A c) = ∫⁻ c, anchor root c * F c := by
  have hp : Measurable fun c : ι → ℂ × ℂ => (flipCfg A c root).1 :=
    measurable_fst.comp ((measurable_pi_apply root).comp (measurable_flipCfg A))
  have ht (a : ℂ) (c : ι → ℂ × ℂ) :
      (flipCfg A (translate a c) root).1 = (flipCfg A c root).1 + a := by
    simp only [flipCfg, translate]
    split_ifs <;> rfl
  have hm : Measurable (fun c : ι → ℂ × ℂ => anchor root c * F (flipCfg A c)) :=
    (measurable_anchor root).mul (hF.comp (measurable_flipCfg A))
  have heq := (measurePreserving_flipCfg (ι := ι) A).lintegral_comp hm
  simp only [flipCfg_flipCfg] at heq
  exact heq.symm.trans (lintegral_reanchor root hp ht hF hinv)

/-- The full original reversal average remains integrable on the translation
quotient whenever its merged-part summands do. -/
theorem integrable_anchor_flip (root : ι) (A : Finset ι)
    {F : (ι → ℂ × ℂ) → ℝ} (hF : Measurable F) (hinv : TranslationInvariant F)
    (hint : Integrable fun c => anchorR root c * F c) :
    Integrable fun c => anchorR root c * F (flipCfg A c) := by
  refine ⟨((measurable_anchorR root).mul (hF.comp (measurable_flipCfg A))).aestronglyMeasurable, ?_⟩
  have hf := hint.2
  unfold HasFiniteIntegral at hf ⊢
  simp_rw [enorm_anchorR_mul] at hf
  change (∫⁻ c, ‖anchorR root c * F (flipCfg A c)‖ₑ) < ∞
  simp_rw [show ∀ c, ‖anchorR root c * F (flipCfg A c)‖ₑ =
    anchor root c * ‖F (flipCfg A c)‖ₑ from
    fun c => enorm_anchorR_mul root (fun c => F (flipCfg A c)) c]
  rw [lintegral_anchor_flip root A hF.enorm (fun a c => by rw [hinv a c])]
  exact hf

/-- Finite averaging is legitimate after fixing the translation coordinate. -/
theorem integrable_anchor_reversalAverage {B : Type*} [Fintype B] [DecidableEq B]
    (blk : ι → B) (root : ι) {F : (ι → ℂ × ℂ) → ℝ}
    (hF : Measurable F) (hinv : TranslationInvariant F)
    (hint : Integrable fun c => anchorR root c * F c) :
    Integrable fun c => anchorR root c * reversalAverage blk F c := by
  have h : Integrable fun c =>
      (∑ A : Finset B, anchorR root c * F (flipCfg (blockLabels blk A) c)) /
        2 ^ Fintype.card B :=
    (integrable_finsetSum _ fun A _ => integrable_anchor_flip root _ hF hinv hint).div_const _
  convert h using 1
  ext c
  rw [reversalAverage, ← mul_div_assoc, Finset.mul_sum]

/-- Averaging reversals cannot increase the absolute integral on the
translation quotient, including when a reversal changes the chosen endpoint. -/
theorem lintegral_anchor_abs_reversalAverage_le {B : Type*} [Fintype B] [DecidableEq B]
    (blk : ι → B) (root : ι) {F : (ι → ℂ × ℂ) → ℝ}
    (hF : Measurable F) (hinv : TranslationInvariant F) :
    (∫⁻ c, anchor root c * ENNReal.ofReal |reversalAverage blk F c|) ≤
      ∫⁻ c, anchor root c * ENNReal.ofReal |F c| := by
  classical
  let D : ℝ := 2 ^ Fintype.card B
  have hD : 0 < D := by dsimp only [D]; positivity
  have hp (c : ι → ℂ × ℂ) : ENNReal.ofReal |reversalAverage blk F c| ≤
      (ENNReal.ofReal D)⁻¹ * ∑ A : Finset B, ENNReal.ofReal |F (flipCfg (blockLabels blk A) c)| := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun A _ => abs_nonneg _),
      ← ENNReal.ofReal_inv_of_pos hD, ← ENNReal.ofReal_mul (inv_nonneg.mpr hD.le)]
    apply ENNReal.ofReal_le_ofReal
    unfold reversalAverage
    rw [abs_div, abs_of_pos hD, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hD.le)
  have hmF : Measurable (fun c => ENNReal.ofReal |F c|) := by
    simpa only [Real.norm_eq_abs] using hF.norm.ennreal_ofReal
  have hm (A : Finset B) : Measurable fun c =>
      anchor root c * ENNReal.ofReal |F (flipCfg (blockLabels blk A) c)| :=
    (measurable_anchor root).mul (hmF.comp (measurable_flipCfg _))
  calc
    _ ≤ ∫⁻ c, (ENNReal.ofReal D)⁻¹ * ∑ A : Finset B,
        anchor root c * ENNReal.ofReal |F (flipCfg (blockLabels blk A) c)| := by
      apply lintegral_mono
      intro c
      exact (mul_le_mul_right (hp c) (anchor root c)).trans_eq (by rw [mul_left_comm, Finset.mul_sum])
    _ = (ENNReal.ofReal D)⁻¹ * ∑ A : Finset B,
        ∫⁻ c, anchor root c * ENNReal.ofReal |F (flipCfg (blockLabels blk A) c)| := by
      rw [lintegral_const_mul' _ _ (by simp [hD]), lintegral_finsetSum _ (fun A _ => hm A)]
    _ = (ENNReal.ofReal D)⁻¹ * ∑ _A : Finset B,
        ∫⁻ c, anchor root c * ENNReal.ofReal |F c| := by
      congr 1
      exact sum_congr rfl fun A _ => lintegral_anchor_flip root _ hmF
        (fun a c => by change ENNReal.ofReal |F (translate a c)| = _; rw [hinv a c])
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_finset,
        ← ENNReal.ofReal_natCast]
      have heq : ENNReal.ofReal ((2 ^ Fintype.card B : ℕ) : ℝ) = ENNReal.ofReal D := by
        simp only [Nat.cast_pow, Nat.cast_ofNat, D]
      rw [heq, ← mul_assoc, ENNReal.inv_mul_cancel (by simpa using hD) ENNReal.ofReal_ne_top, one_mul]

omit [DecidableEq ι] in
/-- Triangle inequality for a finite near/far expansion on the translation quotient. -/
theorem lintegral_anchor_abs_sum_le {J : Type*} (s : Finset J) (root : ι)
    (F : J → (ι → ℂ × ℂ) → ℝ) (hF : ∀ j ∈ s, Measurable (F j)) :
    (∫⁻ c, anchor root c * ENNReal.ofReal |∑ j ∈ s, F j c|) ≤
      ∑ j ∈ s, ∫⁻ c, anchor root c * ENNReal.ofReal |F j c| := by
  have hm (j : J) (hj : j ∈ s) : Measurable fun c =>
      anchor root c * ENNReal.ofReal |F j c| := by
    have ha : Measurable (fun c => ENNReal.ofReal |F j c|) := by
      simpa only [Real.norm_eq_abs] using (hF j hj).norm.ennreal_ofReal
    exact (measurable_anchor root).mul ha
  calc
    _ ≤ ∫⁻ c, ∑ j ∈ s, anchor root c * ENNReal.ofReal |F j c| := by
      apply lintegral_mono
      intro c
      change anchor root c * ENNReal.ofReal |∑ j ∈ s, F j c| ≤
        ∑ j ∈ s, anchor root c * ENNReal.ofReal |F j c|
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => abs_nonneg _)]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (abs_sum_le_sum_abs _ _)) _
    _ = _ := lintegral_finsetSum _ hm

end MultipoleBKT.Limits.RouteDirect

end
