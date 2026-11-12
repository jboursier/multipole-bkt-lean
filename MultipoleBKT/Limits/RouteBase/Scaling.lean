/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteBase.Integrand

/-!
# Scaling interfaces for the appendix integrals

See Lemma A.4 of the paper. These change-of-variable
identities are used for the appendix dipole terms. The bounded lower
activities themselves are integrated through grouped integrals.
-/

@[expose] public section

namespace MultipoleBKT

namespace BoundedLower

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box logKernel)
open Limits

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Pairs of dipoles -/

section Pair

theorem norm_smul_sub_smul {r : ℝ} (hr : 0 ≤ r) (z w : ℂ) : ‖r • z - r • w‖ = r * ‖z - w‖ := by
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hr]

theorem smearedKernel_smul_sub (hχ : IsMollifier χ) (hlam : 0 < lam) (z w : ℂ) :
    smearedKernel χ lam (lam • z - lam • w) =
      logKernel (lam : ℂ) + smearedKernel χ 1 (z - w) := by
  rw [← smul_sub, Complex.real_smul, smearedKernel_ofReal_mul hχ hlam]

theorem exp_mul_logKernel (hlam : 0 < lam) (β : ℝ) :
    Real.exp (β * logKernel (lam : ℂ)) = lam ^ (-β) := by
  rw [logKernel_ofReal hlam, Real.rpow_def_of_pos hlam]
  ring_nf

/-- The dipole weight: `e^{β g_λ(λ (x - y))} = λ^{-β} e^{β g_1(x - y)}`. -/
theorem pairDensity_smul (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (d : ℂ × ℂ) :
    pairDensity χ β lam (lam • d) = lam ^ (-β) * pairDensity χ β 1 d := by
  unfold pairDensity
  rw [Prod.smul_fst, Prod.smul_snd, smearedKernel_smul_sub hχ hlam, mul_add, Real.exp_add,
    exp_mul_logKernel hlam]

/-- The dipole–dipole interaction is scale invariant: `v_λ(λ d, λ e) = v_1(d, e)`. -/
theorem dipoleInteraction_smul (hχ : IsMollifier χ) (hlam : 0 < lam) (d e : ℂ × ℂ) :
    dipoleInteraction χ lam (lam • d) (lam • e) = dipoleInteraction χ 1 d e := by
  unfold dipoleInteraction
  simp only [Prod.smul_fst, Prod.smul_snd, smearedKernel_smul_sub hχ hlam]
  ring

/-- The matching event `𝒜_ij` is scale invariant. -/
theorem isStableDipolePair_smul {r : ℝ} (hr : 0 < r) (d e : ℂ × ℂ) :
    IsStableDipolePair (r • d) (r • e) ↔ IsStableDipolePair d e := by
  simp only [isStableDipolePair_iff, Prod.smul_fst, Prod.smul_snd, norm_smul_sub_smul hr.le,
    mul_le_mul_iff_of_pos_left hr, mul_lt_mul_iff_of_pos_left hr]

/-- The multipole relation at scale `λ` of the dilated dipoles is the relation at scale `1`. -/
theorem multipoleLinked_smul (hlam : 0 < lam) (M : ℝ) (d e : ℂ × ℂ) :
    MultipoleLinked M lam (lam • d) (lam • e) ↔ MultipoleLinked M 1 d e := by
  unfold MultipoleLinked
  simp only [Prod.smul_fst, Prod.smul_snd, norm_smul_sub_smul hlam.le]
  have hmax : ∀ a : ℝ, max (lam * a) lam = lam * max a 1 := fun a => by
    rw [mul_max_of_nonneg _ _ hlam.le, mul_one]
  have hmin : ∀ a b : ℝ, min (lam * a) (lam * b) = lam * min a b := fun a b =>
    (mul_min_of_nonneg _ _ hlam.le).symm
  rw [hmax, hmax, hmin, hmin, hmin, hmin, mul_left_comm M, mul_le_mul_iff_of_pos_left hlam]

theorem stablePairWeight_smul (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (d e : ℂ × ℂ) :
    stablePairWeight χ β lam (lam • d) (lam • e) = stablePairWeight χ β 1 d e := by
  unfold stablePairWeight
  rw [dipoleInteraction_smul hχ hlam]
  congr 1
  exact propext (isStableDipolePair_smul hlam d e)

end Pair

/-! ### Configurations -/

section Config

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

omit [Fintype ι] [LinearOrder ι] in
theorem flipCfg_smul (B : Finset ι) (r : ℝ) (c : ι → ℂ × ℂ) :
    flipCfg B (r • c) = r • flipCfg B c := by
  funext i
  simp only [flipCfg_apply, Pi.smul_apply]
  split_ifs
  · rfl
  · rfl

omit [DecidableEq ι] [LinearOrder ι] in
theorem prod_pairDensity_smul (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (c : ι → ℂ × ℂ) :
    ∏ i, pairDensity χ β lam ((lam • c) i) =
      (lam ^ (-β)) ^ Fintype.card ι * ∏ i, pairDensity χ β 1 (c i) := by
  simp only [Pi.smul_apply, pairDensity_smul hχ hlam, prod_mul_distrib, prod_const, card_univ]

end Config

/-! ### Dilations of rooted integrals -/

section Measure

variable {ι : Type*} [Fintype ι]

theorem isAddHaarMeasure_volume_config : (volume : Measure (ι → ℂ × ℂ)).IsAddHaarMeasure := by
  have : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
    (inferInstance : ((volume : Measure ℂ).prod volume).IsAddHaarMeasure)
  rw [volume_pi]
  exact Measure.pi.isAddHaarMeasure _

theorem finrank_config : Module.finrank ℝ (ι → ℂ × ℂ) = 4 * Fintype.card ι := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_prod, Complex.finrank_real_complex]
  ring

/-- The change of variables `c = r c'` on `(ℂ²)^ι`: `∫ G = r^{4|ι|} ∫ G(r c') dc'`. -/
theorem lintegral_eq_lintegral_comp_smul {r : ℝ} (hr : 0 < r) {G : (ι → ℂ × ℂ) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ c, G c = ENNReal.ofReal (r ^ (4 * Fintype.card ι)) * ∫⁻ c, G (r • c) := by
  have := isAddHaarMeasure_volume_config (ι := ι)
  rw [← lintegral_map hG (measurable_const_smul r), Measure.map_addHaar_smul volume hr.ne',
    lintegral_smul_measure, finrank_config, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- **Rooted integrals.** For `F ≥ 0` measurable and translation invariant and `A ⊆ ℂ`
measurable, `∫ 𝟙_A(x_{i₀}) F(c) dc = |A| ∫ 𝟙_{[0,1]²}(x_{i₀}) F(c) dc`. -/
theorem lintegral_indicator_mul_eq (i₀ : ι) {A : Set ℂ} (hA : MeasurableSet A)
    {F : (ι → ℂ × ℂ) → ℝ≥0∞} (hF : Measurable F) (hinv : TranslationInvariant F) :
    ∫⁻ c, A.indicator 1 (c i₀).1 * F c = volume A * ∫⁻ c, anchor i₀ c * F c := by
  have hx : Measurable fun c : ι → ℂ × ℂ => (c i₀).1 :=
    measurable_fst.comp (measurable_pi_apply i₀)
  have hg : Measurable fun x : ℂ => (box 1).indicator (1 : ℂ → ℝ≥0∞) x :=
    measurable_const.indicator (TwoComponentCoulomb.measurableSet_box 1)
  have hgA : Measurable fun x : ℂ => A.indicator (1 : ℂ → ℝ≥0∞) x :=
    measurable_const.indicator hA
  -- insert `1 = ∫ 𝟙_{[0,1]²}(x_{i₀} - a) da`
  have h1 : ∫⁻ c, A.indicator 1 (c i₀).1 * F c =
      ∫⁻ c, ∫⁻ a : ℂ, (box 1).indicator 1 ((c i₀).1 - a) * (A.indicator 1 (c i₀).1 * F c) := by
    refine lintegral_congr fun c => ?_
    have hm : Measurable fun a : ℂ => (box 1).indicator (1 : ℂ → ℝ≥0∞) ((c i₀).1 - a) :=
      hg.comp (measurable_const.sub measurable_id)
    rw [lintegral_mul_const _ hm, lintegral_indicator_box_one_sub, one_mul]
  have hmeas : Measurable (Function.uncurry fun (c : ι → ℂ × ℂ) (a : ℂ) =>
      (box 1).indicator (1 : ℂ → ℝ≥0∞) ((c i₀).1 - a) * (A.indicator 1 (c i₀).1 * F c)) :=
    (hg.comp ((hx.comp measurable_fst).sub measurable_snd)).mul
      ((hgA.comp (hx.comp measurable_fst)).mul (hF.comp measurable_fst))
  rw [h1, lintegral_lintegral_swap hmeas.aemeasurable]
  -- translate the configuration by `a`
  have h2 : ∀ a : ℂ, ∫⁻ c, (box 1).indicator 1 ((c i₀).1 - a) * (A.indicator 1 (c i₀).1 * F c) =
      ∫⁻ c, anchor i₀ c * F c * A.indicator 1 ((c i₀).1 + a) := by
    intro a
    have key := (measurePreserving_translate (ι := ι) a).lintegral_comp
      (f := fun c => (box 1).indicator (1 : ℂ → ℝ≥0∞) ((c i₀).1 - a) *
        (A.indicator 1 (c i₀).1 * F c))
      ((hg.comp (hx.sub measurable_const)).mul ((hgA.comp hx).mul hF))
    rw [← key]
    refine lintegral_congr fun c => ?_
    have e1 : (translate a c i₀).1 = (c i₀).1 + a := by simp [translate]
    simp only [e1, add_sub_cancel_right, hinv a c, anchor]
    ring
  simp_rw [h2]
  have hmeas2 : Measurable (Function.uncurry fun (a : ℂ) (c : ι → ℂ × ℂ) =>
      anchor i₀ c * F c * A.indicator (1 : ℂ → ℝ≥0∞) ((c i₀).1 + a)) :=
    (((measurable_anchor i₀).comp measurable_snd).mul (hF.comp measurable_snd)).mul
      (hgA.comp ((hx.comp measurable_snd).add measurable_fst))
  rw [lintegral_lintegral_swap hmeas2.aemeasurable]
  have h3 : ∀ c : ι → ℂ × ℂ, ∫⁻ a : ℂ, anchor i₀ c * F c * A.indicator 1 ((c i₀).1 + a) =
      anchor i₀ c * F c * volume A := by
    intro c
    have hm : Measurable fun a : ℂ => A.indicator (1 : ℂ → ℝ≥0∞) ((c i₀).1 + a) :=
      hgA.comp (measurable_const.add measurable_id)
    rw [lintegral_const_mul _ hm,
      lintegral_add_left_eq_self (fun a => A.indicator (1 : ℂ → ℝ≥0∞) a) (c i₀).1,
      lintegral_indicator_one hA]
  simp_rw [h3]
  have hm : Measurable fun c : ι → ℂ × ℂ => anchor i₀ c * F c := (measurable_anchor i₀).mul hF
  rw [lintegral_mul_const _ hm, mul_comm]

omit [Fintype ι] in
theorem translationInvariant_comp_smul {F : (ι → ℂ × ℂ) → ℝ≥0∞} (hinv : TranslationInvariant F)
    (r : ℝ) : TranslationInvariant fun c => F (r • c) := fun a c => by
  have : r • translate a c = translate (r • a) (r • c) := by
    funext i
    simp [translate, smul_add]
  show F (r • translate a c) = F (r • c)
  rw [this]
  exact hinv _ _

/-- **Dilation of a rooted integral.** For `F ≥ 0` measurable and translation invariant and
`λ > 0`, `∫ 𝟙_{[0,1]²}(x_{i₀}) F(λ⁻¹ c) dc = λ^{4|ι|-2} ∫ 𝟙_{[0,1]²}(x_{i₀}) F(c) dc`. -/
theorem lintegral_anchor_comp_inv_smul (i₀ : ι) {F : (ι → ℂ × ℂ) → ℝ≥0∞} (hF : Measurable F)
    (hinv : TranslationInvariant F) (hlam : 0 < lam) :
    ∫⁻ c, anchor i₀ c * F (lam⁻¹ • c) =
      ENNReal.ofReal (lam ^ (4 * Fintype.card ι) * (lam ^ 2)⁻¹) * ∫⁻ c, anchor i₀ c * F c := by
  have hm : Measurable fun c : ι → ℂ × ℂ => anchor i₀ c * F (lam⁻¹ • c) :=
    (measurable_anchor i₀).mul (hF.comp (measurable_const_smul _))
  rw [lintegral_eq_lintegral_comp_smul hlam hm]
  simp only [smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  have hset : MeasurableSet ((fun x : ℂ => lam • x) ⁻¹' box 1) :=
    (measurable_const_smul lam) (TwoComponentCoulomb.measurableSet_box 1)
  have hanchor : ∀ c : ι → ℂ × ℂ,
      anchor i₀ (lam • c) = ((fun x : ℂ => lam • x) ⁻¹' box 1).indicator 1 (c i₀).1 := by
    intro c
    unfold anchor
    simp only [Pi.smul_apply, Prod.smul_fst]
    by_cases h : lam • (c i₀).1 ∈ box 1
    · rw [indicator_of_mem h, indicator_of_mem (show (c i₀).1 ∈ (fun x : ℂ => lam • x) ⁻¹' box 1
        from h)]
      rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (show (c i₀).1 ∉
        (fun x : ℂ => lam • x) ⁻¹' box 1 from h)]
  simp_rw [hanchor]
  rw [lintegral_indicator_mul_eq i₀ hset hF hinv,
    Measure.addHaar_preimage_smul volume hlam.ne', Complex.finrank_real_complex,
    TwoComponentCoulomb.volume_box, Nat.cast_one, mul_one, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity)]

/-- **The box integral of a dilated integrand.** For `F ≥ 0` measurable and translation
invariant, `λ > 0` and `N ∈ ℕ`,
`∫_{(Λ²)^ι} F(λ⁻¹ c) dc ≤ N λ^{4|ι|-2} ∫ 𝟙_{[0,1]²}(x_{i₀}) F(c) dc`. -/
theorem lintegral_boxConfig_comp_inv_smul_le [Nonempty ι] (i₀ : ι) {F : (ι → ℂ × ℂ) → ℝ≥0∞}
    (hF : Measurable F) (hinv : TranslationInvariant F) (hlam : 0 < lam) (N : ℕ) :
    ∫⁻ c in boxConfig ι N, F (lam⁻¹ • c) ≤
      N * ENNReal.ofReal (lam ^ (4 * Fintype.card ι) * (lam ^ 2)⁻¹) *
        ∫⁻ c, anchor i₀ c * F c := by
  have hF' : Measurable fun c : ι → ℂ × ℂ => F (lam⁻¹ • c) := hF.comp (measurable_const_smul _)
  rw [lintegral_boxConfig_eq N i₀ hF' (translationInvariant_comp_smul hinv _)]
  calc ∫⁻ c, anchor i₀ c * F (lam⁻¹ • c) * overlap N c
      ≤ ∫⁻ c, anchor i₀ c * F (lam⁻¹ • c) * N :=
        lintegral_mono fun c => by gcongr; exact overlap_le N c
    _ = (∫⁻ c, anchor i₀ c * F (lam⁻¹ • c)) * N :=
        lintegral_mul_const _ ((measurable_anchor i₀).mul hF')
    _ = _ := by
        rw [lintegral_anchor_comp_inv_smul i₀ hF hinv hlam]
        ring

end Measure

/-! ### The bound on the box integrals of `𝖪^mult` -/

section Bound

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

theorem rpow_neg_pow_mul_eq (hlam : 0 < lam) (β : ℝ) (k : ℕ) :
    (lam ^ (-β)) ^ k * (lam ^ (4 * k) * (lam ^ 2)⁻¹) = lam ^ ((4 - β) * k - 2) := by
  rw [← Real.rpow_natCast (lam ^ (-β)), ← Real.rpow_mul hlam.le, ← Real.rpow_natCast lam (4 * k),
    ← Real.rpow_two, ← Real.rpow_neg hlam.le, ← Real.rpow_add hlam, ← Real.rpow_add hlam]
  congr 1
  push_cast
  ring

omit [DecidableEq ι] [LinearOrder ι] in
/-- **The box integral of a dilated integrand.** Let `G₁` be measurable and translation invariant,
with `𝟙_{[0,1]²}(x_{i₀}) G₁` integrable, and let `G_λ(λ c) = λ^{-β|ι|} G₁(c)`. Then
`∫_{(Λ²)^ι} |G_λ| ≤ N λ^{(4-β)|ι|-2} ∫ |𝟙_{[0,1]²}(x_{i₀}) G₁|` for every `N`. -/
theorem integral_boxConfig_abs_le_of_smul [Nonempty ι] (i₀ : ι) (hlam : 0 < lam) (β : ℝ)
    {G₁ Gl : (ι → ℂ × ℂ) → ℝ} (hG₁ : Measurable G₁) (hinv : TranslationInvariant G₁)
    (hint : Integrable fun c => anchorR i₀ c * G₁ c)
    (hscale : ∀ c, Gl (lam • c) = (lam ^ (-β)) ^ Fintype.card ι * G₁ c) (N : ℕ) :
    ∫ c in boxConfig ι N, |Gl c| ≤
      N * lam ^ ((4 - β) * Fintype.card ι - 2) * ∫ c, |anchorR i₀ c * G₁ c| := by
  set k := Fintype.card ι
  set K : ℝ := (lam ^ (-β)) ^ k
  have hK : 0 < K := by positivity
  have hpt : ∀ c, |Gl c| = K * |G₁ (lam⁻¹ • c)| := by
    intro c
    have := hscale (lam⁻¹ • c)
    rw [smul_inv_smul₀ hlam.ne'] at this
    rw [this, abs_mul, abs_of_pos hK]
  simp_rw [hpt]
  rw [integral_const_mul]
  set G : (ι → ℂ × ℂ) → ℝ≥0∞ := fun c => ‖G₁ c‖ₑ
  have hG : Measurable G := hG₁.enorm
  have hGinv : TranslationInvariant G := fun a c => by simp only [G, hinv a c]
  have hfin : ∫⁻ c, anchor i₀ c * G c < ⊤ := by
    have := hint.2
    unfold HasFiniteIntegral at this
    simpa only [enorm_anchorR_mul] using this
  have hR : ∫ c, |anchorR i₀ c * G₁ c| = (∫⁻ c, anchor i₀ c * G c).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun c => abs_nonneg _)
      hint.abs.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun c => ?_
    rw [← Real.enorm_eq_ofReal_abs, enorm_anchorR_mul]
  have hL : ∫ c in boxConfig ι N, |G₁ (lam⁻¹ • c)| =
      (∫⁻ c in boxConfig ι N, G (lam⁻¹ • c)).toReal := by
    have hm : Measurable fun c : ι → ℂ × ℂ => G₁ (lam⁻¹ • c) :=
      hG₁.comp (measurable_const_smul _)
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun c => abs_nonneg _)
      (continuous_abs.measurable.comp hm).aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun c => ?_
    rw [← Real.enorm_eq_ofReal_abs]
  have hle := lintegral_boxConfig_comp_inv_smul_le i₀ hG hGinv hlam N
  have hfin' : (N : ℝ≥0∞) * ENNReal.ofReal (lam ^ (4 * k) * (lam ^ 2)⁻¹) *
      ∫⁻ c, anchor i₀ c * G c ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.ofReal_ne_top)
      hfin.ne
  have hL' : ∫ c in boxConfig ι N, |G₁ (lam⁻¹ • c)| ≤
      N * (lam ^ (4 * k) * (lam ^ 2)⁻¹) * ∫ c, |anchorR i₀ c * G₁ c| := by
    rw [hL, hR]
    refine (ENNReal.toReal_mono hfin' hle).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity)]
  calc K * ∫ c in boxConfig ι N, |G₁ (lam⁻¹ • c)|
      ≤ K * (N * (lam ^ (4 * k) * (lam ^ 2)⁻¹) * ∫ c, |anchorR i₀ c * G₁ c|) :=
        mul_le_mul_of_nonneg_left hL' hK.le
    _ = N * (K * (lam ^ (4 * k) * (lam ^ 2)⁻¹)) * ∫ c, |anchorR i₀ c * G₁ c| := by ring
    _ = _ := by rw [rpow_neg_pow_mul_eq hlam]
end Bound

end BoundedLower

end MultipoleBKT

end
