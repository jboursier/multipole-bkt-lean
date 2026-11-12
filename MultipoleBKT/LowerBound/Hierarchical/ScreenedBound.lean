/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.UpperBound
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Measurability and boundedness of the screened interaction `ṽ`

eq. (3.18) and Definition 3.11. The lower-bound model of Section 4 (Definition 4.13, eq. (4.18))
integrates `e^{-β ṽ_ij}` against the truncated dipole measure, which charges only dipoles of
length at most `ε₀ R̄ = τ₀ / 8`. The paper uses without comment that these integrals make sense;
we record the two facts needed:

* `measurable_screenedInteraction`: `(d, e) ↦ ṽ(d, e)` is measurable (for `λ > 0`): it is a
  parametric integral of a jointly measurable integrand;
* `exists_abs_screenedInteraction_le`: for `λ > 0` and `8λ ≤ τ`, `ṽ` is bounded on the pairs of
  dipoles of length at most `τ/8`: on the screening disc the screened field is bounded by
  `2 √(π M)/λ + 1/(4τ)` (`M` a bound of `χ`), by the bounded gradient of `g * δ₀^{(λ)}` and (3.20).
-/

@[expose] public section

open MeasureTheory Metric Set ComplexConjugate

namespace MultipoleBKT

namespace Hierarchical

variable {χ : ℂ → ℝ} {lam τ : ℝ}

/-- The image field `(a - z) / (τ² - conj(w - z)(a - z))` is jointly measurable. -/
theorem measurable_screenedImageField_uncurry (τ : ℝ) :
    Measurable fun q : ℂ × ℂ × ℂ => screenedImageField q.1 τ q.2.1 q.2.2 := by
  unfold screenedImageField
  refine (measurable_snd.fst.sub measurable_fst).div ?_
  refine measurable_const.sub (Measurable.mul ?_ (measurable_snd.fst.sub measurable_fst))
  exact Complex.continuous_conj.measurable.comp (measurable_snd.snd.sub measurable_fst)

/-- The screened field `∇u_d(w)` is jointly measurable in `(d, w)`. -/
theorem measurable_screenedField_comp (hχ : IsMollifier χ) (hlam : 0 < lam) (τ : ℝ)
    {α : Type*} [MeasurableSpace α] {g : α → ℂ × ℂ} {h : α → ℂ} (hg : Measurable g)
    (hh : Measurable h) : Measurable fun a => screenedField χ lam τ (g a) (h a) := by
  have hs := (continuous_smearedField hχ hlam).measurable
  have hI := measurable_screenedImageField_uncurry τ
  have hz : Measurable fun a => dipoleMidpoint (g a) := by
    unfold dipoleMidpoint
    exact (hg.fst.add hg.snd).div_const _
  have e1 : Measurable fun a => smearedField χ lam (h a - (g a).1) := hs.comp (hh.sub hg.fst)
  have e2 : Measurable fun a => smearedField χ lam (h a - (g a).2) := hs.comp (hh.sub hg.snd)
  have e3 : Measurable fun a => screenedImageField (dipoleMidpoint (g a)) τ (g a).1 (h a) :=
    hI.comp (hz.prodMk (hg.fst.prodMk hh))
  have e4 : Measurable fun a => screenedImageField (dipoleMidpoint (g a)) τ (g a).2 (h a) :=
    hI.comp (hz.prodMk (hg.snd.prodMk hh))
  exact (e1.sub e2).add (e3.sub e4)

/-- **`ṽ` is measurable**: `(d, e) ↦ ṽ(d, e)` is a measurable function of the two dipoles. -/
theorem measurable_screenedInteraction (hχ : IsMollifier χ) (hlam : 0 < lam) (τ : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => screenedInteraction χ lam τ q.1 q.2 := by
  have hF1 : Measurable fun x : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => screenedField χ lam τ x.1.1 x.2 :=
    measurable_screenedField_comp hχ hlam τ measurable_fst.fst measurable_snd
  have hF2 : Measurable fun x : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => screenedField χ lam τ x.1.2 x.2 :=
    measurable_screenedField_comp hχ hlam τ measurable_fst.snd measurable_snd
  have hinner : Measurable fun x : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ =>
      inner ℝ (screenedField χ lam τ x.1.1 x.2) (screenedField χ lam τ x.1.2 x.2) :=
    Measurable.inner hF1 hF2
  have hm1 : Measurable fun x : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => dist x.2 (dipoleMidpoint x.1.1) := by
    unfold dipoleMidpoint
    fun_prop
  have hm2 : Measurable fun x : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => dist x.2 (dipoleMidpoint x.1.2) := by
    unfold dipoleMidpoint
    fun_prop
  have hset : MeasurableSet {x : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ |
      dist x.2 (dipoleMidpoint x.1.1) < τ ∧ dist x.2 (dipoleMidpoint x.1.2) < τ} :=
    (measurableSet_lt hm1 measurable_const).inter (measurableSet_lt hm2 measurable_const)
  have hGm := hinner.indicator hset
  have heq : (fun q : (ℂ × ℂ) × (ℂ × ℂ) => screenedInteraction χ lam τ q.1 q.2) =
      fun q => (2 * Real.pi)⁻¹ * ∫ w, {x : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ |
        dist x.2 (dipoleMidpoint x.1.1) < τ ∧ dist x.2 (dipoleMidpoint x.1.2) < τ}.indicator
          (fun x => inner ℝ (screenedField χ lam τ x.1.1 x.2)
            (screenedField χ lam τ x.1.2 x.2)) (q, w) := by
    funext q
    unfold screenedInteraction
    rw [← integral_indicator (measurableSet_ball.inter measurableSet_ball)]
    rfl
  rw [heq]
  exact measurable_const.mul hGm.stronglyMeasurable.integral_prod_right'.measurable

/-- On its screening disc, the screened field of a dipole of length at most `τ/8` is bounded by
`2 √(π M) / λ + 1/(4τ)`. -/
theorem norm_screenedField_le_of_mem (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (hτ : 8 * lam ≤ τ) {d : ℂ × ℂ} (hd : ‖d.2 - d.1‖ ≤ τ / 8) {w : ℂ}
    (hw : ‖w - dipoleMidpoint d‖ ≤ τ) :
    ‖screenedField χ lam τ d w‖ ≤ 2 * (Real.sqrt (Real.pi * M) / lam) + 1 / (4 * τ) := by
  have hτ0 : 0 < τ := by linarith
  have hτ' : 8 * max ‖d.2 - d.1‖ lam ≤ τ := by
    rcases le_total ‖d.2 - d.1‖ lam with h | h
    · rw [max_eq_right h]
      exact hτ
    · rw [max_eq_left h]
      linarith
  have h1 : ‖dipoleField χ lam d w‖ ≤ 2 * (Real.sqrt (Real.pi * M) / lam) := by
    unfold dipoleField
    calc ‖smearedField χ lam (w - d.1) - smearedField χ lam (w - d.2)‖
        ≤ ‖smearedField χ lam (w - d.1)‖ + ‖smearedField χ lam (w - d.2)‖ := norm_sub_le _ _
      _ ≤ Real.sqrt (Real.pi * M) / lam + Real.sqrt (Real.pi * M) / lam :=
          add_le_add (norm_smearedField_le hχ hM hlam _) (norm_smearedField_le hχ hM hlam _)
      _ = 2 * (Real.sqrt (Real.pi * M) / lam) := by ring
  have h2 : ‖screenedCorrectionField τ d w‖ ≤ 1 / (4 * τ) := by
    refine (norm_screenedCorrectionField_le hlam hτ' hw).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  unfold screenedField
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- **`ṽ` is bounded** on the pairs of dipoles of length at most `τ/8`, for `λ > 0`, `8λ ≤ τ`. -/
theorem exists_abs_screenedInteraction_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * lam ≤ τ) : ∃ C : ℝ, ∀ d e : ℂ × ℂ, ‖d.2 - d.1‖ ≤ τ / 8 → ‖e.2 - e.1‖ ≤ τ / 8 →
      |screenedInteraction χ lam τ d e| ≤ C := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  set B := 2 * (Real.sqrt (Real.pi * M) / lam) + 1 / (4 * τ) with hB
  refine ⟨(2 * Real.pi)⁻¹ * (B * B * volume.real (ball (0 : ℂ) τ)), fun d e hd he => ?_⟩
  unfold screenedInteraction
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  rw [abs_mul, abs_of_pos hpi]
  refine mul_le_mul_of_nonneg_left ?_ hpi.le
  have hs : volume (ball (dipoleMidpoint d) τ ∩ ball (dipoleMidpoint e) τ) < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) measure_ball_lt_top
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := B * B) hs
    (f := fun w => inner ℝ (screenedField χ lam τ d w) (screenedField χ lam τ e w))
    (fun w hw => by
      rw [mem_inter_iff, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm] at hw
      calc ‖inner ℝ (screenedField χ lam τ d w) (screenedField χ lam τ e w)‖
          ≤ ‖screenedField χ lam τ d w‖ * ‖screenedField χ lam τ e w‖ := norm_inner_le_norm _ _
        _ ≤ B * B := mul_le_mul (norm_screenedField_le_of_mem hχ hM hlam hτ hd hw.1.le)
            (norm_screenedField_le_of_mem hχ hM hlam hτ he hw.2.le) (norm_nonneg _)
            ((norm_nonneg _).trans (norm_screenedField_le_of_mem hχ hM hlam hτ hd hw.1.le)))
  rw [Real.norm_eq_abs] at hbound
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · calc volume.real (ball (dipoleMidpoint d) τ ∩ ball (dipoleMidpoint e) τ)
        ≤ volume.real (ball (dipoleMidpoint d) τ) :=
          measureReal_mono inter_subset_left measure_ball_lt_top.ne
      _ = volume.real (ball (0 : ℂ) τ) := by
          rw [Measure.real, Measure.real, Measure.addHaar_ball_center]
  · have : 0 ≤ B := by
      rw [hB]
      have : 0 ≤ Real.sqrt (Real.pi * M) / lam := div_nonneg (Real.sqrt_nonneg _) hlam.le
      have : 0 < τ := by linarith
      positivity
    positivity

end Hierarchical

end MultipoleBKT

end
