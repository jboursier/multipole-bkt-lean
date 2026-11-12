/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.Kernel
public import MultipoleBKT.Frozen.DipoleConstant
public import MultipoleBKT.Frozen.DipoleNormalization
public import MultipoleBKT.Frozen.CriticalScale
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TwoComponentCoulomb.Gibbs.Basic

/-!
# The dipole constant `𝒵_β` and the normalizations `C_{β,λ}`, `C_{β,λ,ε₀}`

The paper: equation (2.19), equation (2.31) and
(2.32), Lemma 4.12. Throughout, `χ` is an admissible
mollifier, `g_λ = smearedKernel χ lam` and `Λ = box N = [0, √N]²`.

* `integrableOn_dipoleConstant_integrand`, `dipoleConstant_pos` : for `β > 2`,
  `r ↦ e^{β g_1(r)} r` is integrable on `(0, ∞)` and `𝒵_β > 0`.
* `integral_fun_norm_complex` : `∫_ℂ f(|w|) dw = 2π ∫₀^∞ f(r) r dr` (from Mathlib's
  `integral_fun_norm_addHaar`), `integrable_exp_smearedKernel` and `integral_exp_smearedKernel` :
  `∫_ℂ e^{β g_λ} = λ^{2-β} 𝒵_β` (scaling `g_λ(λ v) = g(λ) + g_1(v)`).
* `lintegral_box_prod_sub`, `integral_box_prod_sub_eq` :
  `(1/N) ∫_{Λ²} f(x - y) = ∫_ℂ f(w) V_N(w) dw` with the overlap factor
  `V_N(w) = |Λ ∩ (Λ + w)| / N = (√N - |Re w|)₊ (√N - |Im w|)₊ / N ∈ [0, 1]`, which tends to `1`
  (`tendsto_overlap_div`); hence `tendsto_integral_box_prod_sub` (dominated convergence) and
  `integral_box_prod_sub_le`.
* `tendsto_dipoleNormalization`: equation (2.32)/(4.15), `C_{β,λ} → λ^{2-β} 𝒵_β`.
* `truncatedDipoleNormalization`: `C_{β,λ,ε₀}`  with truncation length `R = ε₀ R̄`
  as a parameter; `integral_compl_closedBall_exp_smearedKernel` : the tail
  `∫_{|w| > R} e^{β g_λ} = 2π R^{2-β} / (β - 2)` for `R ≥ 2λ`;
  `dipoleNormalization_sub_truncated_le`: equation (4.14), `0 ≤ C_{β,λ} - C_{β,λ,R} ≤ 2π R^{2-β}/(β-2)`
  for every `N`; `tendsto_truncatedDipoleNormalization_eq` : the exact limit
  `λ^{2-β} 𝒵_β - 2π R^{2-β}/(β-2)`.
* `rpow_two_sub_le_of_le_criticalScale` : `R ≤ R_{β,λ}` gives `R^{2-β} ≤ λ^{2-β} R^{-2}`.
* Lemma 4.12: `truncatedDipoleNormalization_asymptotics` (equation (4.11)),
  `eventually_half_le_truncatedDipoleNormalization_of_le_criticalScale` (equation (4.12)),
  `eventually_abs_truncated_sub_div_le` (equation (4.13)), all as `N → ∞`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (logKernel box)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam β : ℝ}

/-! ### The integrand of `𝒵_β` -/

/-- For `r ≥ 2λ`, `e^{β g_λ(r)} r = r^{1 - β}`. -/
theorem exp_mul_smearedKernel_mul_eq_rpow (hχ : IsMollifier χ) (hlam : 0 < lam) {r : ℝ}
    (hr : 2 * lam ≤ r) : Real.exp (β * smearedKernel χ lam r) * r = r ^ (1 - β) := by
  have hr0 : 0 < r := by linarith
  rw [smearedKernel_eq_logKernel hχ hlam
      (by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]; exact hr),
    logKernel_ofReal hr0, Real.rpow_def_of_pos hr0,
    show Real.log r * (1 - β) = β * -Real.log r + Real.log r by ring, Real.exp_add,
    Real.exp_log hr0]

/-- `r ↦ e^{β g_λ(r)} r` is continuous on `ℝ`, for `λ > 0`. -/
theorem continuous_exp_smearedKernel_mul (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) :
    Continuous fun r : ℝ => Real.exp (β * smearedKernel χ lam r) * r := by
  have := continuous_smearedKernel hχ hlam
  fun_prop

/-- For `β > 2` and `λ > 0`, `r ↦ e^{β g_λ(r)} r` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_smearedKernel_mul (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 2 < β) :
    IntegrableOn (fun r : ℝ => Real.exp (β * smearedKernel χ lam r) * r) (Ioi 0) := by
  have hc := continuous_exp_smearedKernel_mul hχ hlam β
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ 2 * lam)]
  refine IntegrableOn.union ?_ ?_
  · exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · have h := integrableOn_Ioi_rpow_of_lt (by linarith : 1 - β < -1) (by linarith : 0 < 2 * lam)
    refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
    exact (exp_mul_smearedKernel_mul_eq_rpow hχ hlam (le_of_lt hr)).symm

/-- Equation (2.19): for `β > 2` the integrand `r ↦ e^{β g_1(r)} r` of `𝒵_β` is integrable on
`(0, ∞)`. -/
theorem integrableOn_dipoleConstant_integrand (hχ : IsMollifier χ) (hβ : 2 < β) :
    IntegrableOn (fun r : ℝ => Real.exp (β * smearedKernel χ 1 r) * r) (Ioi 0) :=
  integrableOn_exp_smearedKernel_mul hχ one_pos hβ

/-- `𝒵_β > 0` for `β > 2`. -/
theorem dipoleConstant_pos (hχ : IsMollifier χ) (hβ : 2 < β) : 0 < dipoleConstant χ β := by
  have hint := integrableOn_exp_smearedKernel_mul hχ one_pos hβ
  have hpos : 0 < ∫ r in Ioi (0 : ℝ), Real.exp (β * smearedKernel χ 1 r) * r := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
    · have hsub : Ioi (0 : ℝ) ⊆
          Function.support (fun r : ℝ => Real.exp (β * smearedKernel χ 1 r) * r) ∩ Ioi 0 :=
        fun r hr => ⟨(mul_pos (Real.exp_pos _) hr).ne', hr⟩
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      simp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact (mul_pos (Real.exp_pos _) hr).le
  unfold dipoleConstant
  positivity

/-! ### `∫_ℂ e^{β g_λ} = λ^{2-β} 𝒵_β` -/

/-- Integrals of radial functions on `ℂ` in polar form: `∫_ℂ f(|w|) dw = 2π ∫₀^∞ f(r) r dr`. -/
theorem integral_fun_norm_complex (f : ℝ → ℝ) :
    ∫ w : ℂ, f ‖w‖ = 2 * Real.pi * ∫ r in Ioi (0 : ℝ), f r * r := by
  rw [integral_fun_norm_addHaar volume f, Complex.finrank_real_complex]
  have hball : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real]
  rw [hball]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  rw [mul_assoc]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  ring

/-- Integrability of radial functions on `ℂ`. -/
theorem integrable_fun_norm_complex_iff (f : ℝ → ℝ) :
    Integrable (fun w : ℂ => f ‖w‖) ↔ IntegrableOn (fun r => f r * r) (Ioi 0) := by
  rw [integrable_fun_norm_addHaar volume (f := f), Complex.finrank_real_complex]
  simp only [smul_eq_mul]
  refine integrableOn_congr_fun (fun r _ => by norm_num [mul_comm]) measurableSet_Ioi

/-- `e^{β g_λ}` is integrable on `ℂ` for `β > 2` and `λ > 0`. -/
theorem integrable_exp_smearedKernel (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 2 < β) :
    Integrable fun w : ℂ => Real.exp (β * smearedKernel χ lam w) := by
  have h := (integrable_fun_norm_complex_iff fun r : ℝ => Real.exp (β * smearedKernel χ lam r)).2
    (integrableOn_exp_smearedKernel_mul hχ hlam hβ)
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [smearedKernel_ofReal_norm hχ]

/-- `∫_ℂ e^{β g_1} = 𝒵_β` (for every `β`). -/
theorem integral_exp_smearedKernel_one (hχ : IsMollifier χ) (β : ℝ) :
    ∫ w : ℂ, Real.exp (β * smearedKernel χ 1 w) = dipoleConstant χ β := by
  have h := integral_fun_norm_complex fun r : ℝ => Real.exp (β * smearedKernel χ 1 r)
  simp only [smearedKernel_ofReal_norm hχ] at h
  exact h

/-- Equation (2.32), right-hand side: `∫_ℂ e^{β g_λ} = λ^{2-β} 𝒵_β` for `λ > 0` (and every
`β`). -/
theorem integral_exp_smearedKernel (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) :
    ∫ w : ℂ, Real.exp (β * smearedKernel χ lam w) = lam ^ (2 - β) * dipoleConstant χ β := by
  have hcv := Measure.integral_comp_smul (volume : Measure ℂ)
    (fun w => Real.exp (β * smearedKernel χ lam w)) lam
  rw [Complex.finrank_real_complex] at hcv
  have hpt : ∀ v : ℂ, Real.exp (β * smearedKernel χ lam (lam • v)) =
      lam ^ (-β) * Real.exp (β * smearedKernel χ 1 v) := by
    intro v
    rw [Complex.real_smul, smearedKernel_ofReal_mul hχ hlam, logKernel_ofReal hlam, mul_add,
      Real.exp_add, Real.rpow_def_of_pos hlam]
    congr 2
    ring
  simp_rw [hpt] at hcv
  rw [integral_const_mul, integral_exp_smearedKernel_one hχ, smul_eq_mul,
    abs_of_pos (by positivity)] at hcv
  have h2 : lam ^ (2 - β) = lam ^ 2 * lam ^ (-β) := by
    rw [sub_eq_add_neg, Real.rpow_add hlam, Real.rpow_two]
  rw [h2, mul_assoc, hcv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-! ### Overlap of the box with its translates -/

/-- `min a (a + t) - max 0 t = a - |t|`. -/
theorem min_add_sub_max_zero (a t : ℝ) : min a (a + t) - max 0 t = a - |t| := by
  rcases le_total 0 t with h | h
  · rw [min_eq_left (by linarith), max_eq_right h, abs_of_nonneg h]
  · rw [min_eq_right (by linarith), max_eq_left h, abs_of_nonpos h]
    ring

/-- `Λ ∩ (Λ + w)` is a rectangle. -/
theorem box_inter_preimage_sub (N : ℕ) (w : ℂ) :
    box N ∩ (fun x => x - w) ⁻¹' box N =
      Complex.reProdIm (Icc (max 0 w.re) (min √(N : ℝ) (√(N : ℝ) + w.re)))
        (Icc (max 0 w.im) (min √(N : ℝ) (√(N : ℝ) + w.im))) := by
  ext x
  simp only [box, mem_inter_iff, mem_preimage, Complex.mem_reProdIm, Complex.sub_re,
    Complex.sub_im, mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩
    exact ⟨⟨⟨h1, by linarith⟩, h2, by linarith⟩, ⟨h3, by linarith⟩, h4, by linarith⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩
    exact ⟨⟨⟨h1, h3⟩, h5, h7⟩, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The area of `Λ ∩ (Λ + w)` is `(√N - |Re w|)₊ (√N - |Im w|)₊`. -/
theorem volume_box_inter_preimage_sub (N : ℕ) (w : ℂ) :
    volume (box N ∩ (fun x => x - w) ⁻¹' box N) =
      ENNReal.ofReal (√(N : ℝ) - |w.re|) * ENNReal.ofReal (√(N : ℝ) - |w.im|) := by
  rw [box_inter_preimage_sub, TwoComponentCoulomb.volume_reProdIm_Icc_Icc, min_add_sub_max_zero,
    min_add_sub_max_zero]

/-- Pair integrals over `Λ²` of functions of the difference:
`∫_{Λ²} F(x - y) dx dy = ∫_ℂ F(w) |Λ ∩ (Λ + w)| dw`. -/
theorem lintegral_box_prod_sub (N : ℕ) {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p in box N ×ˢ box N, F (p.1 - p.2) =
      ∫⁻ w, F w * volume (box N ∩ (fun x => x - w) ⁻¹' box N) := by
  have hΛ := TwoComponentCoulomb.measurableSet_box N
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod (fun p : ℂ × ℂ => F (p.1 - p.2))
      (hF.comp (measurable_fst.sub measurable_snd)).aemeasurable]
  have h1 : ∀ x : ℂ, ∫⁻ y in box N, F (x - y) =
      ∫⁻ w, ((fun w => x - w) ⁻¹' box N).indicator F w := by
    intro x
    rw [← lintegral_indicator hΛ, ← lintegral_sub_left_eq_self _ x]
    congr 1
    funext w
    simp only [indicator, sub_sub_cancel]
    rfl
  simp_rw [h1]
  have hmeas : Measurable (Function.uncurry fun (x w : ℂ) =>
      ((fun w => x - w) ⁻¹' box N).indicator F w) := by
    have : Measurable ({p : ℂ × ℂ | p.1 - p.2 ∈ box N}.indicator fun p => F p.2) :=
      (hF.comp measurable_snd).indicator (hΛ.preimage (measurable_fst.sub measurable_snd))
    exact this
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  congr 1
  funext w
  have h2 : ∀ x : ℂ, ((fun w => x - w) ⁻¹' box N).indicator F w =
      ((fun x => x - w) ⁻¹' box N).indicator (fun _ => F w) x := fun x => by
    simp only [indicator]
    rfl
  simp_rw [h2]
  have hm : MeasurableSet ((fun x => x - w) ⁻¹' box N) := hΛ.preimage (measurable_id.sub_const w)
  rw [lintegral_indicator hm, setLIntegral_const, Measure.restrict_apply hm, inter_comm]

/-- The overlap factor `V_N(w) = (√N - |Re w|)₊ (√N - |Im w|)₊ / N` is nonnegative. -/
theorem overlap_div_nonneg (N : ℕ) (w : ℂ) :
    0 ≤ max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 / N := by
  have := le_max_right (√(N : ℝ) - |w.re|) 0
  have := le_max_right (√(N : ℝ) - |w.im|) 0
  positivity

/-- The overlap factor is at most `1`. -/
theorem overlap_div_le_one (N : ℕ) (w : ℂ) :
    max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 / N ≤ 1 := by
  have hs := Real.sqrt_nonneg (N : ℝ)
  have h1 : max (√(N : ℝ) - |w.re|) 0 ≤ √(N : ℝ) :=
    max_le (by linarith [abs_nonneg w.re]) hs
  have h2 : max (√(N : ℝ) - |w.im|) 0 ≤ √(N : ℝ) :=
    max_le (by linarith [abs_nonneg w.im]) hs
  have h3 : max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 ≤ N := by
    calc max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 ≤ √(N : ℝ) * √(N : ℝ) :=
          mul_le_mul h1 h2 (le_max_right _ _) hs
      _ = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).eq_or_lt with h | h
  · rw [← h, div_zero]
    exact zero_le_one
  · exact (div_le_one h).2 h3

/-- `(1 - a / √N)₊ → 1` as `N → ∞`. -/
theorem tendsto_max_one_sub_div_sqrt (a : ℝ) :
    Tendsto (fun N : ℕ => max (1 - a / √(N : ℝ)) 0) atTop (𝓝 1) := by
  have hs : Tendsto (fun N : ℕ => √(N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_const_nhds (x := a)).div_atTop hs)).max (tendsto_const_nhds (x := (0 : ℝ)))
  simpa using h

/-- The overlap factor tends to `1` as `N → ∞`. -/
theorem tendsto_overlap_div (w : ℂ) :
    Tendsto (fun N : ℕ => max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 / N) atTop
      (𝓝 1) := by
  have h := (tendsto_max_one_sub_div_sqrt |w.re|).mul (tendsto_max_one_sub_div_sqrt |w.im|)
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN'
  have e : ∀ a : ℝ, max (√(N : ℝ) - a) 0 = √(N : ℝ) * max (1 - a / √(N : ℝ)) 0 := by
    intro a
    rw [mul_max_of_nonneg _ _ hs.le, mul_zero, mul_sub, mul_one, mul_div_cancel₀ _ hs.ne']
  have hNN : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN'.le
  set m1 := max (1 - |w.re| / √(N : ℝ)) 0
  set m2 := max (1 - |w.im| / √(N : ℝ)) 0
  rw [e, e, eq_div_iff hN'.ne']
  linear_combination (m1 * m2) * hNN.symm

/-- Normalized pair integrals over `Λ²` as integrals against the overlap factor. -/
theorem integral_box_prod_sub_eq (N : ℕ) {f : ℂ → ℝ} (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w) :
    (1 / (N : ℝ)) * ∫ p in box N ×ˢ box N, f (p.1 - p.2) =
      ∫ w, f w * (max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 / N) := by
  have hV : Measurable fun w : ℂ => max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 := by
    fun_prop
  have hm1 : AEStronglyMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2))
      (volume.restrict (box N ×ˢ box N)) :=
    (hf.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable
      (fun w => f w * (max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0)) volume :=
    (hf.mul hV).aestronglyMeasurable
  have hpos : ∀ w : ℂ, 0 ≤ max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 :=
    fun w => mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have key : ∫ p in box N ×ˢ box N, f (p.1 - p.2) =
      ∫ w, f w * (max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun p => hf0 _) hm1,
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun w => mul_nonneg (hf0 w) (hpos w)) hm2,
      lintegral_box_prod_sub N (F := fun w => ENNReal.ofReal (f w))
        (ENNReal.measurable_ofReal.comp hf)]
    congr 1
    refine lintegral_congr fun w => ?_
    rw [volume_box_inter_preimage_sub, ENNReal.ofReal_mul (hf0 w),
      ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_max, ENNReal.ofReal_max,
      ENNReal.ofReal_zero, max_eq_left (by positivity), max_eq_left (by positivity)]
  rw [key, ← integral_const_mul]
  congr 1
  funext w
  ring

/-- **Dominated convergence for pair integrals**: for `f ≥ 0` measurable and integrable on `ℂ`,
`(1/N) ∫_{Λ²} f(x - y) dx dy → ∫_ℂ f` as `N → ∞`. -/
theorem tendsto_integral_box_prod_sub {f : ℂ → ℝ} (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hfi : Integrable f) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∫ p in box N ×ˢ box N, f (p.1 - p.2)) atTop
      (𝓝 (∫ w, f w)) := by
  simp_rw [integral_box_prod_sub_eq _ hf hf0]
  have h := tendsto_integral_of_dominated_convergence f
    (F := fun (N : ℕ) w => f w * (max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 / N))
    (fun N => (hf.mul (by fun_prop)).aestronglyMeasurable) hfi
    (fun N => Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 w) (overlap_div_nonneg N w))]
      exact mul_le_of_le_one_right (hf0 w) (overlap_div_le_one N w))
    (Filter.Eventually.of_forall fun w => by
      simpa using (tendsto_const_nhds (x := f w)).mul (tendsto_overlap_div w))
  exact h

/-- `(1/N) ∫_{Λ²} f(x - y) dx dy ≤ ∫_ℂ f` for `f ≥ 0` measurable and integrable. -/
theorem integral_box_prod_sub_le (N : ℕ) {f : ℂ → ℝ} (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hfi : Integrable f) :
    (1 / (N : ℝ)) * ∫ p in box N ×ˢ box N, f (p.1 - p.2) ≤ ∫ w, f w := by
  rw [integral_box_prod_sub_eq N hf hf0]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
    mul_nonneg (hf0 w) (overlap_div_nonneg N w)) hfi (Filter.Eventually.of_forall fun w => ?_)
  exact mul_le_of_le_one_right (hf0 w) (overlap_div_le_one N w)

/-! ### Lemma 4.12: the normalization constants `C_{β,λ}` and `C_{β,λ,ε₀}` -/

/-- `w ↦ e^{β g_λ(w)}` is continuous, for `λ > 0`. -/
theorem continuous_exp_smearedKernel (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) :
    Continuous fun w : ℂ => Real.exp (β * smearedKernel χ lam w) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_smearedKernel hχ hlam))

/-- `w ↦ e^{β g_λ(w)}` is measurable, for `λ > 0`. -/
theorem measurable_exp_smearedKernel (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) :
    Measurable fun w : ℂ => Real.exp (β * smearedKernel χ lam w) :=
  (continuous_exp_smearedKernel hχ hlam β).measurable

/-- Equation (2.32) and (4.15): for `β > 2` and `λ > 0`,
`C_{β,λ} → ∫_ℂ e^{β g_λ} = λ^{2-β} 𝒵_β` as `N → ∞`. -/
theorem tendsto_dipoleNormalization (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam) :
    Tendsto (fun N : ℕ => dipoleNormalization χ N β lam) atTop
      (𝓝 (lam ^ (2 - β) * dipoleConstant χ β)) := by
  rw [← integral_exp_smearedKernel hχ hlam β]
  exact tendsto_integral_box_prod_sub (f := fun w => Real.exp (β * smearedKernel χ lam w))
    (measurable_exp_smearedKernel hχ hlam β) (fun w => (Real.exp_pos _).le)
    (integrable_exp_smearedKernel hχ hlam hβ)

/-- The truncated normalization `C_{β,λ,ε₀}` of the paper (Lemma 4.12), with the
truncation length `R = ε₀ R̄_{β,λ}` as a free parameter:
`(1/N) ∫_{Λ²} e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ R} dx dy`. -/
noncomputable def truncatedDipoleNormalization (χ : ℂ → ℝ) (N : ℕ) (β lam R : ℝ) : ℝ :=
  (1 / N) * ∫ p in box N ×ˢ box N,
    (closedBall (0 : ℂ) R).indicator (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2)

/-- `C_{β,λ,R} → ∫_{B̄(0,R)} e^{β g_λ}` as `N → ∞` (every `β`, `λ > 0`). -/
theorem tendsto_truncatedDipoleNormalization (hχ : IsMollifier χ) (hlam : 0 < lam) (β R : ℝ) :
    Tendsto (fun N : ℕ => truncatedDipoleNormalization χ N β lam R) atTop
      (𝓝 (∫ w in closedBall (0 : ℂ) R, Real.exp (β * smearedKernel χ lam w))) := by
  have hint : IntegrableOn (fun w : ℂ => Real.exp (β * smearedKernel χ lam w))
      (closedBall (0 : ℂ) R) :=
    (continuous_exp_smearedKernel hχ hlam β).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R)
  rw [← integral_indicator measurableSet_closedBall]
  exact tendsto_integral_box_prod_sub
    ((measurable_exp_smearedKernel hχ hlam β).indicator measurableSet_closedBall)
    (fun w => indicator_nonneg (fun w _ => (Real.exp_pos _).le) w)
    ((integrable_indicator_iff measurableSet_closedBall).2 hint)

/-- Outside `B̄(0, R)` with `R ≥ 2λ`, `e^{β g_λ(w)} = |w|^{-β}`. -/
theorem exp_mul_smearedKernel_eq_rpow (hχ : IsMollifier χ) (hlam : 0 < lam) {w : ℂ}
    (hw : 2 * lam ≤ ‖w‖) : Real.exp (β * smearedKernel χ lam w) = ‖w‖ ^ (-β) := by
  have hw0 : 0 < ‖w‖ := by linarith
  rw [smearedKernel_eq_logKernel hχ hlam hw, TwoComponentCoulomb.logKernel,
    Real.rpow_def_of_pos hw0]
  congr 1
  ring

/-- The tail `∫_{|w| > R} e^{β g_λ(w)} dw = 2π R^{2-β} / (β - 2)` for `β > 2` and `R ≥ 2λ > 0`. -/
theorem integral_compl_closedBall_exp_smearedKernel (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) {R : ℝ} (hR : 2 * lam ≤ R) :
    ∫ w in (closedBall (0 : ℂ) R)ᶜ, Real.exp (β * smearedKernel χ lam w) =
      2 * Real.pi / (β - 2) * R ^ (2 - β) := by
  have hR0 : 0 < R := by linarith
  set h : ℝ → ℝ := (Ioi R).indicator fun r => r ^ (-β) with hh
  have hpt : ∀ w : ℂ, (closedBall (0 : ℂ) R)ᶜ.indicator
      (fun w => Real.exp (β * smearedKernel χ lam w)) w = h ‖w‖ := by
    intro w
    by_cases hw : ‖w‖ ≤ R
    · have h1 : w ∉ (closedBall (0 : ℂ) R)ᶜ := by simpa using hw
      have h2 : ‖w‖ ∉ Ioi R := by simpa using hw
      rw [indicator_of_notMem h1, hh, indicator_of_notMem h2]
    · have hw' : R < ‖w‖ := lt_of_not_ge hw
      have h1 : w ∈ (closedBall (0 : ℂ) R)ᶜ := by simpa using hw'
      have h2 : ‖w‖ ∈ Ioi R := hw'
      rw [indicator_of_mem h1, hh, indicator_of_mem h2]
      exact exp_mul_smearedKernel_eq_rpow hχ hlam (hR.trans hw'.le)
  rw [← integral_indicator measurableSet_closedBall.compl]
  simp_rw [hpt]
  rw [integral_fun_norm_complex]
  have h3 : ∀ r ∈ Ioi (0 : ℝ), h r * r = (Ioi R).indicator (fun r => r ^ (1 - β)) r := by
    intro r hr
    by_cases hrR : r ∈ Ioi R
    · have hr0 : (r : ℝ) ≠ 0 := (mem_Ioi.1 hr).ne'
      rw [hh, indicator_of_mem hrR, indicator_of_mem hrR, ← Real.rpow_add_one hr0]
      ring_nf
    · rw [hh, indicator_of_notMem hrR, indicator_of_notMem hrR, zero_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi h3, setIntegral_indicator measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_right hR0.le,
    integral_Ioi_rpow_of_lt (by linarith : 1 - β < -1) hR0]
  have hb : (1 - β + 1) = 2 - β := by ring
  rw [hb]
  have hb2 : (2 - β) ≠ 0 := by linarith
  have hb3 : (β - 2) ≠ 0 := by linarith
  field_simp
  ring

/-- The pair integral splits along `B̄(0, R)`: `C_{β,λ} = C_{β,λ,R} + D` with
`D = (1/N) ∫_{Λ²} e^{β g_λ(x - y)} 𝟙_{|x - y| > R}`, and `0 ≤ D ≤ ∫_{|w| > R} e^{β g_λ}`. -/
theorem dipoleNormalization_sub_truncated_mem (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (N : ℕ) (R : ℝ) :
    0 ≤ dipoleNormalization χ N β lam - truncatedDipoleNormalization χ N β lam R ∧
      dipoleNormalization χ N β lam - truncatedDipoleNormalization χ N β lam R ≤
        ∫ w in (closedBall (0 : ℂ) R)ᶜ, Real.exp (β * smearedKernel χ lam w) := by
  set f : ℂ → ℝ := fun w => Real.exp (β * smearedKernel χ lam w) with hf
  have hm : Measurable f := measurable_exp_smearedKernel hχ hlam β
  have hf0 : ∀ w, 0 ≤ f w := fun w => (Real.exp_pos _).le
  have hfi : Integrable f := integrable_exp_smearedKernel hχ hlam hβ
  set B : Set ℂ := closedBall 0 R with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hmB : Measurable (B.indicator f) := hm.indicator hBm
  have hmC : Measurable (Bᶜ.indicator f) := hm.indicator hBm.compl
  have hB0 : ∀ w, 0 ≤ B.indicator f w := fun w => indicator_nonneg (fun w _ => hf0 w) w
  have hC0 : ∀ w, 0 ≤ Bᶜ.indicator f w := fun w => indicator_nonneg (fun w _ => hf0 w) w
  set V : ℂ → ℝ := fun w => max (√(N : ℝ) - |w.re|) 0 * max (√(N : ℝ) - |w.im|) 0 / N with hV
  have hVm : Measurable V := by fun_prop
  have hint : ∀ {g : ℂ → ℝ}, Measurable g → (∀ w, 0 ≤ g w) → (∀ w, g w ≤ f w) →
      Integrable fun w => g w * V w := by
    intro g hg hg0 hgf
    refine hfi.mono' (hg.mul hVm).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 w) (overlap_div_nonneg N w))]
    exact (mul_le_of_le_one_right (hg0 w) (overlap_div_le_one N w)).trans (hgf w)
  have hBf : ∀ w, B.indicator f w ≤ f w := fun w => indicator_le_self' (fun w _ => hf0 w) w
  have hCf : ∀ w, Bᶜ.indicator f w ≤ f w := fun w => indicator_le_self' (fun w _ => hf0 w) w
  have e1 : dipoleNormalization χ N β lam = ∫ w, f w * V w :=
    integral_box_prod_sub_eq N hm hf0
  have e2 : truncatedDipoleNormalization χ N β lam R = ∫ w, B.indicator f w * V w :=
    integral_box_prod_sub_eq N hmB hB0
  have e3 : (1 / (N : ℝ)) * ∫ p in box N ×ˢ box N, Bᶜ.indicator f (p.1 - p.2) =
      ∫ w, Bᶜ.indicator f w * V w :=
    integral_box_prod_sub_eq N hmC hC0
  have hsplit : ∫ w, f w * V w = (∫ w, B.indicator f w * V w) + ∫ w, Bᶜ.indicator f w * V w := by
    rw [← integral_add (hint hmB hB0 hBf) (hint hmC hC0 hCf)]
    congr 1
    funext w
    rw [← add_mul, indicator_self_add_compl_apply]
  have hD : dipoleNormalization χ N β lam - truncatedDipoleNormalization χ N β lam R =
      (1 / (N : ℝ)) * ∫ p in box N ×ˢ box N, Bᶜ.indicator f (p.1 - p.2) := by
    rw [e1, e2, e3, hsplit]
    ring
  rw [hD]
  constructor
  · rw [e3]
    exact integral_nonneg fun w => mul_nonneg (hC0 w) (overlap_div_nonneg N w)
  · rw [← integral_indicator hBm.compl]
    exact integral_box_prod_sub_le N hmC hC0
      ((integrable_indicator_iff hBm.compl).2 hfi.integrableOn)

/-- Equation (4.14): for `β > 2` and `R ≥ 2λ > 0`, uniformly in `N`,
`0 ≤ C_{β,λ} - C_{β,λ,R} ≤ (2π / (β - 2)) R^{2-β}`. -/
theorem dipoleNormalization_sub_truncated_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) {R : ℝ} (hR : 2 * lam ≤ R) (N : ℕ) :
    0 ≤ dipoleNormalization χ N β lam - truncatedDipoleNormalization χ N β lam R ∧
      dipoleNormalization χ N β lam - truncatedDipoleNormalization χ N β lam R ≤
        2 * Real.pi / (β - 2) * R ^ (2 - β) := by
  have h := dipoleNormalization_sub_truncated_mem hχ hβ hlam N R
  rw [integral_compl_closedBall_exp_smearedKernel hχ hβ hlam hR] at h
  exact h

/-- The limit of `C_{β,λ,R}` is explicit: `λ^{2-β} 𝒵_β - 2π R^{2-β} / (β - 2)` for `β > 2` and
`R ≥ 2λ > 0`. -/
theorem tendsto_truncatedDipoleNormalization_eq (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) {R : ℝ} (hR : 2 * lam ≤ R) :
    Tendsto (fun N : ℕ => truncatedDipoleNormalization χ N β lam R) atTop
      (𝓝 (lam ^ (2 - β) * dipoleConstant χ β - 2 * Real.pi / (β - 2) * R ^ (2 - β))) := by
  have h := tendsto_truncatedDipoleNormalization hχ hlam β R
  have hsplit := integral_add_compl (μ := volume) (measurableSet_closedBall (x := (0 : ℂ)) (ε := R))
    (integrable_exp_smearedKernel hχ hlam hβ)
  rw [integral_exp_smearedKernel hχ hlam β,
    integral_compl_closedBall_exp_smearedKernel hχ hβ hlam hR] at hsplit
  rwa [show lam ^ (2 - β) * dipoleConstant χ β - 2 * Real.pi / (β - 2) * R ^ (2 - β) =
      ∫ w in closedBall (0 : ℂ) R, Real.exp (β * smearedKernel χ lam w) by linarith]

/-- For `R ≤ R_{β,λ}` (the critical scale) with `λ ≤ R` and `0 < λ ≤ 1`:
`R^{2-β} ≤ λ^{2-β} R^{-2}`, i.e. `(λ / R)^{β-2} ≤ R^{-2}` (the proof of Lemma 4.12). -/
theorem rpow_two_sub_le_of_le_criticalScale (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    {R : ℝ} (hR : lam ≤ R) (hRc : ENNReal.ofReal R ≤ criticalScale β lam) :
    R ^ (2 - β) ≤ lam ^ (2 - β) * (R ^ 2)⁻¹ := by
  have hR0 : 0 < R := hlam.trans_le hR
  have key : R ^ (4 - β) ≤ lam ^ (2 - β) := by
    rcases lt_or_ge β 4 with h4 | h4
    · rw [criticalScale, ite_eq_left h4,
        ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hlam.le _)] at hRc
      calc R ^ (4 - β) ≤ (lam ^ (-(β - 2) / (4 - β))) ^ (4 - β) :=
            Real.rpow_le_rpow hR0.le hRc (by linarith)
        _ = lam ^ (2 - β) := by
            rw [← Real.rpow_mul hlam.le]
            congr 1
            field_simp
            ring
    · calc R ^ (4 - β) ≤ lam ^ (4 - β) := Real.rpow_le_rpow_of_nonpos hlam hR (by linarith)
        _ = lam ^ (2 - β) * lam ^ (2 : ℝ) := by
            rw [← Real.rpow_add hlam]
            ring_nf
        _ ≤ lam ^ (2 - β) * 1 := by
            gcongr
            exact Real.rpow_le_one hlam.le hlam1 (by norm_num)
        _ = lam ^ (2 - β) := mul_one _
  have h4 : R ^ (2 - β) = R ^ (4 - β) * (R ^ 2)⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_neg hR0.le, ← Real.rpow_add hR0]
    ring_nf
  rw [h4]
  gcongr

/-- **Lemma 4.12, equation (4.11)**: for `β > 2`, `0 < λ ≤ 1` and a truncation
length `R` with `2λ ≤ R ≤ R_{β,λ}`, `C_{β,λ,R} = λ^{2-β} (𝒵_β + O(R^{-2}))` as `N → ∞`, with the
explicit constant `2π / (β - 2)` depending only on `β`. -/
theorem truncatedDipoleNormalization_asymptotics (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) {R : ℝ} (hR : 2 * lam ≤ R)
    (hRc : ENNReal.ofReal R ≤ criticalScale β lam) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => truncatedDipoleNormalization χ N β lam R) atTop (𝓝 L) ∧
      |L - lam ^ (2 - β) * dipoleConstant χ β| ≤
        lam ^ (2 - β) * (2 * Real.pi / (β - 2) * (R ^ 2)⁻¹) := by
  refine ⟨_, tendsto_truncatedDipoleNormalization_eq hχ hβ hlam hR, ?_⟩
  have hc : 0 ≤ 2 * Real.pi / (β - 2) := div_nonneg (by positivity) (by linarith)
  have h1 := rpow_two_sub_le_of_le_criticalScale hlam hlam1 (by linarith) hRc
  have h2 : 0 ≤ R ^ (2 - β) := Real.rpow_nonneg (by linarith) _
  rw [show lam ^ (2 - β) * dipoleConstant χ β - 2 * Real.pi / (β - 2) * R ^ (2 - β) -
      lam ^ (2 - β) * dipoleConstant χ β = -(2 * Real.pi / (β - 2) * R ^ (2 - β)) by ring,
    abs_neg, abs_of_nonneg (mul_nonneg hc h2)]
  calc 2 * Real.pi / (β - 2) * R ^ (2 - β) ≤ 2 * Real.pi / (β - 2) * (lam ^ (2 - β) * (R ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = lam ^ (2 - β) * (2 * Real.pi / (β - 2) * (R ^ 2)⁻¹) := by ring

/-- **Lemma 4.12, equation (4.12)**: if `2π / (β - 2) · R^{2-β} <
λ^{2-β} 𝒵_β / 2` (which holds for `R ≤ R_{β,λ}` once `R` is large, see
`rpow_two_sub_le_of_le_criticalScale`), then `C_{β,λ,R} ≥ 𝒵_β λ^{2-β} / 2` for all large `N`. -/
theorem eventually_half_le_truncatedDipoleNormalization (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) {R : ℝ} (hR : 2 * lam ≤ R)
    (hsmall : 2 * Real.pi / (β - 2) * R ^ (2 - β) < 1 / 2 * dipoleConstant χ β * lam ^ (2 - β)) :
    ∀ᶠ N : ℕ in atTop,
      1 / 2 * dipoleConstant χ β * lam ^ (2 - β) ≤ truncatedDipoleNormalization χ N β lam R := by
  have h := tendsto_truncatedDipoleNormalization_eq hχ hβ hlam hR
  have hlt : 1 / 2 * dipoleConstant χ β * lam ^ (2 - β) <
      lam ^ (2 - β) * dipoleConstant χ β - 2 * Real.pi / (β - 2) * R ^ (2 - β) := by
    linarith
  filter_upwards [h.eventually (eventually_gt_nhds hlt)] with N hN
  exact hN.le

/-- `C_{β,λ} ≥ 𝒵_β λ^{2-β} / 2` for all large `N`. -/
theorem eventually_half_le_dipoleNormalization (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) :
    ∀ᶠ N : ℕ in atTop,
      1 / 2 * dipoleConstant χ β * lam ^ (2 - β) ≤ dipoleNormalization χ N β lam := by
  have hZ := dipoleConstant_pos hχ hβ
  have hl : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hlt : 1 / 2 * dipoleConstant χ β * lam ^ (2 - β) < lam ^ (2 - β) * dipoleConstant χ β := by
    nlinarith
  filter_upwards [(tendsto_dipoleNormalization hχ hβ hlam).eventually (eventually_gt_nhds hlt)]
    with N hN
  exact hN.le

/-- **Lemma 4.12, equation (4.13)**: for `β > 2`, `0 < λ ≤ 1` and
`2λ ≤ R ≤ R_{β,λ}`, for all large `N`,
`|C_{β,λ,R} - C_{β,λ}| / C_{β,λ} ≤ C R^{-2}` with `C = 4π / ((β - 2) 𝒵_β)`. -/
theorem eventually_abs_truncated_sub_div_le (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) {R : ℝ} (hR : 2 * lam ≤ R) (hRc : ENNReal.ofReal R ≤ criticalScale β lam) :
    ∀ᶠ N : ℕ in atTop,
      |truncatedDipoleNormalization χ N β lam R - dipoleNormalization χ N β lam| /
          dipoleNormalization χ N β lam ≤
        4 * Real.pi / ((β - 2) * dipoleConstant χ β) * (R ^ 2)⁻¹ := by
  have hZ := dipoleConstant_pos hχ hβ
  have hl : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hb : 0 < β - 2 := by linarith
  have h1 := rpow_two_sub_le_of_le_criticalScale hlam hlam1 (by linarith) hRc
  filter_upwards [eventually_half_le_dipoleNormalization hχ hβ hlam] with N hN
  have hpos : 0 < dipoleNormalization χ N β lam := lt_of_lt_of_le (by positivity) hN
  obtain ⟨h2, h3⟩ := dipoleNormalization_sub_truncated_le hχ hβ hlam hR N
  rw [abs_sub_comm, abs_of_nonneg h2, div_le_iff₀ hpos]
  have hR2 : 0 ≤ (R ^ 2)⁻¹ := by positivity
  calc dipoleNormalization χ N β lam - truncatedDipoleNormalization χ N β lam R
      ≤ 2 * Real.pi / (β - 2) * R ^ (2 - β) := h3
    _ ≤ 2 * Real.pi / (β - 2) * (lam ^ (2 - β) * (R ^ 2)⁻¹) := by gcongr
    _ = 4 * Real.pi / ((β - 2) * dipoleConstant χ β) * (R ^ 2)⁻¹ *
          (1 / 2 * dipoleConstant χ β * lam ^ (2 - β)) := by
        field_simp
        ring
    _ ≤ 4 * Real.pi / ((β - 2) * dipoleConstant χ β) * (R ^ 2)⁻¹ *
          dipoleNormalization χ N β lam := by
        gcongr

/-- **Lemma 4.12, equation (4.12)**, in the form used by the paper: for `β > 2`,
`0 < λ ≤ 1` and `2λ ≤ R ≤ R_{β,λ}` with `R² > 4π / ((β - 2) 𝒵_β)` (true for `R = ε₀ R̄_{β,λ}` once
`λ` is small), `C_{β,λ,R} ≥ 𝒵_β λ^{2-β} / 2` for all large `N`. -/
theorem eventually_half_le_truncatedDipoleNormalization_of_le_criticalScale
    (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam) (hlam1 : lam ≤ 1) {R : ℝ}
    (hR : 2 * lam ≤ R) (hRc : ENNReal.ofReal R ≤ criticalScale β lam)
    (hRlarge : 4 * Real.pi / ((β - 2) * dipoleConstant χ β) < R ^ 2) :
    ∀ᶠ N : ℕ in atTop,
      1 / 2 * dipoleConstant χ β * lam ^ (2 - β) ≤ truncatedDipoleNormalization χ N β lam R := by
  have hZ := dipoleConstant_pos hχ hβ
  have hl : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hb : 0 < β - 2 := by linarith
  have hR0 : 0 < R := by linarith
  have h1 := rpow_two_sub_le_of_le_criticalScale hlam hlam1 (by linarith) hRc
  refine eventually_half_le_truncatedDipoleNormalization hχ hβ hlam hR ?_
  have hc : 0 ≤ 2 * Real.pi / (β - 2) := div_nonneg (by positivity) hb.le
  have h2 : 2 * Real.pi / (β - 2) * (R ^ 2)⁻¹ < 1 / 2 * dipoleConstant χ β := by
    have hR2 : 0 < R ^ 2 := by positivity
    rw [div_lt_iff₀ (by positivity)] at hRlarge
    have e : 2 * Real.pi / (β - 2) * (R ^ 2)⁻¹ = 2 * Real.pi / ((β - 2) * R ^ 2) := by
      field_simp
    rw [e, div_lt_iff₀ (by positivity)]
    linarith
  calc 2 * Real.pi / (β - 2) * R ^ (2 - β)
      ≤ 2 * Real.pi / (β - 2) * (lam ^ (2 - β) * (R ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 hc
    _ = 2 * Real.pi / (β - 2) * (R ^ 2)⁻¹ * lam ^ (2 - β) := by ring
    _ < 1 / 2 * dipoleConstant χ β * lam ^ (2 - β) := mul_lt_mul_of_pos_right h2 hl

end MultipoleBKT

end
