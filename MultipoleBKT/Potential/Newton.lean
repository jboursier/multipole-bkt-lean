/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.SmearedCharge
import TwoComponentCoulomb.Potential.DiscPotential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Newton's theorem for a radial smeared charge

The potential `U_{z,λ}(x) = ∫ g(x - y) dδ_z^{(λ)}(y)` of one smeared charge, for a general
admissible mollifier `χ` (`IsMollifier χ`) and `λ > 0` (Section 2.1; `g = logKernel`).

Since `χ` is radial, `δ_z^{(λ)}` is invariant under the rotations about `z`
(`map_rotate_smearedCharge`), so `U_{z,λ}(x)` equals its average over these rotations. The circle
average of `log ‖a - e^{iθ} w‖` is `log (max ‖w‖ ‖a‖)` (`integral_Ioo_log_norm_sub_exp_mul`, from
Mathlib's `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`), and Fubini gives:

* `integral_logKernel_sub_smearedCharge_eq_max` :
  `U_{z,λ}(x) = ∫ -log (max |x - z| |y - z|) dδ_z^{(λ)}(y)` for every `x`; the `min` form
  `integral_logKernel_sub_smearedCharge_eq_min`,
  `U_{z,λ}(x) = ∫ min (g(x - z), g(y - z)) dδ_z^{(λ)}(y)` for `x ≠ z`; and the profile form
  `integral_logKernel_sub_smearedCharge_eq_profile` (`U_{z,λ}(x)` depends only on `|x - z|`).
* `integral_logKernel_sub_smearedCharge_of_le` : **Newton's theorem**, `U_{z,λ}(x) = g(x - z)` for
  `|x - z| ≥ λ`.
* `integral_logKernel_sub_smearedCharge_le` : `U_{z,λ}(x) ≤ g(x - z)` for `x ≠ z`;
  `integral_logKernel_sub_smearedCharge_le_center` :
  `U_{z,λ}(x) ≤ U_{z,λ}(z) = ∫ g(y - z) dδ_z^{(λ)}(y)`;
  `integral_logKernel_sub_center_smearedCharge` : `U_{z,λ}(z) = g(λ) + c_χ` with the explicit
  constant `c_χ = ∫ g dδ_0^{(1)}`.
* `continuous_integral_logKernel_sub_smearedCharge` : `U_{z,λ}` is continuous, through the
  continuity of the radial profile `s ↦ ∫ -log (max s |y|) dδ_0^{(λ)}(y)`
  (`continuous_integral_neg_log_max_smearedCharge`).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

/-! ### The circle average of the logarithm -/

/-- The integral of `log ‖a - e^{iθ} w‖` over a period: for all `a w : ℂ`,
`∫_{-π}^{π} log ‖a - e^{iθ} w‖ dθ = 2π log (max ‖w‖ ‖a‖)`. -/
theorem integral_Ioo_log_norm_sub_exp_mul (a w : ℂ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, Real.log ‖a - Complex.exp (θ * Complex.I) * w‖ =
      2 * Real.pi * Real.log (max ‖w‖ ‖a‖) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp only [mul_zero, sub_zero, norm_zero]
    rw [setIntegral_const, Real.volume_real_Ioo, max_eq_right (norm_nonneg a), smul_eq_mul]
    congr 1
    rw [max_eq_left (by linarith [Real.pi_pos])]
    ring
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  set h : ℝ → ℝ := fun t => Real.log ‖a - circleMap 0 ‖w‖ t‖ with hh
  have hper : Function.Periodic h (2 * Real.pi) := fun t => by
    simp only [hh, periodic_circleMap 0 ‖w‖ t]
  have hfun : ∀ θ : ℝ, Real.log ‖a - Complex.exp (θ * Complex.I) * w‖ = h (θ + Complex.arg w) := by
    intro θ
    have : Complex.exp (θ * Complex.I) * w = circleMap 0 ‖w‖ (θ + Complex.arg w) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
      simp only [circleMap, zero_add, Complex.ofReal_add, add_mul, Complex.exp_add]
      ring
    rw [this]
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simp_rw [hfun]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi,
    intervalIntegral.integral_comp_add_right]
  have h1 := hper.intervalIntegral_add_eq (-Real.pi + Complex.arg w) (-Real.pi)
  have e1 : -Real.pi + Complex.arg w + 2 * Real.pi = Real.pi + Complex.arg w := by ring
  have e2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [e1, e2] at h1
  rw [h1, intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo,
    TwoComponentCoulomb.integral_Ioo_log_norm_sub_circleMap a hr]

/-! ### Rotations about the centre -/

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- Rotations `y ↦ z + u (y - z)` (`‖u‖ = 1`) about the centre preserve integrals against
`δ_z^{(λ)}`. -/
theorem integral_comp_rotate_smearedCharge (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) {u : ℂ}
    (hu : ‖u‖ = 1) (f : ℂ → ℝ) :
    ∫ y, f (z + u * (y - z)) ∂smearedCharge χ z lam = ∫ y, f y ∂smearedCharge χ z lam := by
  conv_rhs => rw [← map_rotate_smearedCharge hχ z lam hu]
  rw [(measurableEmbedding_rotate z hu).integral_map]

/-- Rotations about the centre preserve integrability against `δ_z^{(λ)}`. -/
theorem integrable_comp_rotate_smearedCharge_iff (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) {u : ℂ}
    (hu : ‖u‖ = 1) (f : ℂ → ℝ) :
    Integrable (fun y => f (z + u * (y - z))) (smearedCharge χ z lam) ↔
      Integrable f (smearedCharge χ z lam) := by
  conv_rhs => rw [← map_rotate_smearedCharge hχ z lam hu]
  rw [(measurableEmbedding_rotate z hu).integrable_map_iff]
  rfl

/-! ### The potential of one smeared charge -/

/-- `y ↦ log ‖x - y‖` is integrable for `δ_z^{(λ)}`. -/
theorem integrable_log_norm_sub_smearedCharge (hχ : IsMollifier χ) (x z : ℂ) (lam : ℝ) :
    Integrable (fun y => Real.log ‖x - y‖) (smearedCharge χ z lam) := by
  have h := (integrable_logKernel_sub_smearedCharge hχ x z lam).neg
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [logKernel, norm_sub_rev]

/-- **Radial formula for the potential** (rotation averaging): for `λ > 0` and every `x`,
`∫ log ‖x - y‖ dδ_z^{(λ)}(y) = ∫ log (max ‖x - z‖ ‖y - z‖) dδ_z^{(λ)}(y)`. -/
theorem integral_log_norm_sub_smearedCharge_eq_max (hχ : IsMollifier χ) (x z : ℂ)
    (hlam : 0 < lam) :
    ∫ y, Real.log ‖x - y‖ ∂smearedCharge χ z lam =
      ∫ y, Real.log (max ‖x - z‖ ‖y - z‖) ∂smearedCharge χ z lam := by
  have hprob : IsProbabilityMeasure (smearedCharge χ z lam) :=
    isProbabilityMeasure_smearedCharge hχ z hlam
  set f : ℂ → ℝ := fun v => Real.log ‖x - v‖ with hf
  set F : ℝ → ℂ → ℝ :=
    fun θ y => Real.log ‖(x - z) - Complex.exp (θ * Complex.I) * (y - z)‖ with hF
  have hu : ∀ θ : ℝ, ‖Complex.exp (θ * Complex.I)‖ = 1 := fun θ => Complex.norm_exp_ofReal_mul_I θ
  have hFθ : ∀ θ : ℝ, F θ = fun y => f (z + Complex.exp (θ * Complex.I) * (y - z)) := by
    intro θ
    funext y
    simp only [hF, hf]
    congr 2
    ring
  have hint0 : Integrable f (smearedCharge χ z lam) :=
    integrable_log_norm_sub_smearedCharge hχ x z lam
  have hrot : ∀ θ : ℝ, ∫ y, F θ y ∂smearedCharge χ z lam = ∫ y, f y ∂smearedCharge χ z lam :=
    fun θ => by rw [hFθ θ, integral_comp_rotate_smearedCharge hχ z lam (hu θ)]
  have hFint : ∀ θ : ℝ, Integrable (F θ) (smearedCharge χ z lam) := fun θ => by
    rw [hFθ θ]
    exact (integrable_comp_rotate_smearedCharge_iff hχ z lam (hu θ) f).2 hint0
  have hFnorm : ∀ θ : ℝ, ∫ y, ‖F θ y‖ ∂smearedCharge χ z lam =
      ∫ y, ‖f y‖ ∂smearedCharge χ z lam := fun θ => by
    rw [hFθ θ]
    exact integral_comp_rotate_smearedCharge hχ z lam (hu θ) (fun v => ‖f v‖)
  have hmeas : Measurable (Function.uncurry F) := by
    have hc : Continuous fun p : ℝ × ℂ =>
        ‖(x - z) - Complex.exp (p.1 * Complex.I) * (p.2 - z)‖ := by fun_prop
    exact Real.measurable_log.comp hc.measurable
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioo (-Real.pi) Real.pi)).prod (smearedCharge χ z lam)) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun θ => hFint θ, ?_⟩
    simp only [Function.uncurry_apply_pair, hFnorm]
    exact integrable_const _
  have hswap := integral_integral_swap hint
  simp only [hrot] at hswap
  rw [setIntegral_const, Real.volume_real_Ioo, smul_eq_mul] at hswap
  have hin : ∀ y : ℂ, ∫ θ in Ioo (-Real.pi) Real.pi, F θ y =
      2 * Real.pi * Real.log (max ‖x - z‖ ‖y - z‖) := fun y => by
    simp only [hF]
    rw [integral_Ioo_log_norm_sub_exp_mul, max_comm]
  simp only [hin] at hswap
  rw [integral_const_mul, max_eq_left (by linarith [Real.pi_pos]),
    show Real.pi - -Real.pi = 2 * Real.pi by ring] at hswap
  exact mul_left_cancel₀ (by positivity) hswap

/-! ### Elementary facts on the logarithm -/

/-- `|log (max A B)| ≤ |log A| + |log B|`. -/
theorem abs_log_max_le (A B : ℝ) : |Real.log (max A B)| ≤ |Real.log A| + |Real.log B| := by
  rcases max_choice A B with h | h <;> rw [h] <;>
    linarith [abs_nonneg (Real.log A), abs_nonneg (Real.log B)]

/-- `-log (max A B) = min (-log A) (-log B)` for `A, B > 0`. -/
theorem neg_log_max_eq_min {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    -Real.log (max A B) = min (-Real.log A) (-Real.log B) := by
  rcases le_total A B with h | h
  · rw [max_eq_right h, min_eq_right (neg_le_neg (Real.log_le_log hA h))]
  · rw [max_eq_left h, min_eq_left (neg_le_neg (Real.log_le_log hB h))]

/-- `g(t u) = g(t) + g(u)` for `t > 0` real and `u ≠ 0`. -/
theorem logKernel_ofReal_mul {t : ℝ} (ht : 0 < t) {u : ℂ} (hu : u ≠ 0) :
    logKernel ((t : ℂ) * u) = logKernel (t : ℂ) + logKernel u := by
  have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  simp only [logKernel, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
  rw [Real.log_mul ht.ne' hu']
  ring

/-- `g(t) = -log t` for `t > 0`. -/
theorem logKernel_ofReal {t : ℝ} (ht : 0 < t) : logKernel (t : ℂ) = -Real.log t := by
  simp [logKernel, abs_of_pos ht]

/-! ### Atoms and integrability -/

/-- Every point is `δ_z^{(λ)}`-null: almost every `y` differs from a given `w`. -/
theorem ae_ne_smearedCharge (χ : ℂ → ℝ) (z w : ℂ) (lam : ℝ) :
    ∀ᵐ y ∂smearedCharge χ z lam, y ≠ w := by
  rw [ae_iff]
  have h : {a : ℂ | ¬a ≠ w} = {w} := by
    ext a
    simp
  rw [h]
  exact smearedCharge_singleton χ z w lam

/-- `y ↦ log (max s ‖y - z‖)` is integrable for `δ_z^{(λ)}`. -/
theorem integrable_log_max_norm_sub_smearedCharge (hχ : IsMollifier χ) (s : ℝ) (z : ℂ)
    (lam : ℝ) :
    Integrable (fun y => Real.log (max s ‖y - z‖)) (smearedCharge χ z lam) := by
  have := isFiniteMeasure_smearedCharge hχ z lam
  have h0 : Integrable (fun y => Real.log ‖y - z‖) (smearedCharge χ z lam) := by
    refine (integrable_log_norm_sub_smearedCharge hχ z z lam).congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp [norm_sub_rev]
  have hm : Measurable fun y : ℂ => Real.log (max s ‖y - z‖) := by
    have : Continuous fun y : ℂ => max s ‖y - z‖ := by fun_prop
    exact Real.measurable_log.comp this.measurable
  refine Integrable.mono' ((integrable_const |Real.log s|).add h0.abs) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_log_max_le _ _

/-! ### The potential of one smeared charge -/

/-- **Radial formula for the potential** `U_{z,λ}(x) = ∫ g(x - y) dδ_z^{(λ)}(y)`: for `λ > 0` and
every `x`, `U_{z,λ}(x) = ∫ -log (max ‖x - z‖ ‖y - z‖) dδ_z^{(λ)}(y)`. -/
theorem integral_logKernel_sub_smearedCharge_eq_max (hχ : IsMollifier χ) (x z : ℂ)
    (hlam : 0 < lam) :
    ∫ y, logKernel (x - y) ∂smearedCharge χ z lam =
      ∫ y, -Real.log (max ‖x - z‖ ‖y - z‖) ∂smearedCharge χ z lam := by
  simp only [logKernel]
  rw [integral_neg, integral_neg, integral_log_norm_sub_smearedCharge_eq_max hχ x z hlam]

/-- **Radial formula for the potential**, `min` form: for `λ > 0` and `x ≠ z`,
`U_{z,λ}(x) = ∫ min (g(x - z), g(y - z)) dδ_z^{(λ)}(y)`. -/
theorem integral_logKernel_sub_smearedCharge_eq_min (hχ : IsMollifier χ) {x z : ℂ} (hx : x ≠ z)
    (hlam : 0 < lam) :
    ∫ y, logKernel (x - y) ∂smearedCharge χ z lam =
      ∫ y, min (logKernel (x - z)) (logKernel (y - z)) ∂smearedCharge χ z lam := by
  rw [integral_logKernel_sub_smearedCharge_eq_max hχ x z hlam]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_smearedCharge χ z z lam] with y hy
  exact neg_log_max_eq_min (norm_pos_iff.2 (sub_ne_zero.2 hx)) (norm_pos_iff.2 (sub_ne_zero.2 hy))

/-- **Radial formula for the potential**, profile form: `U_{z,λ}(x)` only depends on `‖x - z‖`,
`U_{z,λ}(x) = ∫ -log (max ‖x - z‖ ‖y‖) dδ_0^{(λ)}(y)`. -/
theorem integral_logKernel_sub_smearedCharge_eq_profile (hχ : IsMollifier χ) (x z : ℂ)
    (hlam : 0 < lam) :
    ∫ y, logKernel (x - y) ∂smearedCharge χ z lam =
      ∫ y, -Real.log (max ‖x - z‖ ‖y‖) ∂smearedCharge χ 0 lam := by
  rw [integral_logKernel_sub_smearedCharge_eq_max hχ x z hlam]
  have h := map_add_right_smearedCharge χ 0 z lam
  rw [zero_add] at h
  rw [← h, (measurableEmbedding_addRight z).integral_map]
  simp

/-- **Newton's theorem**: outside the support, `‖x - z‖ ≥ λ`, the potential of `δ_z^{(λ)}` is that
of a point charge at `z`: `U_{z,λ}(x) = g(x - z)`. -/
theorem integral_logKernel_sub_smearedCharge_of_le (hχ : IsMollifier χ) {x z : ℂ}
    (hlam : 0 < lam) (hx : lam ≤ ‖x - z‖) :
    ∫ y, logKernel (x - y) ∂smearedCharge χ z lam = logKernel (x - z) := by
  have hprob : IsProbabilityMeasure (smearedCharge χ z lam) :=
    isProbabilityMeasure_smearedCharge hχ z hlam
  rw [integral_logKernel_sub_smearedCharge_eq_max hχ x z hlam]
  have h : ∀ᵐ y ∂smearedCharge χ z lam,
      -Real.log (max ‖x - z‖ ‖y - z‖) = logKernel (x - z) := by
    filter_upwards [ae_mem_closedBall_smearedCharge hχ hlam] with y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [max_eq_left (hy.trans hx)]
    rfl
  rw [integral_congr_ae h, integral_const, probReal_univ, one_smul]

/-- The potential is dominated by that of a point charge: `U_{z,λ}(x) ≤ g(x - z)` for `x ≠ z`. -/
theorem integral_logKernel_sub_smearedCharge_le (hχ : IsMollifier χ) {x z : ℂ} (hx : x ≠ z)
    (hlam : 0 < lam) :
    ∫ y, logKernel (x - y) ∂smearedCharge χ z lam ≤ logKernel (x - z) := by
  have hprob : IsProbabilityMeasure (smearedCharge χ z lam) :=
    isProbabilityMeasure_smearedCharge hχ z hlam
  have hA : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  rw [integral_logKernel_sub_smearedCharge_eq_max hχ x z hlam]
  calc ∫ y, -Real.log (max ‖x - z‖ ‖y - z‖) ∂smearedCharge χ z lam
      ≤ ∫ _, logKernel (x - z) ∂smearedCharge χ z lam :=
        integral_mono (integrable_log_max_norm_sub_smearedCharge hχ _ z lam).neg
          (integrable_const _) fun y =>
            neg_le_neg (Real.log_le_log hA (le_max_left _ _))
    _ = logKernel (x - z) := by rw [integral_const, probReal_univ, one_smul]

/-- The potential is maximal at the centre: `U_{z,λ}(x) ≤ U_{z,λ}(z) = ∫ g(y - z) dδ_z^{(λ)}(y)`. -/
theorem integral_logKernel_sub_smearedCharge_le_center (hχ : IsMollifier χ) (x z : ℂ)
    (hlam : 0 < lam) :
    ∫ y, logKernel (x - y) ∂smearedCharge χ z lam ≤
      ∫ y, logKernel (y - z) ∂smearedCharge χ z lam := by
  rw [integral_logKernel_sub_smearedCharge_eq_max hχ x z hlam]
  refine integral_mono_ae (integrable_log_max_norm_sub_smearedCharge hχ _ z lam).neg
    (integrable_logKernel_sub_smearedCharge hχ z z lam) ?_
  filter_upwards [ae_ne_smearedCharge χ z z lam] with y hy
  exact neg_le_neg (Real.log_le_log (norm_pos_iff.2 (sub_ne_zero.2 hy)) (le_max_right _ _))

/-- The value at the centre, by scaling: `∫ g(y - z) dδ_z^{(λ)}(y) = g(λ) + c_χ` with the explicit
constant `c_χ = ∫ g dδ_0^{(1)} = ∫ g χ`. -/
theorem integral_logKernel_sub_center_smearedCharge (hχ : IsMollifier χ) (z : ℂ)
    (hlam : 0 < lam) :
    ∫ y, logKernel (y - z) ∂smearedCharge χ z lam =
      logKernel (lam : ℂ) + ∫ y, logKernel y ∂smearedCharge χ 0 1 := by
  have hprob : IsProbabilityMeasure (smearedCharge χ 0 1) :=
    isProbabilityMeasure_smearedCharge hχ 0 one_pos
  rw [integral_smearedCharge_eq_integral_one hχ z hlam]
  have h : ∀ᵐ y ∂smearedCharge χ 0 1,
      logKernel (z + (lam : ℂ) * y - z) = logKernel (lam : ℂ) + logKernel y := by
    filter_upwards [ae_ne_smearedCharge χ 0 0 1] with y hy
    rw [add_sub_cancel_left, logKernel_ofReal_mul hlam hy]
  have hint : Integrable (fun y => logKernel y) (smearedCharge χ 0 1) := by
    simpa using integrable_logKernel_sub_smearedCharge hχ 0 0 1
  rw [integral_congr_ae h, integral_add (integrable_const _) hint, integral_const, probReal_univ,
    one_smul]

/-! ### Continuity of the potential -/

/-- The radial profile `s ↦ ∫ -log (max s ‖y‖) dδ_0^{(λ)}(y)` of the potential is continuous on
`ℝ` (for every `λ`). -/
theorem continuous_integral_neg_log_max_smearedCharge (hχ : IsMollifier χ) (lam : ℝ) :
    Continuous fun s : ℝ => ∫ y, -Real.log (max s ‖y‖) ∂smearedCharge χ 0 lam := by
  have h0 : Integrable (fun y => Real.log ‖y‖) (smearedCharge χ 0 lam) := by
    simpa using integrable_log_norm_sub_smearedCharge hχ 0 0 lam
  have := isFiniteMeasure_smearedCharge hχ 0 lam
  rw [continuous_iff_continuousAt]
  intro s₀
  set S : ℝ := |s₀| + 1 with hS
  refine continuousAt_of_dominated (bound := fun y => |Real.log ‖y‖| + |Real.log S|) ?_ ?_
    (h0.abs.add (integrable_const _)) ?_
  · refine Filter.Eventually.of_forall fun s => ?_
    have : Continuous fun y : ℂ => max s ‖y‖ := by fun_prop
    exact (Real.measurable_log.comp this.measurable).neg.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds s₀ one_pos] with s hs
    filter_upwards [ae_ne_smearedCharge χ 0 0 lam] with y hy
    have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hsS : s ≤ S := by
      rw [Real.ball_eq_Ioo, mem_Ioo] at hs
      linarith [le_abs_self s₀]
    rw [norm_neg, Real.norm_eq_abs]
    rcases max_choice s ‖y‖ with h | h
    · rw [h]
      have hys : ‖y‖ ≤ s := h ▸ le_max_right s ‖y‖
      have h1 : Real.log ‖y‖ ≤ Real.log s := Real.log_le_log hy0 hys
      have h2 : Real.log s ≤ Real.log S := Real.log_le_log (hy0.trans_le hys) hsS
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log ‖y‖), abs_nonneg (Real.log S)]
      · linarith [le_abs_self (Real.log S), abs_nonneg (Real.log ‖y‖)]
    · rw [h]
      linarith [abs_nonneg (Real.log S)]
  · filter_upwards [ae_ne_smearedCharge χ 0 0 lam] with y hy
    have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
    have : Continuous fun s : ℝ => -Real.log (max s ‖y‖) :=
      ((continuous_id.max continuous_const).log fun s =>
        (hy0.trans_le (le_max_right s ‖y‖)).ne').neg
    exact this.continuousAt

/-- The potential `x ↦ U_{z,λ}(x) = ∫ g(x - y) dδ_z^{(λ)}(y)` is continuous, for `λ > 0`. -/
theorem continuous_integral_logKernel_sub_smearedCharge (hχ : IsMollifier χ) (z : ℂ)
    (hlam : 0 < lam) :
    Continuous fun x => ∫ y, logKernel (x - y) ∂smearedCharge χ z lam := by
  have h : (fun x => ∫ y, logKernel (x - y) ∂smearedCharge χ z lam) =
      (fun s : ℝ => ∫ y, -Real.log (max s ‖y‖) ∂smearedCharge χ 0 lam) ∘ fun x => ‖x - z‖ := by
    funext x
    exact integral_logKernel_sub_smearedCharge_eq_profile hχ x z hlam
  rw [h]
  exact (continuous_integral_neg_log_max_smearedCharge hχ lam).comp (by fun_prop)

end MultipoleBKT

end
