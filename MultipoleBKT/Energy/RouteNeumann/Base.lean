/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.ElectricEnergy
import TwoComponentCoulomb.Potential.DiscField

/-!
# The screened objects and their elementary API

The definitions implement the image-charge potential in (3.16) and (3.20). The potential has an arbitrary additive
constant. The Green average and its zero-mean normalization are identified
with it in `RouteNeumann.GreenAverage` and `RouteNeumann.Identification`.

This lower module keeps the displayed Green kernel independent of the weak
Neumann theory. The public import paths are `Energy.Screened` and
`Energy.ScreenedNeumann`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ}

/-! ### The image charge of a point in a disc -/

/-- The barycentre `z = (x + y) / 2` of the dipole `d = (x, y)` (equation (3.16)). -/
noncomputable def dipoleMidpoint (d : ℂ × ℂ) : ℂ := (d.1 + d.2) / 2

/-- The field at `w` of the image charge of a unit charge at `a` for the disc `B(z, τ)`:
`(a - z) / (τ² - conj (w - z) (a - z))`, the gradient of `screenedImagePotential z τ a`
(equation (3.19), scaled from the unit disc). -/
noncomputable def screenedImageField (z : ℂ) (τ : ℝ) (a w : ℂ) : ℂ :=
  (a - z) / ((τ : ℂ) ^ 2 - conj (w - z) * (a - z))

/-- The potential `-log |τ² - (w - z) conj (a - z)|` of the image charge of a unit charge at `a`
for the disc `B(z, τ)` (equation (3.19), scaled from the unit disc:
`-log |1 - x ȳ|` with `x = (w - z)/τ`, `y = (a - z)/τ`, up to the constant `log τ²`). -/
noncomputable def screenedImagePotential (z : ℂ) (τ : ℝ) (a w : ℂ) : ℝ :=
  -Real.log ‖(τ : ℂ) ^ 2 - (w - z) * conj (a - z)‖

/-- The image point `a* = z + τ² / conj (a - z)` of `a` in the circle `∂B(z, τ)` (the display before (3.19)). -/
noncomputable def imagePoint (z : ℂ) (τ : ℝ) (a : ℂ) : ℂ :=
  z + (τ : ℂ) ^ 2 / conj (a - z)

theorem norm_ofReal_sq (τ : ℝ) : ‖(τ : ℂ) ^ 2‖ = τ ^ 2 := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `|a* - z| = τ² / |a - z|`. -/
theorem norm_imagePoint_sub (z : ℂ) (τ : ℝ) (a : ℂ) :
    ‖imagePoint z τ a - z‖ = τ ^ 2 / ‖a - z‖ := by
  rw [imagePoint, add_sub_cancel_left, norm_div, norm_ofReal_sq, Complex.norm_conj]

/-- **The image field is a point field**: for `a ≠ z`, the image field is the field
`-(w - a*) / |w - a*|²` of a unit point charge at the image point `a*`. -/
theorem screenedImageField_eq_of_ne {z a : ℂ} (τ : ℝ) (ha : a ≠ z) (w : ℂ) :
    screenedImageField z τ a w =
      -((‖w - imagePoint z τ a‖ ^ 2)⁻¹ : ℝ) • (w - imagePoint z τ a) := by
  have hb : a - z ≠ 0 := sub_ne_zero.2 ha
  rw [TwoComponentCoulomb.gradLogKernel_eq_neg_conj_inv, map_inv₀, screenedImageField,
    imagePoint]
  have e : conj (w - (z + (τ : ℂ) ^ 2 / conj (a - z))) =
      (conj (w - z) * (a - z) - (τ : ℂ) ^ 2) / (a - z) := by
    rw [map_sub, map_add, map_div₀, Complex.conj_conj, map_pow, Complex.conj_ofReal, map_sub]
    field_simp
    ring
  rw [e, inv_div, ← div_neg, neg_sub]

/-- The denominator of the image field does not vanish when `|w - z| |a - z| < τ²`. -/
theorem screenedImage_denom_ne_zero {z a w : ℂ} {τ : ℝ} (h : ‖w - z‖ * ‖a - z‖ < τ ^ 2) :
    (τ : ℂ) ^ 2 - conj (w - z) * (a - z) ≠ 0 := by
  intro h0
  rw [sub_eq_zero] at h0
  have := congrArg norm h0
  rw [norm_ofReal_sq, norm_mul, Complex.norm_conj] at this
  linarith

/-- The argument of the logarithm in the image potential does not vanish when
`|w - z| |a - z| < τ²`. -/
theorem screenedImagePotential_arg_ne_zero {z a w : ℂ} {τ : ℝ}
    (h : ‖w - z‖ * ‖a - z‖ < τ ^ 2) : (τ : ℂ) ^ 2 - (w - z) * conj (a - z) ≠ 0 := by
  intro h0
  rw [sub_eq_zero] at h0
  have := congrArg norm h0
  rw [norm_ofReal_sq, norm_mul, Complex.norm_conj] at this
  linarith

/-- The image field is continuous where its denominator does not vanish. -/
theorem continuousAt_screenedImageField {z a w : ℂ} {τ : ℝ}
    (h : (τ : ℂ) ^ 2 - conj (w - z) * (a - z) ≠ 0) :
    ContinuousAt (screenedImageField z τ a) w := by
  unfold screenedImageField
  refine continuousAt_const.div ?_ h
  exact (continuousAt_const.sub
    ((Complex.continuous_conj.comp (continuous_id.sub continuous_const)).continuousAt.mul
      continuousAt_const))

/-- The image field is measurable. -/
theorem measurable_screenedImageField (z : ℂ) (τ : ℝ) (a : ℂ) :
    Measurable (screenedImageField z τ a) := by
  unfold screenedImageField
  exact measurable_const.div (measurable_const.sub
    ((Complex.continuous_conj.comp (continuous_id.sub continuous_const)).measurable.mul
      measurable_const))

/-- **`∇(image potential) = image field`**, away from the image point. -/
theorem hasFDerivAt_screenedImagePotential {z a w : ℂ} {τ : ℝ}
    (h : (τ : ℂ) ^ 2 - (w - z) * conj (a - z) ≠ 0) :
    HasFDerivAt (screenedImagePotential z τ a) (toDual ℝ ℂ (screenedImageField z τ a w)) w := by
  set c : ℂ := conj (a - z) with hc
  set F : ℂ → ℂ := fun x => (τ : ℂ) ^ 2 - (x - z) * c with hF
  have hd : HasDerivAt F (-(1 * c)) w :=
    (((hasDerivAt_id w).sub_const z).mul_const c).const_sub ((τ : ℂ) ^ 2)
  have hF' := hd.hasFDerivAt.restrictScalars ℝ
  have h2 := (hasFDerivAt_neg_log_norm h).comp w hF'
  refine h2.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    toDual_apply_apply, Complex.inner, smul_eq_mul]
  congr 1
  have h' : (τ : ℂ) ^ 2 - conj (w - z) * (a - z) ≠ 0 := by
    intro h0
    apply h
    have := congrArg conj h0
    simpa [hc, mul_comm] using this
  rw [TwoComponentCoulomb.gradLogKernel_eq_neg_conj_inv]
  simp only [screenedImageField, map_neg, map_inv₀, map_div₀, map_sub, map_mul, map_pow,
    Complex.conj_ofReal, Complex.conj_conj, hc] at h h' ⊢
  field_simp

/-- The image potential is `C¹` away from the image point. -/
theorem contDiffAt_screenedImagePotential {z a w : ℂ} {τ : ℝ}
    (h : (τ : ℂ) ^ 2 - (w - z) * conj (a - z) ≠ 0) :
    ContDiffAt ℝ 1 (screenedImagePotential z τ a) w := by
  have hF : ContDiff ℝ 1 fun x : ℂ => (τ : ℂ) ^ 2 - (x - z) * conj (a - z) := by
    have : ContDiff ℝ 1 fun x : ℂ => (x - z) * conj (a - z) :=
      (contDiff_id.sub contDiff_const).mul contDiff_const
    exact contDiff_const.sub this
  have hn := (contDiffAt_norm ℝ h).comp w hF.contDiffAt
  exact (hn.log (norm_ne_zero_iff.2 h)).neg

/-- **The Neumann identity for one point charge** (the display after (3.19), scaled): on the circle
`|w - z| = τ`, for `|a - z| < τ`, the point field of `a` plus its image field has
`(w - z) · (·) = -1`, i.e. normal derivative `-1/τ`. -/
theorem inner_sub_add_screenedImageField_eq {z a w : ℂ} {τ : ℝ} (hw : ‖w - z‖ = τ) (hτ : 0 < τ)
    (ha : ‖a - z‖ < τ) :
    inner ℝ (w - z) (-((‖w - a‖ ^ 2)⁻¹ : ℝ) • (w - a) + screenedImageField z τ a w) = -1 := by
  set p := w - z with hp'
  set b := a - z with hb'
  have hwa : w - a = p - b := by rw [hp', hb']; ring
  rw [hwa, screenedImageField, ← hb']
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    linarith
  have hpb : p - b ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0] at hw
    linarith
  have hpbc : conj p - conj b ≠ 0 := by
    rw [← map_sub]
    exact (map_ne_zero _).2 hpb
  have hA : (τ : ℂ) ^ 2 - conj p * b ≠ 0 := by
    have := screenedImage_denom_ne_zero (w := w) (z := z) (a := a) (τ := τ) (by
      rw [← hp', ← hb', hw, sq]
      exact mul_lt_mul_of_pos_left ha hτ)
    rwa [← hp', ← hb'] at this
  have hAc : (τ : ℂ) ^ 2 - conj b * p ≠ 0 := by
    intro h0
    apply hA
    have := congrArg conj h0
    simpa [map_sub, map_mul, mul_comm] using this
  have hpp : p * conj p = (τ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    push_cast
    ring
  rw [Complex.inner, TwoComponentCoulomb.gradLogKernel_eq_neg_conj_inv]
  have key : (-conj (p - b)⁻¹ + b / ((τ : ℂ) ^ 2 - conj p * b)) * conj p =
      conj (-((τ : ℂ) ^ 2 / ((τ : ℂ) ^ 2 - conj p * b))) +
        conj p * b / ((τ : ℂ) ^ 2 - conj p * b) := by
    simp only [map_neg, map_div₀, map_sub, map_pow, Complex.conj_ofReal, map_mul,
      Complex.conj_conj, map_inv₀]
    field_simp
    linear_combination ((τ : ℂ) ^ 2 * conj b - conj p * b * conj b) * hpp
  rw [key, Complex.add_re, Complex.conj_re, ← Complex.add_re]
  have e : -((τ : ℂ) ^ 2 / ((τ : ℂ) ^ 2 - conj p * b)) +
      conj p * b / ((τ : ℂ) ^ 2 - conj p * b) = -1 := by
    field_simp
    ring
  rw [e]
  simp

/-! ### The screened dipole field -/

/-- The potential `h = g * (δ_x^{(λ)} - δ_y^{(λ)})` of the dipole `d = (x, y)` (equation (2.55), for one dipole). -/
noncomputable def dipolePotential (χ : ℂ → ℝ) (lam : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℝ :=
  (∫ v, logKernel (w - v) ∂smearedCharge χ d.1 lam) -
    ∫ v, logKernel (w - v) ∂smearedCharge χ d.2 lam

/-- The field `∇h = ∇(g * δ₀^{(λ)})(· - x) - ∇(g * δ₀^{(λ)})(· - y)` of the dipole `d = (x, y)`. -/
noncomputable def dipoleField (χ : ℂ → ℝ) (lam : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℂ :=
  smearedField χ lam (w - d.1) - smearedField χ lam (w - d.2)

/-- The correction `ũ = u - g * (δ_x^{(λ)} - δ_y^{(λ)})` of Lemma 3.5 (equation (3.20)) for
the dipole `d = (x, y)` and the disc `B(z, τ)`, `z` the barycentre: the potential of the image
charges of `x` and `y`. -/
noncomputable def screenedCorrection (τ : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℝ :=
  screenedImagePotential (dipoleMidpoint d) τ d.1 w -
    screenedImagePotential (dipoleMidpoint d) τ d.2 w

/-- The field `∇ũ` of the image charges of the dipole `d` for the disc `B(z, τ)`. -/
noncomputable def screenedCorrectionField (τ : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℂ :=
  screenedImageField (dipoleMidpoint d) τ d.1 w - screenedImageField (dipoleMidpoint d) τ d.2 w

/-- **The screened dipole potential** `u = h + ũ`: the image-charge solution of the Neumann
problem (3.16) in `B(z, τ)` (the weak form is
`MultipoleBKT.integral_fderiv_apply_screenedField` and the boundary condition
`inner_screenedField_eq_zero`). -/
noncomputable def screenedPotential (χ : ℂ → ℝ) (lam τ : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℝ :=
  dipolePotential χ lam d w + screenedCorrection τ d w

/-- **The screened dipole field** `∇u = ∇h + ∇ũ` (`hasGradientAt_screenedPotential`). -/
noncomputable def screenedField (χ : ℂ → ℝ) (lam τ : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℂ :=
  dipoleField χ lam d w + screenedCorrectionField τ d w

/-- **The interaction of the energy upper bound**, equation (3.18):
`ṽ_ij = (1/2π) ∫_{B(z_i,τ) ∩ B(z_j,τ)} ∇u_i · ∇u_j` for `d = (x_i, y_i)`, `e = (x_j, y_j)`. -/
noncomputable def screenedInteraction (χ : ℂ → ℝ) (lam τ : ℝ) (d e : ℂ × ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ w in ball (dipoleMidpoint d) τ ∩ ball (dipoleMidpoint e) τ,
    inner ℝ (screenedField χ lam τ d w) (screenedField χ lam τ e w)

/-- **Definition 3.11**: `ṽ_ij` with the screening radius
`τ₀ = 8 ε₀ R`, where `R` stands for the truncation scale `R̄_{β,λ}` (Definition 2.18). -/
noncomputable def upperBoundInteraction (χ : ℂ → ℝ) (lam ε₀ R : ℝ) (d e : ℂ × ℂ) : ℝ :=
  screenedInteraction χ lam (8 * ε₀ * R) d e

/-- The dipole potential is that of the one-dipole configuration. -/
theorem dipolePotential_eq_electricPotential (χ : ℂ → ℝ) (lam : ℝ) (d : ℂ × ℂ) :
    dipolePotential χ lam d = electricPotential χ (dipoleCharge 1)
      (dipoleCentre fun _ : Fin 1 => d) fun _ => lam := by
  funext w
  simp [dipolePotential, electricPotential, dipoleCharge, dipoleCentre, Fintype.sum_sum_type,
    sub_eq_add_neg]

/-- The dipole field is that of the one-dipole configuration. -/
theorem dipoleField_eq_electricField (χ : ℂ → ℝ) (lam : ℝ) (d : ℂ × ℂ) :
    dipoleField χ lam d = electricField χ (dipoleCharge 1)
      (dipoleCentre fun _ : Fin 1 => d) fun _ => lam := by
  funext w
  simp [dipoleField, electricField, dipoleCharge, dipoleCentre, Fintype.sum_sum_type,
    sub_eq_add_neg]

/-! ### The geometry of the screening disc -/

section Geometry

variable {lam τ : ℝ} {d : ℂ × ℂ}

theorem fst_sub_dipoleMidpoint (d : ℂ × ℂ) : d.1 - dipoleMidpoint d = (d.1 - d.2) / 2 := by
  rw [dipoleMidpoint]
  ring

theorem snd_sub_dipoleMidpoint (d : ℂ × ℂ) : d.2 - dipoleMidpoint d = -((d.1 - d.2) / 2) := by
  rw [dipoleMidpoint]
  ring

theorem norm_fst_sub_dipoleMidpoint (d : ℂ × ℂ) :
    ‖d.1 - dipoleMidpoint d‖ = ‖d.2 - d.1‖ / 2 := by
  rw [fst_sub_dipoleMidpoint, norm_div, norm_sub_rev]
  norm_num

theorem norm_snd_sub_dipoleMidpoint (d : ℂ × ℂ) :
    ‖d.2 - dipoleMidpoint d‖ = ‖d.2 - d.1‖ / 2 := by
  rw [snd_sub_dipoleMidpoint, norm_neg, norm_div, norm_sub_rev]
  norm_num

theorem dipoleMidpoint_swap (d : ℂ × ℂ) : dipoleMidpoint d.swap = dipoleMidpoint d := by
  simp [dipoleMidpoint, add_comm]

/-- The standing assumption `τ ≥ 8 max(r, λ)`, `λ > 0` of Lemma 3.4 gives `τ > 0`. -/
theorem pos_of_screening (hlam : 0 < lam) (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) : 0 < τ := by
  have := le_max_right ‖d.2 - d.1‖ lam
  linarith

theorem norm_le_of_screening (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) : ‖d.2 - d.1‖ ≤ τ / 8 := by
  have := le_max_left ‖d.2 - d.1‖ lam
  linarith

theorem lam_le_of_screening (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) : lam ≤ τ / 8 := by
  have := le_max_right ‖d.2 - d.1‖ lam
  linarith

/-- On `B(z, 2τ)` neither image charge is reached: `|w - z| |a - z| < τ²` for `a ∈ {x, y}`. -/
theorem mul_norm_lt_of_screening (hlam : 0 < lam) (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ}
    (hw : ‖w - dipoleMidpoint d‖ < 2 * τ) :
    ‖w - dipoleMidpoint d‖ * ‖d.1 - dipoleMidpoint d‖ < τ ^ 2 ∧
      ‖w - dipoleMidpoint d‖ * ‖d.2 - dipoleMidpoint d‖ < τ ^ 2 := by
  have hτ0 := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have key : ‖w - dipoleMidpoint d‖ * (‖d.2 - d.1‖ / 2) < τ ^ 2 := by
    calc ‖w - dipoleMidpoint d‖ * (‖d.2 - d.1‖ / 2) ≤ 2 * τ * (τ / 16) := by
          refine mul_le_mul hw.le (by linarith) (by positivity) (by linarith)
      _ < τ ^ 2 := by nlinarith
  rw [norm_fst_sub_dipoleMidpoint, norm_snd_sub_dipoleMidpoint]
  exact ⟨key, key⟩

/-- Outside `B̄(z, 3τ/16)` the smeared charges of the dipole act as point charges:
`|w - a| > λ` for `a ∈ {x, y}` when `|w - z| ≥ τ / 2`. -/
theorem lam_lt_norm_sub_of_screening (hlam : 0 < lam) (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ)
    {w a : ℂ} (ha : ‖a - dipoleMidpoint d‖ = ‖d.2 - d.1‖ / 2)
    (hw : τ / 2 ≤ ‖w - dipoleMidpoint d‖) : lam < ‖w - a‖ := by
  have hτ0 := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have hl := lam_le_of_screening hτ
  have h1 : ‖w - dipoleMidpoint d‖ ≤ ‖w - a‖ + ‖a - dipoleMidpoint d‖ := by
    simpa using norm_add_le (w - a) (a - dipoleMidpoint d)
  linarith

end Geometry

/-! ### Regularity of the screened field -/

section Regularity

variable {lam τ : ℝ} {d : ℂ × ℂ}

/-- `∇ũ = screenedCorrectionField` on `B(z, 2τ)`. -/
theorem hasFDerivAt_screenedCorrection (hlam : 0 < lam) (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ)
    {w : ℂ} (hw : ‖w - dipoleMidpoint d‖ < 2 * τ) :
    HasFDerivAt (screenedCorrection τ d) (toDual ℝ ℂ (screenedCorrectionField τ d w)) w := by
  obtain ⟨h1, h2⟩ := mul_norm_lt_of_screening hlam hτ hw
  have := (hasFDerivAt_screenedImagePotential (screenedImagePotential_arg_ne_zero h1)).sub
    (hasFDerivAt_screenedImagePotential (screenedImagePotential_arg_ne_zero h2))
  rw [screenedCorrectionField, map_sub]
  exact this

/-- `ũ` is `C¹` on `B(z, 2τ)`. -/
theorem contDiffOn_screenedCorrection (hlam : 0 < lam) (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ContDiffOn ℝ 1 (screenedCorrection τ d) (ball (dipoleMidpoint d) (2 * τ)) := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  obtain ⟨h1, h2⟩ := mul_norm_lt_of_screening hlam hτ hw
  exact ((contDiffAt_screenedImagePotential (screenedImagePotential_arg_ne_zero h1)).sub
    (contDiffAt_screenedImagePotential (screenedImagePotential_arg_ne_zero h2))).contDiffWithinAt

/-- `∇ũ` is continuous on `B(z, 2τ)`. -/
theorem continuousOn_screenedCorrectionField (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ContinuousOn (screenedCorrectionField τ d) (ball (dipoleMidpoint d) (2 * τ)) := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  obtain ⟨h1, h2⟩ := mul_norm_lt_of_screening hlam hτ hw
  exact ((continuousAt_screenedImageField (screenedImage_denom_ne_zero h1)).sub
    (continuousAt_screenedImageField (screenedImage_denom_ne_zero h2))).continuousWithinAt

/-- `∇ũ` is measurable. -/
theorem measurable_screenedCorrectionField (τ : ℝ) (d : ℂ × ℂ) :
    Measurable (screenedCorrectionField τ d) :=
  (measurable_screenedImageField _ _ _).sub (measurable_screenedImageField _ _ _)

/-- `∇h` is the gradient of the dipole potential. -/
theorem hasGradientAt_dipolePotential (hχ : IsMollifier χ) (hlam : 0 < lam) (d : ℂ × ℂ)
    (w : ℂ) : HasGradientAt (dipolePotential χ lam d) (dipoleField χ lam d w) w := by
  rw [dipolePotential_eq_electricPotential, dipoleField_eq_electricField]
  exact hasGradientAt_electricPotential hχ (fun _ => hlam) w

/-- The dipole potential is `C¹`. -/
theorem contDiff_dipolePotential (hχ : IsMollifier χ) (hlam : 0 < lam) (d : ℂ × ℂ) :
    ContDiff ℝ 1 (dipolePotential χ lam d) := by
  rw [dipolePotential_eq_electricPotential]
  exact contDiff_electricPotential hχ fun _ => hlam

/-- The dipole field is continuous. -/
theorem continuous_dipoleField (hχ : IsMollifier χ) (hlam : 0 < lam) (d : ℂ × ℂ) :
    Continuous (dipoleField χ lam d) := by
  rw [dipoleField_eq_electricField]
  exact continuous_electricField hχ fun _ => hlam

/-- **`∇u = screenedField`** on `B(z, 2τ)`. -/
theorem hasGradientAt_screenedPotential (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ} (hw : ‖w - dipoleMidpoint d‖ < 2 * τ) :
    HasGradientAt (screenedPotential χ lam τ d) (screenedField χ lam τ d w) w := by
  rw [hasGradientAt_iff_hasFDerivAt, screenedField, map_add]
  exact (hasGradientAt_dipolePotential hχ hlam d w).hasFDerivAt.add
    (hasFDerivAt_screenedCorrection hlam hτ hw)

/-- The screened field is continuous on `B(z, 2τ)`. -/
theorem continuousOn_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ContinuousOn (screenedField χ lam τ d) (ball (dipoleMidpoint d) (2 * τ)) :=
  (continuous_dipoleField hχ hlam d).continuousOn.add
    (continuousOn_screenedCorrectionField hlam hτ)

/-- The screened field is measurable. -/
theorem measurable_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam) (τ : ℝ) (d : ℂ × ℂ) :
    Measurable (screenedField χ lam τ d) :=
  (continuous_dipoleField hχ hlam d).measurable.add (measurable_screenedCorrectionField τ d)

/-- **The Neumann boundary condition** `∂u/∂ν = 0` on `∂B(z, τ)` (equation (3.16)):
`(w - z) · ∇u(w) = 0` for `|w - z| = τ`. -/
theorem inner_screenedField_eq_zero (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ} (hw : ‖w - dipoleMidpoint d‖ = τ) :
    inner ℝ (w - dipoleMidpoint d) (screenedField χ lam τ d w) = 0 := by
  have hτ0 := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have hw2 : τ / 2 ≤ ‖w - dipoleMidpoint d‖ := by linarith
  have h1 := lam_lt_norm_sub_of_screening hlam hτ (norm_fst_sub_dipoleMidpoint d) hw2
  have h2 := lam_lt_norm_sub_of_screening hlam hτ (norm_snd_sub_dipoleMidpoint d) hw2
  have ha1 : ‖d.1 - dipoleMidpoint d‖ < τ := by rw [norm_fst_sub_dipoleMidpoint]; linarith
  have ha2 : ‖d.2 - dipoleMidpoint d‖ < τ := by rw [norm_snd_sub_dipoleMidpoint]; linarith
  have e : screenedField χ lam τ d w =
      (-((‖w - d.1‖ ^ 2)⁻¹ : ℝ) • (w - d.1) + screenedImageField (dipoleMidpoint d) τ d.1 w) -
        (-((‖w - d.2‖ ^ 2)⁻¹ : ℝ) • (w - d.2) + screenedImageField (dipoleMidpoint d) τ d.2 w) := by
    rw [screenedField, dipoleField, screenedCorrectionField, smearedField_of_lt hχ hlam h1,
      smearedField_of_lt hχ hlam h2]
    ring
  rw [e, inner_sub_right, inner_sub_add_screenedImageField_eq hw hτ0 ha1,
    inner_sub_add_screenedImageField_eq hw hτ0 ha2]
  ring

/-- Reversing the dipole (`x ↔ y`, same barycentre) reverses the screened field. -/
theorem screenedField_swap (χ : ℂ → ℝ) (lam τ : ℝ) (d : ℂ × ℂ) :
    screenedField χ lam τ d.swap = -screenedField χ lam τ d := by
  funext w
  simp only [screenedField, dipoleField, screenedCorrectionField, dipoleMidpoint_swap,
    Prod.fst_swap, Prod.snd_swap, Pi.neg_apply]
  ring

end Regularity

/-! ### The interaction `ṽ` -/

/-- `ṽ_ij = ṽ_ji`. -/
theorem screenedInteraction_comm (χ : ℂ → ℝ) (lam τ : ℝ) (d e : ℂ × ℂ) :
    screenedInteraction χ lam τ d e = screenedInteraction χ lam τ e d := by
  simp only [screenedInteraction, inter_comm (ball (dipoleMidpoint d) τ), real_inner_comm]

/-- `ṽ_ij` is odd in `x_i - y_i` at fixed barycentre (Section 4.9). -/
theorem screenedInteraction_swap_left (χ : ℂ → ℝ) (lam τ : ℝ) (d e : ℂ × ℂ) :
    screenedInteraction χ lam τ d.swap e = -screenedInteraction χ lam τ d e := by
  simp only [screenedInteraction, screenedField_swap, dipoleMidpoint_swap, Pi.neg_apply,
    inner_neg_left, integral_neg, mul_neg]

/-- `ṽ_ij = 0` when the screening discs are disjoint, `|z_i - z_j| ≥ 2τ`. -/
theorem screenedInteraction_eq_zero_of_le (χ : ℂ → ℝ) (lam τ : ℝ) {d e : ℂ × ℂ}
    (h : 2 * τ ≤ ‖dipoleMidpoint d - dipoleMidpoint e‖) :
    screenedInteraction χ lam τ d e = 0 := by
  have hdisj : ball (dipoleMidpoint d) τ ∩ ball (dipoleMidpoint e) τ = ∅ := by
    rw [← disjoint_iff_inter_eq_empty]
    refine ball_disjoint_ball ?_
    rw [dist_eq_norm]
    linarith
  simp [screenedInteraction, hdisj]

end MultipoleBKT

end
