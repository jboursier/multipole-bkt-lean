/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.MassProfile
public import TwoComponentCoulomb.Potential.Fundamental
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TwoComponentCoulomb.Potential.ElectricDecay
import TwoComponentCoulomb.Potential.SmearedCharge

/-!
# Weak Poisson equation before regularity

See Lemmas 3.1 and 3.2 of the paper.

The field here is the convolution of the locally integrable point field with
an admissible bounded measurable charge. Fubini and the weak fundamental-solution
identity prove its weak Poisson equation. No derivative of the smeared potential
is assumed, so this module can be imported by the regularity provider.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (logKernel)
open InnerProductSpace

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {α : ℝ}

/-- A function integrable on the disc `B(z, α + 1)` is integrable for `δ_z^{(α)}`, `α > 0`. -/
theorem integrable_smearedCharge_of_integrableOn {E : Type*} [NormedAddCommGroup E]
    (hχ : IsMollifier χ) {z : ℂ} (hα : 0 < α) {f : ℂ → E} (hf : IntegrableOn f (ball z (α + 1))) :
    Integrable f (smearedCharge χ z α) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  exact (Integrable.smul_measure (hf.mono_set (closedBall_subset_ball (lt_add_one α)))
    ENNReal.ofReal_ne_top).mono_measure (smearedCharge_le_smul_restrict hχ hM hα)

/-- `y ↦ |x - y|⁻¹` is integrable for `δ_z^{(α)}`, `α > 0`. -/
theorem integrable_inv_norm_sub_smearedCharge (hχ : IsMollifier χ) (x z : ℂ) (hα : 0 < α) :
    Integrable (fun y : ℂ => ‖x - y‖⁻¹) (smearedCharge χ z α) :=
  integrable_smearedCharge_of_integrableOn hχ hα
    (TwoComponentCoulomb.integrableOn_comp_sub_ball (f := fun w : ℂ => ‖w‖⁻¹)
      TwoComponentCoulomb.integrableOn_inv_norm_ball_zero x z (α + 1))

/-- Rotations `y ↦ z + u (y - z)` (`‖u‖ = 1`) about the centre preserve integrals against
`δ_z^{(α)}` (vector-valued form of `integral_comp_rotate_smearedCharge`). -/
theorem integral_comp_rotate_smearedCharge' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hχ : IsMollifier χ) (z : ℂ) (α : ℝ) {u : ℂ} (hu : ‖u‖ = 1) (f : ℂ → E) :
    ∫ y, f (z + u * (y - z)) ∂smearedCharge χ z α = ∫ y, f y ∂smearedCharge χ z α := by
  conv_rhs => rw [← map_rotate_smearedCharge hχ z α hu]
  rw [(measurableEmbedding_rotate z hu).integral_map]

/-- `∇(-log |x|) = -x / |x|²` at `x₀ ≠ 0`. -/
theorem hasFDerivAt_neg_log_norm {x₀ : ℂ} (hx₀ : x₀ ≠ 0) :
    HasFDerivAt (fun x : ℂ => -Real.log ‖x‖) (toDual ℝ ℂ (-(‖x₀‖ ^ 2)⁻¹ • x₀)) x₀ := by
  have hn : ‖x₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx₀)
  have h := ((hasStrictFDerivAt_norm_sq x₀).hasFDerivAt.log hn).const_mul (-(1 / 2 : ℝ))
  have hfun : (fun x : ℂ => -(1 / 2 : ℝ) * Real.log (‖x‖ ^ 2)) = fun x : ℂ => -Real.log ‖x‖ := by
    funext x
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun] at h
  refine h.congr_fderiv ?_
  ext v
  simp only [smul_apply, innerSL_apply_apply, toDual_apply_apply,
    smul_eq_mul, real_inner_smul_left, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp

/-- Circles are null for `δ_z^{(λ)}`: a.e. `|y| ≠ r`. -/
theorem ae_norm_ne_smearedCharge (χ : ℂ → ℝ) (z : ℂ) (lam r : ℝ) :
    ∀ᵐ y ∂smearedCharge χ z lam, ‖y‖ ≠ r := by
  rw [ae_iff]
  have h : {y : ℂ | ¬‖y‖ ≠ r} = sphere (0 : ℂ) r := by
    ext y
    simp
  rw [h]
  exact smearedCharge_absolutelyContinuous χ z lam (Measure.addHaar_sphere volume 0 r)

namespace RouteFlux

variable {χ : ℂ → ℝ} {α : ℝ}

/-- The locally integrable point field, defined on the whole plane. -/
noncomputable def pointField (w : ℂ) : ℂ := -((‖w‖ ^ 2)⁻¹ : ℝ) • w

/-- Convolution of the point field with a charge of bounded measurable density. -/
noncomputable def convolvedField (χ : ℂ → ℝ) (z : ℂ) (α : ℝ) (x : ℂ) : ℂ :=
  ∫ y, pointField (x - y) ∂smearedCharge χ z α

/-- Translating the source translates its convolution field. -/
theorem convolvedField_translate (χ : ℂ → ℝ) (z : ℂ) (α : ℝ) (x : ℂ) :
    convolvedField χ z α x = convolvedField χ 0 α (x - z) := by
  unfold convolvedField
  have he := map_add_right_smearedCharge χ 0 z α
  rw [zero_add] at he
  rw [← he, (measurableEmbedding_addRight z).integral_map]
  congr 1
  funext y
  congr 1
  ring

/-- The point field `y ↦ -(x - y) / |x - y|²` is integrable for `δ_z^{(α)}`, `α > 0`. -/
theorem integrable_gradLogKernel_sub_smearedCharge (hχ : IsMollifier χ) (x z : ℂ) (hα : 0 < α) :
    Integrable (fun y : ℂ => pointField (x - y)) (smearedCharge χ z α) :=
  integrable_smearedCharge_of_integrableOn hχ hα
    (TwoComponentCoulomb.integrableOn_comp_sub_ball (f := fun w : ℂ => -((‖w‖ ^ 2)⁻¹ : ℝ) • w)
      TwoComponentCoulomb.integrableOn_gradLogKernel_ball_zero x z (α + 1))

/-- Local uniform integrability bound for the singular point field after convolution.
It uses only bounded density and bounded support, rather than radiality. -/
theorem exists_integral_norm_pointField_le (hχ : IsMollifier χ) (z : ℂ)
    (hα : 0 < α) (R : ℝ) :
    ∃ C : ℝ, ∀ x ∈ ball (0 : ℂ) R,
      ∫ y, ‖pointField (x - y)‖ ∂smearedCharge χ z α ≤ C := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hM0 := hχ.nonneg_of_le hM
  have ha : 0 < α + 1 := by linarith
  obtain ⟨C, hC⟩ :=
    TwoComponentCoulomb.exists_integral_inv_norm_sub_smearedCharge_le z ha R
  let D := ENNReal.ofReal (M / α ^ 2) * volume (ball z (α + 1))
  have hD : D ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hle : smearedCharge χ z α ≤ D • TwoComponentCoulomb.smearedCharge z (α + 1) := by
    have e : (volume : Measure ℂ).restrict (ball z (α + 1)) =
        volume (ball z (α + 1)) • TwoComponentCoulomb.smearedCharge z (α + 1) := by
      rw [TwoComponentCoulomb.smearedCharge_eq, smul_smul,
        ENNReal.mul_inv_cancel (measure_ball_pos volume z ha).ne' measure_ball_lt_top.ne,
        one_smul]
    calc smearedCharge χ z α ≤
        ENNReal.ofReal (M / α ^ 2) • (volume : Measure ℂ).restrict (ball z (α + 1)) := by
          refine (smearedCharge_le_smul_restrict hχ hM hα).trans ?_
          intro s
          simp only [Measure.smul_apply, smul_eq_mul]
          gcongr
          exact closedBall_subset_ball (lt_add_one α)
      _ = D • TwoComponentCoulomb.smearedCharge z (α + 1) := by rw [e, smul_smul]
  refine ⟨D.toReal * C, fun x hx => ?_⟩
  have hi := TwoComponentCoulomb.integrable_inv_norm_sub_smearedCharge ha x z
  simp_rw [pointField, TwoComponentCoulomb.norm_gradLogKernel]
  calc ∫ y, ‖x - y‖⁻¹ ∂smearedCharge χ z α ≤
      ∫ y, ‖x - y‖⁻¹ ∂(D • TwoComponentCoulomb.smearedCharge z (α + 1)) :=
        integral_mono_measure hle (Eventually.of_forall fun _ => by positivity)
          (hi.smul_measure hD)
    _ = D.toReal * ∫ y, ‖x - y‖⁻¹ ∂TwoComponentCoulomb.smearedCharge z (α + 1) := by
      rw [integral_smul_measure, smul_eq_mul]
    _ ≤ D.toReal * C := mul_le_mul_of_nonneg_left (hC x hx) ENNReal.toReal_nonneg

/-- Integrability of `(x, y) ↦ ∇ξ(x) · ∇g(x - y)` for `volume ⊗ δ_z^{(α)}` (`ξ` of class `C¹` with
compact support): domination of `δ_z^{(α)}` by a multiple of Lebesgue measure on a disc reduces it
to the uniform-disc case of `TwoComponentCoulomb`. -/
theorem integrable_fderiv_apply_gradLogKernel_sub_prod_smearedCharge (hχ : IsMollifier χ)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (z : ℂ) (hα : 0 < α) :
    Integrable (fun p : ℂ × ℂ => fderiv ℝ ξ p.1 (pointField (p.1 - p.2)))
      (volume.prod (smearedCharge χ z α)) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have ha : 0 < α + 1 := by linarith
  have h1 := TwoComponentCoulomb.integrable_fderiv_apply_gradLogKernel_sub_smearedCharge hξ hc ha z
  have hball : volume (ball z (α + 1)) ≠ ∞ := measure_ball_lt_top.ne
  have hball0 : volume (ball z (α + 1)) ≠ 0 := (measure_ball_pos volume z ha).ne'
  have e : (volume : Measure ℂ).restrict (ball z (α + 1)) =
      volume (ball z (α + 1)) • TwoComponentCoulomb.smearedCharge z (α + 1) := by
    rw [TwoComponentCoulomb.smearedCharge_eq, smul_smul, ENNReal.mul_inv_cancel hball0 hball,
      one_smul]
  have h2 : Integrable (fun p : ℂ × ℂ => fderiv ℝ ξ p.1 (pointField (p.1 - p.2)))
      (volume.prod ((volume : Measure ℂ).restrict (ball z (α + 1)))) := by
    rw [e, Measure.prod_smul_right]
    exact h1.smul_measure hball
  have hle1 : smearedCharge χ z α ≤
      ENNReal.ofReal (M / α ^ 2) • (volume : Measure ℂ).restrict (ball z (α + 1)) := by
    refine (smearedCharge_le_smul_restrict hχ hM hα).trans fun s => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    exact closedBall_subset_ball (lt_add_one α)
  have hle : (volume : Measure ℂ).prod (smearedCharge χ z α) ≤ ENNReal.ofReal (M / α ^ 2) •
      (volume : Measure ℂ).prod ((volume : Measure ℂ).restrict (ball z (α + 1))) := by
    rw [← Measure.prod_smul_right]
    exact Measure.prod_mono le_rfl hle1
  exact (h2.smul_measure ENNReal.ofReal_ne_top).mono_measure hle

private theorem apply_convolvedField (hχ : IsMollifier χ) (z : ℂ) (hα : 0 < α)
    (L : ℂ →L[ℝ] ℝ) (x : ℂ) :
    L (convolvedField χ z α x) = ∫ y, L (pointField (x - y)) ∂smearedCharge χ z α :=
  (L.integral_comp_comm (integrable_gradLogKernel_sub_smearedCharge hχ x z hα)).symm

private theorem integrable_test_convolvedField (hχ : IsMollifier χ) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (z : ℂ) (hα : 0 < α) :
    Integrable (fun x => fderiv ℝ ξ x (convolvedField χ z α x)) := by
  have he := apply_convolvedField hχ z hα
  simp_rw [he]
  exact (integrable_fderiv_apply_gradLogKernel_sub_prod_smearedCharge hχ hξ hc z hα).integral_prod_left

/-- The weak Poisson identity for the convolution field, before any regularity claim.
This is `-Δ(g * δ_z) = 2π δ_z` tested against a compactly supported `C¹` function. -/
theorem weakPoisson_convolvedField (hχ : IsMollifier χ) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (z : ℂ) (hα : 0 < α) :
    ∫ x, fderiv ℝ ξ x (convolvedField χ z α x) =
      2 * Real.pi * ∫ y, ξ y ∂smearedCharge χ z α := by
  have := isFiniteMeasure_smearedCharge hχ z α
  have hp := integrable_fderiv_apply_gradLogKernel_sub_prod_smearedCharge hχ hξ hc z hα
  simp_rw [apply_convolvedField hχ z hα]
  rw [integral_integral_swap hp]
  simp_rw [pointField, TwoComponentCoulomb.integral_fderiv_apply_gradLogKernel hξ hc]
  rw [integral_const_mul]

/-- The weak Poisson equation for the difference of two smoothing radii,
the opening identity in the proof of Lemma 3.2. -/
theorem weakPoisson_sub_convolvedField (hχ : IsMollifier χ) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (z : ℂ) (hα : 0 < α)
    {η : ℝ} (hη : 0 < η) :
    ∫ x, fderiv ℝ ξ x (convolvedField χ z α x - convolvedField χ z η x) =
      2 * Real.pi * ((∫ y, ξ y ∂smearedCharge χ z α) -
        ∫ y, ξ y ∂smearedCharge χ z η) := by
  simp_rw [map_sub]
  rw [integral_sub (integrable_test_convolvedField hχ hξ hc z hα)
    (integrable_test_convolvedField hχ hξ hc z hη),
    weakPoisson_convolvedField hχ hξ hc z hα, weakPoisson_convolvedField hχ hξ hc z hη,
    mul_sub]

end RouteFlux

end MultipoleBKT

end
