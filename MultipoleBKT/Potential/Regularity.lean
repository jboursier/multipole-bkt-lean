/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.TwoRadius
public import MultipoleBKT.Potential.RouteHessian.Smoothed
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TwoComponentCoulomb.Potential.Fundamental
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Regularity of `g̃₁ = g * δ₀^{(1)}` and `g₁` (Lemma 3.1)

See Lemma 3.1 of the paper. The first derivative is identified through the weak Poisson
equation and circle flux in `RouteFlux.Potential`. Its continuity follows from
local integrability of the point field and boundedness of the source density.

The radial and angular integration-by-parts identities in `RouteHessian.Weak`
identify the weak Hessian across the origin. Its essential bound gives the
global Lipschitz bound through smooth approximation in `RouteHessian.Lipschitz`.
The convolved weak Hessian is continuous by `L¹` translation continuity.
It is the classical Hessian of the double smoothing. The regularity and
Taylor interfaces use these Hessian bounds.

Here `χ` is an admissible bounded measurable radial mollifier and `M` is a
pointwise bound for its density. The bounds are uniform in position and scale
as the inverse radius for the gradient and inverse radius squared for its
Lipschitz constant.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam α η : ℝ}

/-! ### The field -/

/-- The radial field from Lemma 3.1. -/
noncomputable def smearedField (χ : ℂ → ℝ) (lam : ℝ) (x : ℂ) : ℂ :=
  -((smearedCharge χ 0 lam).real (ball 0 ‖x‖) / ‖x‖ ^ 2) • x

/-- The explicit radial field is the convolution field recovered from Poisson flux. -/
theorem smearedField_eq_convolvedField (hχ : IsMollifier χ) (hlam : 0 < lam) (x : ℂ) :
    smearedField χ lam x = RouteFlux.convolvedField χ 0 lam x := by
  rw [RouteFlux.convolvedField_eq_massProfile hχ hlam]
  rfl

/-- The gradient identification from the Poisson equation and circle flux.
See Lemma 3.1 of the paper. -/
theorem hasFDerivAt_smearedPotential (hχ : IsMollifier χ) (hlam : 0 < lam) (x₀ : ℂ) :
    HasFDerivAt (smearedPotential χ lam) (toDual ℝ ℂ (smearedField χ lam x₀)) x₀ := by
  rw [smearedField_eq_convolvedField hχ hlam]
  exact RouteFlux.hasFDerivAt_smearedPotential hχ hlam x₀

/-- **The gradient of the potential**, gradient form. -/
theorem hasGradientAt_smearedPotential (hχ : IsMollifier χ) (hlam : 0 < lam) (x : ℂ) :
    HasGradientAt (smearedPotential χ lam) (smearedField χ lam x) x :=
  hasGradientAt_iff_hasFDerivAt.2 (hasFDerivAt_smearedPotential hχ hlam x)

theorem differentiable_smearedPotential (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Differentiable ℝ (smearedPotential χ lam) := fun x =>
  (hasFDerivAt_smearedPotential hχ hlam x).differentiableAt

theorem fderiv_smearedPotential (hχ : IsMollifier χ) (hlam : 0 < lam) (x : ℂ) :
    fderiv ℝ (smearedPotential χ lam) x = toDual ℝ ℂ (smearedField χ lam x) :=
  (hasFDerivAt_smearedPotential hχ hlam x).fderiv

/-- `∇(g * δ₀^{(λ)})(x) · v = ⟪smearedField χ λ x, v⟫`. -/
theorem fderiv_smearedPotential_apply (hχ : IsMollifier χ) (hlam : 0 < lam) (x v : ℂ) :
    fderiv ℝ (smearedPotential χ lam) x v = ⟪smearedField χ lam x, v⟫ := by
  rw [fderiv_smearedPotential hχ hlam, toDual_apply_apply]

/-! ### Mass of discs -/

/-- `δ₀^{(λ)}(B(0, s)) ≤ π M s² / λ²`. -/
theorem smearedCharge_real_ball_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {s : ℝ} (hs : 0 ≤ s) :
    (smearedCharge χ 0 lam).real (ball 0 s) ≤ Real.pi * M / lam ^ 2 * s ^ 2 :=
  RouteFlux.massProfile_le_sq hχ hM hlam hs

theorem smearedCharge_real_ball_le_one (hχ : IsMollifier χ) (hlam : 0 < lam) (s : ℝ) :
    (smearedCharge χ 0 lam).real (ball 0 s) ≤ 1 :=
  RouteFlux.massProfile_le_one hχ hlam s

/-! ### Bounds on the field -/

/-- `|smearedField χ λ x| = δ₀^{(λ)}(B(0, |x|)) / |x|`. -/
theorem norm_smearedField (χ : ℂ → ℝ) (lam : ℝ) (x : ℂ) :
    ‖smearedField χ lam x‖ = (smearedCharge χ 0 lam).real (ball 0 ‖x‖) / ‖x‖ := by
  rw [smearedField, norm_smul, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg measureReal_nonneg (by positivity))]
  rcases eq_or_ne ‖x‖ 0 with h | h
  · simp [h]
  · field_simp

/-- `|∇(g * δ₀^{(λ)})(x)| ≤ π M |x| / λ²`. -/
theorem norm_smearedField_le_mul (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (x : ℂ) :
    ‖smearedField χ lam x‖ ≤ Real.pi * M / lam ^ 2 * ‖x‖ := by
  rw [norm_smearedField]
  rcases eq_or_ne ‖x‖ 0 with h | h
  · simp [h]
  have hx : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
  rw [div_le_iff₀ hx]
  calc (smearedCharge χ 0 lam).real (ball 0 ‖x‖) ≤ Real.pi * M / lam ^ 2 * ‖x‖ ^ 2 :=
        smearedCharge_real_ball_le hχ hM hlam hx.le
    _ = Real.pi * M / lam ^ 2 * ‖x‖ * ‖x‖ := by ring

/-- `|∇(g * δ₀^{(λ)})(x)| ≤ 1 / |x|` (Newton's bound). -/
theorem norm_smearedField_le_inv (hχ : IsMollifier χ) (hlam : 0 < lam) (x : ℂ) :
    ‖smearedField χ lam x‖ ≤ ‖x‖⁻¹ := by
  rw [norm_smearedField, div_eq_mul_inv]
  calc (smearedCharge χ 0 lam).real (ball 0 ‖x‖) * ‖x‖⁻¹ ≤ 1 * ‖x‖⁻¹ :=
        mul_le_mul_of_nonneg_right (smearedCharge_real_ball_le_one hχ hlam _) (by positivity)
    _ = ‖x‖⁻¹ := one_mul _

/-- **Bounded gradient**: `|∇(g * δ₀^{(λ)})(x)| ≤ √(π M) / λ` (Lemma 3.1). -/
theorem norm_smearedField_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (x : ℂ) :
    ‖smearedField χ lam x‖ ≤ Real.sqrt (Real.pi * M) / lam := by
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  set r : ℝ := Real.sqrt (Real.pi * M) / lam with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = Real.pi * M / lam ^ 2 := by
    rw [hr, div_pow, Real.sq_sqrt (by positivity)]
  rcases le_or_gt (‖x‖ * r) 1 with h | h
  · calc ‖smearedField χ lam x‖ ≤ Real.pi * M / lam ^ 2 * ‖x‖ :=
          norm_smearedField_le_mul hχ hM hlam x
      _ = r * (‖x‖ * r) := by rw [← hr2]; ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left h hr0
      _ = r := mul_one r
  · have hx : 0 < ‖x‖ := by
      rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
      · rw [← h0, zero_mul] at h
        exact absurd h (by norm_num)
      · exact h0
    refine (norm_smearedField_le_inv hχ hlam x).trans ?_
    rw [inv_le_iff_one_le_mul₀ hx]
    linarith

/-! ### The field is globally Lipschitz -/

/-- **Lipschitz gradient**: `|∇(g * δ₀^{(λ)})(x) - ∇(g * δ₀^{(λ)})(y)| ≤ (3 π M / λ²) |x - y|`. -/
theorem norm_smearedField_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (x y : ℂ) :
    ‖smearedField χ lam x - smearedField χ lam y‖ ≤ 3 * (Real.pi * M / lam ^ 2) * ‖x - y‖ := by
  rw [smearedField_eq_convolvedField hχ hlam, smearedField_eq_convolvedField hχ hlam]
  exact RouteHessian.norm_convolvedField_sub_le hχ hM hlam x y

/-- The field is Lipschitz, hence continuous. -/
theorem lipschitzWith_smearedField (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) :
    LipschitzWith (Real.toNNReal (3 * (Real.pi * M / lam ^ 2))) (smearedField χ lam) := by
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  exact norm_smearedField_sub_le hχ hM hlam x y

theorem continuous_smearedField (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Continuous (smearedField χ lam) := by
  have he : smearedField χ lam = RouteFlux.convolvedField χ 0 lam :=
    funext (smearedField_eq_convolvedField hχ hlam)
  rw [he]
  exact RouteFlux.continuous_convolvedField hχ hlam

/-- The field is odd. -/
theorem smearedField_neg (χ : ℂ → ℝ) (lam : ℝ) (x : ℂ) :
    smearedField χ lam (-x) = -smearedField χ lam x := by
  simp only [smearedField, norm_neg, smul_neg]

/-- The average of the field against `δ₀^{(μ)}` vanishes (`χ` is even, (3.14)). -/
theorem integral_smearedField_smearedCharge (hχ : IsMollifier χ) (lam mu : ℝ) :
    ∫ x, smearedField χ lam x ∂smearedCharge χ 0 mu = 0 := by
  have h := map_neg_smearedCharge hχ 0 mu
  rw [neg_zero] at h
  have e : ∫ x, smearedField χ lam x ∂smearedCharge χ 0 mu =
      -∫ x, smearedField χ lam x ∂smearedCharge χ 0 mu := by
    conv_lhs => rw [← h]
    rw [measurableEmbedding_neg.integral_map, ← integral_neg]
    simp only [smearedField_neg]
  exact self_eq_neg.1 e

/-! ### Convolution with a probability measure -/

section Convolution

variable {f : ℂ → ℝ} {f' : ℂ → ℂ →L[ℝ] ℝ}

/-- Differentiation under the integral sign for `z ↦ ∫ f(z - a) dμ(a)`, when `f` has a bounded
continuous derivative and `μ` is finite. -/
theorem hasFDerivAt_integral_comp_sub (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f')
    {C : ℝ} (hC : ∀ x, ‖f' x‖ ≤ C) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hint : ∀ z, Integrable (fun a => f (z - a)) μ) (z₀ : ℂ) :
    HasFDerivAt (fun z => ∫ a, f (z - a) ∂μ) (∫ a, f' (z₀ - a) ∂μ) z₀ := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun z a => f' (z - a))
    (bound := fun _ => C) univ_mem
    (Filter.Eventually.of_forall fun z => (hint z).aestronglyMeasurable) (hint z₀)
    (hf'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a z _ => hC _) (integrable_const C)
    (Filter.Eventually.of_forall fun a z _ => ?_)
  have h := (hf (z - a)).comp z ((hasFDerivAt_id z).sub_const a)
  simp only [ContinuousLinearMap.comp_id] at h
  exact h

/-- The derivative `∫ f'(z - a) dμ(a)` is bounded by `C` for a probability measure. -/
theorem norm_integral_comp_sub_le {C : ℝ} (hC : ∀ x, ‖f' x‖ ≤ C) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] (z : ℂ) : ‖∫ a, f' (z - a) ∂μ‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun a => f' (z - a))
    (Filter.Eventually.of_forall fun a => hC (z - a))
  rwa [probReal_univ, mul_one] at h

end Convolution

/-! ### The second-order Taylor bound -/

/-- **Second-order Taylor bound**: if `f` is differentiable with an `L`-Lipschitz derivative, then
`|f(a + h) - f(a) - f'(a) h| ≤ L |h|²`. -/
theorem abs_sub_sub_fderiv_le {f : ℂ → ℝ} {f' : ℂ → ℂ →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) {L : ℝ} (hL : ∀ x y, ‖f' x - f' y‖ ≤ L * ‖x - y‖)
    (a h : ℂ) : |f (a + h) - f a - f' a h| ≤ L * ‖h‖ ^ 2 := by
  have hL0 : 0 ≤ L := by
    have := (norm_nonneg _).trans (hL 1 0)
    simpa using this
  have hbound : ∀ x ∈ closedBall a ‖h‖, ‖f' x - f' a‖ ≤ L * ‖h‖ := fun x hx => by
    refine (hL x a).trans (mul_le_mul_of_nonneg_left ?_ hL0)
    rwa [mem_closedBall, dist_eq_norm] at hx
  have key := (convex_closedBall a ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := f) (f' := f') (φ := f' a)
    (fun x _ => (hf x).hasFDerivWithinAt) hbound (mem_closedBall_self (norm_nonneg h))
    (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left])
  rw [add_sub_cancel_left, Real.norm_eq_abs] at key
  calc |f (a + h) - f a - f' a h| ≤ L * ‖h‖ * ‖h‖ := key
    _ = L * ‖h‖ ^ 2 := by ring

/-- The Taylor bound in `fderiv` form: if `f` is differentiable with
`|∇f(x) - ∇f(y)| ≤ L |x - y|`, then `|f(a + h) - f(a) - ∇f(a) · h| ≤ L |h|²`. -/
theorem abs_sub_sub_fderiv_le_of_differentiable {f : ℂ → ℝ} (hf : Differentiable ℝ f) {L : ℝ}
    (hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖) (a h : ℂ) :
    |f (a + h) - f a - fderiv ℝ f a h| ≤ L * ‖h‖ ^ 2 :=
  abs_sub_sub_fderiv_le (fun x => (hf x).hasFDerivAt) hL a h

/-! ### Regularity of `g * δ₀^{(λ)}` -/

/-- `|∇(g * δ₀^{(λ)})| ≤ √(π M) / λ`, in `fderiv` form. -/
theorem norm_fderiv_smearedPotential_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (x : ℂ) :
    ‖fderiv ℝ (smearedPotential χ lam) x‖ ≤ Real.sqrt (Real.pi * M) / lam := by
  rw [fderiv_smearedPotential hχ hlam, LinearIsometryEquiv.norm_map]
  exact norm_smearedField_le hχ hM hlam x

/-- `∇(g * δ₀^{(λ)})` is `3 π M / λ²`-Lipschitz, in `fderiv` form. -/
theorem norm_fderiv_smearedPotential_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (x y : ℂ) :
    ‖fderiv ℝ (smearedPotential χ lam) x - fderiv ℝ (smearedPotential χ lam) y‖ ≤
      3 * (Real.pi * M / lam ^ 2) * ‖x - y‖ := by
  rw [fderiv_smearedPotential hχ hlam, fderiv_smearedPotential hχ hlam, ← map_sub,
    LinearIsometryEquiv.norm_map]
  have hM0 := hχ.nonneg_of_le hM
  have h := (lipschitzWith_smearedField hχ hM hlam).dist_le_mul x y
  have hL : 0 ≤ 3 * (Real.pi * M / lam ^ 2) := by positivity
  rw [Real.coe_toNNReal _ hL] at h
  simpa only [dist_eq_norm] using h

theorem continuous_fderiv_smearedPotential (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Continuous (fderiv ℝ (smearedPotential χ lam)) := by
  have h : fderiv ℝ (smearedPotential χ lam) = fun x => toDual ℝ ℂ (smearedField χ lam x) :=
    funext (fderiv_smearedPotential hχ hlam)
  rw [h]
  exact (toDual ℝ ℂ).continuous.comp (continuous_smearedField hχ hlam)

/-! ### Regularity of the two-radius kernels -/

/-- The derivative of `g * δ₀^{(α)} * δ₀^{(η)}`: `∫ ∇(g * δ₀^{(η)})(z - a) dδ₀^{(α)}(a)`. -/
theorem hasFDerivAt_twoRadiusKernel (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    HasFDerivAt (twoRadiusKernel χ α η)
      (∫ a, fderiv ℝ (smearedPotential χ η) (z - a) ∂smearedCharge χ 0 α) z := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  have hfun : twoRadiusKernel χ α η =
      fun z => ∫ a, smearedPotential χ η (z - a) ∂smearedCharge χ 0 α :=
    funext fun z => twoRadiusKernel_eq_integral_smearedPotential hχ α η z
  rw [hfun]
  exact hasFDerivAt_integral_comp_sub
    (fun x => (differentiable_smearedPotential hχ hη x).hasFDerivAt)
    (continuous_fderiv_smearedPotential hχ hη) (norm_fderiv_smearedPotential_le hχ hM hη) _
    (fun v => integrable_smearedPotential_comp hχ hη (continuous_const.sub continuous_id) 0 α) z

theorem differentiable_twoRadiusKernel (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) :
    Differentiable ℝ (twoRadiusKernel χ α η) := fun z =>
  (hasFDerivAt_twoRadiusKernel hχ hα hη z).differentiableAt

theorem fderiv_twoRadiusKernel (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    fderiv ℝ (twoRadiusKernel χ α η) z =
      ∫ a, fderiv ℝ (smearedPotential χ η) (z - a) ∂smearedCharge χ 0 α :=
  (hasFDerivAt_twoRadiusKernel hχ hα hη z).fderiv

/-- The weak Hessian of the actual singly smoothed potential.
See Lemma 3.1 of the paper. -/
theorem weakHessian_smearedPotential (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (v w : ℂ) :
    (∫ x, fderiv ℝ ξ x v * fderiv ℝ (smearedPotential χ lam) x w) =
      -(∫ x, ξ x * ⟪RouteHessian.radialHessian χ lam x v, w⟫) := by
  simp_rw [fderiv_smearedPotential_apply hχ hlam, smearedField_eq_convolvedField hχ hlam]
  exact RouteHessian.weakHessian_convolvedField hχ hlam hξ hc v w

/-- The convolved weak Hessian is the classical derivative of the double-smoothed field.
See Lemma 3.1 of the paper. -/
theorem hasFDerivAt_integral_smearedField (hχ : IsMollifier χ)
    (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    HasFDerivAt (fun x => ∫ a, smearedField χ η (x - a) ∂smearedCharge χ 0 α)
      (twoRadiusHessian χ α η z) z := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hweak (ξ : ℂ → ℝ) (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (v w : ℂ) :
      (∫ y, fderiv ℝ ξ y v * ⟪smearedField χ η y, w⟫) =
        -(∫ y, ξ y * ⟪RouteHessian.radialHessian χ η y v, w⟫) := by
    have hh := weakHessian_smearedPotential hχ hη hξ hc v w
    simpa only [fderiv_smearedPotential_apply hχ hη] using hh
  have hd := RouteHessian.hasFDerivAt_convolution_integrable_of_weak
    (continuous_smearedField hχ hη) (RouteHessian.measurable_radialHessian hχ)
    (norm_smearedField_le hχ hM hη) (RouteHessian.norm_radialHessian_le hχ hM hη)
    hweak (RouteHessian.integrable_chargeDensity hχ hα) z
  rw [← RouteHessian.integral_charge_comp_sub_eq_convolution hχ,
    ← RouteHessian.integral_charge_comp_sub_eq_convolution hχ] at hd
  exact hd

private theorem fderiv_twoRadiusKernel_eq_toDual (hχ : IsMollifier χ)
    (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    fderiv ℝ (twoRadiusKernel χ α η) z =
      toDual ℝ ℂ (∫ a, smearedField χ η (z - a) ∂smearedCharge χ 0 α) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  have hi : Integrable (fun a => smearedField χ η (z - a)) (smearedCharge χ 0 α) :=
    Integrable.of_bound ((continuous_smearedField hχ hη).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable _
      (Eventually.of_forall fun a => norm_smearedField_le hχ hM hη (z - a))
  rw [fderiv_twoRadiusKernel hχ hα hη]
  simp_rw [fderiv_smearedPotential hχ hη]
  exact (toDual ℝ ℂ).toContinuousLinearMap.integral_comp_comm hi

/-- The classical Hessian of the double smoothing is the convolved radial weak Hessian.
See Lemma 3.1 of the paper. -/
theorem hasFDerivAt_fderiv_twoRadiusKernel (hχ : IsMollifier χ)
    (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    HasFDerivAt (fderiv ℝ (twoRadiusKernel χ α η))
      ((toDual ℝ ℂ).toContinuousLinearMap.comp (twoRadiusHessian χ α η z)) z := by
  have hd := (toDual ℝ ℂ).toContinuousLinearMap.hasFDerivAt.comp z
    (hasFDerivAt_integral_smearedField hχ hα hη z)
  have he : fderiv ℝ (twoRadiusKernel χ α η) = fun x =>
      toDual ℝ ℂ (∫ a, smearedField χ η (x - a) ∂smearedCharge χ 0 α) :=
    funext (fderiv_twoRadiusKernel_eq_toDual hχ hα hη)
  rw [he]
  exact hd

/-- The Hessian of the double smoothing is continuous everywhere.
See Lemma 3.1 of the paper. -/
theorem continuous_fderiv_fderiv_twoRadiusKernel (hχ : IsMollifier χ)
    (hα : 0 < α) (hη : 0 < η) :
    Continuous (fderiv ℝ (fderiv ℝ (twoRadiusKernel χ α η))) := by
  have he : fderiv ℝ (fderiv ℝ (twoRadiusKernel χ α η)) = fun x =>
      (toDual ℝ ℂ).toContinuousLinearMap.comp (twoRadiusHessian χ α η x) :=
    funext (fun x => (hasFDerivAt_fderiv_twoRadiusKernel hχ hα hη x).fderiv)
  rw [he]
  exact continuous_const.clm_comp (continuous_twoRadiusHessian hχ hα hη)

/-- The double smoothing is `C²` for a bounded measurable radial mollifier.
See Lemma 3.1 of the paper. -/
theorem contDiff_twoRadiusKernel_two (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) :
    ContDiff ℝ 2 (twoRadiusKernel χ α η) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨differentiable_twoRadiusKernel hχ hα hη, by simp, ?_⟩
  exact contDiff_one_iff_fderiv.mpr ⟨
    fun x => (hasFDerivAt_fderiv_twoRadiusKernel hχ hα hη x).differentiableAt,
    continuous_fderiv_fderiv_twoRadiusKernel hχ hα hη⟩

/-- The classical Hessian has the same operator bound as the weak radial tensor.
See Lemma 3.1 of the paper. -/
theorem norm_fderiv_fderiv_twoRadiusKernel_le (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    ‖fderiv ℝ (fderiv ℝ (twoRadiusKernel χ α η)) z‖ ≤ 3 * (Real.pi * M / η ^ 2) := by
  rw [(hasFDerivAt_fderiv_twoRadiusKernel hχ hα hη z).fderiv]
  have hn : ‖(toDual ℝ ℂ).toContinuousLinearMap‖ = 1 :=
    (toDual ℝ ℂ).norm_toContinuousLinearMap
  exact ((toDual ℝ ℂ).toContinuousLinearMap.opNorm_comp_le _).trans (by
    rw [hn, one_mul]
    exact norm_twoRadiusHessian_le hχ hM hα hη z)

/-- The classical Hessian of the double smoothing is also its weak Hessian.
See Lemma 3.1 of the paper. -/
theorem weakHessian_twoRadiusKernel (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (v w : ℂ) :
    (∫ x, fderiv ℝ ξ x v * fderiv ℝ (twoRadiusKernel χ α η) x w) =
      -(∫ x, ξ x * ⟪twoRadiusHessian χ α η x v, w⟫) := by
  let g : ℂ → ℝ := fun x => fderiv ℝ (twoRadiusKernel χ α η) x w
  have hg (x : ℂ) := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x
    (hasFDerivAt_fderiv_twoRadiusKernel hχ hα hη x)
  have hgd (x : ℂ) : fderiv ℝ g x v = ⟪twoRadiusHessian χ α η x v, w⟫ := by
    change fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ w) ∘
      fderiv ℝ (twoRadiusKernel χ α η)) x v = _
    rw [(hg x).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    change toDual ℝ ℂ (twoRadiusHessian χ α η x v) w = _
    exact toDual_apply_apply
  have hgcont : Continuous g :=
    ((contDiff_twoRadiusKernel_two hχ hα hη).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcξv : HasCompactSupport (fun x => fderiv ℝ ξ x v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) rfl
  have hi1 : Integrable (fun x => fderiv ℝ ξ x v * g x) :=
    (((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hgcont).integrable_of_hasCompactSupport hcξv.mul_right
  have hi2 : Integrable (fun x => ξ x * fderiv ℝ g x v) := by
    simp_rw [hgd]
    exact (hξ.continuous.mul (((continuous_twoRadiusHessian hχ hα hη).clm_apply
      continuous_const).inner continuous_const)).integrable_of_hasCompactSupport hc.mul_right
  have hi0 : Integrable (fun x => ξ x * g x) :=
    (hξ.continuous.mul hgcont).integrable_of_hasCompactSupport hc.mul_right
  have hw := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi0
    (fun x _ => hξ.differentiable one_ne_zero x) (fun x _ => (hg x).differentiableAt)
  simp_rw [hgd] at hw
  change (∫ x, fderiv ℝ ξ x v * g x) = _
  linarith

/-- The equal-radius kernel has a continuous classical Hessian at every positive scale.
See Lemma 3.1 of the paper. -/
theorem contDiff_smearedKernel_two (hχ : IsMollifier χ) (hlam : 0 < lam) :
    ContDiff ℝ 2 (smearedKernel χ lam) := by
  rw [← twoRadiusKernel_self]
  exact contDiff_twoRadiusKernel_two hχ hlam hlam

/-- **Bounded gradient** of `g * δ₀^{(α)} * δ₀^{(η)}`: `|∇| ≤ √(π M) / η`. -/
theorem norm_fderiv_twoRadiusKernel_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    ‖fderiv ℝ (twoRadiusKernel χ α η) z‖ ≤ Real.sqrt (Real.pi * M) / η := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  rw [fderiv_twoRadiusKernel hχ hα hη]
  exact norm_integral_comp_sub_le (norm_fderiv_smearedPotential_le hχ hM hη) _ z

/-- **Lipschitz gradient** of `g * δ₀^{(α)} * δ₀^{(η)}`, with constant `3 π M / η²`. -/
theorem norm_fderiv_twoRadiusKernel_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hα : 0 < α) (hη : 0 < η) (z w : ℂ) :
    ‖fderiv ℝ (twoRadiusKernel χ α η) z - fderiv ℝ (twoRadiusKernel χ α η) w‖ ≤
      3 * (Real.pi * M / η ^ 2) * ‖z - w‖ := by
  exact (convex_univ : Convex ℝ (univ : Set ℂ)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hasFDerivAt_fderiv_twoRadiusKernel hχ hα hη x).differentiableAt)
    (fun x _ => norm_fderiv_fderiv_twoRadiusKernel_le hχ hM hα hη x)
    (mem_univ w) (mem_univ z)

/-! ### Lemma 3.1 -/

/-- **Lemma 3.1** for `g̃₁ = g * δ₀^{(1)}`: it is
differentiable, its gradient is bounded, and its gradient is globally Lipschitz. -/
theorem regularity_smearedPotential_one (hχ : IsMollifier χ) :
    Differentiable ℝ (smearedPotential χ 1) ∧
      (∃ C, ∀ x, ‖fderiv ℝ (smearedPotential χ 1) x‖ ≤ C) ∧
      ∃ L, ∀ x y, ‖fderiv ℝ (smearedPotential χ 1) x - fderiv ℝ (smearedPotential χ 1) y‖ ≤
        L * ‖x - y‖ := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  exact ⟨differentiable_smearedPotential hχ one_pos,
    ⟨_, norm_fderiv_smearedPotential_le hχ hM one_pos⟩,
    ⟨_, norm_fderiv_smearedPotential_sub_le hχ hM one_pos⟩⟩

/-- **Lemma 3.1** for `g₁ = g * δ₀^{(1)} * δ₀^{(1)}`: it is
differentiable, its gradient is bounded, and its gradient is globally Lipschitz. -/
theorem regularity_smearedKernel_one (hχ : IsMollifier χ) :
    Differentiable ℝ (smearedKernel χ 1) ∧
      (∃ C, ∀ x, ‖fderiv ℝ (smearedKernel χ 1) x‖ ≤ C) ∧
      ∃ L, ∀ x y, ‖fderiv ℝ (smearedKernel χ 1) x - fderiv ℝ (smearedKernel χ 1) y‖ ≤
        L * ‖x - y‖ := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hd := (contDiff_smearedKernel_two hχ one_pos).differentiable (by norm_num)
  rw [← twoRadiusKernel_self] at hd ⊢
  exact ⟨hd,
    ⟨_, norm_fderiv_twoRadiusKernel_le hχ hM one_pos one_pos⟩,
    ⟨_, norm_fderiv_twoRadiusKernel_sub_le hχ hM one_pos one_pos⟩⟩

/-- **Taylor bound for `g̃₁`** (equation (3.14)):
`|g̃₁(a + h) - g̃₁(a) - ∇g̃₁(a) · h| ≤ C |h|²`. -/
theorem taylor_smearedPotential_one (hχ : IsMollifier χ) :
    ∃ C, ∀ a h : ℂ, |smearedPotential χ 1 (a + h) - smearedPotential χ 1 a -
      fderiv ℝ (smearedPotential χ 1) a h| ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨hd, -, L, hL⟩ := regularity_smearedPotential_one hχ
  exact ⟨L, abs_sub_sub_fderiv_le_of_differentiable hd hL⟩

/-- **Taylor bound for `g₁`**: `|g₁(a + h) - g₁(a) - ∇g₁(a) · h| ≤ C |h|²`. -/
theorem taylor_smearedKernel_one (hχ : IsMollifier χ) :
    ∃ C, ∀ a h : ℂ, |smearedKernel χ 1 (a + h) - smearedKernel χ 1 a -
      fderiv ℝ (smearedKernel χ 1) a h| ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨hd, -, L, hL⟩ := regularity_smearedKernel_one hχ
  exact ⟨L, abs_sub_sub_fderiv_le_of_differentiable hd hL⟩

/-- The Taylor bound for `g̃₁` with the explicit gradient `smearedField χ 1` and the explicit
constant `3 π M`: `|g̃₁(a + h) - g̃₁(a) - ⟪∇g̃₁(a), h⟫| ≤ 3 π M |h|²`. -/
theorem abs_smearedPotential_one_sub_sub_inner_le (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) (a h : ℂ) :
    |smearedPotential χ 1 (a + h) - smearedPotential χ 1 a - ⟪smearedField χ 1 a, h⟫| ≤
      3 * (Real.pi * M) * ‖h‖ ^ 2 := by
  have h1 := abs_sub_sub_fderiv_le_of_differentiable (differentiable_smearedPotential hχ one_pos)
    (norm_fderiv_smearedPotential_sub_le hχ hM one_pos) a h
  rw [fderiv_smearedPotential_apply hχ one_pos] at h1
  simpa using h1

end MultipoleBKT

end
