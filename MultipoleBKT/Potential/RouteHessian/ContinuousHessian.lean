/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.Translation
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Continuous Hessians after a second convolution

See Lemma 3.1 of the paper. Smooth approximation identifies the derivative after convolution
with an integrable density. The convolved weak Hessian is continuous by
`L¹` translation continuity, so it is the classical derivative everywhere.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ContinuousLinearMap
open scoped RealInnerProductSpace Convolution

namespace MultipoleBKT.RouteHessian

/-- Associativity with two integrable scalar factors and a bounded measurable factor. -/
theorem convolution_assoc_of_integrable_bounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {φ ψ : ℂ → ℝ} {G : ℂ → E}
    (hφ : Integrable φ) (hψ : Integrable ψ) (hG : Measurable G)
    {K : ℝ} (hK : ∀ x, ‖G x‖ ≤ K) (z : ℂ) :
    (((φ ⋆[lsmul ℝ ℝ] ψ) ⋆[lsmul ℝ ℝ] G) z) =
      (φ ⋆[lsmul ℝ ℝ] (ψ ⋆[lsmul ℝ ℝ] G)) z := by
  have hi := (hφ.convolution_integrand (lsmul ℝ ℝ) hψ).smul_bdd K
    ((hG.comp (measurable_const.sub measurable_fst)).aestronglyMeasurable)
    (Eventually.of_forall fun p : ℂ × ℂ => hK (z - p.1))
  change Integrable (fun p : ℂ × ℂ => (φ p.2 * ψ (p.1 - p.2)) • G (z - p.1))
    (volume.prod volume) at hi
  simp only [mul_smul] at hi
  exact convolution_assoc' (lsmul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ)
    (fun a b c => by simp only [lsmul_apply, smul_eq_mul, mul_smul])
    (hφ.ae_convolution_exists (lsmul ℝ ℝ) hψ)
    (Eventually.of_forall fun x => integrable_smul_sub_of_bound hψ hG.aestronglyMeasurable hK x) hi

/-- The two scalar factors can be interchanged before convolving a bounded tensor. -/
theorem convolution_left_comm_of_integrable_bounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {φ ψ : ℂ → ℝ} {G : ℂ → E}
    (hφ : Integrable φ) (hψ : Integrable ψ) (hG : Measurable G)
    {K : ℝ} (hK : ∀ x, ‖G x‖ ≤ K) :
    (φ ⋆[lsmul ℝ ℝ] (ψ ⋆[lsmul ℝ ℝ] G)) =
      (ψ ⋆[lsmul ℝ ℝ] (φ ⋆[lsmul ℝ ℝ] G)) := by
  have hc : (φ ⋆[lsmul ℝ ℝ] ψ) = (ψ ⋆[lsmul ℝ ℝ] φ) :=
    convolution_symm (lsmul ℝ ℝ) (by ext; rfl)
  ext z
  rw [← convolution_assoc_of_integrable_bounded hφ hψ hG hK z, hc,
    convolution_assoc_of_integrable_bounded hψ hφ hG hK z]

/-- A bounded continuous classical derivative may be integrated against an `L¹` density. -/
theorem hasFDerivAt_convolution_of_bounded_derivative {F : ℂ → ℂ} {D : ℂ → ℂ →L[ℝ] ℂ}
    (hF : Continuous F) (hD : Continuous D) (hd : ∀ x, HasFDerivAt F (D x) x)
    {B K : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hK : ∀ x, ‖D x‖ ≤ K)
    {φ : ℂ → ℝ} (hφ : Integrable φ) (z : ℂ) :
    HasFDerivAt (φ ⋆[lsmul ℝ ℝ] F) ((φ ⋆[lsmul ℝ ℝ] D) z) z := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x t => φ t • D (x - t)) (bound := fun t => ‖φ t‖ * K) univ_mem
    (Eventually.of_forall fun x =>
      (integrable_smul_sub_of_bound hφ hF.aestronglyMeasurable hB x).aestronglyMeasurable)
    (integrable_smul_sub_of_bound hφ hF.aestronglyMeasurable hB z)
    (integrable_smul_sub_of_bound hφ hD.aestronglyMeasurable hK z).aestronglyMeasurable
    (Eventually.of_forall fun t x _ => ?_) (hφ.norm.mul_const K)
    (Eventually.of_forall fun t x _ => ?_)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _)
  · have hh := (hd (x - t)).comp x ((hasFDerivAt_id x).sub_const t)
    simpa only [ContinuousLinearMap.comp_id, Pi.smul_def, Function.comp_def, id_eq, lsmul_apply]
      using hh.const_smul (φ t)

/-- Smooth approximate identities converge uniformly for uniformly continuous functions. -/
theorem tendstoUniformly_bump_convolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {G : ℂ → E} (hG : UniformContinuous G) :
    TendstoUniformly (fun n => (shrinkingBump n).normed volume ⋆[lsmul ℝ ℝ] G) G atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hG (ε / 2) (by positivity)
  filter_upwards [tendsto_shrinkingBump.eventually (eventually_lt_nhds hδ)] with n hn
  intro x
  rw [dist_comm]
  refine ((shrinkingBump n).dist_normed_convolution_le hG.continuous.aestronglyMeasurable
    (fun y hy => (hd ((mem_ball.mp hy).trans hn)).le)).trans_lt (by linarith)

/-- Convolving a continuous field with an integrable density differentiates its weak
Hessian. The derivative is continuous even for a merely measurable density and tensor. -/
theorem hasFDerivAt_convolution_integrable_of_weak {F : ℂ → ℂ} {H : ℂ → ℂ →L[ℝ] ℂ}
    (hF : Continuous F) (hH : Measurable H) {B K : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) (hK : ∀ x, ‖H x‖ ≤ K)
    (hweak : ∀ (ξ : ℂ → ℝ), ContDiff ℝ 1 ξ → HasCompactSupport ξ → ∀ v w : ℂ,
      (∫ y, fderiv ℝ ξ y v * ⟪F y, w⟫) = -(∫ y, ξ y * ⟪H y v, w⟫))
    {φ : ℂ → ℝ} (hφ : Integrable φ) (z : ℂ) :
    HasFDerivAt (φ ⋆[lsmul ℝ ℝ] F) ((φ ⋆[lsmul ℝ ℝ] H) z) z := by
  have hHloc : LocallyIntegrable H volume := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    exact IntegrableOn.of_bound hS.measure_lt_top hH.aestronglyMeasurable K
      (Eventually.of_forall hK)
  have hcontD (n : ℕ) : Continuous ((shrinkingBump n).normed volume ⋆[lsmul ℝ ℝ] H) :=
    (shrinkingBump n).hasCompactSupport_normed.continuous_convolution_left (lsmul ℝ ℝ)
      (shrinkingBump n).continuous_normed hHloc
  have hcontF (n : ℕ) : Continuous ((shrinkingBump n).normed volume ⋆[lsmul ℝ ℝ] F) :=
    (shrinkingBump n).hasCompactSupport_normed.continuous_convolution_left (lsmul ℝ ℝ)
      (shrinkingBump n).continuous_normed hF.locallyIntegrable
  have hd (n : ℕ) (x : ℂ) := hasFDerivAt_convolution_of_weak hF hH hK hweak
    ((shrinkingBump n).contDiff_normed (μ := volume))
    ((shrinkingBump n).hasCompactSupport_normed (μ := volume)) x
  have hd' (n : ℕ) (x : ℂ) :
      HasFDerivAt ((shrinkingBump n).normed volume ⋆[lsmul ℝ ℝ] (φ ⋆[lsmul ℝ ℝ] F))
        (((shrinkingBump n).normed volume ⋆[lsmul ℝ ℝ] (φ ⋆[lsmul ℝ ℝ] H)) x) x := by
    have hh := hasFDerivAt_convolution_of_bounded_derivative (hcontF n) (hcontD n) (hd n)
      (norm_bump_convolution_le (shrinkingBump n) hB)
      (norm_bump_convolution_le (shrinkingBump n) hK) hφ x
    rw [convolution_left_comm_of_integrable_bounded hφ
      ((shrinkingBump n).integrable_normed (μ := volume)) hF.measurable hB,
      convolution_left_comm_of_integrable_bounded hφ
        ((shrinkingBump n).integrable_normed (μ := volume)) hH hK] at hh
    exact hh
  have hφF : Continuous (φ ⋆[lsmul ℝ ℝ] F) :=
    BddAbove.continuous_convolution_right_of_integrable (lsmul ℝ ℝ)
      (by exact ⟨B, fun _ hx => by rcases hx with ⟨x, rfl⟩; exact hB x⟩) hφ hF
  exact hasFDerivAt_of_tendstoUniformly
    (tendstoUniformly_bump_convolution (uniformContinuous_convolution_of_integrable_bounded
      hφ hH.aestronglyMeasurable hK)) hd'
    (ContDiffBump.convolution_tendsto_right_of_continuous tendsto_shrinkingBump hφF) z

end MultipoleBKT.RouteHessian

end
