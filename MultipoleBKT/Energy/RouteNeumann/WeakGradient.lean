/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.Identification
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Weak gradients in the Neumann energy completion

The finite-energy class used after (3.19) consists of potential-gradient
pairs. This module verifies the distributional gradient identity throughout
the completion. The extension from classical pairs is by continuous L²
pairings. A cutoff extends each classical potential before integration by parts.
-/

public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace

namespace MultipoleBKT.RouteNeumann

private theorem classical_weak_gradient {z : ℂ} {τ : ℝ} (hτ : 0 < τ)
    {u : ℂ → ℝ} {F : ℂ → ℂ} {ρ : ℝ} (hρ : τ < ρ)
    (hu : ContDiffOn ℝ 1 u (ball z ρ))
    (hF : ∀ w ∈ ball z ρ, HasGradientAt u (F w) w)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball z τ) (v : ℂ) :
    (∫ w in ball z τ, u w * fderiv ℝ ξ w v) =
      -(∫ w in ball z τ, inner ℝ (F w) (ξ w • v)) := by
  let r := (τ + ρ) / 2
  have hτr : τ < r := by dsimp [r]; linarith
  have hrρ : r < ρ := by dsimp [r]; linarith
  let ψ := annulusCutoff z τ r
  let f : ℂ → ℝ := fun w => ψ w * u w
  have hf : ContDiff ℝ 1 f := contDiff_mul_of_eq_zero hrρ
    (contDiff_annulusCutoff z τ r)
    (fun w hw => annulusCutoff_eq_zero hτ.le hτr hw) hu
  have he : ∀ w ∈ ball z τ, f w = u w := by
    intro w hw
    dsimp [f, ψ]
    rw [annulusCutoff_eq_one hτ.le hτr
      (by simpa [dist_eq_norm] using (mem_ball.mp hw).le), one_mul]
  have hde : ∀ w ∈ ball z τ, fderiv ℝ f w = toDual ℝ ℂ (F w) := by
    intro w hw
    have hev : f =ᶠ[𝓝 w] u := by
      filter_upwards [isOpen_ball.mem_nhds hw] with x hx
      exact he x hx
    rw [hev.fderiv_eq, (hF w (ball_subset_ball hρ.le hw)).hasFDerivAt.fderiv]
  have hi₁ : Integrable (fun w => fderiv ℝ f w v * ξ w) :=
    (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      hξ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hi₂ : Integrable (fun w => f w * fderiv ℝ ξ w v) :=
    (hf.continuous.mul ((hξ.continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun w => f w * ξ w) :=
    (hf.continuous.mul hξ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun w _ => hf.differentiable one_ne_zero w)
    (fun w _ => hξ.differentiable one_ne_zero w)
  have hξ0 : ∀ w ∉ ball z τ, ξ w = 0 := by
    intro w hw
    exact image_eq_zero_of_notMem_tsupport (fun h => hw (hs h))
  have hDξ0 : ∀ w ∉ ball z τ, fderiv ℝ ξ w v = 0 := by
    intro w hw
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hw (hs h))]
    rfl
  have hleft : (∫ w, f w * fderiv ℝ ξ w v) =
      ∫ w in ball z τ, u w * fderiv ℝ ξ w v := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun w hw => by rw [hDξ0 w hw, mul_zero])]
    exact setIntegral_congr_fun measurableSet_ball fun w hw => by rw [he w hw]
  have hright : (∫ w, fderiv ℝ f w v * ξ w) =
      ∫ w in ball z τ, inner ℝ (F w) (ξ w • v) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun w hw => by rw [hξ0 w hw, mul_zero])]
    apply setIntegral_congr_fun measurableSet_ball
    intro w hw
    dsimp only
    rw [hde w hw, toDual_apply_apply, inner_smul_right]
    ring
  rw [hleft, hright] at hibp
  exact hibp

/-- Every pair in the energy completion has the asserted weak gradient.
This proves the testing identity across all L² limits of the classical pairs. -/
theorem energySpace_weak_gradient {z : ℂ} {τ : ℝ} (hτ : 0 < τ)
    {U : EnergyPair z τ} (hU : U ∈ energySpace z τ)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball z τ) (v : ℂ) :
    (∫ w in ball z τ, U.1 w * fderiv ℝ ξ w v) =
      -(∫ w in ball z τ, inner ℝ (U.2 w) (ξ w • v)) := by
  have hD : MemLp (fun w => fderiv ℝ ξ w v) 2 (volume.restrict (ball z τ)) :=
    memLp_of_continuousOn_closedBall
      (((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn)
  have hT : MemLp (fun w => ξ w • v) 2 (volume.restrict (ball z τ)) :=
    memLp_of_continuousOn_closedBall (hξ.continuous.smul continuous_const).continuousOn
  let D := hD.toLp (fun w => fderiv ℝ ξ w v)
  let T := hT.toLp (fun w => ξ w • v)
  have hclosed : IsClosed {W : EnergyPair z τ |
      inner ℝ W.1 D = -inner ℝ W.2 T} :=
    isClosed_eq (continuous_fst.inner continuous_const)
      (continuous_snd.inner continuous_const).neg
  have hall : classicalPairs z τ ⊆ {W : EnergyPair z τ |
      inner ℝ W.1 D = -inner ℝ W.2 T} := by
    rintro W ⟨u, F, ρ, hρ, hu, hF, hp, hFp, rfl⟩
    change inner ℝ (hp.toLp u) (hD.toLp _) = -inner ℝ (hFp.toLp F) (hT.toLp _)
    rw [inner_toLp_real, inner_toLp_field]
    exact classical_weak_gradient hτ hρ hu hF hξ hc hs v
  have h := closure_minimal hall hclosed hU
  change inner ℝ U.1 (hD.toLp _) = -inner ℝ U.2 (hT.toLp _) at h
  rw [L2.inner_def, L2.inner_def] at h
  have hl : (∫ w in ball z τ, inner ℝ (U.1 w) ((hD.toLp _) w)) =
      ∫ w in ball z τ, U.1 w * fderiv ℝ ξ w v := by
    apply integral_congr_ae
    filter_upwards [hD.coeFn_toLp] with w hw
    rw [hw]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hr : (∫ w in ball z τ, inner ℝ (U.2 w) ((hT.toLp _) w)) =
      ∫ w in ball z τ, inner ℝ (U.2 w) (ξ w • v) := by
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp] with w hw
    rw [hw]
  rwa [hl, hr] at h

end MultipoleBKT.RouteNeumann
