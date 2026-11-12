/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.Lipschitz
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-!
# Translation continuity and convolution with a bounded measurable tensor

See Lemma 3.1 of the paper. Translation is continuous in `L¹`. Thus convolution of an integrable
density with a bounded measurable tensor is uniformly continuous.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ContinuousLinearMap
open scoped RealInnerProductSpace Convolution

namespace MultipoleBKT.RouteHessian

/-- Translation continuity in `L¹`, in the integral form needed for the Hessian. -/
theorem tendsto_integral_norm_translate_sub {φ : ℂ → ℝ} (hφ : Integrable φ) (z : ℂ) :
    Tendsto (fun x : ℂ => ∫ t, ‖φ (x - t) - φ (z - t)‖) (𝓝 z) (𝓝 0) := by
  let τ : ℂ → C(ℂ, ℂ) := fun x => ⟨fun t => x - t, continuous_const.sub continuous_id⟩
  have hτ : Continuous τ := ContinuousMap.continuous_of_continuous_uncurry τ
    (continuous_fst.sub continuous_snd)
  let f : Lp ℝ 1 (volume : Measure ℂ) := (memLp_one_iff_integrable.mpr hφ).toLp φ
  let T (x : ℂ) : Lp ℝ 1 (volume : Measure ℂ) :=
    Lp.compMeasurePreserving (τ x) (volume.measurePreserving_sub_left x) f
  have hT : Continuous T := continuous_const.compMeasurePreservingLp hτ
    (fun x => volume.measurePreserving_sub_left x) (by simp)
  have hae (x : ℂ) : T x =ᵐ[volume] fun t => φ (x - t) := by
    have hf := (memLp_one_iff_integrable.mpr hφ).coeFn_toLp
    filter_upwards [Lp.coeFn_compMeasurePreserving f (volume.measurePreserving_sub_left x),
      (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hf] with t ht ht'
    exact ht.trans ht'
  have he (x : ℂ) : ‖T x - T z‖ = ∫ t, ‖φ (x - t) - φ (z - t)‖ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (T x) (T z), hae x, hae z] with t ht hx hz
    rw [ht]
    change ‖T x t - T z t‖ = _
    rw [hx, hz]
  have ht := ((hT.tendsto z).sub_const (T z)).norm
  simpa only [he, sub_self, norm_zero] using ht

/-- A convolution difference is controlled by an `L¹` translation difference. -/
theorem norm_convolution_sub_le_translation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {φ : ℂ → ℝ} {G : ℂ → E}
    (hφ : Integrable φ) (hG : AEStronglyMeasurable G volume) {K : ℝ}
    (hK : ∀ t, ‖G t‖ ≤ K) (x z : ℂ) :
    ‖(φ ⋆[lsmul ℝ ℝ] G) x - (φ ⋆[lsmul ℝ ℝ] G) z‖ ≤
      (∫ t, ‖φ ((x - z) - t) - φ (-t)‖) * K := by
  have hi (a : ℂ) : ConvolutionExistsAt φ G a (lsmul ℝ ℝ) volume :=
    integrable_smul_sub_of_bound hφ hG hK a
  have hi' (a : ℂ) : Integrable (fun t => φ (a - t) • G t) := (hi a).integrable_swap
  have hb := ((hφ.comp_sub_left x).sub
    (hφ.comp_sub_left z)).norm.mul_const K
  rw [convolution_lsmul_swap, convolution_lsmul_swap, ← integral_sub (hi' x) (hi' z)]
  calc
    _ ≤ ∫ t, ‖φ (x - t) - φ (z - t)‖ * K :=
      norm_integral_le_of_norm_le hb (Eventually.of_forall fun t => by
        rw [← sub_smul, norm_smul]
        exact mul_le_mul_of_nonneg_left (hK t) (norm_nonneg _))
    _ = (∫ t, ‖φ (x - t) - φ (z - t)‖) * K := integral_mul_const _ _
    _ = _ := by
      congr 1
      rw [← integral_add_left_eq_self (fun t => ‖φ (x - t) - φ (z - t)‖) z]
      simp only [sub_add_eq_sub_sub, sub_self, zero_sub]

/-- An integrable density convolved with a bounded measurable tensor is uniformly
continuous. This uses translation continuity of the density, not continuity of the tensor. -/
theorem uniformContinuous_convolution_of_integrable_bounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {φ : ℂ → ℝ} {G : ℂ → E} (hφ : Integrable φ)
    (hG : AEStronglyMeasurable G volume) {K : ℝ} (hK : ∀ t, ‖G t‖ ≤ K) :
    UniformContinuous (φ ⋆[lsmul ℝ ℝ] G) := by
  have hK0 : 0 ≤ K := (norm_nonneg (G 0)).trans (hK 0)
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have ht := tendsto_integral_norm_translate_sub hφ 0
  obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhds_nhds.mp ht (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun x z hxz => ?_⟩
  have hh := hd (show dist (x - z) 0 < δ by simpa only [dist_eq_norm, sub_zero] using hxz)
  simp only [zero_sub, dist_zero_right, Real.norm_eq_abs] at hh
  have hb : (∫ t, ‖φ ((x - z) - t) - φ (-t)‖) < ε / (K + 1) :=
    (le_abs_self _).trans_lt hh
  rw [dist_eq_norm]
  calc
    _ ≤ (∫ t, ‖φ ((x - z) - t) - φ (-t)‖) * K :=
      norm_convolution_sub_le_translation hφ hG hK x z
    _ ≤ (∫ t, ‖φ ((x - z) - t) - φ (-t)‖) * (K + 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith : K ≤ K + 1)
        (integral_nonneg fun t => norm_nonneg (φ ((x - z) - t) - φ (-t)))
    _ < ε := (lt_div_iff₀ (by positivity : 0 < K + 1)).mp hb

end MultipoleBKT.RouteHessian

end
