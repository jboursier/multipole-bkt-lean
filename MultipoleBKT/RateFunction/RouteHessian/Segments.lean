/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.RouteHessian.Derivatives

/-!
# Derivatives along rate-function segments

The calculation in (5.157) and Step 5 of the proof of Theorem 2 is applied along affine segments. For the closed-box
convexity interface we also allow coordinates constant along a face. Such coordinates
are differentiated as constant functions, without differentiating entropy at zero.
-/

@[expose] public section

namespace MultipoleBKT

open Finset Real Set

variable {p : ℕ} {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

/-- Internal segment calculation. Each moving coordinate must be positive. -/
theorem hasDerivAt_rateFunction_line (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) (x v : Fin p → ℝ) (t : ℝ)
    (hz : x + t • v ∈ rateDomain p) (hc : ∀ i, 0 < (x + t • v) i ∨ v i = 0) :
    HasDerivAt (fun u : ℝ => rateFunction p msf kmult (x + u • v))
      (rateGradient p msf kmult (x + t • v) v) t := by
  have he := HasDerivAt.sum (u := univ)
    (A := fun (i : Fin p) (u : ℝ) => rateEntTerm msf i (x i + u * v i))
    (A' := fun i => (Real.log ((i : ℕ) + 1).factorial + Real.log (x i + t * v i) -
      Real.log (msf ((i : ℕ) + 1))) * v i) (x := t) fun i _ => by
      rcases hc i with hi | hi
      · simpa only [Function.comp_def, id_eq, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          using (hasDerivAt_rateEntTerm msf i hi).comp t
          (((hasDerivAt_id t).mul_const (v i)).const_add (x i))
      · simpa only [hi, mul_zero, add_zero] using
          (hasDerivAt_const t (rateEntTerm msf i (x i)))
  have hh := ((rateCluster_smooth_of_small hk hlam hsmall).2 _ hz).1.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const v).const_add x)
  have h := (he.add_const 1).add hh
  convert h using 1
  · funext u
    simp only [rateFunction_eq_ent, Finset.sum_apply, Function.comp_def, id_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp only [rateGradient, add_apply, FunLike.coe_sum, Finset.sum_apply, smul_apply,
      smul_eq_mul, coordCLM, ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply, one_smul]

/-- Internal second derivative along a segment, with constant face coordinates allowed. -/
theorem hasDerivAt_rateGradient_line (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) (x v : Fin p → ℝ) (t : ℝ)
    (hz : x + t • v ∈ rateDomain p) (hc : ∀ i, 0 < (x + t • v) i ∨ v i = 0) :
    HasDerivAt (fun u : ℝ => rateGradient p msf kmult (x + u • v) v)
      (rateHessian p kmult (x + t • v) v v) t := by
  have he := HasDerivAt.sum (u := univ)
    (A := fun (i : Fin p) (u : ℝ) =>
      (Real.log ((i : ℕ) + 1).factorial + Real.log (x i + u * v i) -
        Real.log (msf ((i : ℕ) + 1))) * v i)
    (A' := fun i => (x i + t * v i)⁻¹ * v i * v i) (x := t) fun i _ => by
      rcases hc i with hi | hi
      · simpa only [Function.comp_def, id_eq, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          using (((((Real.hasDerivAt_log hi.ne').comp t
          (((hasDerivAt_id t).mul_const (v i)).const_add (x i))).const_add _).sub_const _).mul_const _)
      · simpa only [hi, mul_zero] using (hasDerivAt_const t (0 : ℝ))
  have hh := ((rateCluster_smooth_of_small hk hlam hsmall).2 _ hz).2.1.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const v).const_add x)
  have hh' := hh.clm_apply (hasDerivAt_const t v)
  simp only [map_zero, add_zero] at hh'
  have h := he.add hh'
  convert h using 1
  · funext u
    simp only [rateGradient, add_apply, FunLike.coe_sum, Finset.sum_apply, smul_apply,
      smul_eq_mul, coordCLM, ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply, Function.comp_def, id_eq]
  · simp only [rateHessian_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_smul]

/-- On a face, the Hessian is positive in every nonzero direction tangent to that face.
This extends the positive-coordinate calculation without claiming differentiability at zero. -/
theorem rateHessian_pos_on_face (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 < 1)
    {γ v : Fin p → ℝ} (hγ : ∀ i, γ i ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, 0 < γ i ∨ v i = 0) (hv : v ≠ 0) :
    0 < rateHessian p kmult γ v v := by
  set B := 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2
  have herr := rateHessian_sub_diagonal_le hk hlam hsmall (mem_rateDomain_of_mem_Icc hγ) v v
  have hs : ∑ i, v i ^ 2 ≤ ∑ i, (γ i)⁻¹ * v i * v i := by
    refine sum_le_sum fun i _ => ?_
    rcases hc i with hi | hi
    · have h := (le_div_iff₀ hi).mpr (mul_le_of_le_one_right (sq_nonneg (v i)) (hγ i).2)
      convert h using 1
      simp only [div_eq_mul_inv, sq]
      ring
    · simp [hi]
  have hn : B * ‖v‖ * ‖v‖ ≤ B * ∑ i, v i ^ 2 := by
    calc B * ‖v‖ * ‖v‖ = B * ‖v‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sq_le_sum_sq v) (by positivity)
  have hp := sum_sq_pos_of_ne_zero hv
  have hlt : B * ∑ i, v i ^ 2 < ∑ i, v i ^ 2 := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hB hp
  linarith [(abs_le.mp herr).1]

end MultipoleBKT

end
