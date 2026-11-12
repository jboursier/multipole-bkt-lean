/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.Smoothness
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Full rate-function Hessian on positive coordinates

The entropy Hessian is the reciprocal-coordinate diagonal. Adding the cluster Hessian
proves the perturbation estimate and (5.157) in
the paper. Derivatives are asserted only where
all coordinates are positive.
-/

@[expose] public section

namespace MultipoleBKT

open Finset Real Set Filter Topology

variable {p : ℕ}

/-- The coordinate term `s (log k! - 1 + log s - log 𝗆(k))`, `k = i + 1`, of the rate
function. -/
noncomputable def rateEntTerm (msf : ℕ → ℝ) (i : Fin p) (s : ℝ) : ℝ :=
  s * (Real.log ((i : ℕ) + 1).factorial - 1 + Real.log s - Real.log (msf ((i : ℕ) + 1)))

theorem rateFunction_eq_ent (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) :
    rateFunction p msf kmult γ = ∑ i : Fin p, rateEntTerm msf i (γ i) + 1 + rateCluster p kmult γ :=
  rfl

theorem rateFunction_sub_eq (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ η : Fin p → ℝ) :
    rateFunction p msf kmult η - rateFunction p msf kmult γ =
      ∑ i : Fin p, (rateEntTerm msf i (η i) - rateEntTerm msf i (γ i)) +
        (rateCluster p kmult η - rateCluster p kmult γ) := by
  rw [rateFunction_eq_ent, rateFunction_eq_ent, sum_sub_distrib]
  ring

theorem continuous_rateEntTerm (msf : ℕ → ℝ) (i : Fin p) : Continuous (rateEntTerm msf i) := by
  have : rateEntTerm msf i = fun s => s * (Real.log ((i : ℕ) + 1).factorial - 1 -
      Real.log (msf ((i : ℕ) + 1))) + s * Real.log s := by
    funext s
    rw [rateEntTerm]
    ring
  rw [this]
  exact (continuous_id.mul continuous_const).add Real.continuous_mul_log

theorem hasDerivAt_rateEntTerm (msf : ℕ → ℝ) (i : Fin p) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (rateEntTerm msf i)
      (Real.log ((i : ℕ) + 1).factorial + Real.log s - Real.log (msf ((i : ℕ) + 1))) s := by
  have h := (hasDerivAt_id s).mul (((hasDerivAt_const s
    (Real.log ((i : ℕ) + 1).factorial - 1)).add (Real.hasDerivAt_log hs.ne')).sub
    (hasDerivAt_const s (Real.log (msf ((i : ℕ) + 1)))))
  have hfun : rateEntTerm msf i = id * ((fun _ => Real.log ((i : ℕ) + 1).factorial - 1) +
      Real.log - fun _ => Real.log (msf ((i : ℕ) + 1))) := by
    funext x
    simp [rateEntTerm]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [id, Pi.add_apply, Pi.sub_apply]
  field_simp
  ring

/-- With the sup norm, `‖v‖² ≤ ∑ᵢ vᵢ²`. -/
theorem norm_sq_le_sum_sq (v : Fin p → ℝ) : ‖v‖ ^ 2 ≤ ∑ i : Fin p, v i ^ 2 := by
  have h : ‖v‖ ≤ √(∑ i : Fin p, v i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (single_le_sum (fun j _ => sq_nonneg (v j)) (mem_univ i))
  calc ‖v‖ ^ 2 ≤ (√(∑ i : Fin p, v i ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i : Fin p, v i ^ 2 := Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)

theorem sum_sq_pos_of_ne_zero {v : Fin p → ℝ} (hv : v ≠ 0) : 0 < ∑ i : Fin p, v i ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact lt_of_lt_of_le (pow_pos (abs_pos.mpr hi) 2 |>.trans_eq (sq_abs _))
    (single_le_sum (fun j _ => sq_nonneg (v j)) (mem_univ i))

/-- The full gradient, with the entropy and cluster contributions. -/
noncomputable def rateGradient (p : ℕ) (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ)
    (γ : Fin p → ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin p, (Real.log ((i : ℕ) + 1).factorial + Real.log (γ i) -
    Real.log (msf ((i : ℕ) + 1))) • coordCLM i) + fderiv ℝ (rateCluster p kmult) γ

/-- The reciprocal-coordinate entropy diagonal plus the cluster Hessian. This formula
is defined everywhere, but represents the Hessian only at positive coordinates. -/
noncomputable def rateHessian (p : ℕ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) :
    (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin p, ((γ i)⁻¹ • coordCLM i).smulRight (coordCLM i)) +
    fderiv ℝ (fderiv ℝ (rateCluster p kmult)) γ

variable {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

theorem continuousOn_rateFunction (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) :
    ContinuousOn (rateFunction p msf kmult) (rateDomain p) := by
  have hH := (rateCluster_smooth_of_small hk hlam hsmall).1.continuousOn
  have hE : Continuous fun γ : Fin p → ℝ => ∑ i, rateEntTerm msf i (γ i) + 1 :=
    (continuous_finsetSum _ fun i _ =>
      (continuous_rateEntTerm msf i).comp (continuous_apply i)).add continuous_const
  have := hE.continuousOn.add hH
  exact this

/-- The full first derivative at a positive point. -/
theorem hasFDerivAt_rateFunction (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ}
    (hγ : γ ∈ rateDomain p) (hpos : ∀ i, 0 < γ i) :
    HasFDerivAt (rateFunction p msf kmult) (rateGradient p msf kmult γ) γ := by
  have he := HasFDerivAt.sum (u := univ)
    (A := fun (i : Fin p) (y : Fin p → ℝ) => rateEntTerm msf i (y i)) (x := γ)
    fun i _ => by
      simpa only [Function.comp_def] using
        (hasDerivAt_rateEntTerm msf i (hpos i)).comp_hasFDerivAt γ
          (hasFDerivAt_apply (𝕜 := ℝ) i γ)
  have heq : (∑ i : Fin p, fun y : Fin p → ℝ => rateEntTerm msf i (y i)) =
      fun y => ∑ i : Fin p, rateEntTerm msf i (y i) := by
    funext y
    simp only [Finset.sum_apply]
  rw [heq] at he
  exact (he.add_const 1).add ((rateCluster_smooth_of_small hk hlam hsmall).2 γ hγ).1

/-- Differentiating the full gradient gives the full Hessian at positive coordinates. -/
theorem hasFDerivAt_rateGradient (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ}
    (hγ : γ ∈ rateDomain p) (hpos : ∀ i, 0 < γ i) :
    HasFDerivAt (rateGradient p msf kmult) (rateHessian p kmult γ) γ := by
  have he := HasFDerivAt.sum (u := univ)
    (A := fun (i : Fin p) (y : Fin p → ℝ) => (Real.log ((i : ℕ) + 1).factorial + Real.log (y i) -
      Real.log (msf ((i : ℕ) + 1))) • coordCLM i) (x := γ) fun i _ =>
      ((((Real.hasDerivAt_log (hpos i).ne').comp_hasFDerivAt γ
        (hasFDerivAt_apply (𝕜 := ℝ) i γ)).const_add _).sub_const _).smul_const (coordCLM i)
  have heq : (∑ i : Fin p, fun y : Fin p → ℝ =>
      (Real.log ((i : ℕ) + 1).factorial + Real.log (y i) -
        Real.log (msf ((i : ℕ) + 1))) • coordCLM i) =
      fun y => ∑ i : Fin p, (Real.log ((i : ℕ) + 1).factorial + Real.log (y i) -
        Real.log (msf ((i : ℕ) + 1))) • coordCLM i := by
    funext y
    simp only [Finset.sum_apply]
  rw [heq] at he
  exact he.add ((rateCluster_smooth_of_small hk hlam hsmall).2 γ hγ).2.1

/-- The displayed Hessian formula, with the literal iterated Fréchet derivative. -/
theorem fderiv2_rateFunction (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ}
    (hγ : γ ∈ rateDomain p) (hpos : ∀ i, 0 < γ i) :
    fderiv ℝ (fderiv ℝ (rateFunction p msf kmult)) γ = rateHessian p kmult γ := by
  have heq : fderiv ℝ (rateFunction p msf kmult) =ᶠ[𝓝 γ] rateGradient p msf kmult := by
    have hpopen : IsOpen {y : Fin p → ℝ | ∀ i, 0 < y i} :=
      by
        simpa only [Set.iInter_ofPred] using
          (isOpen_iInter_of_finite fun i : Fin p => isOpen_lt continuous_const (continuous_apply i))
    filter_upwards [isOpen_rateDomain.mem_nhds hγ, hpopen.mem_nhds hpos] with y hy hp
    exact (hasFDerivAt_rateFunction hk hlam hsmall hy hp).fderiv
  exact ((hasFDerivAt_rateGradient (msf := msf) hk hlam hsmall hγ hpos).congr_of_eventuallyEq
    heq).fderiv

/-- Evaluation of the Hessian on two directions. -/
theorem rateHessian_apply (γ v w : Fin p → ℝ) :
    rateHessian p kmult γ v w = ∑ i : Fin p, (γ i)⁻¹ * v i * w i +
      fderiv ℝ (fderiv ℝ (rateCluster p kmult)) γ v w := by
  simp only [rateHessian, add_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  rfl

/-- The operator-norm bound for the perturbation, evaluated on arbitrary directions. -/
theorem rateHessian_sub_diagonal_le (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ}
    (hγ : γ ∈ rateDomain p) (v w : Fin p → ℝ) :
    |rateHessian p kmult γ v w - ∑ i : Fin p, (γ i)⁻¹ * v i * w i| ≤
      (16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2) * ‖v‖ * ‖w‖ := by
  rw [rateHessian_apply, add_sub_cancel_left, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (rateCluster p kmult)) γ v‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ (rateCluster p kmult)) γ‖ * ‖v‖ * ‖w‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ _ := by
      gcongr
      exact ((rateCluster_smooth_of_small hk hlam hsmall).2 γ hγ).2.2.2.2

/-- (5.157). The domination holds
as a quadratic-form inequality at every positive point of the unit box. -/
theorem rateHessian_ge_half_diagonal (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 ≤ 1 / 2)
    {γ : Fin p → ℝ} (hγ : ∀ i, γ i ∈ Icc (0 : ℝ) 1) (hpos : ∀ i, 0 < γ i)
    (v : Fin p → ℝ) :
    (1 / 2 : ℝ) * ∑ i : Fin p, v i ^ 2 / γ i ≤ rateHessian p kmult γ v v := by
  set B := 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2
  have hB0 : 0 ≤ B := by positivity
  have herr := rateHessian_sub_diagonal_le hk hlam hsmall (mem_rateDomain_of_mem_Icc hγ) v v
  have hs : ∑ i : Fin p, v i ^ 2 ≤ ∑ i : Fin p, v i ^ 2 / γ i := by
    refine sum_le_sum fun i _ => ?_
    exact (le_div_iff₀ (hpos i)).mpr (mul_le_of_le_one_right (sq_nonneg _) (hγ i).2)
  have hnorm := norm_sq_le_sum_sq v
  have hd : ∑ i : Fin p, (γ i)⁻¹ * v i * v i = ∑ i : Fin p, v i ^ 2 / γ i := by
    apply sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv, sq]
    ring
  rw [hd] at herr
  have hn : B * ‖v‖ * ‖v‖ ≤ (1 / 2 : ℝ) * ∑ i : Fin p, v i ^ 2 / γ i := by
    calc B * ‖v‖ * ‖v‖ = B * ‖v‖ ^ 2 := by ring
      _ ≤ B * ∑ i : Fin p, v i ^ 2 / γ i := mul_le_mul_of_nonneg_left (hnorm.trans hs) hB0
      _ ≤ _ := mul_le_mul_of_nonneg_right hB (sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hpos i).le)
  linarith [(abs_le.mp herr).1]

/-- Entrywise perturbation estimate preceding (5.157). Coordinate directions are the standard basis vectors. -/
theorem fderiv2_rateFunction_entry_bound (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ}
    (hγ : γ ∈ rateDomain p) (hpos : ∀ i, 0 < γ i) (i j : Fin p) :
    |fderiv ℝ (fderiv ℝ (rateFunction p msf kmult)) γ (Pi.single i 1) (Pi.single j 1) -
      (if i = j then (γ i)⁻¹ else 0)| ≤ 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 := by
  rw [fderiv2_rateFunction hk hlam hsmall hγ hpos]
  have h := rateHessian_sub_diagonal_le hk hlam hsmall hγ (Pi.single i 1) (Pi.single j 1)
  have hd : (∑ k : Fin p, (γ k)⁻¹ * ((Pi.single i 1 : Fin p → ℝ) k) * (Pi.single j 1 : Fin p → ℝ) k) =
      if i = j then (γ i)⁻¹ else 0 := by
    rw [Fintype.sum_eq_single i (fun k hk => by simp [Pi.single_eq_of_ne hk])]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  simpa only [hd, Pi.norm_single, norm_one, mul_one] using h

/-- The full positive-coordinate Hessian domination with the literal second derivative,
(5.157). -/
theorem fderiv2_rateFunction_ge_half_diagonal (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 ≤ 1 / 2)
    {γ : Fin p → ℝ} (hγ : ∀ i, γ i ∈ Icc (0 : ℝ) 1) (hpos : ∀ i, 0 < γ i)
    (v : Fin p → ℝ) :
    (1 / 2 : ℝ) * ∑ i, v i ^ 2 / γ i ≤
      fderiv ℝ (fderiv ℝ (rateFunction p msf kmult)) γ v v := by
  rw [fderiv2_rateFunction hk hlam hsmall (mem_rateDomain_of_mem_Icc hγ) hpos]
  exact rateHessian_ge_half_diagonal hk hlam hsmall hB hγ hpos v

end MultipoleBKT

end
