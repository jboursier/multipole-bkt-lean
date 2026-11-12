/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.RouteHessian.Segments
public import MultipoleBKT.Frozen.Simplex
public import Mathlib.Analysis.Convex.Deriv

/-!
# Strict convexity from the full rate-function Hessian

The proof follows the paper, (5.157). The entropy diagonal dominates the small cluster Hessian. On
positive coordinates this proves strict convexity directly. The retained closed-box
interface uses the same calculation along each face. Coordinates identically zero
on a segment are treated as constant functions, so entropy is never differentiated
at zero.
-/

@[expose] public section

namespace MultipoleBKT

open Finset Real Set

variable {p : ℕ}

/-- Internal one-dimensional strict-convexity criterion. Differentiation is required
only in the open interval, while continuity includes its endpoints. -/
private theorem strictConvexOn_interval_of_second_pos {ψ ψ' ψ'' : ℝ → ℝ}
    (hcont : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (h1 : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt ψ (ψ' t) t)
    (h2 : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt ψ' (ψ'' t) t)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ'' t) :
    StrictConvexOn ℝ (Icc 0 1) ψ := by
  have hmono : StrictMonoOn ψ' (Ioo (0 : ℝ) 1) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo 0 1)
      (fun t ht => (h2 t ht).continuousAt.continuousWithinAt)
      (fun t ht => (h2 t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hpos t (interior_subset ht))
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1) hcont ?_
  rw [interior_Icc]
  intro s hs t ht hst
  rw [(h1 s hs).deriv, (h1 t ht).deriv]
  exact hmono hs ht hst

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function whose second derivative is positive definite on a convex set is strictly convex
there. -/
private theorem strictConvexOn_of_positive_hessian {U : Set E} (hU : Convex ℝ U) {q : E → ℝ}
    {Dq : E → E →L[ℝ] ℝ} {D2q : E → E →L[ℝ] E →L[ℝ] ℝ}
    (h1 : ∀ x ∈ U, HasFDerivAt q (Dq x) x) (h2 : ∀ x ∈ U, HasFDerivAt Dq (D2q x) x)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < D2q x v v) : StrictConvexOn ℝ U q := by
  refine ⟨hU, fun x hx y hy hxy a b ha hb hab => ?_⟩
  set v := y - x with hv_def
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hz : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ U := by
    intro t ht
    have : x + t • v = (1 - t) • x + t • y := by
      rw [hv_def, smul_sub, sub_smul, one_smul]
      abel
    rw [this]
    exact hU hx hy (by linarith [ht.2]) ht.1 (by ring)
  have hzd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hψ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => q (x + t • v)) (Dq (x + t • v) v) t :=
    fun t ht => (h1 _ (hz t ht)).comp_hasDerivAt t (hzd t)
  have hψ' : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Dq (x + t • v) v) (D2q (x + t • v) v v) t := by
    intro t ht
    have hc : HasDerivAt (fun t : ℝ => Dq (x + t • v)) (D2q (x + t • v) v) t :=
      (h2 _ (hz t ht)).comp_hasDerivAt t (hzd t)
    have h := hc.clm_apply (hasDerivAt_const t v)
    refine h.congr_deriv ?_
    rw [map_zero, add_zero]
  have hsc := strictConvexOn_interval_of_second_pos
    (fun t ht => (hψ t ht).continuousAt.continuousWithinAt)
    (fun t ht => hψ t (Ioo_subset_Icc_self ht))
    (fun t ht => hψ' t (Ioo_subset_Icc_self ht))
    (fun t ht => hpos _ (hz t (Ioo_subset_Icc_self ht)) v hv)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1' : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have key := hsc.2 h0 h1' zero_ne_one ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_smul, add_zero, one_smul, zero_add] at key
  have e1 : x + b • v = a • x + b • y := by
    obtain rfl : a = 1 - b := by linarith
    rw [hv_def, smul_sub, sub_smul, one_smul]
    abel
  have e2 : x + v = y := by rw [hv_def]; abel
  rw [e1, e2] at key
  exact key

/-- The box `[0,1]^p`. -/
def unitBox (p : ℕ) : Set (Fin p → ℝ) :=
  Set.univ.pi fun _ => Icc (0 : ℝ) 1

theorem mem_unitBox {γ : Fin p → ℝ} : γ ∈ unitBox p ↔ ∀ i, γ i ∈ Icc (0 : ℝ) 1 := by
  simp only [unitBox, Set.mem_pi, Set.mem_univ, true_imp_iff]

theorem convex_unitBox : Convex ℝ (unitBox p) :=
  convex_pi fun _ _ => convex_Icc 0 1

theorem unitBox_subset_rateDomain : unitBox p ⊆ rateDomain p := fun _ hγ =>
  mem_rateDomain_of_mem_Icc (mem_unitBox.mp hγ)

theorem simplex_subset_unitBox (x : ℝ) : simplex p x ⊆ unitBox p := fun _ hγ =>
  mem_unitBox.mpr hγ.1

theorem convex_simplex (x : ℝ) : Convex ℝ (simplex p x) := by
  intro γ hγ η hη a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have := convex_Icc (0 : ℝ) 1 (hγ.1 i) (hη.1 i) ha hb hab
    simpa using this
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * (a * γ i + b * η i) =
        a * ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * γ i + b * ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * η i := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [e, hγ.2, hη.2]
    linear_combination (1 - x) * hab

variable {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

/-- Strict convexity on the closed box, obtained from the full Hessian along its faces.
This retains the interface consumed by the minimizer theorem. -/
theorem strictConvexOn_rateFunction_box (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 < 1) :
    StrictConvexOn ℝ (unitBox p) (rateFunction p msf kmult) := by
  refine ⟨convex_unitBox, fun x hx y hy hxy a b ha hb hab => ?_⟩
  set v := y - x with hv_def
  have hv : v ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hz : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ unitBox p :=
    fun t ht => convex_unitBox.add_smul_sub_mem hx hy ht
  have hcoord : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i, 0 < (x + t • v) i ∨ v i = 0 := by
    intro t ht i
    by_cases hzero : x i = 0 ∧ y i = 0
    · right
      simp [hv_def, Pi.sub_apply, hzero.1, hzero.2]
    · left
      have hxi := (mem_unitBox.mp hx i).1
      have hyi := (mem_unitBox.mp hy i).1
      have he : (x + t • v) i = (1 - t) * x i + t * y i := by
        simp only [hv_def, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [he]
      rcases lt_or_eq_of_le hxi with hi | hi
      · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith [ht.2]) hi) (mul_nonneg ht.1.le hyi)
      · have hypos : 0 < y i := lt_of_le_of_ne hyi (fun h => hzero ⟨hi.symm, h.symm⟩)
        exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.2]) hxi) (mul_pos ht.1 hypos)
  have hcont : ContinuousOn (fun t : ℝ => rateFunction p msf kmult (x + t • v)) (Icc 0 1) :=
    (continuousOn_rateFunction hk hlam hsmall).comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun t ht => unitBox_subset_rateDomain (hz t ht))
  have hsc := strictConvexOn_interval_of_second_pos hcont
    (fun t ht => hasDerivAt_rateFunction_line hk hlam hsmall x v t
      (unitBox_subset_rateDomain (hz t (Ioo_subset_Icc_self ht))) (hcoord t ht))
    (fun t ht => hasDerivAt_rateGradient_line hk hlam hsmall x v t
      (unitBox_subset_rateDomain (hz t (Ioo_subset_Icc_self ht))) (hcoord t ht))
    (fun t ht => rateHessian_pos_on_face hk hlam hsmall hB
      (mem_unitBox.mp (hz t (Ioo_subset_Icc_self ht))) (hcoord t ht) hv)
  have key := hsc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) zero_ne_one ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_smul, add_zero, one_smul, zero_add] at key
  have he : x + b • v = a • x + b • y := by
    obtain rfl : a = 1 - b := by linarith
    rw [hv_def, smul_sub, sub_smul, one_smul]
    abel
  have he1 : x + v = y := by rw [hv_def]; abel
  rwa [he, he1] at key

/-- Positive-coordinate strict convexity from (5.157). -/
theorem strictConvexOn_rateFunction_positive (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 < 1) :
    StrictConvexOn ℝ (unitBox p ∩ {γ | ∀ i, 0 < γ i}) (rateFunction p msf kmult) := by
  have hconv : Convex ℝ (unitBox p ∩ {γ : Fin p → ℝ | ∀ i, 0 < γ i}) := by
    apply convex_unitBox.inter
    simpa [Set.iInter_ofPred, coordCLM] using
      (convex_iInter fun i : Fin p => convex_halfSpace_gt (coordCLM i).toLinearMap.isLinear 0)
  apply strictConvexOn_of_positive_hessian hconv
    (Dq := rateGradient p msf kmult) (D2q := rateHessian p kmult)
    (fun γ hγ => hasFDerivAt_rateFunction hk hlam hsmall (unitBox_subset_rateDomain hγ.1) hγ.2)
    (fun γ hγ => hasFDerivAt_rateGradient hk hlam hsmall (unitBox_subset_rateDomain hγ.1) hγ.2)
  intro γ hγ v hv
  exact rateHessian_pos_on_face hk hlam hsmall hB (mem_unitBox.mp hγ.1)
    (fun i => Or.inl (hγ.2 i)) hv

/-- Strict convexity on `Δ_{p,x}`. -/
theorem strictConvexOn_rateFunction_simplex (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 < 1) (x : ℝ) :
    StrictConvexOn ℝ (simplex p x) (rateFunction p msf kmult) :=
  (strictConvexOn_rateFunction_box hk hlam hsmall hB).subset (simplex_subset_unitBox x)
    (convex_simplex x)

end MultipoleBKT

end
