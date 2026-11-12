/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.Minimizer
public import MultipoleBKT.RateFunction.RouteHessian.Integration

/-!
# Weighted quadratic gap by Hessian integration and a boundary limit

We follow Step 5 of the proof of Theorem 2 in the paper. Every compact proper subsegment from the positive minimizer has
positive coordinates. Integrating (5.157) twice gives the weighted
quadratic bound there. Continuity then lets the segment parameter increase to one,
including endpoints with zero coordinates.
-/

@[expose] public section

namespace MultipoleBKT

open Finset Set Filter Topology

variable {p : ℕ} {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

/-- Internal first-order condition, obtained from nonnegative right-hand slopes. -/
theorem rateGradient_nonneg_of_isMinOn (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ η : Fin p → ℝ}
    (hγ : γ ∈ simplex p 0) (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ)
    (hpos : ∀ i, 0 < γ i) (hη : η ∈ simplex p 0) :
    0 ≤ rateGradient p msf kmult γ (η - γ) := by
  have hd' : HasDerivAt (fun t : ℝ => rateFunction p msf kmult (γ + t • (η - γ)))
      (rateGradient p msf kmult γ (η - γ)) 0 := by
    have h := hasDerivAt_rateFunction_line (msf := msf) hk hlam hsmall γ (η - γ) 0
      (by simpa only [zero_smul, add_zero] using
        unitBox_subset_rateDomain (simplex_subset_unitBox 0 hγ))
      (by simpa only [zero_smul, add_zero] using fun i => Or.inl (b := (η - γ) i = 0) (hpos i))
    simpa only [zero_smul, add_zero] using h
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ t⁻¹ •
      (rateFunction p msf kmult (γ + (0 + t) • (η - γ)) -
        rateFunction p msf kmult (γ + (0 : ℝ) • (η - γ))) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds one_pos),
      self_mem_nhdsWithin] with t ht1 ht0
    have ht : 0 < t := ht0
    have hmem := (convex_simplex 0).add_smul_sub_mem hγ hη ⟨ht.le, ht1.le⟩
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hmin hmem))
  exact ge_of_tendsto hd'.tendsto_slope_zero_right he

/-- Internal compact-subsegment estimate. All differentiated coordinates remain positive.
The factor `1/4` is the product of the Hessian's `1/2` and the integral of `t`. -/
theorem rateFunction_segment_quadratic (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 ≤ 1 / 2)
    {γ η : Fin p → ℝ} (hγ : γ ∈ unitBox p) (hpos : ∀ i, 0 < γ i)
    (hη : η ∈ unitBox p) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    rateFunction p msf kmult γ + rateGradient p msf kmult γ (η - γ) * s +
      s ^ 2 / 4 * ∑ i, (η i - γ i) ^ 2 / max (η i) (γ i) ≤
      rateFunction p msf kmult (γ + s • (η - γ)) := by
  set v := η - γ with hv_def
  have hz : ∀ t ∈ Icc (0 : ℝ) s, γ + t • v ∈ unitBox p := fun t ht =>
    convex_unitBox.add_smul_sub_mem hγ hη ⟨ht.1, ht.2.trans hs.2.le⟩
  have hp : ∀ t ∈ Icc (0 : ℝ) s, ∀ i, 0 < (γ + t • v) i := by
    intro t ht i
    have hi := (mem_unitBox.mp hη i).1
    have he : (γ + t • v) i = (1 - t) * γ i + t * η i := by
      simp only [hv_def, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [he]
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith [ht.2, hs.2]) (hpos i))
      (mul_nonneg ht.1 hi)
  have hmax : ∀ t ∈ Icc (0 : ℝ) s, ∀ i, (γ + t • v) i ≤ max (η i) (γ i) := by
    intro t ht i
    have he : (γ + t • v) i = (1 - t) * γ i + t * η i := by
      simp only [hv_def, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [he]
    calc (1 - t) * γ i + t * η i ≤
        (1 - t) * max (η i) (γ i) + t * max (η i) (γ i) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith [ht.2, hs.2]))
          (mul_le_mul_of_nonneg_left (le_max_left _ _) ht.1)
      _ = _ := by ring
  have hcurv : ∀ t ∈ Icc (0 : ℝ) s,
      (1 / 2 : ℝ) * ∑ i, v i ^ 2 / max (η i) (γ i) ≤ rateHessian p kmult (γ + t • v) v v := by
    intro t ht
    refine le_trans (mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => ?_) (by norm_num))
      (rateHessian_ge_half_diagonal hk hlam hsmall hB (mem_unitBox.mp (hz t ht)) (hp t ht) v)
    exact div_le_div_of_nonneg_left (sq_nonneg _) (hp t ht i) (hmax t ht i)
  have h := quadratic_lower_of_hasDerivAt2 hs.1
    (fun t ht => hasDerivAt_rateFunction_line (msf := msf) hk hlam hsmall γ v t
      (unitBox_subset_rateDomain (hz t ht)) (fun i => Or.inl (hp t ht i)))
    (fun t ht => hasDerivAt_rateGradient_line (msf := msf) hk hlam hsmall γ v t
      (unitBox_subset_rateDomain (hz t ht)) (fun i => Or.inl (hp t ht i))) hcurv
  simp only [zero_smul, add_zero] at h
  change rateFunction p msf kmult γ + rateGradient p msf kmult γ v * s +
    s ^ 2 / 4 * ∑ i, v i ^ 2 / max (η i) (γ i) ≤ _
  convert h using 1
  ring

/-- The integrated Hessian bound, extended to the boundary by continuity.
This is a weighted Bregman lower bound, proved without relative entropy. -/
theorem rateFunction_weighted_bregman (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 ≤ 1 / 2)
    {γ η : Fin p → ℝ} (hγ : γ ∈ unitBox p) (hpos : ∀ i, 0 < γ i) (hη : η ∈ unitBox p) :
    rateFunction p msf kmult γ + rateGradient p msf kmult γ (η - γ) +
      (1 / 4 : ℝ) * ∑ i, (η i - γ i) ^ 2 / max (η i) (γ i) ≤
      rateFunction p msf kmult η := by
  have hpath : Continuous (fun s : ℝ => γ + s • (η - γ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have he : γ + (1 : ℝ) • (η - γ) = η := by simp
  have hr : Tendsto (fun s : ℝ => rateFunction p msf kmult (γ + s • (η - γ)))
      (𝓝[<] 1) (𝓝 (rateFunction p msf kmult η)) := by
    apply ((continuousOn_rateFunction hk hlam hsmall).continuousAt
      (isOpen_rateDomain.mem_nhds (unitBox_subset_rateDomain hη))).tendsto.comp
    simpa only [he] using (hpath.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun s : ℝ => rateFunction p msf kmult γ +
      rateGradient p msf kmult γ (η - γ) * s +
      s ^ 2 / 4 * ∑ i, (η i - γ i) ^ 2 / max (η i) (γ i))
      (𝓝[<] 1) (𝓝 (rateFunction p msf kmult γ + rateGradient p msf kmult γ (η - γ) +
        (1 / 4 : ℝ) * ∑ i, (η i - γ i) ^ 2 / max (η i) (γ i))) := by
    have hc : Continuous (fun s : ℝ => rateFunction p msf kmult γ +
        rateGradient p msf kmult γ (η - γ) * s +
        s ^ 2 / 4 * ∑ i, (η i - γ i) ^ 2 / max (η i) (γ i)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).add
        (((continuous_id.pow 2).div_const 4).mul continuous_const)
    simpa only [one_pow, mul_one] using
      (hc.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds zero_lt_one),
    self_mem_nhdsWithin] with s hs0 hs1
  exact rateFunction_segment_quadratic hk hlam hsmall hB hγ hpos hη ⟨hs0.le, hs1⟩

/-- The weighted quadratic gap at the minimizer in Step 5 of the proof of Theorem 2.
The endpoint may have zero coordinates. This stronger sum form implies the displayed
one-coordinate estimate. -/
theorem rateFunction_weighted_gap (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 ≤ 1 / 2)
    {γ η : Fin p → ℝ} (hγ : γ ∈ simplex p 0)
    (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ) (hη : η ∈ simplex p 0) :
    (1 / 4 : ℝ) * ∑ i, (η i - γ i) ^ 2 / max (η i) (γ i) ≤
      rateFunction p msf kmult η - rateFunction p msf kmult γ := by
  have hp := pos_of_isMinOn_rateFunction hk hlam hsmall hγ hmin
  have hg := rateGradient_nonneg_of_isMinOn hk hlam hsmall hγ hmin hp hη
  have h := rateFunction_weighted_bregman (msf := msf) hk hlam hsmall hB
    (simplex_subset_unitBox 0 hγ) hp (simplex_subset_unitBox 0 hη)
  linarith

/-- The displayed one-coordinate estimate of Step 5, obtained by integrating
(5.157) and taking the boundary limit. -/
theorem rateFunction_coordinate_gap (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 ≤ 1 / 2)
    {γ η : Fin p → ℝ} (hγ : γ ∈ simplex p 0)
    (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ) (hη : η ∈ simplex p 0)
    (i : Fin p) :
    (η i - γ i) ^ 2 / (4 * max (η i) (γ i)) ≤
      rateFunction p msf kmult η - rateFunction p msf kmult γ := by
  have hsum : (η i - γ i) ^ 2 / max (η i) (γ i) ≤
      ∑ j, (η j - γ j) ^ 2 / max (η j) (γ j) :=
    single_le_sum (fun j _ => div_nonneg (sq_nonneg (η j - γ j)) (le_max_of_le_left (hη.1 j).1 : 0 ≤ max (η j) (γ j))) (mem_univ i)
  calc (η i - γ i) ^ 2 / (4 * max (η i) (γ i)) =
      (1 / 4 : ℝ) * ((η i - γ i) ^ 2 / max (η i) (γ i)) := by ring
    _ ≤ (1 / 4 : ℝ) * ∑ j, (η j - γ j) ^ 2 / max (η j) (γ j) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ _ := rateFunction_weighted_gap hk hlam hsmall hB hγ hmin hη

end MultipoleBKT

end
