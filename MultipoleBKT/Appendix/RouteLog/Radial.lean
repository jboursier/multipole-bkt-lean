/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Moments
public import TwoComponentCoulomb.LowerBound.PolarPi

/-!
# The three regimes of the logarithmic radial moment

See (A.42). The exponent `a` below is `4 - β`.
The radial density is `t max(t, λ)^(a-2)`. Splitting at `λ` gives an explicit
boundary term and an annular logarithmic moment. No positive auxiliary exponent
is introduced at the critical value `a = 0`.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set
open scoped ENNReal

/-- A logarithmic radial moment with its polar radial density. -/
noncomputable def radialLogMoment (a lam h : ℝ) (q : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..h,
    t * max t lam ^ (a - 2) * (1 + Real.log (h / max t lam)) ^ q

private theorem continuous_radialLogIntegrand {lam h : ℝ} (hlam : 0 < lam)
    (hh : 0 < h) (a : ℝ) (q : ℕ) :
    Continuous (fun t : ℝ =>
      t * max t lam ^ (a - 2) * (1 + Real.log (h / max t lam)) ^ q) := by
  have hm : Continuous (fun t : ℝ => max t lam) := continuous_id.max continuous_const
  have hm0 (t : ℝ) : max t lam ≠ 0 := (lt_max_of_lt_right hlam).ne'
  exact (continuous_id.mul (hm.rpow_const fun t => Or.inl (hm0 t))).mul
    ((continuous_const.add ((continuous_const.div hm hm0).log
      fun t => div_ne_zero hh.ne' (hm0 t))).pow q)

private theorem log_ratio_max_nonneg {lam h t : ℝ} (hlam : 0 < lam)
    (hlh : lam ≤ h) (hth : t ≤ h) : 0 ≤ 1 + Real.log (h / max t lam) := by
  have := Real.log_nonneg ((one_le_div (lt_max_of_lt_right hlam)).2 (max_le hth hlh))
  linarith

/-- Splitting the logarithmic radial moment into its core and annulus. -/
theorem radialLogMoment_split (a : ℝ) (q : ℕ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) :
    radialLogMoment a lam h q = lam ^ a / 2 * (1 + Real.log (h / lam)) ^ q +
      ∫ t in lam..h, t ^ (a - 1) * (1 + Real.log (h / t)) ^ q := by
  have hh : 0 < h := hlam.trans_le hlh
  have hc := continuous_radialLogIntegrand hlam hh a q
  unfold radialLogMoment
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 lam) (hc.intervalIntegrable lam h)]
  have hlow :
      (∫ t in (0 : ℝ)..lam,
        t * max t lam ^ (a - 2) * (1 + Real.log (h / max t lam)) ^ q) =
      lam ^ a / 2 * (1 + Real.log (h / lam)) ^ q := by
    calc
      _ = ∫ t in (0 : ℝ)..lam,
          t * lam ^ (a - 2) * (1 + Real.log (h / lam)) ^ q :=
        intervalIntegral.integral_congr fun t ht => by
          rw [max_eq_right (((uIcc_of_le hlam.le) ▸ ht).2)]
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, integral_id]
        have hp : lam ^ 2 * lam ^ (a - 2) = lam ^ a := by
          rw [← Real.rpow_two, ← Real.rpow_add hlam]
          congr 1
          ring
        calc
          (lam ^ 2 - 0 ^ 2) / 2 * lam ^ (a - 2) * (1 + Real.log (h / lam)) ^ q =
              (lam ^ 2 * lam ^ (a - 2)) / 2 * (1 + Real.log (h / lam)) ^ q := by ring
          _ = _ := by rw [hp]
  have hhigh :
      (∫ t in lam..h,
        t * max t lam ^ (a - 2) * (1 + Real.log (h / max t lam)) ^ q) =
      ∫ t in lam..h, t ^ (a - 1) * (1 + Real.log (h / t)) ^ q := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hlt := ((uIcc_of_le hlh) ▸ ht).1
    dsimp only
    rw [max_eq_left hlt, show t * t ^ (a - 2) = t ^ (a - 1) by
      rw [mul_comm, ← Real.rpow_add_one (hlam.trans_le hlt).ne']
      congr 1
      ring]
  rw [hlow, hhigh]

/-- The ordered inner-radius logarithmic moment for `2 < β < 4`.
The constant depends on the exponent and moment order, and is uniform in both cutoffs. -/
theorem radialLogMoment_le_of_pos {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) (q : ℕ)
    {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) :
    radialLogMoment a lam h q ≤ momentConstant a q * h ^ a := by
  rw [radialLogMoment_split a q hlam hlh]
  have hp : 0 ≤ lam ^ a := Real.rpow_nonneg hlam.le _
  have hlog : 0 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  have hb : lam ^ a / 2 ≤ lam ^ a / a :=
    div_le_div_of_nonneg_left hp ha ha2
  have hm := mul_le_mul_of_nonneg_right hb (pow_nonneg hlog q)
  have hi := integral_power_log_add_boundary_le ha q hlam hlh
  linarith

/-- Exact critical logarithmic moment, used at `β = 4`. -/
theorem radialLogMoment_zero (q : ℕ) {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) :
    radialLogMoment 0 lam h q = (1 + Real.log (h / lam)) ^ q / 2 +
      ((1 + Real.log (h / lam)) ^ (q + 1) - 1) / (q + 1) := by
  rw [radialLogMoment_split 0 q hlam hlh]
  simp only [Real.rpow_zero, zero_sub, Real.rpow_neg_one]
  rw [integral_inverse_log_pow q hlam hlh]
  ring

/-- Critical bound with the logarithm retained. -/
theorem radialLogMoment_le_zero (q : ℕ) {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) :
    radialLogMoment 0 lam h q ≤
      (1 / 2 + 1 / ((q : ℝ) + 1)) * (1 + Real.log (h / lam)) ^ (q + 1) := by
  rw [radialLogMoment_zero q hlam hlh]
  have hL : 1 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  have hp : (1 + Real.log (h / lam)) ^ q ≤ (1 + Real.log (h / lam)) ^ (q + 1) := by
    exact pow_le_pow_right₀ hL (Nat.le_succ q)
  calc
    _ ≤ (1 + Real.log (h / lam)) ^ (q + 1) / 2 +
        (1 + Real.log (h / lam)) ^ (q + 1) / ((q : ℝ) + 1) :=
      add_le_add (div_le_div_of_nonneg_right hp (by norm_num))
        (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (by positivity))
    _ = _ := by ring

/-- The logarithmic factor can be bounded by its value at the lower cutoff. -/
theorem radialLogMoment_le_log_mul (a : ℝ) (q : ℕ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) :
    radialLogMoment a lam h q ≤
      (1 + Real.log (h / lam)) ^ q * radialLogMoment a lam h 0 := by
  have hh := hlam.trans_le hlh
  unfold radialLogMoment
  simp only [pow_zero, mul_one]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hh.le
    ((continuous_radialLogIntegrand hlam hh a q).intervalIntegrable 0 h)
    (((continuous_radialLogIntegrand hlam hh a 0).congr
      (fun t => by simp)).const_mul _ |>.intervalIntegrable 0 h)
  intro t ht
  have hm : 0 < max t lam := lt_max_of_lt_right hlam
  have hlog := log_ratio_max_nonneg hlam hlh ht.2
  have hle : 1 + Real.log (h / max t lam) ≤ 1 + Real.log (h / lam) := by
    gcongr
    exact le_max_right _ _
  have hp := pow_le_pow_left₀ hlog hle q
  have hd : 0 ≤ t * max t lam ^ (a - 2) :=
    mul_nonneg ht.1 (Real.rpow_nonneg hm.le _)
  nlinarith [mul_le_mul_of_nonneg_left hp hd]

/-- Negative-exponent moments, used for `β > 4`. -/
theorem radialLogMoment_le_of_neg {a : ℝ} (ha : a < 0) (q : ℕ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) :
    radialLogMoment a lam h q ≤
      (1 / 2 + 1 / (-a)) * lam ^ a * (1 + Real.log (h / lam)) ^ q := by
  have hbase : radialLogMoment a lam h 0 ≤ (1 / 2 + 1 / (-a)) * lam ^ a := by
    rw [radialLogMoment_split a 0 hlam hlh]
    simp only [pow_zero, mul_one]
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [uIcc_of_le hlh]
      exact fun ht => (not_le_of_gt hlam) ht.1⟩)]
    rw [show a - 1 + 1 = a by ring]
    have hh : 0 ≤ h ^ a := Real.rpow_nonneg (hlam.trans_le hlh).le _
    have hd : h ^ a / a ≤ 0 := div_nonpos_of_nonneg_of_nonpos hh ha.le
    have he : (h ^ a - lam ^ a) / a = h ^ a / a + lam ^ a / (-a) := by ring
    rw [he]
    calc
      _ = (1 / 2 + 1 / (-a)) * lam ^ a + h ^ a / a := by ring
      _ ≤ _ := add_le_of_nonpos_right hd
  have hp : 0 ≤ (1 + Real.log (h / lam)) ^ q := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    positivity
  calc
    _ ≤ (1 + Real.log (h / lam)) ^ q * radialLogMoment a lam h 0 :=
      radialLogMoment_le_log_mul a q hlam hlh
    _ ≤ (1 + Real.log (h / lam)) ^ q * ((1 / 2 + 1 / (-a)) * lam ^ a) :=
      mul_le_mul_of_nonneg_left hbase hp
    _ = _ := by ring

/-- Lower Lebesgue and Bochner forms of the logarithmic radial moment agree. -/
theorem lintegral_radialLogMoment (a : ℝ) (q : ℕ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) :
    ∫⁻ t in Ioc 0 h,
      ENNReal.ofReal (t * max t lam ^ (a - 2) * (1 + Real.log (h / max t lam)) ^ q) =
      ENNReal.ofReal (radialLogMoment a lam h q) := by
  have hh := hlam.trans_le hlh
  rw [radialLogMoment, intervalIntegral.integral_of_le hh.le,
    ofReal_integral_eq_lintegral_ofReal
      ((continuous_radialLogIntegrand hlam hh a q).continuousOn.integrableOn_Icc.mono_set
        Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht =>
        mul_nonneg (mul_nonneg ht.1.le (Real.rpow_nonneg (lt_max_of_lt_right hlam).le _))
          (pow_nonneg (log_ratio_max_nonneg hlam hlh ht.2) q)))]

end MultipoleBKT.RouteLog

end
