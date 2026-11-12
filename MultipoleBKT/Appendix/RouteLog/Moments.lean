/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RadialIntegral

/-!
# Finite logarithmic radial moments

See the proof of Lemma A.4 and (A.42).
Integration by parts retains the logarithmic moments. The positive-exponent bound
is uniform in the lower cutoff. The zero exponent has a logarithmic primitive.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set
open scoped ENNReal

/-- The finite polynomial moment constant obtained by integration by parts. -/
noncomputable def momentConstant (a : ℝ) : ℕ → ℝ
  | 0 => 1 / a
  | q + 1 => 1 / a + (q + 1) / a * momentConstant a q

theorem momentConstant_pos {a : ℝ} (ha : 0 < a) (q : ℕ) :
    0 < momentConstant a q := by
  induction q with
  | zero => simpa [momentConstant] using one_div_pos.mpr ha
  | succ q ih => simp only [momentConstant]; positivity

private theorem continuousOn_power_log (a : ℝ) (q : ℕ) {lam h : ℝ} (hlam : 0 < lam) :
    ContinuousOn (fun t : ℝ => t ^ (a - 1) * (1 + Real.log (h / t)) ^ q) (Icc lam h) := by
  refine (continuousOn_id.rpow_const fun t ht => Or.inl (hlam.trans_le ht.1).ne').mul ?_
  refine (continuousOn_const.add ?_).pow q
  refine Real.continuousOn_log.comp (continuousOn_const.div continuousOn_id
    fun t ht => (hlam.trans_le ht.1).ne') ?_
  intro t ht
  change h / t ≠ 0
  exact div_ne_zero (hlam.trans_le (ht.1.trans ht.2)).ne' (hlam.trans_le ht.1).ne'

private theorem hasDerivAt_log_ratio {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => 1 + Real.log (h / t)) (-t⁻¹) t := by
  have hd := ((Real.hasDerivAt_log (div_pos hh ht).ne').comp t
    ((hasDerivAt_const t h).div (hasDerivAt_id t) ht.ne')).const_add 1
  change HasDerivAt (fun t : ℝ => 1 + Real.log (h / t))
    ((h / t)⁻¹ * ((0 * t - h * 1) / t ^ 2)) t at hd
  convert hd using 1
  field_simp
  ring

private theorem hasDerivAt_power_log (a : ℝ) (q : ℕ) {h t : ℝ}
    (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t ^ a * (1 + Real.log (h / t)) ^ (q + 1))
      (a * (t ^ (a - 1) * (1 + Real.log (h / t)) ^ (q + 1)) -
        (q + 1) * (t ^ (a - 1) * (1 + Real.log (h / t)) ^ q)) t := by
  convert (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).mul
    ((hasDerivAt_log_ratio hh ht).pow (q + 1)) using 1
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply]
  rw [show t ^ a = t ^ (a - 1) * t by
    rw [← Real.rpow_add_one ht.ne']; congr 1; ring]
  field_simp
  ring

/-- Integration by parts for the annular logarithmic moment.
This is the recurrence used for the inner ordered-radius integral in Appendix A. -/
theorem integral_power_log_recurrence (a : ℝ) (q : ℕ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) :
    a * (∫ t in lam..h, t ^ (a - 1) * (1 + Real.log (h / t)) ^ (q + 1)) =
      h ^ a - lam ^ a * (1 + Real.log (h / lam)) ^ (q + 1) +
        (q + 1) * (∫ t in lam..h, t ^ (a - 1) * (1 + Real.log (h / t)) ^ q) := by
  have hh : 0 < h := hlam.trans_le hlh
  have hi (j : ℕ) : IntervalIntegrable
      (fun t : ℝ => t ^ (a - 1) * (1 + Real.log (h / t)) ^ j) volume lam h :=
    ((continuousOn_power_log a j hlam).mono (by rw [uIcc_of_le hlh])).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_power_log a q hh
      (hlam.trans_le ((uIcc_of_le hlh) ▸ ht).1))
    ((hi (q + 1)).const_mul a |>.sub ((hi q).const_mul (q + 1)))
  simp only [div_self hh.ne', Real.log_one, add_zero, one_pow, mul_one] at he
  rw [intervalIntegral.integral_sub ((hi (q + 1)).const_mul a) ((hi q).const_mul (q + 1)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  linarith

/-- Uniform positive-exponent logarithmic moment, with its lower boundary term retained. -/
theorem integral_power_log_add_boundary_le {a : ℝ} (ha : 0 < a) (q : ℕ)
    {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) :
    (∫ t in lam..h, t ^ (a - 1) * (1 + Real.log (h / t)) ^ q) +
      lam ^ a / a * (1 + Real.log (h / lam)) ^ q ≤ momentConstant a q * h ^ a := by
  have hh : 0 < h := hlam.trans_le hlh
  have hlog : 0 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  induction q with
  | zero =>
      simp only [pow_zero, mul_one, momentConstant]
      rw [integral_rpow (Or.inl (by linarith : -1 < a - 1))]
      rw [show a - 1 + 1 = a by ring]
      field_simp
      nlinarith
  | succ q ih =>
      have hrec := integral_power_log_recurrence a q hlam hlh
      have hb : 0 ≤ lam ^ a / a * (1 + Real.log (h / lam)) ^ q := by positivity
      have hi : (∫ t in lam..h, t ^ (a - 1) * (1 + Real.log (h / t)) ^ q) ≤
          momentConstant a q * h ^ a := le_trans (le_add_of_nonneg_right hb) ih
      have hq : (0 : ℝ) ≤ q + 1 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hi hq
      rw [momentConstant]
      have heq :
          (∫ t in lam..h, t ^ (a - 1) * (1 + Real.log (h / t)) ^ (q + 1)) +
            lam ^ a / a * (1 + Real.log (h / lam)) ^ (q + 1) =
          (h ^ a + (q + 1) *
            (∫ t in lam..h, t ^ (a - 1) * (1 + Real.log (h / t)) ^ q)) / a := by
        apply (eq_div_iff ha.ne').2
        calc
          _ = a * (∫ t in lam..h, t ^ (a - 1) * (1 + Real.log (h / t)) ^ (q + 1)) +
              lam ^ a * (1 + Real.log (h / lam)) ^ (q + 1) := by field_simp
          _ = _ := by linarith
      rw [heq]
      calc
        _ ≤ (h ^ a + (q + 1) * (momentConstant a q * h ^ a)) / a := by
          exact div_le_div_of_nonneg_right (add_le_add_right hmul _) ha.le
        _ = _ := by ring

/-- The critical logarithmic primitive, without absorbing its logarithm. -/
theorem integral_inverse_log_pow (q : ℕ) {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) :
    ∫ t in lam..h, t⁻¹ * (1 + Real.log (h / t)) ^ q =
      ((1 + Real.log (h / lam)) ^ (q + 1) - 1) / (q + 1) := by
  have hh : 0 < h := hlam.trans_le hlh
  have hi : IntervalIntegrable (fun t : ℝ => t⁻¹ * (1 + Real.log (h / t)) ^ q)
      volume lam h := by
    simpa only [zero_sub, Real.rpow_neg_one] using
      ((continuousOn_power_log 0 q hlam).mono (by rw [uIcc_of_le hlh])).intervalIntegrable (μ := volume)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -(1 + Real.log (h / t)) ^ (q + 1) / (q + 1))
    (fun t ht => by
      have ht0 : 0 < t := hlam.trans_le ((uIcc_of_le hlh) ▸ ht).1
      convert (((hasDerivAt_log_ratio hh ht0).pow (q + 1)).neg.div_const (q + 1)) using 1
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      field_simp) hi
  simp only [div_self hh.ne', Real.log_one, add_zero, one_pow] at he
  rw [he]
  ring

/-- The untruncated logarithmic moment at zero. The estimate is uniform in the
lower cutoff before monotone convergence removes it. -/
theorem lintegral_power_log_moment {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (q : ℕ) :
    ∫⁻ t in Ioc 0 h, ENNReal.ofReal (t ^ (a - 1) * (1 + Real.log (h / t)) ^ q) ≤
      ENNReal.ofReal (momentConstant a q * h ^ a) := by
  let s : ℕ → Set ℝ := fun n => Ioc (h / ((n : ℝ) + 1)) h
  have hpos (n : ℕ) : 0 < h / ((n : ℝ) + 1) := div_pos hh (by positivity)
  have hle (n : ℕ) : h / ((n : ℝ) + 1) ≤ h :=
    div_le_self hh.le (by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n])
  have hdir : Directed (· ⊆ ·) s := by
    intro n m
    refine ⟨max n m, Ioc_subset_Ioc_left ?_, Ioc_subset_Ioc_left ?_⟩ <;>
      gcongr <;> omega
  have hunion : (⋃ n, s n) = Ioc 0 h := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := mem_iUnion.mp ht
      exact ⟨(hpos n).trans hn.1, hn.2⟩
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_gt (h / t)
      apply mem_iUnion.mpr
      refine ⟨n, ?_, ht.2⟩
      apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
      have he := (div_lt_iff₀ ht.1).mp hn
      nlinarith
  rw [← hunion, setLIntegral_iUnion_of_directed _ hdir]
  apply iSup_le
  intro n
  have hi : IntegrableOn
      (fun t : ℝ => t ^ (a - 1) * (1 + Real.log (h / t)) ^ q) (s n) :=
    (continuousOn_power_log (h := h) a q (hpos n)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (s n)]
      (fun t : ℝ => t ^ (a - 1) * (1 + Real.log (h / t)) ^ q) := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
    apply Filter.Eventually.of_forall
    intro t ht
    have ht0 : 0 < t := (hpos n).trans ht.1
    have hlog : 0 ≤ Real.log (h / t) := Real.log_nonneg ((one_le_div ht0).2 ht.2)
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, ← intervalIntegral.integral_of_le (hle n)]
  apply ENNReal.ofReal_le_ofReal
  have hb := integral_power_log_add_boundary_le ha q (hpos n) (hle n)
  have hlog : 0 ≤ Real.log (h / (h / ((n : ℝ) + 1))) :=
    Real.log_nonneg ((one_le_div (hpos n)).2 (hle n))
  have hboundary : 0 ≤ (h / ((n : ℝ) + 1)) ^ a / a *
      (1 + Real.log (h / (h / ((n : ℝ) + 1)))) ^ q := by positivity
  linarith

end MultipoleBKT.RouteLog

end
