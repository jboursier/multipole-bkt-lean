/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Products
public import MultipoleBKT.Frozen.AlphaExponent

/-!
# The logarithmic radial cutoff gain

See (A.42). The offset `17` is retained in the integrand. The constants
in the three regimes are independent of the lower and upper cutoffs.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set Finset
open scoped ENNReal

/-- The radial integral displayed in (A.42), for `k+1` radii. -/
noncomputable def cutoffLogIntegral (β lam h : ℝ) (k q : ℕ) : ℝ≥0∞ :=
  ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
    ENNReal.ofReal ((1 + Real.log (17 * h / minimumRadius lam r)) ^ q) *
      ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β))

private theorem dilated_minimum_log_le {k : ℕ} (a : ℝ) (q : ℕ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) :
    (∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
      ENNReal.ofReal ((1 + Real.log (17 * h / minimumRadius lam r)) ^ q) *
        ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (a - 2))) ≤
      ENNReal.ofReal (1 + Real.log 17) ^ q *
        ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
          ENNReal.ofReal ((1 + Real.log (h / minimumRadius lam r)) ^ q) *
            ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (a - 2)) := by
  have hset : MeasurableSet (Set.univ.pi fun _ : Fin (k + 1) => Ioc (0 : ℝ) h) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have h17 : 0 ≤ Real.log 17 := Real.log_nonneg (by norm_num)
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  apply setLIntegral_mono' hset
  intro r hr
  obtain ⟨i, _, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => max (r i) lam)
  have hmin : minimumRadius lam r = max (r i) lam := he
  have hm0 : 0 < minimumRadius lam r := hmin ▸ lt_max_of_lt_right hlam
  have hmh : minimumRadius lam r ≤ h := by
    rw [hmin]
    exact max_le (hr i (Set.mem_univ i)).2 hlh
  have hlog : 0 ≤ Real.log (h / minimumRadius lam r) :=
    Real.log_nonneg ((one_le_div hm0).2 hmh)
  have heq : 1 + Real.log (17 * h / minimumRadius lam r) =
      1 + Real.log 17 + Real.log (h / minimumRadius lam r) := by
    rw [mul_div_assoc, Real.log_mul (by norm_num)
      (div_pos (hlam.trans_le hlh) hm0).ne']
    ring
  have hp : (1 + Real.log (17 * h / minimumRadius lam r)) ^ q ≤
      ((1 + Real.log 17) * (1 + Real.log (h / minimumRadius lam r))) ^ q := by
    apply pow_le_pow_left₀ (by rw [heq]; positivity)
    rw [heq]
    nlinarith
  rw [← mul_assoc]
  apply mul_le_mul' ?_ le_rfl
  rw [ENNReal.ofReal_pow (by linarith : 0 ≤ 1 + Real.log (h / minimumRadius lam r)),
    ← mul_pow, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal hp

/-- The subcritical logarithmic cutoff estimate, with a constant independent of `λ,h`. -/
theorem radial_cutoff_gain_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4) (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      cutoffLogIntegral β lam h k q ≤ ENNReal.ofReal (C * h ^ ((4 - β) * (k + 1))) := by
  let a := 4 - β
  have ha : 0 < a := by dsimp [a]; linarith
  have ha2 : a ≤ 2 := by dsimp [a]; linarith
  let C := (1 + Real.log 17) ^ q * ((k : ℝ) + 1) *
    momentConstant a q * momentConstant a 0 ^ k
  have h17 : 0 < 1 + Real.log 17 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 17 by norm_num)
    linarith
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos (mul_pos (pow_pos h17 q) (by positivity))
      (momentConstant_pos ha q)) (pow_pos (momentConstant_pos ha 0) k)
  refine ⟨C, hC, fun lam h hlam hlh => ?_⟩
  have hh := hlam.trans_le hlh
  have he : 2 - β = a - 2 := by dsimp [a]; ring
  unfold cutoffLogIntegral
  rw [he]
  refine (dilated_minimum_log_le a q hlam hlh).trans ?_
  calc
    _ ≤ ENNReal.ofReal (1 + Real.log 17) ^ q *
        ((k + 1) * ENNReal.ofReal (momentConstant a q * h ^ a) *
          ENNReal.ofReal (momentConstant a 0 * h ^ a) ^ k) := by
      gcongr
      exact lintegral_minimum_log_le_of_pos ha ha2 q hlam hlh
    _ = _ := by
      have hp : h ^ (a * (k + 1)) = h ^ a * (h ^ a) ^ k := by
        rw [mul_add, mul_one, Real.rpow_add hh, Real.rpow_mul hh.le, Real.rpow_natCast]
        ring
      rw [show (4 - β) * (k + 1) = a * (k + 1) from rfl, hp]
      dsimp only [C]
      rw [ENNReal.ofReal_mul (momentConstant_pos ha q).le,
        ENNReal.ofReal_mul (momentConstant_pos ha 0).le, mul_pow]
      have hCq := (momentConstant_pos ha q).le
      have hC0 := (momentConstant_pos ha 0).le
      simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
        ENNReal.ofReal_natCast, ENNReal.ofReal_add, ENNReal.ofReal_one]
      ring

/-- At `β = 4`, the moment has exactly `k+1+q` logarithmic factors. -/
theorem radial_cutoff_gain_four (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      cutoffLogIntegral 4 lam h k q ≤
        ENNReal.ofReal (C * (1 + Real.log (h / lam)) ^ (k + 1 + q)) := by
  let C := (1 + Real.log 17) ^ q * ((k : ℝ) + 1) *
    (1 / 2 + 1 / ((q : ℝ) + 1)) * (3 / 2 : ℝ) ^ k
  have h17 : 0 < 1 + Real.log 17 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 17 by norm_num)
    linarith
  refine ⟨C, by dsimp only [C]; positivity, fun lam h hlam hlh => ?_⟩
  have hL : 0 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  unfold cutoffLogIntegral
  norm_num only [show (2 : ℝ) - 4 = -2 by norm_num]
  have hd := dilated_minimum_log_le (k := k) 0 q hlam hlh
  simp only [zero_sub] at hd
  refine hd.trans ?_
  calc
    _ ≤ ENNReal.ofReal (1 + Real.log 17) ^ q *
        ((k + 1) * ENNReal.ofReal (1 / 2 + 1 / ((q : ℝ) + 1)) *
          ENNReal.ofReal (3 / 2 : ℝ) ^ k *
          ENNReal.ofReal (1 + Real.log (h / lam)) ^ (k + 1 + q)) := by
      gcongr
      exact lintegral_minimum_log_le_zero q hlam hlh
    _ = _ := by
      dsimp only [C]
      simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
        ENNReal.ofReal_natCast, ENNReal.ofReal_add, ENNReal.ofReal_one]
      ring

/-- For `β > 4`, the logarithms remain of order `q`. -/
theorem radial_cutoff_gain_gt_four {β : ℝ} (hβ : 4 < β) (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      cutoffLogIntegral β lam h k q ≤ ENNReal.ofReal
        (C * lam ^ ((4 - β) * (k + 1)) * (1 + Real.log (h / lam)) ^ q) := by
  let a := 4 - β
  have ha : a < 0 := by dsimp [a]; linarith
  let c := 1 / 2 + 1 / (-a)
  have hc : 0 < c := by dsimp [c]; have : 0 < -a := neg_pos.mpr ha; positivity
  let C := (1 + Real.log 17) ^ q * ((k : ℝ) + 1) * c ^ (k + 1)
  have h17 : 0 < 1 + Real.log 17 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 17 by norm_num)
    linarith
  refine ⟨C, by dsimp only [C]; positivity, fun lam h hlam hlh => ?_⟩
  have hL : 0 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  have he : 2 - β = a - 2 := by dsimp [a]; ring
  unfold cutoffLogIntegral
  rw [he]
  refine (dilated_minimum_log_le a q hlam hlh).trans ?_
  calc
    _ ≤ ENNReal.ofReal (1 + Real.log 17) ^ q *
        ((k + 1) * ENNReal.ofReal c ^ (k + 1) *
          ENNReal.ofReal (lam ^ a) ^ (k + 1) *
          ENNReal.ofReal (1 + Real.log (h / lam)) ^ q) := by
      gcongr
      exact lintegral_minimum_log_le_of_neg ha q hlam hlh
    _ = _ := by
      have hp : lam ^ ((4 - β) * (k + 1)) = (lam ^ a) ^ (k + 1) := by
        rw [Real.rpow_mul hlam.le,
          show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
      rw [hp]
      dsimp only [C]
      simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
        ENNReal.ofReal_natCast, ENNReal.ofReal_add, ENNReal.ofReal_one]
      ring

end MultipoleBKT.RouteLog

end
