/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Radial

/-!
# Several logarithmic radial variables

See (A.42). Choose a radius attaining the minimum, then integrate its
logarithmic moment and the remaining zeroth moments by Tonelli. This retains
the powers of the logarithm in all three temperature regimes.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set Finset
open scoped ENNReal

/-- The smallest regularized radius in a nonempty family. -/
noncomputable def minimumRadius {k : ℕ} (lam : ℝ) (r : Fin (k + 1) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => max (r i) lam)

private theorem log_min_le_sum {k : ℕ} (q : ℕ) (lam h : ℝ) (r : Fin (k + 1) → ℝ) :
    ENNReal.ofReal ((1 + Real.log (h / minimumRadius lam r)) ^ q) ≤
      ∑ i, ENNReal.ofReal ((1 + Real.log (h / max (r i) lam)) ^ q) := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => max (r i) lam)
  have heq : minimumRadius lam r = max (r i) lam := he
  rw [heq]
  exact Finset.single_le_sum
    (f := fun j : Fin (k + 1) => ENNReal.ofReal ((1 + Real.log (h / max (r j) lam)) ^ q))
    (fun _ _ => bot_le) hi

private theorem integral_one_marked_moment {k : ℕ} (a : ℝ) (q : ℕ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) (i : Fin (k + 1)) :
    ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
      ENNReal.ofReal ((1 + Real.log (h / max (r i) lam)) ^ q) *
        ∏ j, ENNReal.ofReal (r j * max (r j) lam ^ (a - 2)) =
      ENNReal.ofReal (radialLogMoment a lam h q) *
        ENNReal.ofReal (radialLogMoment a lam h 0) ^ k := by
  let f : Fin (k + 1) → ℝ → ℝ≥0∞ := fun j t =>
    ENNReal.ofReal (t * max t lam ^ (a - 2)) *
      (if j = i then ENNReal.ofReal ((1 + Real.log (h / max t lam)) ^ q) else 1)
  have hf (j : Fin (k + 1)) : Measurable (f j) := by
    by_cases hji : j = i
    · simp only [f, hji, ite_true]; fun_prop
    · simp only [f, hji, ite_false, mul_one]; fun_prop
  have hprod (r : Fin (k + 1) → ℝ) :
      ENNReal.ofReal ((1 + Real.log (h / max (r i) lam)) ^ q) *
          ∏ j, ENNReal.ofReal (r j * max (r j) lam ^ (a - 2)) = ∏ j, f j (r j) := by
    simp only [f, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
      ite_true, mul_comm]
  simp_rw [hprod]
  change (∫⁻ r : Fin (k + 1) → ℝ, ∏ j, f j (r j)
    ∂((Measure.pi fun _ : Fin (k + 1) => (volume : Measure ℝ)).restrict
      (Set.univ.pi fun _ : Fin (k + 1) => Ioc 0 h))) = _
  rw [Measure.restrict_pi_pi,
    TwoComponentCoulomb.lintegral_fin_prod_eq_prod (fun _ => volume.restrict (Ioc 0 h)) f hf]
  have hint (j : Fin (k + 1)) : ∫⁻ t in Ioc 0 h, f j t =
      if j = i then ENNReal.ofReal (radialLogMoment a lam h q)
      else ENNReal.ofReal (radialLogMoment a lam h 0) := by
    by_cases hji : j = i
    · simp only [f, hji, ite_true]
      have he : ∀ t ∈ Ioc (0 : ℝ) h,
          ENNReal.ofReal (t * max t lam ^ (a - 2)) *
            ENNReal.ofReal ((1 + Real.log (h / max t lam)) ^ q) =
          ENNReal.ofReal (t * max t lam ^ (a - 2) *
            (1 + Real.log (h / max t lam)) ^ q) := by
        intro t ht
        rw [ENNReal.ofReal_mul (mul_nonneg ht.1.le (Real.rpow_nonneg (lt_max_of_lt_right hlam).le _))]
      rw [setLIntegral_congr_fun measurableSet_Ioc he, lintegral_radialLogMoment a q hlam hlh]
    · simp only [f, hji, ite_false, mul_one]
      simpa only [pow_zero, mul_one] using lintegral_radialLogMoment a 0 hlam hlh
  simp_rw [hint]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i,
      if j = i then ENNReal.ofReal (radialLogMoment a lam h q)
      else ENNReal.ofReal (radialLogMoment a lam h 0)) =
      ENNReal.ofReal (radialLogMoment a lam h 0) ^ k := by
    rw [Finset.prod_congr rfl (fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj))]
    simp
  rw [he]
  simp [mul_comm]

/-- Reduction of a minimum-radius logarithm to one logarithmic moment.
The other radii retain their zeroth moments. -/
theorem lintegral_minimum_log_le {k : ℕ} (a : ℝ) (q : ℕ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) :
    ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
      ENNReal.ofReal ((1 + Real.log (h / minimumRadius lam r)) ^ q) *
        ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (a - 2)) ≤
      (k + 1) * ENNReal.ofReal (radialLogMoment a lam h q) *
        ENNReal.ofReal (radialLogMoment a lam h 0) ^ k := by
  have hset : MeasurableSet (Set.univ.pi fun _ : Fin (k + 1) => Ioc (0 : ℝ) h) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  calc
    _ ≤ ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
        ∑ i, ENNReal.ofReal ((1 + Real.log (h / max (r i) lam)) ^ q) *
          ∏ j, ENNReal.ofReal (r j * max (r j) lam ^ (a - 2)) := by
      apply setLIntegral_mono' hset
      intro r _
      rw [← Finset.sum_mul]
      gcongr
      exact log_min_le_sum q lam h r
    _ = ∑ i : Fin (k + 1), ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
        ENNReal.ofReal ((1 + Real.log (h / max (r i) lam)) ^ q) *
          ∏ j, ENNReal.ofReal (r j * max (r j) lam ^ (a - 2)) := by
      apply lintegral_finsetSum
      intro i _
      fun_prop
    _ = _ := by
      simp_rw [integral_one_marked_moment a q hlam hlh]
      simp [mul_assoc]

/-- The subcritical part of (A.42), with a constant uniform in `λ,h`. -/
theorem lintegral_minimum_log_le_of_pos {k : ℕ} {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (q : ℕ) {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) :
    ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
      ENNReal.ofReal ((1 + Real.log (h / minimumRadius lam r)) ^ q) *
        ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (a - 2)) ≤
      (k + 1) * ENNReal.ofReal (momentConstant a q * h ^ a) *
        ENNReal.ofReal (momentConstant a 0 * h ^ a) ^ k := by
  refine (lintegral_minimum_log_le a q hlam hlh).trans ?_
  gcongr
  · exact radialLogMoment_le_of_pos ha ha2 q hlam hlh
  · exact radialLogMoment_le_of_pos ha ha2 0 hlam hlh

/-- The critical part of (A.42): exactly `k+1+q` logarithms. -/
theorem lintegral_minimum_log_le_zero {k : ℕ} (q : ℕ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) :
    ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
      ENNReal.ofReal ((1 + Real.log (h / minimumRadius lam r)) ^ q) *
        ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (-2 : ℝ)) ≤
      (k + 1) * ENNReal.ofReal (1 / 2 + 1 / ((q : ℝ) + 1)) *
        ENNReal.ofReal (3 / 2 : ℝ) ^ k *
        ENNReal.ofReal (1 + Real.log (h / lam)) ^ (k + 1 + q) := by
  have hb := lintegral_minimum_log_le (k := k) 0 q hlam hlh
  simp only [zero_sub] at hb
  refine hb.trans ?_
  calc
    _ ≤ (k + 1) *
        ENNReal.ofReal ((1 / 2 + 1 / ((q : ℝ) + 1)) *
          (1 + Real.log (h / lam)) ^ (q + 1)) *
        ENNReal.ofReal ((3 / 2 : ℝ) * (1 + Real.log (h / lam))) ^ k := by
      gcongr
      · exact radialLogMoment_le_zero q hlam hlh
      · convert radialLogMoment_le_zero 0 hlam hlh using 1
        norm_num
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), mul_pow]
      rw [ENNReal.ofReal_pow (by
        have := Real.log_nonneg ((one_le_div hlam).2 hlh); linarith)]
      rw [show k + 1 + q = q + 1 + k by omega, pow_add]
      ring

/-- The supercritical part of (A.42), retaining `q` logarithms. -/
theorem lintegral_minimum_log_le_of_neg {k : ℕ} {a : ℝ} (ha : a < 0) (q : ℕ)
    {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) :
    ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 h),
      ENNReal.ofReal ((1 + Real.log (h / minimumRadius lam r)) ^ q) *
        ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (a - 2)) ≤
      (k + 1) * ENNReal.ofReal (1 / 2 + 1 / (-a)) ^ (k + 1) *
        ENNReal.ofReal (lam ^ a) ^ (k + 1) *
        ENNReal.ofReal (1 + Real.log (h / lam)) ^ q := by
  refine (lintegral_minimum_log_le a q hlam hlh).trans ?_
  calc
    _ ≤ (k + 1) * ENNReal.ofReal ((1 / 2 + 1 / (-a)) * lam ^ a *
        (1 + Real.log (h / lam)) ^ q) *
        ENNReal.ofReal ((1 / 2 + 1 / (-a)) * lam ^ a) ^ k := by
      gcongr
      · exact radialLogMoment_le_of_neg ha q hlam hlh
      · simpa using radialLogMoment_le_of_neg ha 0 hlam hlh
    _ = _ := by
      have hc : 0 ≤ 1 / 2 + 1 / (-a) := by
        have : 0 < -a := neg_pos.mpr ha
        positivity
      rw [ENNReal.ofReal_mul (mul_nonneg hc (Real.rpow_nonneg hlam.le _)),
        ENNReal.ofReal_mul hc,
        ENNReal.ofReal_pow (by
          have := Real.log_nonneg ((one_le_div hlam).2 hlh); linarith), mul_pow,
        pow_succ, pow_succ]
      ring

end MultipoleBKT.RouteLog

end
