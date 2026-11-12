/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.ScalarGain
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Density

/-!
# The logarithmic radial integral after the external root cancellation

See Lemma A.4 and (A.42). Mark a smallest radius and integrate the product of
single logarithmic moments. The extra root logarithm raises the mark order
by one. All moment coefficients are independent of epsilon_0.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJext

open MeasureTheory Set Finset Limits GeneralExpansion
open scoped Classical ENNReal

/-- The radial cube with the minimum-radius logarithm and the actual cut density. -/
noncomputable def vectorWeight {I : Type*} [Fintype I] [Nonempty I]
    (χ : ℂ → ℝ) (β lam h : ℝ) (q : ℕ) (u : I → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + Real.log (17 * h / minRho lam u)) ^ q) *
    ∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2)

/-- Tonelli and polar coordinates for a specified marked dipole. -/
theorem lintegral_marked_product_le {I : Type*} [Fintype I] [DecidableEq I]
    {χ : ℂ → ℝ} {β lam h : ℝ} (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (hlam : 0 < lam) (hlh : lam ≤ h) (q : ℕ) (m : I) :
    (∫⁻ u : I → ℂ, ∏ i, cutWeight χ β lam h (u i) *
      ENNReal.ofReal (rho lam (u i) ^ 2 *
        (1 + Real.log (h / rho lam (u i))) ^ (if i = m then q else 0))) ≤
      ENNReal.ofReal ((2 * Real.pi * Real.exp (β * MultipoleIntegral.kernelConst χ)) ^ Fintype.card I *
        MultipoleBKT.RouteLog.radialLogMoment (4 - β) lam h q *
          MultipoleBKT.RouteLog.radialLogMoment (4 - β) lam h 0 ^ (Fintype.card I - 1)) := by
  let A := 2 * Real.pi * Real.exp (β * MultipoleIntegral.kernelConst χ)
  let B := MultipoleBKT.RouteLog.radialLogMoment (4 - β) lam h
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB (q : ℕ) : 0 ≤ B q := radialLogMoment_nonneg (4 - β) q hlam hlh
  rw [volume_pi, lintegral_pi_prod (fun _ : I => (volume : Measure ℂ))
    (fun i w => cutWeight χ β lam h w * ENNReal.ofReal (rho lam w ^ 2 *
      (1 + Real.log (h / rho lam w)) ^ (if i = m then q else 0)))
    (fun i => (measurable_cutWeight hχ hlam β h).mul (by unfold rho; fun_prop))]
  calc
    _ ≤ ∏ i : I, ENNReal.ofReal (A * B (if i = m then q else 0)) :=
      prod_le_prod fun i _ => lintegral_cutWeight_log_le hχ hβ hlam hlh _
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg hA (hB _)),
        prod_mul_distrib, prod_const, card_univ,
        ← mul_prod_erase univ (fun i : I => B (if i = m then q else 0)) (mem_univ m)]
      simp only [ite_true]
      have he : (∏ i ∈ univ.erase m, B (if i = m then q else 0)) = B 0 ^ (Fintype.card I - 1) := by
        rw [prod_congr rfl (fun i hi => congrArg B (ite_eq_right (mem_erase.mp hi).1)), prod_const,
          card_erase_of_mem (mem_univ _), card_univ]
      rw [he, mul_assoc]

/-- Comparison with the product moments on the actual cube, including the
regularized core below lambda. No separated-core surrogate is used. -/
theorem lintegral_vectorWeight_le {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {χ : ℂ → ℝ} {β lam h : ℝ} (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (hlam : 0 < lam) (hlh : lam ≤ h) (q : ℕ) :
    (∫⁻ u : I → ℂ, vectorWeight χ β lam h q u) ≤
      ENNReal.ofReal ((Fintype.card I : ℝ) * (1 + Real.log 17) ^ q *
        (2 * Real.pi * Real.exp (β * MultipoleIntegral.kernelConst χ)) ^ Fintype.card I *
          (MultipoleBKT.RouteLog.radialLogMoment (4 - β) lam h q *
            MultipoleBKT.RouteLog.radialLogMoment (4 - β) lam h 0 ^ (Fintype.card I - 1))) := by
  let K := (1 + Real.log 17) ^ q
  have h17 : 0 ≤ Real.log 17 := Real.log_nonneg (by norm_num)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let P (m : I) (u : I → ℂ) := ∏ i, cutWeight χ β lam h (u i) *
    ENNReal.ofReal (rho lam (u i) ^ 2 *
      (1 + Real.log (h / rho lam (u i))) ^ (if i = m then q else 0))
  have hPm (m : I) : Measurable (P m) := Finset.measurable_prod _ fun i _ =>
    ((measurable_cutWeight hχ hlam β h).comp (measurable_pi_apply i)).mul (by unfold rho; fun_prop)
  have hpt (u : I → ℂ) : vectorWeight χ β lam h q u ≤ ENNReal.ofReal K * ∑ m, P m u := by
    by_cases hu : ∀ i, ‖u i‖ ≤ h
    · obtain ⟨m, hm⟩ := exists_minRho_eq lam u
      have hm0 := rho_pos hlam (u m)
      have hmh : rho lam (u m) ≤ h := max_le (hu m) hlh
      have hlog : 0 ≤ Real.log (h / rho lam (u m)) := Real.log_nonneg ((one_le_div hm0).2 hmh)
      have he : Real.log (17 * h / rho lam (u m)) = Real.log 17 + Real.log (h / rho lam (u m)) := by
        rw [mul_div_assoc, Real.log_mul (by norm_num) (div_pos (hlam.trans_le hlh) hm0).ne']
      have hb : (1 + Real.log (17 * h / minRho lam u)) ^ q ≤
          K * (1 + Real.log (h / rho lam (u m))) ^ q := by
        rw [hm, he, ← mul_pow]
        apply pow_le_pow_left₀ (by linarith)
        nlinarith [mul_nonneg h17 hlog]
      have hprod : P m u = ENNReal.ofReal ((1 + Real.log (h / rho lam (u m))) ^ q) *
          ∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2) := by
        dsimp only [P]
        have heach (i : I) : cutWeight χ β lam h (u i) *
            ENNReal.ofReal (rho lam (u i) ^ 2 * (1 + Real.log (h / rho lam (u i))) ^ (if i = m then q else 0)) =
            (cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2)) *
              ENNReal.ofReal ((1 + Real.log (h / rho lam (u i))) ^ (if i = m then q else 0)) := by
          rw [ENNReal.ofReal_mul (sq_nonneg (rho lam (u i)))]
          ring
        simp_rw [heach]
        rw [prod_mul_distrib]
        have hp : (∏ i : I, ENNReal.ofReal ((1 + Real.log (h / rho lam (u i))) ^
            (if i = m then q else 0))) = ENNReal.ofReal ((1 + Real.log (h / rho lam (u m))) ^ q) := by
          rw [← mul_prod_erase univ _ (mem_univ m)]
          have hr : (∏ i ∈ univ.erase m, ENNReal.ofReal ((1 + Real.log (h / rho lam (u i))) ^
              (if i = m then q else 0))) = 1 := prod_eq_one fun i hi => by
            rw [ite_eq_right (mem_erase.mp hi).1, pow_zero, ENNReal.ofReal_one]
          rw [hr, mul_one, ite_eq_left rfl]
        rw [hp, mul_comm]
      change ENNReal.ofReal ((1 + Real.log (17 * h / minRho lam u)) ^ q) * _ ≤ _
      refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hb) le_rfl).trans ?_
      rw [ENNReal.ofReal_mul hK, mul_assoc, ← hprod]
      exact mul_le_mul' le_rfl (single_le_sum (f := fun m => P m u) (fun _ _ => bot_le) (mem_univ m))
    · push Not at hu
      obtain ⟨i, hi⟩ := hu
      have hz : cutWeight χ β lam h (u i) = 0 := by
        unfold cutWeight
        rw [indicator_of_notMem (show u i ∉ Metric.closedBall (0 : ℂ) h by intro hx; exact (not_le.mpr hi) (mem_closedBall_zero_iff.mp hx)), ENNReal.ofReal_zero]
      unfold vectorWeight
      rw [prod_eq_zero (mem_univ i) (by rw [hz, zero_mul]), mul_zero]
      exact bot_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ (fun m _ => hPm m)]
  calc
    _ ≤ ENNReal.ofReal K * ∑ _m : I, ENNReal.ofReal
        ((2 * Real.pi * Real.exp (β * MultipoleIntegral.kernelConst χ)) ^ Fintype.card I *
          MultipoleBKT.RouteLog.radialLogMoment (4 - β) lam h q *
            MultipoleBKT.RouteLog.radialLogMoment (4 - β) lam h 0 ^ (Fintype.card I - 1)) := by
      gcongr with m
      exact lintegral_marked_product_le hχ hβ hlam hlh q m
    _ = _ := by
      rw [sum_const, card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hK]
      congr 1
      ring

/-- The three beta regimes and final absorption give the cutoff gain with
one coefficient uniform in epsilon_0 for every logarithmic order. -/
theorem vectorWeight_gain {χ : ℂ → ℝ} {β : ℝ} (hχ : IsMollifier χ) (hβ : 2 < β)
    (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I],
      Fintype.card I = k → ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      (∫⁻ u : I → ℂ, vectorWeight χ β lam (eps * truncationScale p₀ β lam) q u) ≤
        ENNReal.ofReal (C * eps ^ (alphaExponent β * k) * lam ^ ((2 - β) * k)) := by
  obtain ⟨C, hC, hb⟩ := moment_product_bad_le hβ p₀ hk q
  let D := (k : ℝ) * (1 + Real.log 17) ^ q *
    (2 * Real.pi * Real.exp (β * MultipoleIntegral.kernelConst χ)) ^ k
  have hD : 0 < D := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 17)
    dsimp only [D]
    positivity
  refine ⟨D * C, mul_pos hD hC, fun I _ _ _ hI eps lam hlam hle heps => ?_⟩
  have heps0 := hlam.trans_le hle
  have hlh : lam ≤ eps * truncationScale p₀ β lam := hle.trans
    (le_mul_of_one_le_right heps0.le (Appendix.one_le_truncationScale hβ hlam (hle.trans heps)))
  have hv := lintegral_vectorWeight_le (I := I) (β := β) hχ (by linarith) hlam hlh q
  rw [hI] at hv
  refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
  exact (mul_le_mul_of_nonneg_left (hb eps lam hlam hle heps) hD.le).trans_eq (by ring)

end MultipoleBKT.SmallIntegral.RouteJext

end
