/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuous counting shells

The paper: (5.30) and the proof of
(5.48). A reciprocal is the integral of
`t⁻²` over the scales `f/2 < t < f`. Exchange the finite sum and the integral,
then insert the uniform packing bound on the counting function.
-/

@[expose] public section

open MeasureTheory Set

namespace MultipoleBKT.UpperBound

/-- The exact single-shell identity behind (5.30). -/
theorem integral_continuous_shell {f : ℝ} (hf : 0 < f) :
    ∫ t in Ioo (f / 2) f, t ^ (-2 : ℝ) = 1 / f := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith : f / 2 ≤ f),
    integral_rpow (Or.inr ⟨by norm_num, by
      rw [uIcc_of_le (by linarith : f / 2 ≤ f)]
      simp only [mem_Icc, not_and]
      intro h
      linarith⟩)]
  simp only [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp [hf.ne']
  ring

/-- The shell indicator is integrable on the scale half-line. -/
theorem integrable_continuous_shell {D f : ℝ} (hD : 0 < D) :
    Integrable (fun t : ℝ => if t < f ∧ f < 2 * t then t ^ (-2 : ℝ) else 0)
      (volume.restrict (Ioi (D / 2))) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (by linarith : 0 < D / 2)
  have hs : MeasurableSet {t : ℝ | t < f ∧ f < 2 * t} :=
    (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_lt measurable_const (measurable_const.mul measurable_id))
  apply (h.indicator hs).congr
  filter_upwards [] with t
  by_cases ht : t < f ∧ f < 2 * t <;> simp [Set.indicator, ht]


/-- (5.30): the reciprocal sum equals the integral of the continuous counting function.
The upper endpoint can be extended to infinity because each shell has bounded support. -/
theorem sum_reciprocal_eq_integral_count {ι : Type*} (T : Finset ι) (f : ι → ℝ)
    {D : ℝ} (hD : 0 < D) (hf : ∀ j ∈ T, D ≤ f j) :
    ∑ j ∈ T, 1 / f j = ∫ t in Ioi (D / 2),
      t ^ (-2 : ℝ) * ((T.filter fun j => t < f j ∧ f j < 2 * t).card : ℝ) := by
  classical
  have hj : ∀ j ∈ T, (∫ t in Ioi (D / 2),
      if t < f j ∧ f j < 2 * t then t ^ (-2 : ℝ) else 0) = 1 / f j := by
    intro j hj
    have hsub : Ioo (f j / 2) (f j) ⊆ Ioi (D / 2) := by
      intro t ht
      change D / 2 < t
      linarith [hf j hj, ht.1]
    calc _ = ∫ t in Ioi (D / 2), (Ioo (f j / 2) (f j)).indicator
          (fun t : ℝ => t ^ (-2 : ℝ)) t := by
            congr 1
            funext t
            congr 1
            ext
            simp only [mem_Ioo]
            constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      _ = _ := by
        rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
          inter_eq_left.mpr hsub, integral_continuous_shell (hD.trans_le (hf j hj))]
  calc
    _ = ∑ j ∈ T, ∫ t in Ioi (D / 2),
        if t < f j ∧ f j < 2 * t then t ^ (-2 : ℝ) else 0 :=
      Finset.sum_congr rfl (fun j hjT => (hj j hjT).symm)
    _ = ∫ t in Ioi (D / 2), ∑ j ∈ T,
        if t < f j ∧ f j < 2 * t then t ^ (-2 : ℝ) else 0 :=
      (integral_finsetSum T (fun j _ => integrable_continuous_shell (f := f j) hD)).symm
    _ = _ := by
      congr 1
      funext t
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The literal bounded-interval version of (5.30). In the paper
`D = d_{i,bad}` and `U = 2 ε₀ R̄`, or `D = max(r_i, λ)` in Step 3. -/
theorem sum_reciprocal_eq_integral_count_between {ι : Type*} (T : Finset ι) (f : ι → ℝ)
    {D U : ℝ} (hD : 0 < D) (hf : ∀ j ∈ T, D ≤ f j) (hU : ∀ j ∈ T, f j ≤ U) :
    ∑ j ∈ T, 1 / f j = ∫ t in Ioo (D / 2) U,
      t ^ (-2 : ℝ) * ((T.filter fun j => t < f j ∧ f j < 2 * t).card : ℝ) := by
  classical
  rw [sum_reciprocal_eq_integral_count T f hD hf]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
  intro t ht
  have hUt : U ≤ t := by
    have hnot := ht.2
    simp only [mem_Ioo, not_and, not_lt] at hnot
    exact hnot ht.1
  have hempty : (T.filter fun j => t < f j ∧ f j < 2 * t) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hjT, hjt, _⟩ := Finset.mem_filter.mp hj
    linarith [hU j hjT]
  rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]

/-- Inserting a uniform continuous-shell count and integrating `t⁻²` gives the packing integral. -/
theorem sum_div_le_of_continuous_count {ι : Type*} (T : Finset ι) (f : ι → ℝ)
    {D : ℝ} (hD : 0 < D) (hf : ∀ j ∈ T, D ≤ f j) (K : ℕ)
    (hK : ∀ t : ℝ, 0 < t → (T.filter fun j => t < f j ∧ f j < 2 * t).card ≤ K) :
    ∑ j ∈ T, D / f j ≤ 2 * K := by
  classical
  have hint := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num)
    (by linarith : 0 < D / 2)
  have hcount : Integrable (fun t : ℝ => t ^ (-2 : ℝ) *
      ((T.filter fun j => t < f j ∧ f j < 2 * t).card : ℝ)) (volume.restrict (Ioi (D / 2))) := by
    have := integrable_finsetSum T (fun j _ => integrable_continuous_shell (f := f j) hD)
    convert this using 1
    funext t
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hle : (∫ t in Ioi (D / 2), t ^ (-2 : ℝ) *
      ((T.filter fun j => t < f j ∧ f j < 2 * t).card : ℝ)) ≤
      ∫ t in Ioi (D / 2), t ^ (-2 : ℝ) * K := by
    apply integral_mono_ae hcount (hint.mul_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hK t (by linarith [Set.mem_Ioi.mp ht])))
      (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht]) _)
  rw [integral_mul_const, integral_Ioi_rpow_of_lt (by norm_num) (by linarith : 0 < D / 2)] at hle
  rw [← sum_reciprocal_eq_integral_count T f hD hf] at hle
  simp only [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one] at hle
  norm_num only [neg_div, neg_neg, div_neg, div_one] at hle
  calc ∑ j ∈ T, D / f j = D * ∑ j ∈ T, 1 / f j := by rw [Finset.mul_sum]; congr 1; funext j; ring
    _ ≤ D * ((D / 2)⁻¹ * K) := mul_le_mul_of_nonneg_left hle hD.le
    _ = 2 * K := by field_simp

end MultipoleBKT.UpperBound

end
