/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Radial

/-!
# Scaling the literal ordered integral

See (A.13) through
(A.14). Scale every radius by the core radius. This
identifies the coefficient with the integral at unit core radius.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set
open scoped ENNReal

/-- The one-dimensional positive dilation formula, on a measurable set. -/
theorem setLIntegral_dilate {a : ℝ} (ha : 0 < a) (D : Set ℝ)
    (hD : MeasurableSet D) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ r in D, f r = ENNReal.ofReal a * ∫⁻ t in (fun t => a * t) ⁻¹' D, f (a * t) := by
  have hm := Real.smul_map_volume_mul_left ha.ne'
  rw [abs_of_pos ha] at hm
  rw [← lintegral_indicator hD]
  conv_lhs => rw [← hm]
  rw [lintegral_smul_measure, lintegral_map (hf.indicator hD) (measurable_const_mul a)]
  rw [← lintegral_indicator (hD.preimage (measurable_const_mul a))]
  simp only [smul_eq_mul]
  congr 1


/-- Scaling of the full inner integral, including its core. -/
theorem orderedInner_scale {lam : ℝ} (hlam : 0 < lam) (β r : ℝ) :
    orderedInner β lam (lam * r) =
      ENNReal.ofReal (lam ^ (4 - β)) * orderedInner β 1 r := by
  have hm : Measurable fun t : ℝ => ENNReal.ofReal (t * max t lam ^ (2 - β)) :=
    ENNReal.measurable_ofReal.comp ((continuous_id.mul
      ((continuous_id.max continuous_const).rpow_const
        (fun t => Or.inl (lt_max_of_lt_right hlam).ne'))).measurable)
  have hpre : (fun t : ℝ => lam * t) ⁻¹' Ioc 0 (lam * r) = Ioc 0 r := by
    ext t
    change 0 < lam * t ∧ lam * t ≤ lam * r ↔ 0 < t ∧ t ≤ r
    constructor <;> rintro ⟨ht, hs⟩ <;> constructor <;> nlinarith
  unfold orderedInner
  rw [setLIntegral_dilate hlam _ measurableSet_Ioc _ hm, hpre]
  have hpt (t : ℝ) : (lam * t) * max (lam * t) lam ^ (2 - β) =
      lam ^ (3 - β) * (t * max t 1 ^ (2 - β)) := by
    rw [show max (lam * t) lam = lam * max t 1 by
      rw [mul_max_of_nonneg _ _ hlam.le, mul_one], Real.mul_rpow hlam.le (by positivity)]
    rw [show 3 - β = 1 + (2 - β) by ring, Real.rpow_add hlam, Real.rpow_one]
    ring
  simp_rw [hpt, ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul hlam.le]
  have he : lam * lam ^ (3 - β) = lam ^ (4 - β) := by
    calc
      _ = lam ^ (1 : ℝ) * lam ^ (3 - β) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hlam]; congr 1; ring
  rw [he]

/-- Exact scaling of the ordered infinite-cutoff integral. -/
theorem orderedRadial_scale_infinite {lam : ℝ} (hlam : 0 < lam) (β : ℝ) (n : ℕ) :
    orderedRadial β lam (Ioi 0) n =
      ENNReal.ofReal (lam ^ ((4 - β) * (n + 1) - 2)) * orderedRadial β 1 (Ioi 0) n := by
  have hm : Measurable fun r : ℝ => ENNReal.ofReal (r * max r lam ^ (-β)) *
      orderedInner β lam r ^ n := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul ((orderedInner_mono β lam).measurable.pow_const n)
    exact (continuous_id.mul ((continuous_id.max continuous_const).rpow_const
      (fun r => Or.inl (lt_max_of_lt_right hlam).ne'))).measurable
  have hpre : (fun t : ℝ => lam * t) ⁻¹' Ioi 0 = Ioi 0 := by
    ext t
    change 0 < lam * t ↔ 0 < t
    constructor <;> intro ht <;> nlinarith
  unfold orderedRadial
  rw [setLIntegral_dilate hlam _ measurableSet_Ioi _ hm, hpre]
  have hpt (t : ℝ) : (lam * t) * max (lam * t) lam ^ (-β) =
      lam ^ (1 - β) * (t * max t 1 ^ (-β)) := by
    rw [show max (lam * t) lam = lam * max t 1 by
      rw [mul_max_of_nonneg _ _ hlam.le, mul_one], Real.mul_rpow hlam.le (by positivity)]
    rw [sub_eq_add_neg, Real.rpow_add hlam, Real.rpow_one]
    ring
  simp_rw [hpt, ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _),
    orderedInner_scale hlam, mul_pow]
  have heq (t : ℝ) : ENNReal.ofReal (lam ^ (1 - β)) * ENNReal.ofReal (t * max t 1 ^ (-β)) *
      (ENNReal.ofReal (lam ^ (4 - β)) ^ n * orderedInner β 1 t ^ n) =
      (ENNReal.ofReal (lam ^ (1 - β)) * ENNReal.ofReal (lam ^ (4 - β)) ^ n) *
        (ENNReal.ofReal (t * max t 1 ^ (-β)) * orderedInner β 1 t ^ n) := by ring
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)), ← mul_assoc,
    ← ENNReal.ofReal_pow (Real.rpow_nonneg hlam.le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _), ← ENNReal.ofReal_mul hlam.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
  have he : lam * (lam ^ (1 - β) * lam ^ ((4 - β) * n)) =
      lam ^ ((4 - β) * (n + 1) - 2) := by
    calc
      _ = lam ^ (1 : ℝ) * (lam ^ (1 - β) * lam ^ ((4 - β) * n)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hlam, ← Real.rpow_add hlam]; congr 1; ring
  rw [he]

/-- Finiteness in the precise infinite-cutoff size range, proved by the
low-temperature and critical or high-temperature radial regimes. -/
theorem orderedRadial_infinite_ne_top {β : ℝ} (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hE : (4 - β) * k - 2 < 0) {lam : ℝ} (hlam : 0 < lam) :
    orderedRadial β lam (Ioi 0) (k - 1) ≠ ⊤ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hj : j + 2 - 1 = j + 1 := by omega
  rw [hj]
  by_cases hb4 : β < 4
  · obtain ⟨C, _, hC⟩ := orderedRadial_infinite_lt_four hβ hb4 j (by exact_mod_cast hE)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC lam hlam)
  · obtain ⟨C, _, hC⟩ := orderedRadial_infinite_ge_four (le_of_not_gt hb4) j
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC lam hlam)

end MultipoleBKT.MultipoleIntegral

end
