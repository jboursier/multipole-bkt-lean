/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Reversal

/-!
# Edge kernels and their integrals

The edge integrals in the proof of Lemma A.5:
a near edge contributes `C min(ρᵢ, ρⱼ)²`, an even edge
`∫ b̂_ij dz ≤ C s²(1 + log(t/s))`, an odd edge `∫ min(1, R²/max d²) ∏ dt/t ≤ C(1 + log(R/ρ_*))`.

We trade the logarithms for small powers `δ > 0` (`(1 + log x) ≤ C_δ x^δ`), which the strict
inequality `(4 - β) k < 2` absorbs. The basic kernel is
`kern δ p T t = t^{δ-2} min(1, T/t)^p` (as an `ℝ≥0∞`-valued function, nonincreasing in `t`), with
`∫_ℂ kern δ p T |z| dz ≤ 2π T^δ (1/δ + 1/(p - δ))` for `0 < δ < p` (`lintegral_kern_le`).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset
open scoped ENNReal

/-- The kernel `t^{δ-2} min(1, T/t)^p`, nonincreasing in `t ≥ 0` (with value `∞` at `0`). -/
noncomputable def kern (δ p T : ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal t ^ (δ - 2) * min 1 (ENNReal.ofReal T / ENNReal.ofReal t) ^ p

theorem ennreal_rpow_le_rpow_of_nonpos {x y : ℝ≥0∞} {z : ℝ} (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  have h1 : y ^ z = (y ^ (-z))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
  have h2 : x ^ z = (x ^ (-z))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
  rw [h1, h2]
  exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hxy (neg_nonneg.2 hz))

theorem kern_antitone {δ p T : ℝ} (hδ : δ ≤ 2) (hp : 0 ≤ p) : Antitone (kern δ p T) := by
  intro a b hab
  unfold kern
  refine mul_le_mul' ?_ ?_
  · exact ennreal_rpow_le_rpow_of_nonpos (ENNReal.ofReal_le_ofReal hab) (by linarith)
  · refine ENNReal.rpow_le_rpow ?_ hp
    exact min_le_min le_rfl (ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal hab) _)

theorem measurable_kern (δ p T : ℝ) : Measurable (kern δ p T) := by
  unfold kern
  fun_prop

theorem kern_of_pos {δ p T t : ℝ} (ht : 0 < t) (hT : 0 ≤ T) (hp : 0 ≤ p) :
    kern δ p T t = ENNReal.ofReal (t ^ (δ - 2) * min 1 (T / t) ^ p) := by
  unfold kern
  rw [ENNReal.ofReal_rpow_of_pos ht, ← ENNReal.ofReal_div_of_pos ht, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_min, ENNReal.ofReal_rpow_of_nonneg (le_min zero_le_one
      (div_nonneg hT ht.le)) hp, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]

/-- The real kernel `r ↦ r^{δ-1} min(1, T/r)^p` is integrable on `(0, ∞)` for `0 < δ < p`, with
integral at most `T^δ (1/δ + 1/(p - δ))`. -/
theorem integral_kern_radial_le {δ p T : ℝ} (hδ : 0 < δ) (hδp : δ < p) (hT : 0 < T) :
    IntegrableOn (fun r : ℝ => r ^ (δ - 2) * min 1 (T / r) ^ p * r) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), r ^ (δ - 2) * min 1 (T / r) ^ p * r ≤ T ^ δ * (1 / δ + 1 / (p - δ)) := by
  have hp : 0 ≤ p := by linarith
  have e1 : ∀ r ∈ Ioc (0 : ℝ) T, r ^ (δ - 2) * min 1 (T / r) ^ p * r = r ^ (δ - 1) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    rw [min_eq_left ((one_le_div hr0).2 hr.2), Real.one_rpow, mul_one,
      ← Real.rpow_add_one hr0.ne']
    ring_nf
  have e2 : ∀ r ∈ Ioi T, r ^ (δ - 2) * min 1 (T / r) ^ p * r = T ^ p * r ^ (δ - 1 - p) := by
    intro r hr
    have hr0 : 0 < r := hT.trans hr
    rw [min_eq_right ((div_le_one hr0).2 (le_of_lt hr)), Real.div_rpow hT.le hr0.le]
    rw [show r ^ (δ - 1 - p) = r ^ (δ - 2) * r / r ^ p by
      rw [eq_div_iff (Real.rpow_pos_of_pos hr0 p).ne', ← Real.rpow_add_one hr0.ne',
        ← Real.rpow_add hr0]
      ring_nf]
    field_simp
  have i1 : IntegrableOn (fun r : ℝ => r ^ (δ - 1)) (Ioc 0 T) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 (by linarith)).congr_set_ae
      Ioo_ae_eq_Ioc.symm
  have i2 : IntegrableOn (fun r : ℝ => T ^ p * r ^ (δ - 1 - p)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hT).const_mul _
  have i1' : IntegrableOn (fun r : ℝ => r ^ (δ - 2) * min 1 (T / r) ^ p * r) (Ioc 0 T) :=
    i1.congr_fun (fun r hr => (e1 r hr).symm) measurableSet_Ioc
  have i2' : IntegrableOn (fun r : ℝ => r ^ (δ - 2) * min 1 (T / r) ^ p * r) (Ioi T) :=
    i2.congr_fun (fun r hr => (e2 r hr).symm) measurableSet_Ioi
  have hsplit : Ioi (0 : ℝ) = Ioc 0 T ∪ Ioi T := (Ioc_union_Ioi_eq_Ioi hT.le).symm
  refine ⟨hsplit ▸ i1'.union i2', ?_⟩
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1' i2',
    setIntegral_congr_fun measurableSet_Ioc e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hT,
    ← intervalIntegral.integral_of_le hT.le, integral_rpow (Or.inl (by linarith))]
  have hTd : T ^ (δ - 1 + 1) = T ^ δ := by ring_nf
  have hTd' : T ^ p * T ^ (δ - 1 - p + 1) = T ^ δ := by
    rw [← Real.rpow_add hT]; ring_nf
  rw [hTd, show (δ - 1 - p + 1) = δ - p by ring, Real.zero_rpow (by linarith), sub_zero,
    show δ - 1 + 1 = δ by ring]
  rw [show T ^ p * (-T ^ (δ - p) / (δ - p)) = T ^ p * T ^ (δ - p) / (p - δ) by
    rw [neg_div, ← div_neg, neg_sub]; ring]
  rw [← Real.rpow_add hT, show p + (δ - p) = δ by ring]
  apply le_of_eq
  field_simp

/-- `∫_ℂ t^{δ-2} min(1, T/t)^p |_{t = |z|} dz ≤ 2π T^δ (1/δ + 1/(p - δ))` for `0 < δ < p`, `T > 0`. -/
theorem lintegral_kern_le {δ p T : ℝ} (hδ : 0 < δ) (hδp : δ < p) (hT : 0 < T) :
    ∫⁻ z : ℂ, kern δ p T ‖z‖ ≤ ENNReal.ofReal (2 * Real.pi * (T ^ δ * (1 / δ + 1 / (p - δ)))) := by
  have hp : 0 ≤ p := by linarith
  obtain ⟨hint, hle⟩ := integral_kern_radial_le hδ hδp hT
  have hint' : Integrable fun z : ℂ => ‖z‖ ^ (δ - 2) * min 1 (T / ‖z‖) ^ p :=
    (integrable_fun_norm_complex_iff fun r => r ^ (δ - 2) * min 1 (T / r) ^ p).2 hint
  have hae : (fun z : ℂ => kern δ p T ‖z‖) =ᵐ[volume]
      fun z => ENNReal.ofReal (‖z‖ ^ (δ - 2) * min 1 (T / ‖z‖) ^ p) := by
    have : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
    filter_upwards [this] with z hz
    exact kern_of_pos (norm_pos_iff.2 hz) hT.le hp
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal hint'
    (Filter.Eventually.of_forall fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (le_min zero_le_one (div_nonneg hT.le (norm_nonneg _))) _))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_fun_norm_complex fun r => r ^ (δ - 2) * min 1 (T / r) ^ p]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

end Limits

end MultipoleBKT

end
