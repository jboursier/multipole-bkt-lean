/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.LogAbsorption

/-!
# Explicit radial factorization for the limiting integrands

See Lemma 4.26 of the paper. Absorb logarithms into a small positive power, factor the
vector integral, and evaluate each one-dimensional radial integral.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set
open SmallIntegral SmallIntegral.RouteJ
open scoped ENNReal

/-- The one-dimensional radial estimate used after small-power absorption.
The coefficient depends only on the exponent, before λ is chosen. -/
theorem integral_radial_rpow_le {a lam : ℝ} (ha : a < -2) (hlam : 0 < lam) :
    (∫ r in Ioi (0 : ℝ), r * max r lam ^ a) ≤
      (1 + 1 / (-(a + 2))) * lam ^ (a + 2) := by
  have hc := Appendix.continuous_max_rpow hlam (a + 1)
  have hlow : IntegrableOn (fun r : ℝ => max r lam ^ (a + 1)) (Ioc 0 lam) :=
    hc.integrableOn_Ioc
  have htail : IntegrableOn (fun r : ℝ => max r lam ^ (a + 1)) (Ioi lam) := by
    refine (integrableOn_Ioi_rpow_of_lt (by linarith : a + 1 < -1) hlam).congr_fun
      (fun r hr => ?_) measurableSet_Ioi
    rw [max_eq_left (le_of_lt hr)]
  have hint : IntegrableOn (fun r : ℝ => max r lam ^ (a + 1)) (Ioi 0) := by
    simpa only [Ioc_union_Ioi_eq_Ioi hlam.le] using hlow.union htail
  have hrad : IntegrableOn (fun r : ℝ => r * max r lam ^ a) (Ioi 0) := by
    have h := (integrable_fun_norm_complex_iff (fun r : ℝ => max r lam ^ a)).mp
      (integrable_rpow_rho hlam ha)
    simpa only [mul_comm] using h
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), max r lam ^ (a + 1) := by
      apply setIntegral_mono_on hrad hint measurableSet_Ioi
      intro r hr
      rw [Real.rpow_add_one (ne_of_gt (hlam.trans_le (le_max_right r lam)))]
      exact (mul_le_mul_of_nonneg_right (le_max_left r lam)
        (Real.rpow_nonneg (hlam.le.trans (le_max_right r lam)) a)).trans_eq (mul_comm _ _)
    _ = (∫ r in Ioc (0 : ℝ) lam, max r lam ^ (a + 1)) +
        ∫ r in Ioi lam, max r lam ^ (a + 1) := by
      rw [← setIntegral_union (by
        apply Set.disjoint_left.mpr
        intro r hr hs
        exact (not_lt_of_ge hr.2) hs) measurableSet_Ioi hlow htail,
        Ioc_union_Ioi_eq_Ioi hlam.le]
    _ = lam ^ (a + 2) + -(lam ^ (a + 2) / (a + 2)) := by
      rw [Appendix.integral_Ioc_max_rpow hlam le_rfl,
        intervalIntegral.integral_same, add_zero]
      have ht : (∫ r in Ioi lam, max r lam ^ (a + 1)) = ∫ r in Ioi lam, r ^ (a + 1) :=
        setIntegral_congr_fun measurableSet_Ioi fun r hr => by rw [max_eq_left (le_of_lt hr)]
      rw [ht, integral_Ioi_rpow_of_lt (by linarith : a + 1 < -1) hlam]
      ring_nf
    _ = _ := by rw [div_neg]; ring

/-- Polar coordinates turn the one-dimensional estimate into the bound for
one free dipole vector. -/
theorem lintegral_rpow_rho_le {a lam : ℝ} (ha : a < -2) (hlam : 0 < lam) :
    (∫⁻ u : ℂ, ENNReal.ofReal (rho lam u ^ a)) ≤
      ENNReal.ofReal ((2 * Real.pi * (1 + 1 / (-(a + 2)))) * lam ^ (a + 2)) := by
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (max r lam ^ a)
  have hf : Measurable f := by fun_prop
  have hp := TwoComponentCoulomb.lintegral_radial_set univ MeasurableSet.univ f hf
  simp only [mem_univ, Set.ofPred_true, Measure.restrict_univ, indicator_univ] at hp
  change (∫⁻ u : ℂ, f ‖u‖) ≤ _
  rw [hp]
  have heq (r : ℝ) : ENNReal.ofReal r * (f r * ENNReal.ofReal (2 * Real.pi)) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (r * max r lam ^ a) := by
    rw [ENNReal.ofReal_mul' (Real.rpow_nonneg (hlam.le.trans (le_max_right _ _)) _)]
    dsimp only [f]
    ring
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hint : IntegrableOn (fun r : ℝ => r * max r lam ^ a) (Ioi 0) := by
    have h := (integrable_fun_norm_complex_iff (fun r : ℝ => max r lam ^ a)).mp
      (integrable_rpow_rho hlam ha)
    simpa only [mul_comm] using h
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem
    measurableSet_Ioi (fun r hr => mul_nonneg (le_of_lt hr) (by positivity)))]
  refine (mul_le_mul_right (ENNReal.ofReal_le_ofReal (integral_radial_rpow_le ha hlam)) _).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  congr 1
  ring

/-- Fubini factorizes the radial product into identical one-vector integrals. -/
theorem lintegral_product_rpow_rho {I : Type*} [Fintype I]
    {a lam : ℝ} (ha : a < -2) (hlam : 0 < lam) :
    (∫⁻ u : I → ℂ, ENNReal.ofReal (∏ i, rho lam (u i) ^ a)) =
      (∫⁻ z : ℂ, ENNReal.ofReal (rho lam z ^ a)) ^ Fintype.card I := by
  classical
  have hint : Integrable (fun u : I → ℂ => ∏ i, rho lam (u i) ^ a) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun _ => integrable_rpow_rho hlam ha)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun u => prod_nonneg fun i _ =>
      Real.rpow_nonneg (rho_pos hlam (u i)).le a),
    integral_fintype_prod_volume_eq_pow (ι := I) (fun z : ℂ => rho lam z ^ a),
    ENNReal.ofReal_pow (integral_nonneg fun z => Real.rpow_nonneg (rho_pos hlam z).le a),
    ofReal_integral_eq_lintegral_ofReal (integrable_rpow_rho hlam ha)
      (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (rho_pos hlam z).le a)]

/-- The λ-explicit small-power factorization of Lemma 4.26.
Any positive η below the subcritical gap works. The loss λ^(-kη)
cancels the η contribution in the k one-dimensional integrals. -/
theorem exists_lintegral_logRadialWeight_le_of_eta {I : Type*} [Fintype I] [Nonempty I]
    {β η : ℝ} (hη : 0 < η) (hgap : η < β - 4 + 2 / (Fintype.card I : ℝ)) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      (∫⁻ u : I → ℂ, ENNReal.ofReal (logRadialWeight β lam q u)) ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  classical
  let k := Fintype.card I
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let a := 2 - 2 / (k : ℝ) + η - β
  have ha : a < -2 := by dsimp only [a, k]; linarith
  let D := 2 * Real.pi * (1 + 1 / (-(a + 2)))
  have hden : 0 < -(a + 2) := by linarith
  have hD : 0 < D := by dsimp only [D]; positivity
  let L := (1 + (q : ℝ) / η) ^ q
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨L * D ^ k, mul_pos hL (pow_pos hD _), fun lam hlam => ?_⟩
  calc
    _ ≤ ∫⁻ u : I → ℂ, ENNReal.ofReal ((L * lam ^ (-η * k)) *
          ∏ i, rho lam (u i) ^ a) :=
      lintegral_mono fun u => ENNReal.ofReal_le_ofReal (logRadialWeight_le_product hlam hη q u)
    _ = ENNReal.ofReal (L * lam ^ (-η * k)) *
        (∫⁻ z : ℂ, ENNReal.ofReal (rho lam z ^ a)) ^ k := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ L * lam ^ (-η * k))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_product_rpow_rho ha hlam]
    _ ≤ ENNReal.ofReal (L * lam ^ (-η * k)) *
        ENNReal.ofReal (D * lam ^ (a + 2)) ^ k :=
      mul_le_mul_right (pow_le_pow_left' (lintegral_rpow_rho_le ha hlam) k) _
    _ = _ := by
      rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ D * lam ^ (a + 2)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ L * lam ^ (-η * k)),
        mul_pow, ← Real.rpow_natCast (lam ^ (a + 2)) k, ← Real.rpow_mul hlam.le]
      congr 1
      calc
        _ = (L * D ^ k) * (lam ^ (-η * k) * lam ^ ((a + 2) * k)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hlam]
          congr 2
          dsimp only [a]
          field_simp
          ring

/-- Choose η as half the subcritical gap, before choosing λ. -/
theorem exists_lintegral_logRadialWeight_factorized_le {I : Type*} [Fintype I] [Nonempty I]
    {β : ℝ} (hk : (Fintype.card I : ℕ∞) ≤ pStar β) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      (∫⁻ u : I → ℂ, ENNReal.ofReal (logRadialWeight β lam q u)) ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  have hgap := two_sub_two_div_lt_of_le_pStar (Fintype.card_pos (α := I)) hk
  let η := (β - 4 + 2 / (Fintype.card I : ℝ)) / 2
  exact exists_lintegral_logRadialWeight_le_of_eta (η := η) (by dsimp [η]; linarith)
    (by dsimp [η]; linarith) q

end MultipoleBKT.Limits.RouteDirect

end
