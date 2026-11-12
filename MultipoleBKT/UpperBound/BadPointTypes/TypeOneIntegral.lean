/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneData
public import MultipoleBKT.UpperBound.BadPointTypes.Forest

/-!
# Lemma 5.40: integrating the bound for fixed data

The paper: proof of Lemma 5.40, Step 5 ( for
`β ∈ (2,4)`, for `β ≥ 4`): "integrating for each cluster over all indices except one
and then integrating out that last variable over the whole domain". For valid data
(`TypeOneValid`), the product of the factors `typeOneFactor` is integrated along the forest
whose roots are the overcrowded roots and the long singletons, whose members hang from their
roots and whose good charges hang from their partners (`lintegral_forest_le`):

* an overcrowded cluster at scale `d` contributes `N d^{-β/2} (64π d^{2-β/2})^q`
  (`q` members in discs of radius `8d`);
* a long singleton contributes `N (h/4)^{-β/2}`;
* a good charge contributes at most `K_g ≥ ∫_{|u| ≤ h} max(|u|/4, λ)^{-β/2} du`.

`lintegral_typeOneFactor_le` is the resulting bound, `typeOneBound`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset MeasureTheory
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {n : ℕ}

/-- The good kernel `u ↦ 𝟙_{|u| ≤ h} max(|u|/4, λ)^{-β/2}`. -/
noncomputable def goodKernel (β lam h : ℝ) (u : ℂ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : ℂ) h).indicator
    (fun u => ENNReal.ofReal (max (‖u‖ / 4) lam ^ (-(β / 2)))) u

theorem measurable_goodKernel {lam : ℝ} (hlam : 0 < lam) (β h : ℝ) : Measurable (goodKernel β lam h) := by
  unfold goodKernel
  refine Measurable.indicator ?_ Metric.isClosed_closedBall.measurableSet
  refine ENNReal.measurable_ofReal.comp ?_
  exact (((continuous_norm.div_const 4).max continuous_const).rpow_const fun u =>
    Or.inl (lt_max_of_lt_right hlam).ne').measurable

/-- The exponent `e = q(2 - β/2) - β/2` of an overcrowded cluster of `q + 1` charges. -/
noncomputable def clusterExponent (q : ℕ) (β : ℝ) : ℝ := q * (2 - β / 2) - β / 2

/-- **The bound for fixed data**: the product over overcrowded roots of
`N (64π)^q d^{q(2-β/2) - β/2}`, over long singletons of `N (h/4)^{-β/2}`, and `K_g` per good
charge. -/
noncomputable def typeOneBound (q : ℕ) (β lam h Kg : ℝ) (Nₐ : ℕ) (D : TOData n) : ℝ :=
  (∏ v ∈ Finset.univ.filter (fun v => D.1 v = 0),
      ((Nₐ : ℝ) * (64 * Real.pi) ^ q * dyad lam (D.2.2 v) ^ clusterExponent q β)) *
    ((Nₐ : ℝ) * (h / 4) ^ (-(β / 2))) ^ (Finset.univ.filter fun v => D.1 v = 1).card *
    Kg ^ (Finset.univ.filter fun v => D.1 v = 3).card

theorem typeOneFactor_eq_goodKernel {β lam h : ℝ} {Nₐ : ℕ} {D : TOData n} {z : Charge n → ℂ}
    {v : Charge n} (hv : D.1 v = 3) :
    typeOneFactor β lam h Nₐ D z v = goodKernel β lam h (z v - z (D.2.1 v)) :=
  typeOneFactor_of_three hv

/-- The integral of the factor of a member: `∫ 𝟙_{|t - y| ≤ 8d} d^{-β/2} dt = 64π d^{2-β/2}`. -/
theorem lintegral_member_le {β d : ℝ} (hd : 0 < d) (y : ℂ) :
    ∫⁻ t : ℂ, (Metric.closedBall (0 : ℂ) (8 * d)).indicator 1 (t - y) *
        ENNReal.ofReal (d ^ (-(β / 2))) =
      ENNReal.ofReal (64 * Real.pi * d ^ (2 - β / 2)) := by
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_sub_right_eq_self (fun t => (Metric.closedBall (0 : ℂ) (8 * d)).indicator 1 t) y,
    lintegral_indicator_one measurableSet_closedBall, Complex.volume_closedBall]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show (2 : ℝ) - β / 2 = 2 + (-(β / 2)) by ring, Real.rpow_add hd]
  norm_cast
  ring

/-- **Integration for fixed valid data** (Step 5 of the proof of Lemma 5.40, before the
summation over the dyadic scales). -/
theorem lintegral_typeOneFactor_le {q : ℕ} {β lam h Kg : ℝ} (hlam : 0 < lam) (hh : 0 ≤ h)
    (hKg0 : 0 ≤ Kg)
    (hKg : ∫⁻ u, goodKernel β lam h u ≤ ENNReal.ofReal Kg) {Nₐ : ℕ} {D : TOData n}
    (hD : TypeOneValid q D) :
    ∫⁻ z : Charge n → ℂ, ∏ v, typeOneFactor β lam h Nₐ D z v ≤
      ENNReal.ofReal (typeOneBound q β lam h Kg Nₐ D) := by
  classical
  obtain ⟨hV1, hV2, hV3, -, hV5, -⟩ := hD
  set R := Finset.univ.filter fun v => D.1 v = 0 ∨ D.1 v = 1 with hR
  set w : Charge n → ℝ≥0∞ := fun v => if D.1 v = 0 then
    ENNReal.ofReal (dyad lam (D.2.2 v) ^ (-(β / 2))) else ENNReal.ofReal ((h / 4) ^ (-(β / 2)))
  set hf : Charge n → ℂ → ℝ≥0∞ := fun v t => (box Nₐ).indicator 1 t * w v
  set ψ : Charge n → ℂ → ℂ → ℝ≥0∞ := fun v t y => if D.1 v = 2 then
    (Metric.closedBall (0 : ℂ) (8 * dyad lam (D.2.2 (D.2.1 v)))).indicator 1 (t - y) *
      ENNReal.ofReal (dyad lam (D.2.2 (D.2.1 v)) ^ (-(β / 2)))
    else goodKernel β lam h (t - y)
  set K : Charge n → ℝ≥0∞ := fun v => if D.1 v = 2 then
    ENNReal.ofReal (64 * Real.pi * dyad lam (D.2.2 (D.2.1 v)) ^ (2 - β / 2)) else ENNReal.ofReal Kg
  set dep : Charge n → ℕ := fun v => if D.1 v = 0 ∨ D.1 v = 1 then 0 else if D.1 v = 2 then 1 else 2
  have hdyad : ∀ s, 0 < dyad lam s := fun s => by unfold dyad; positivity
  -- the factors in forest form
  have hsplit : ∀ z : Charge n → ℂ, ∏ v, typeOneFactor β lam h Nₐ D z v =
      (∏ r ∈ R, hf r (z r)) * ∏ c ∈ Rᶜ, ψ c (z c) (z (D.2.1 c)) := by
    intro z
    rw [← prod_mul_prod_compl R]
    congr 1
    · refine prod_congr rfl fun v hv => ?_
      rcases (mem_filter.1 hv).2 with h0 | h1
      · rw [typeOneFactor_of_zero h0]
        simp [hf, w, h0]
      · rw [typeOneFactor_of_one h1]
        have : D.1 v ≠ 0 := by rw [h1]; decide
        simp [hf, w, this]
    · refine prod_congr rfl fun v hv => ?_
      have hv' : ¬ (D.1 v = 0 ∨ D.1 v = 1) := by
        intro h'
        exact (mem_compl.1 hv) (mem_filter.2 ⟨mem_univ v, h'⟩)
      by_cases h2 : D.1 v = 2
      · rw [typeOneFactor_of_two h2]
        simp [ψ, h2]
      · have h3 : D.1 v = 3 := by
          push Not at hv'
          revert hv' h2
          generalize D.1 v = k
          fin_cases k <;> simp
        rw [typeOneFactor_of_three h3]
        simp [ψ, h2, goodKernel]
  simp_rw [hsplit]
  have hdepdec : ∀ c, c ∉ R → dep (D.2.1 c) < dep c := by
    intro c hc
    have hc' : ¬ (D.1 c = 0 ∨ D.1 c = 1) := fun h' => hc (mem_filter.2 ⟨mem_univ c, h'⟩)
    by_cases h2 : D.1 c = 2
    · have hp := hV1 c h2
      simp [dep, hp, h2]
    · have h3 : D.1 c = 3 := by
        push Not at hc'
        revert hc' h2
        generalize D.1 c = k
        fin_cases k <;> simp
      rcases hV2 c h3 with hp | hp
      · simp [dep, hp, h3]
      · simp [dep, hp, h3]
  have hψm : ∀ v, Measurable (Function.uncurry (ψ v)) := by
    intro v
    by_cases h2 : D.1 v = 2
    · simp only [ψ, h2, ite_true]
      exact ((measurable_const.indicator measurableSet_closedBall).comp
        (measurable_fst.sub measurable_snd)).mul measurable_const
    · simp only [ψ, h2, ite_false]
      exact (measurable_goodKernel hlam β h).comp (measurable_fst.sub measurable_snd)
  have hKle : ∀ c, c ∉ R → ∀ y, ∫⁻ t, ψ c t y ≤ K c := by
    intro c _ y
    by_cases h2 : D.1 c = 2
    · simp only [ψ, K, h2, ite_true]
      exact (lintegral_member_le (hdyad _) y).le
    · simp only [ψ, K, h2, ite_false]
      rw [lintegral_sub_right_eq_self (fun t => goodKernel β lam h t) y]
      exact hKg
  have hhm : ∀ r, Measurable (hf r) := fun r =>
    (measurable_const.indicator (TwoComponentCoulomb.measurableSet_box Nₐ)).mul measurable_const
  refine (lintegral_forest_le R D.2.1 dep hdepdec ψ hψm K hKle hf hhm).trans (le_of_eq ?_)
  -- evaluating the bound
  have hroot : ∀ r, ∫⁻ t, hf r t = (Nₐ : ℝ≥0∞) * w r := by
    intro r
    simp only [hf]
    rw [lintegral_mul_const' _ _ (by simp only [w]; split_ifs <;> exact ENNReal.ofReal_ne_top),
      lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box Nₐ),
      TwoComponentCoulomb.volume_box]
  simp_rw [hroot]
  set R0 := Finset.univ.filter fun v => D.1 v = 0 with hR0
  set R1 := Finset.univ.filter fun v => D.1 v = 1 with hR1
  set S2 := Finset.univ.filter fun v => D.1 v = 2 with hS2
  set S3 := Finset.univ.filter fun v => D.1 v = 3 with hS3
  have hRsplit : R = R0 ∪ R1 := by
    ext v
    simp [R, R0, R1]
  have hR01 : Disjoint R0 R1 := by
    rw [disjoint_filter]
    intro v _ h0 h1
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hRc : Rᶜ = S2 ∪ S3 := by
    ext v
    simp only [R, S2, S3, mem_compl, mem_filter, mem_univ, true_and, mem_union]
    generalize D.1 v = k
    fin_cases k <;> simp
  have hS23 : Disjoint S2 S3 := by
    rw [disjoint_filter]
    intro v _ h2 h3
    rw [h2] at h3
    exact absurd h3 (by decide)
  rw [hRc, prod_union hS23, hRsplit, prod_union hR01]
  -- the roots of kind 1 and the goods
  have hR1prod : ∏ r ∈ R1, (Nₐ : ℝ≥0∞) * w r =
      ENNReal.ofReal (((Nₐ : ℝ) * (h / 4) ^ (-(β / 2))) ^ R1.card) := by
    have hh4 : 0 ≤ (h / 4) ^ (-(β / 2)) := Real.rpow_nonneg (by positivity) _
    rw [prod_congr rfl (g := fun _ => (Nₐ : ℝ≥0∞) * ENNReal.ofReal ((h / 4) ^ (-(β / 2))))
      fun r hr => by
        have h1 := (mem_filter.1 hr).2
        have : D.1 r ≠ 0 := by rw [h1]; decide
        simp only [w, this, ite_false], prod_const, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have hS3prod : ∏ c ∈ S3, K c = ENNReal.ofReal (Kg ^ S3.card) := by
    rw [prod_congr rfl (g := fun _ => ENNReal.ofReal Kg) fun c hc => by
      have h3 := (mem_filter.1 hc).2
      have : D.1 c ≠ 2 := by rw [h3]; decide
      simp only [K, this, ite_false], prod_const, ENNReal.ofReal_pow hKg0]
  -- the members, grouped by root
  have hS2prod : ∏ c ∈ S2, K c = ∏ r ∈ R0,
      ENNReal.ofReal (64 * Real.pi * dyad lam (D.2.2 r) ^ (2 - β / 2)) ^ q := by
    rw [prod_congr rfl (g := fun c =>
        ENNReal.ofReal (64 * Real.pi * dyad lam (D.2.2 (D.2.1 c)) ^ (2 - β / 2))) fun c hc => by
      have h2 := (mem_filter.1 hc).2
      simp only [K, h2, ite_true]]
    rw [← prod_fiberwise_of_maps_to' (t := R0) (g := D.2.1)
      (fun c hc => mem_filter.2 ⟨mem_univ _, hV1 c (mem_filter.1 hc).2⟩)
      (fun r => ENNReal.ofReal (64 * Real.pi * dyad lam (D.2.2 r) ^ (2 - β / 2)))]
    refine prod_congr rfl fun r hr => ?_
    rw [prod_const]
    congr 1
    rw [filter_filter]
    exact hV3 r (mem_filter.1 hr).2
  rw [hR1prod, hS3prod, hS2prod]
  -- the overcrowded roots
  have hR0prod : (∏ r ∈ R0, (Nₐ : ℝ≥0∞) * w r) *
      ∏ r ∈ R0, ENNReal.ofReal (64 * Real.pi * dyad lam (D.2.2 r) ^ (2 - β / 2)) ^ q =
      ENNReal.ofReal (∏ r ∈ R0,
        ((Nₐ : ℝ) * (64 * Real.pi) ^ q * dyad lam (D.2.2 r) ^ clusterExponent q β)) := by
    rw [← prod_mul_distrib, ENNReal.ofReal_prod_of_nonneg fun r _ => by
      have := hdyad (D.2.2 r)
      positivity]
    refine prod_congr rfl fun r hr => ?_
    have h0 := (mem_filter.1 hr).2
    simp only [w, h0, ite_true]
    have hd := hdyad (D.2.2 r)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold clusterExponent
    rw [mul_pow, ← Real.rpow_natCast (dyad lam (D.2.2 r) ^ (2 - β / 2)),
      ← Real.rpow_mul hd.le, show (q : ℝ) * (2 - β / 2) - β / 2 =
        -(β / 2) + (2 - β / 2) * q by ring, Real.rpow_add hd]
    ring
  unfold typeOneBound
  have hh4 : 0 ≤ (h / 4) ^ (-(β / 2)) := Real.rpow_nonneg (by positivity) _
  rw [ENNReal.ofReal_mul (by
      refine mul_nonneg (prod_nonneg fun r _ => ?_) (pow_nonneg (by positivity) _)
      have := hdyad (D.2.2 r)
      positivity),
    ENNReal.ofReal_mul (prod_nonneg fun r _ => by
      have := hdyad (D.2.2 r)
      positivity), ← hR0prod]
  ring

end BadPointTypes

end MultipoleBKT

end
