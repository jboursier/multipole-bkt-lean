/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.SourceSum
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.RootLog

/-!
# The actual frozen screening and bad-label root factors

See (A.41)
and Step 3 of the proof of Lemma A.7.
The extended screening radius and the bad-label correction of the pointwise expansion are
compared with the regularized root before its logarithmic integration.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset Limits SmallIntegral MultipoleIntegralZ UpperBound RouteCases
open TwoComponentCoulomb (box)
open scoped Classical ENNReal

/-- The scalar root left by the pointwise expansion after cancelling the largest-radius square. -/
theorem frozen_sourceRoot_scalar {N p₀ : ℕ} {β lam M eps R : ℝ}
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (d : ℂ × ℂ)
    (hlam : 0 < lam) (hR : rhoD lam d ≤ R) :
    (routeFrozenRadius p₀ β lam eps V Z d ^ 2)⁻¹ +
        |routeFrozenBad p₀ β lam M eps V Z d| / R ^ 2 ≤
      17 * (if IsGoodZ p₀ β lam M eps V Z d then
        (goodRadiusZ p₀ β lam eps V Z d ^ 2)⁻¹ else (rhoD lam d ^ 2)⁻¹) := by
  let τ := routeFrozenRadius p₀ β lam eps V Z d
  let m := rhoD lam d
  have hm : 0 < m := rhoD_pos hlam d
  have hτ : 0 < τ := hlam.trans_le (routeFrozenRadius_lower p₀ β lam eps V Z d).1
  have hg : 0 < goodRadiusZ p₀ β lam eps V Z d := hlam.trans_le (lam_le_goodRadiusZ d)
  have hmτ : m ≤ 4 * τ := by
    apply max_le
    · have := (routeFrozenRadius_lower p₀ β lam eps V Z d).2
      dsimp only [τ] at *
      linarith
    · have := (routeFrozenRadius_lower p₀ β lam eps V Z d).1
      dsimp only [τ] at *
      linarith
  by_cases hgood : IsGoodZ p₀ β lam M eps V Z d
  · rw [ite_eq_left hgood,routeFrozenBad,ite_eq_left hgood,abs_zero,zero_div,add_zero]
    have hgτ : goodRadiusZ p₀ β lam eps V Z d ≤ τ := le_max_left _ _
    have hi := inv_anti₀ (sq_pos_of_pos hg) (pow_le_pow_left₀ hg.le hgτ 2)
    exact hi.trans (le_mul_of_one_le_left (inv_nonneg.2 (sq_nonneg _)) (by norm_num))
  · rw [ite_eq_right hgood,routeFrozenBad,ite_eq_right hgood,abs_neg,abs_one,one_div]
    have hτm : (τ ^ 2)⁻¹ ≤ 16 * (m ^ 2)⁻¹ := by
      apply (le_div_iff₀ (sq_pos_of_pos hm)).2
      have hs : m ^ 2 ≤ 16 * τ ^ 2 := by nlinarith [sq_nonneg (4 * τ - m)]
      have ht := (div_le_iff₀ (sq_pos_of_pos hτ)).2 hs
      convert ht using 1
      ring
    have hRm : (R ^ 2)⁻¹ ≤ (m ^ 2)⁻¹ := inv_anti₀ (sq_pos_of_pos hm)
      (pow_le_pow_left₀ hm.le hR 2)
    change (τ ^ 2)⁻¹ + (R ^ 2)⁻¹ ≤ 17 * (m ^ 2)⁻¹
    linarith

/-- The regularized spatial root is exactly the normalized good/bad alternative. -/
theorem normalized_rootM_eq {N p₀ : ℕ} {β lam M eps : ℝ}
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (d : ℂ × ℂ) (hlam : 0 < lam) :
    ENNReal.ofReal ((rhoD lam d ^ 2)⁻¹) *
      rootM p₀ β lam M eps V Z (d.1-d.2) d.2 =
      (box N).indicator 1 d.2 * ENNReal.ofReal
        (if IsGoodZ p₀ β lam M eps V Z d then
          (goodRadiusZ p₀ β lam eps V Z d ^ 2)⁻¹ else (rhoD lam d ^ 2)⁻¹) := by
  have hd : (d.2 + (d.1-d.2),d.2) = d := by ext <;> simp
  unfold rootM
  rw [hd]
  change ENNReal.ofReal ((rhoD lam d ^ 2)⁻¹) *
    ((box N).indicator 1 d.2 *
      ((if IsGoodZ p₀ β lam M eps V Z d then
        ENNReal.ofReal ((rhoD lam d / goodRadiusZ p₀ β lam eps V Z d) ^ 2) else 0) +
       (if IsGoodZ p₀ β lam M eps V Z d then 0 else 1))) = _
  by_cases hgood : IsGoodZ p₀ β lam M eps V Z d
  · rw [ite_eq_left hgood,ite_eq_left hgood,add_zero,ite_eq_left hgood]
    rw [mul_left_comm]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [(rhoD_pos hlam d).ne']
  · rw [ite_eq_right hgood,ite_eq_right hgood,zero_add,mul_one,ite_eq_right hgood,mul_comm]

/-- The actual screening and bad-root factors are below the normalized root
on every configuration, including configurations containing a bad dipole. -/
theorem frozen_sourceRoot_le {N p₀ : ℕ} {β lam M eps R : ℝ}
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (d : ℂ × ℂ)
    (hlam : 0 < lam) (hR : rhoD lam d ≤ R) :
    (box N).indicator 1 d.2 * ENNReal.ofReal
      ((routeFrozenRadius p₀ β lam eps V Z d ^ 2)⁻¹ +
        |routeFrozenBad p₀ β lam M eps V Z d| / R ^ 2) ≤
      17 * (ENNReal.ofReal ((rhoD lam d ^ 2)⁻¹) *
        rootM p₀ β lam M eps V Z (d.1-d.2) d.2) := by
  rw [normalized_rootM_eq V Z d hlam]
  have hs := ENNReal.ofReal_le_ofReal (frozen_sourceRoot_scalar (p₀ := p₀) (β := β) (M := M) (eps := eps) V Z d hlam hR)
  rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat] at hs
  exact (mul_le_mul' le_rfl hs).trans_eq (by ring)

/-- Logarithmic integration of the actual root after radius allocation.
The coefficient of the bad-point term is independent of epsilon. -/
theorem lintegral_frozen_sourceRoot_log_le {N p₀ : ℕ} {β lam M eps R a : ℝ}
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ)
    (hlam : 0 < lam) (hlh : lam ≤ eps * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hV : badPointsOn p₀ β lam M eps V Z = V)
    (w : ℂ) (hw : ‖w‖ ≤ eps * truncationScale p₀ β lam)
    (ha : 0 < a) (ham : a ≤ max ‖w‖ lam) (hmR : max ‖w‖ lam ≤ R) :
    (∫⁻ y : ℂ, (box N).indicator 1 y * ENNReal.ofReal
      ((routeFrozenRadius p₀ β lam eps V Z (y+w,y) ^ 2)⁻¹ +
        |routeFrozenBad p₀ β lam M eps V Z (y+w,y)| / R ^ 2)) ≤
      17 * ENNReal.ofReal (N / (eps * truncationScale p₀ β lam) ^ 2 +
        (128 * Real.pi + 4 * Real.pi * M ^ 2) * V.card *
          (1 + Real.log (17 * (eps * truncationScale p₀ β lam) / a))) := by
  have he (y : ℂ) : (y+w)-y = w := by ring
  have hrho (y : ℂ) : rhoD lam (y+w,y) = max ‖w‖ lam := by
    change max ‖y+w-y‖ lam = _
    rw [he y]
  have hp (y : ℂ) := frozen_sourceRoot_le (p₀ := p₀) (β := β) (M := M) (eps := eps) V Z (y+w,y) hlam
    (show rhoD lam (y+w,y) ≤ R by rw [hrho]; exact hmR)
  have hb := lintegral_mono (μ := (volume : Measure ℂ)) hp
  simp_rw [he,hrho] at hb
  rw [lintegral_const_mul' _ _ (by norm_num)] at hb
  exact hb.trans (mul_le_mul' le_rfl (lintegral_normalized_rootM_log_le hlam hlh hM hV hw ha ham))

end MultipoleBKT.ExpansionK.RouteSpatial

end
