/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.Configuration

/-!
# Absorbing the activity-tree radial logarithms

See (A.63). Apply the three radial regimes after the logarithmic spatial
calculation. Only the area coefficient contains epsilon to a negative power.
The bad-point coefficient is independent of epsilon.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits SmallIntegral
open SmallIntegral.RouteJ SmallIntegral.RouteJext GeneralExpansion
open scoped Classical ENNReal

/-- The final frozen-model estimate for each normalized original tree, including
case E. Both radial moment orders are evaluated before the logarithms are absorbed. -/
theorem frozen_activityTree_bound {χ : ℂ → ℝ} {β M : ℝ} (hχ : IsMollifier χ) (hβ : 2 < β)
    (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k →
      ∀ {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      UpperBound.badPointsOn p₀ β lam M eps V Z = V →
      ∀ (T : SimpleGraph W) [DecidableRel T.Adj], T.IsTree →
      ∀ (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (root : W),
      (∫⁻ c : W → ℂ × ℂ, (ENNReal.ofReal ((rhoD lam (c root) ^ 2)⁻¹) *
          rootM p₀ β lam M eps V Z ((c root).1 - (c root).2) (c root).2) *
        activityTree M lam (eps * truncationScale p₀ β lam) T A E mark c *
          activityDensity χ β lam (eps * truncationScale p₀ β lam) c) ≤
        ENNReal.ofReal (lam ^ ((2 - β) * k) *
          (C * eps ^ (-2 : ℝ) * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * eps ^ (alphaExponent β * k) * V.card)) := by
  obtain ⟨Ca, hCa, hcap⟩ := vectorWeight_gain hχ hβ p₀ hk (k - 1)
  obtain ⟨Cb, hCb, hbad⟩ := vectorWeight_gain hχ hβ p₀ hk k
  let K := (4 * Real.pi * (M ^ 2 + 5)) ^ (k - 1)
  let C := K * (Ca + (128 * Real.pi + 4 * Real.pi * M ^ 2) * Cb)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun eps lam hlam hle heps hM3 W _ _ _ hW N V Z hV T _ hT A E mark root => ?_⟩
  have heps0 := hlam.trans_le hle
  have hscale := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hlh : lam ≤ eps * truncationScale p₀ β lam := hle.trans
    (le_mul_of_one_le_right heps0.le (Appendix.one_le_truncationScale hβ hlam (hle.trans heps)))
  have hα : 0 ≤ alphaExponent β * k := by
    have hα : 0 ≤ alphaExponent β := by unfold alphaExponent; split_ifs <;> linarith
    exact mul_nonneg hα (Nat.cast_nonneg k)
  have hepsgain := Real.rpow_le_one heps0.le heps hα
  have hcap' := hcap W hW eps lam hlam hle heps
  have hbad' := hbad W hW eps lam hlam hle heps
  have hcap0 : (∫⁻ u : W → ℂ, vectorWeight χ β lam (eps * truncationScale p₀ β lam) (k - 1) u) ≤
      ENNReal.ofReal (Ca * lam ^ ((2 - β) * k)) := by
    refine hcap'.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ Ca * 1 * lam ^ ((2 - β) * k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hepsgain hCa.le)
          (Real.rpow_nonneg hlam.le _)
      _ = _ := by ring
  have hs := lintegral_frozen_activityTree_le_vectors hχ hlam hM3 hlh V Z hV T hT A E mark root
  rw [hW] at hs
  refine hs.trans ?_
  calc
    _ ≤ ENNReal.ofReal K *
        (ENNReal.ofReal (N / (eps * truncationScale p₀ β lam) ^ 2) *
          ENNReal.ofReal (Ca * lam ^ ((2 - β) * k)) +
          ENNReal.ofReal ((128 * Real.pi + 4 * Real.pi * M ^ 2) * V.card) *
            ENNReal.ofReal (Cb * eps ^ (alphaExponent β * k) * lam ^ ((2 - β) * k))) :=
      mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hcap0) (mul_le_mul' le_rfl hbad'))
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hK.le]
      apply ENNReal.ofReal_le_ofReal
      have he : (eps * truncationScale p₀ β lam) ^ 2 = eps ^ 2 * truncationScale p₀ β lam ^ 2 := mul_pow _ _ _
      rw [Real.rpow_neg heps0.le, Real.rpow_two,
        Real.rpow_neg hscale.le, Real.rpow_two, he]
      have hca : K * Ca ≤ C := by
        dsimp only [C]
        nlinarith [mul_pos hK hCa, mul_pos hK (mul_pos Real.pi_pos hCb)]
      have hcb : K * ((128 * Real.pi + 4 * Real.pi * M ^ 2) * Cb) ≤ C := by dsimp only [C]; nlinarith [mul_pos hK hCa]
      have ha := mul_le_mul_of_nonneg_right hca
        (show 0 ≤ (eps ^ 2)⁻¹ * N * (truncationScale p₀ β lam ^ 2)⁻¹ by positivity)
      have hb := mul_le_mul_of_nonneg_right hcb
        (show 0 ≤ eps ^ (alphaExponent β * k) * V.card by positivity)
      have hfin := mul_le_mul_of_nonneg_left (add_le_add ha hb)
        (Real.rpow_nonneg hlam.le ((2 - β) * k))
      convert hfin using 1 <;> field_simp

/-- The screened-model counterpart of (A.63) for each normalized original tree. The fixed inverse screening radius supplies the area term. -/
theorem screened_activityTree_bound {χ : ℂ → ℝ} {β M : ℝ} (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k →
      ∀ (N : ℕ) (T : SimpleGraph W) [DecidableRel T.Adj], T.IsTree →
      ∀ (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (root : W),
      (∫⁻ c : W → ℂ × ℂ, ((TwoComponentCoulomb.box N).indicator 1 (c root).2 *
          ENNReal.ofReal (((eps * truncationScale p₀ β lam) ^ 2)⁻¹)) *
        activityTree M lam (eps * truncationScale p₀ β lam) T A E mark c *
          activityDensity χ β lam (eps * truncationScale p₀ β lam) c) ≤
        ENNReal.ofReal (C * eps ^ (-2 : ℝ) * N *
          lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  obtain ⟨Ca,hCa,hbound⟩ := vectorWeight_gain hχ hβ p₀ hk (k - 1)
  let K := (4 * Real.pi * (M ^ 2 + 5)) ^ (k - 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K * Ca, mul_pos hK hCa, fun eps lam hlam hle heps W _ _ _ hW N T _ hT A E mark root => ?_⟩
  have heps0 := hlam.trans_le hle
  have hscale := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hlh : lam ≤ eps * truncationScale p₀ β lam := hle.trans
    (le_mul_of_one_le_right heps0.le (Appendix.one_le_truncationScale hβ hlam (hle.trans heps)))
  have hα : 0 ≤ alphaExponent β * k := by
    have ha : 0 ≤ alphaExponent β := by unfold alphaExponent; split_ifs <;> linarith
    exact mul_nonneg ha (Nat.cast_nonneg k)
  have hm := hbound W hW eps lam hlam hle heps
  have hm' : (∫⁻ u : W → ℂ, vectorWeight χ β lam (eps * truncationScale p₀ β lam) (k - 1) u) ≤
      ENNReal.ofReal (Ca * lam ^ ((2 - β) * k)) := by
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := Real.rpow_le_one heps0.le heps hα
    calc
      _ ≤ Ca * 1 * lam ^ ((2 - β) * k) := by gcongr
      _ = _ := by ring
  have hs := lintegral_screened_activityTree_le_vectors (β := β) hχ hlam hM hlh N T hT A E mark root
  rw [hW] at hs
  refine hs.trans ((mul_le_mul' le_rfl hm').trans_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_neg heps0.le, Real.rpow_two, Real.rpow_neg hscale.le, Real.rpow_two, mul_pow]
  dsimp only [K]
  simp only [mul_pow]
  ring

end MultipoleBKT.ExpansionK.RouteSpatial

end
