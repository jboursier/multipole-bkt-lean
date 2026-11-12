/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Configuration

/-!
# Uniform external-gain bounds for one retained tree

See (A.20), the proof of Lemma A.4. The area term carries epsilon_0 to power
minus two. The bad-point coefficient is chosen before epsilon_0.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJext

open MeasureTheory Set Finset SimpleGraph Limits RouteJ GeneralExpansion
open scoped Classical ENNReal

/-- The logarithmic tree integration followed by the three-regime radial gain.
Only the area coefficient contains a negative power of the cutoff. -/
theorem term_bound {χ : ℂ → ℝ} {β M : ℝ} (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k →
      ∀ {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (A E F : Finset (Sym2 W)),
      (fromEdgeSet ((F ∪ (A ∪ E) : Finset (Sym2 W)) : Set (Sym2 W))).IsTree →
      (fromEdgeSet ((F ∪ (A ∪ E) : Finset (Sym2 W)) : Set (Sym2 W))).edgeFinset = F ∪ (A ∪ E) →
      ∀ root : W, (∫⁻ c in boxConfig W N, term χ β lam M eps p₀ V Z A E F root c) ≤
        ENNReal.ofReal (lam ^ ((2 - β) * k) *
          (C * eps ^ (-2 : ℝ) * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * eps ^ (alphaExponent β * k) * V.card)) := by
  obtain ⟨Ca, hCa, hcap⟩ := vectorWeight_gain hχ hβ p₀ hk (k - 1)
  obtain ⟨Cb, hCb, hbad⟩ := vectorWeight_gain hχ hβ p₀ hk k
  let K := (4 * Real.pi * (M ^ 2 + 5)) ^ (k - 1)
  let C := K * (Ca + 8 * Real.pi * Cb)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun eps lam hlam hle heps W _ _ _ hW N V Z A E F hT hTE root => ?_⟩
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
  have hs := lintegral_term_le_vectors hχ hlam hM p₀ V Z A E F hT hTE hlh root
  rw [hW] at hs
  refine hs.trans ?_
  calc
    _ ≤ ENNReal.ofReal K *
        (ENNReal.ofReal (N / (16 * (eps * truncationScale p₀ β lam) ^ 2)) *
          ENNReal.ofReal (Ca * lam ^ ((2 - β) * k)) +
          ENNReal.ofReal (8 * Real.pi * V.card) *
            ENNReal.ofReal (Cb * eps ^ (alphaExponent β * k) * lam ^ ((2 - β) * k))) :=
      mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hcap0) (mul_le_mul' le_rfl hbad'))
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hK.le]
      apply ENNReal.ofReal_le_ofReal
      have he : (eps * truncationScale p₀ β lam) ^ 2 = eps ^ 2 * truncationScale p₀ β lam ^ 2 := mul_pow _ _ _
      rw [Real.rpow_neg heps0.le, Real.rpow_two,
        Real.rpow_neg hscale.le, Real.rpow_two, he]
      have hca : K * Ca / 16 ≤ C := by
        dsimp only [C]
        nlinarith [mul_pos hK hCa, mul_pos hK (mul_pos Real.pi_pos hCb)]
      have hcb : K * (8 * Real.pi * Cb) ≤ C := by dsimp only [C]; nlinarith [mul_pos hK hCa]
      have ha := mul_le_mul_of_nonneg_right hca
        (show 0 ≤ (eps ^ 2)⁻¹ * N * (truncationScale p₀ β lam ^ 2)⁻¹ by positivity)
      have hb := mul_le_mul_of_nonneg_right hcb
        (show 0 ≤ eps ^ (alphaExponent β * k) * V.card by positivity)
      have hfin := mul_le_mul_of_nonneg_left (add_le_add ha hb)
        (Real.rpow_nonneg hlam.le ((2 - β) * k))
      convert hfin using 1 <;> field_simp

end MultipoleBKT.SmallIntegral.RouteJext

end
