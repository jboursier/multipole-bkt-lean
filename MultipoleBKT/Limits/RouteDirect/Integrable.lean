/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.ParityMajorant

/-!
# Integrability through the written logarithmic majorant

See Lemma 4.26 of the paper. The parity terms are bounded by the separate odd and even trees.
Spatial integration gives logarithms, followed by the paper's final power absorption.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [LinearOrder I] [Nonempty I]
  [Fintype B] [DecidableEq B]
variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- Internal uniform domination interface for a parity average. All geometric
choices are bounded by the same finite sum before λ and M are specified. -/
theorem exists_parity_average_le_mixedTreeSum (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hinter : ∀ i j, E.Adj i j → blk i ≠ blk j)
    (hconn : ∀ b b', (nodeGraph (Sym2.map blk) E.edgeFinset).Reachable b b')
    {Cw : ℝ} (hCw : 0 ≤ Cw) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ lam : ℝ, 0 < lam → ∀ M : ℝ, 1 ≤ M →
      ∀ G : (I → ℂ × ℂ) → ℝ,
      (∀ c, |G c| ≤ Cw *
      (if ∀ b, ((nearGraph M lam c).induce {i | blk i = b}).Connected then 1 else 0) *
      (∏ i, pairDensity χ β lam (c i)) *
      ∑ F ∈ E.edgeFinset.powerset.filter (CutEven (Sym2.map blk)),
        (∏ e ∈ E.edgeFinset \ F, |alphaE hχ β lam M c e|) * ∏ e ∈ F, |gammaE hχ β lam M c e|) →
      ∀ c, ENNReal.ofReal |G c| ≤ ENNReal.ofReal D * mixedTreeSum χ β lam M c := by
  obtain ⟨C, hC, hb⟩ := exists_parity_term_le_mixedTreeSum hχ hβ blk hblk E hinter hconn
  let Fs := E.edgeFinset.powerset.filter (CutEven (Sym2.map blk))
  refine ⟨Cw * C * Fs.card, by positivity, fun lam hlam M hM G hbound c => ?_⟩
  have hsum0 (c : I → ℂ × ℂ) (F : Finset (Sym2 I)) :
      0 ≤ (∏ e ∈ E.edgeFinset \ F, |alphaE hχ β lam M c e|) * ∏ e ∈ F, |gammaE hχ β lam M c e| :=
    mul_nonneg (prod_nonneg fun _ _ => abs_nonneg _) (prod_nonneg fun _ _ => abs_nonneg _)
  by_cases hnear : ∀ b, ((nearGraph M lam c).induce {i | blk i = b}).Connected
  · have h := hbound c
    rw [ite_eq_left hnear, mul_one] at h
    simp only [mul_assoc, Finset.mul_sum] at h
    have hpd : 0 ≤ ∏ i, pairDensity χ β lam (c i) := prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le
    calc
      _ ≤ ∑ F ∈ Fs, ENNReal.ofReal (Cw * ((∏ i, pairDensity χ β lam (c i)) *
          ((∏ e ∈ E.edgeFinset \ F, |alphaE hχ β lam M c e|) * ∏ e ∈ F, |gammaE hχ β lam M c e|))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun F _ => mul_nonneg hCw (mul_nonneg hpd (hsum0 c F)))]
        exact ENNReal.ofReal_le_ofReal h
      _ ≤ ∑ _F ∈ Fs, ENNReal.ofReal (Cw * C) * mixedTreeSum χ β lam M c := by
        apply sum_le_sum
        intro F hF
        rw [ENNReal.ofReal_mul hCw, ENNReal.ofReal_mul hCw, mul_assoc]
        exact mul_le_mul_right (hb lam hlam M hM F (mem_powerset.mp (mem_filter.mp hF).1)
          (mem_filter.mp hF).2 c hnear) _
      _ = _ := by
        rw [sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring_nf
  · have h := hbound c
    rw [ite_eq_right hnear, mul_zero, zero_mul, zero_mul] at h
    rw [le_antisymm h (abs_nonneg _), ENNReal.ofReal_zero]
    exact bot_le

/-- Internal domination interface for an averaged term. The substantive
integrability is supplied here by the single-tail logarithmic route. -/
theorem integrable_anchor_of_parity_bound (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 1 ≤ M) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hinter : ∀ i j, E.Adj i j → blk i ≠ blk j)
    (hconn : ∀ b b', (nodeGraph (Sym2.map blk) E.edgeFinset).Reachable b b')
    (root : I) {G : (I → ℂ × ℂ) → ℝ} (hG : Measurable G)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hbound : ∀ c, |G c| ≤ Cw *
      (if ∀ b, ((nearGraph M lam c).induce {i | blk i = b}).Connected then 1 else 0) *
      (∏ i, pairDensity χ β lam (c i)) *
      ∑ F ∈ E.edgeFinset.powerset.filter (CutEven (Sym2.map blk)),
        (∏ e ∈ E.edgeFinset \ F, |alphaE hχ β lam M c e|) * ∏ e ∈ F, |gammaE hχ β lam M c e|) :
    Integrable fun c => anchorR root c * G c := by
  obtain ⟨D, hD, hb⟩ := exists_parity_average_le_mixedTreeSum (β := β) hχ (by linarith)
    blk hblk E hinter hconn hCw
  have hpt := hb lam hlam M hM G hbound
  refine ⟨((measurable_anchorR root).mul hG).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  change (∫⁻ c, ‖anchorR root c * G c‖ₑ) < ∞
  simp_rw [enorm_anchorR_mul, Real.enorm_eq_ofReal_abs]
  have hle : (∫⁻ c, anchor root c * ENNReal.ofReal |G c|) ≤
      ENNReal.ofReal D * ∫⁻ c, anchor root c * mixedTreeSum χ β lam M c := by
    calc
      _ ≤ ∫⁻ c, ENNReal.ofReal D *
          (anchor root c * mixedTreeSum χ β lam M c) :=
        lintegral_mono fun c => (mul_le_mul_right (hpt c) (anchor root c)).trans_eq (by ring)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lintegral_mixedTreeSum_lt_top hχ hβ hlam hM hk root))

end MultipoleBKT.Limits.RouteDirect

end
