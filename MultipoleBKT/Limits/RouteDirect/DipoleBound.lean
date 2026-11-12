/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.DipoleTerms
public import MultipoleBKT.Limits.RouteDirect.BoxBound

/-!
# The direct logarithmic proof of the dipole integral bound

See Lemma A.5 of the paper. Take `M=30`, split near and far bonds, average the merged
parts, retain the separate odd and even trees, and integrate the logarithms.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral

open MeasureTheory Finset Set SimpleGraph
open Limits Limits.RouteDirect
open scoped Classical ENNReal

variable {I : Type*} [Fintype I] [LinearOrder I] [Nonempty I]
variable {χ : ℂ → ℝ} {β : ℝ}

/-- Each merged dipole term has the uniform rooted bound supplied by the
ordered logarithmic radial integral. -/
theorem exists_lintegral_dipSym_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hI : 2 ≤ Fintype.card I) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (E : SimpleGraph I) (hE : E.Connected) {E' : Finset (Sym2 I)}
    (hE' : E' ∈ E.edgeFinset.powerset) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ c, anchor root c * ENNReal.ofReal |dipSym χ β lam 30 E E' c|) ≤
        ENNReal.ofReal (A * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  obtain ⟨Cw, hCw, hw⟩ := exists_abs_dipWeight_le_uniform hχ (by linarith : 0 ≤ β) E
  have hsub := mem_powerset.mp hE'
  obtain ⟨D, hD, hd⟩ := exists_parity_average_le_mixedTreeSum (β := β) hχ (by linarith)
    (blkOf E E') (blkOf_surjective E E') (interPart E E')
    (fun _ _ h => h.2) (reachable_interPart hE E') hCw
  obtain ⟨Ct, hCt, ht⟩ := exists_lintegral_mixedTreeSum_le (I := I) (M := 30) hχ hβ
    (by norm_num) hI hk
  refine ⟨D * Ct, mul_nonneg hD hCt.le, fun lam hlam root => ?_⟩
  have hpt := hd lam hlam 30 (by norm_num) (dipSym χ β lam 30 E E') (fun c =>
    (abs_dipSym_le hχ (by norm_num : (1 : ℝ) ≤ 30) E hsub c).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hw lam hlam 30 E' hsub c)
          (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le))
        (sum_nonneg fun _ _ => mul_nonneg (prod_nonneg fun _ _ => abs_nonneg _)
          (prod_nonneg fun _ _ => abs_nonneg _))))
  calc
    _ ≤ ∫⁻ c, ENNReal.ofReal D * (anchor root c * mixedTreeSum χ β lam 30 c) :=
      lintegral_mono fun c => (mul_le_mul_right (hpt c) (anchor root c)).trans_eq (by ring)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (Ct * lam ^ ((4 - β) * Fintype.card I - 2)) :=
      mul_le_mul_right (ht lam hlam root) _
    _ = _ := by rw [← ENNReal.ofReal_mul hD]; congr 1; ring

/-- The dipole integral estimate of the paper for every nontrivial carrier, obtained
from the logarithmic radial integral rather than dilation of configurations. -/
theorem exists_abs_integral_dipBox_log_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hI : 2 ≤ Fintype.card I) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (E : SimpleGraph I) (hE : E.Connected) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ N : ℕ,
      |∫ c in boxConfig I N, dipBox χ β lam E c| ≤
        A * (N * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  let root : I := Classical.arbitrary I
  have hterm : ∀ E' ∈ E.edgeFinset.powerset, ∃ A : ℝ, 0 ≤ A ∧
      ∀ lam : ℝ, 0 < lam → ∀ N : ℕ,
      |∫ c in boxConfig I N, dipSym χ β lam 30 E E' c| ≤
        A * (N * lam ^ ((4 - β) * Fintype.card I - 2)) := by
    intro E' hE'
    obtain ⟨A, hA, ha⟩ := exists_lintegral_dipSym_le hχ hβ hI hk E hE hE'
    refine ⟨A, hA, fun lam hlam N => ?_⟩
    have hint := integrable_anchor_dipSym hχ hβ hlam (by norm_num : (1 : ℝ) ≤ 30) hk E hE hE' root
    calc
      _ ≤ ∫ c in boxConfig I N, |dipSym χ β lam 30 E E' c| := abs_integral_le_integral_abs
      _ ≤ (N : ℝ) * ∫ c, |anchorR root c * dipSym χ β lam 30 E E' c| :=
        integral_boxConfig_abs_le_anchor root (measurable_dipSym hχ hlam β 30 E E')
          (dipSym_translate E E') hint N
      _ ≤ (N : ℝ) * (A * lam ^ ((4 - β) * Fintype.card I - 2)) := by
        gcongr
        exact integral_anchor_abs_le root hint (by positivity) (ha lam hlam root)
      _ = _ := by ring
  choose! A hA0 hA using hterm
  refine ⟨∑ E' ∈ E.edgeFinset.powerset, A E', sum_nonneg (fun E' hE' => hA0 E' hE'),
    fun lam hlam N => ?_⟩
  obtain ⟨B, hB⟩ := exists_abs_dipTerm_le (M := 30) hχ (by linarith : 0 ≤ β) hlam E
  have hsum : (∫ c in boxConfig I N, dipBox χ β lam E c) =
      ∑ E' ∈ E.edgeFinset.powerset, ∫ c in boxConfig I N, dipSym χ β lam 30 E E' c := by
    simp_rw [dipBox_eq_sum (M := 30)]
    rw [integral_finsetSum _ (fun E' hE' => integrableOn_boxConfig_of_bounded
      (measurable_dipTerm hχ hlam β 30 E E') (hB E' hE') N)]
    apply sum_congr rfl
    intro E' hE'
    unfold dipSym
    exact (integral_boxConfig_avg_flip (blkOf E E') (measurable_dipTerm hχ hlam β 30 E E')
      (hB E' hE') N).symm
  rw [hsum, sum_mul]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun E' hE' => hA E' hE' lam hlam N)

end MultipoleBKT.SmallIntegral

end
