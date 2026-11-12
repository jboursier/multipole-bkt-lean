/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.RelativeIntegrands

/-!
# Uniform absolute bounds for the specified limiting integrands

See Lemma 4.26 of the paper. The original reversal averages are retained after merging.
The constants precede λ, and the resulting power is `λ^((4-β)k-2)`.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph SmallIntegral
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [LinearOrder I] [Nonempty I]
  [Fintype B] [DecidableEq B]
variable {χ : ℂ → ℝ} {β M : ℝ}

/-- Uniform integration of a fixed merged near/far term. -/
theorem exists_lintegral_blockAverage_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) (hI : 2 ≤ Fintype.card I) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hconn : (E ⊔ sameBlockGraph blk).Connected)
    {F : Finset (Sym2 I)} (hF : F ⊆ E.edgeFinset) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ c, anchor root c * ENNReal.ofReal |blockAverage χ β lam M blk E F c|) ≤
        ENNReal.ofReal (A * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  obtain ⟨Cw, hCw, hw⟩ := exists_abs_blockTermWeight_le_uniform (β := β) hχ (by linarith) blk E
  obtain ⟨D, hD, hd⟩ := exists_parity_average_le_mixedTreeSum (β := β) hχ (by linarith)
    (mergedOf blk E F) (fun C => C.exists_rep) (mergedInter blk E F) (fun _ _ h => h.2)
    (mergedInter_reachable blk E F hconn) hCw
  obtain ⟨Ct, hCt, ht⟩ := exists_lintegral_mixedTreeSum_factorized_le (I := I) hχ hβ hM hI hk
  refine ⟨D * Ct, mul_nonneg hD hCt.le, fun lam hlam root => ?_⟩
  have hpt := hd lam hlam M hM (blockAverage χ β lam M blk E F) (fun c =>
    (abs_blockAverage_le hχ hM blk hblk E hF c).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hw lam hlam M F hF c)
          (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le))
        (sum_nonneg fun _ _ => mul_nonneg (prod_nonneg fun _ _ => abs_nonneg _)
          (prod_nonneg fun _ _ => abs_nonneg _))))
  calc
    _ ≤ ∫⁻ c, ENNReal.ofReal D * (anchor root c * mixedTreeSum χ β lam M c) :=
      lintegral_mono fun c => (mul_le_mul_right (hpt c) (anchor root c)).trans_eq (by ring)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (Ct * lam ^ ((4 - β) * Fintype.card I - 2)) :=
      mul_le_mul_right (ht lam hlam root) _
    _ = _ := by rw [← ENNReal.ofReal_mul hD]; congr 1; ring

/-- The absolute integral of the full original block average has the displayed
uniform power. Merger averages occur only inside the finite near/far sum. -/
theorem exists_lintegral_symBox_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) (hI : 2 ≤ Fintype.card I) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hconn : (E ⊔ sameBlockGraph blk).Connected) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ c, anchor root c * ENNReal.ofReal |symBox χ β lam M blk E c|) ≤
        ENNReal.ofReal (A * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  have hall : ∀ F ∈ E.edgeFinset.powerset, ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ c, anchor root c * ENNReal.ofReal |blockAverage χ β lam M blk E F c|) ≤
        ENNReal.ofReal (A * lam ^ ((4 - β) * Fintype.card I - 2)) :=
    fun F hF => exists_lintegral_blockAverage_le hχ hβ hM hI hk blk hblk E hconn (mem_powerset.mp hF)
  choose! A hA ha using hall
  refine ⟨∑ F ∈ E.edgeFinset.powerset, A F, sum_nonneg (fun F hF => hA F hF), fun lam hlam root => ?_⟩
  simp_rw [symBox_eq_sum_blockAverage hχ hM blk hblk E]
  calc
    _ ≤ ∑ F ∈ E.edgeFinset.powerset, ∫⁻ c, anchor root c *
        ENNReal.ofReal |reversalAverage blk (blockAverage χ β lam M blk E F) c| :=
      lintegral_anchor_abs_sum_le _ root _ (fun F _ =>
        measurable_reversalAverage blk (measurable_blockAverage hχ hlam blk E F))
    _ ≤ ∑ F ∈ E.edgeFinset.powerset, ∫⁻ c, anchor root c *
        ENNReal.ofReal |blockAverage χ β lam M blk E F c| := by
      apply sum_le_sum
      intro F _
      exact lintegral_anchor_abs_reversalAverage_le blk root
        (measurable_blockAverage hχ hlam blk E F) (blockAverage_translate blk E F)
    _ ≤ ∑ F ∈ E.edgeFinset.powerset, ENNReal.ofReal (A F * lam ^ ((4 - β) * Fintype.card I - 2)) :=
      sum_le_sum fun F hF => ha F hF lam hlam root
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun F hF => mul_nonneg (hA F hF) (by positivity)), sum_mul]

/-- Each merged singleton term uses the small-power radial factorization
of Lemma 4.26. -/
private theorem exists_lintegral_dipSym_factorized_le (hχ : IsMollifier χ) (hβ : 2 < β)
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
  obtain ⟨Ct, hCt, ht⟩ := exists_lintegral_mixedTreeSum_factorized_le (I := I) (M := 30) hχ hβ
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

/-- The full singleton average satisfies the same absolute integral bound. -/
theorem exists_lintegral_singletonBox_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hI : 2 ≤ Fintype.card I) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (E : SimpleGraph I) (hE : E.Connected) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ c, anchor root c * ENNReal.ofReal |singletonBox χ β lam E c|) ≤
        ENNReal.ofReal (A * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  have hall := fun F hF => exists_lintegral_dipSym_factorized_le hχ hβ hI hk E hE (E' := F) hF
  choose! A hA ha using hall
  refine ⟨∑ F ∈ E.edgeFinset.powerset, A F, sum_nonneg (fun F hF => hA F hF), fun lam hlam root => ?_⟩
  simp_rw [singletonBox_eq_sum (M := 30)]
  calc
    _ ≤ ∑ F ∈ E.edgeFinset.powerset, ∫⁻ c, anchor root c *
        ENNReal.ofReal |reversalAverage id (dipSym χ β lam 30 E F) c| :=
      lintegral_anchor_abs_sum_le _ root _ (fun F _ =>
        measurable_reversalAverage id (measurable_dipSym hχ hlam β 30 E F))
    _ ≤ ∑ F ∈ E.edgeFinset.powerset, ∫⁻ c, anchor root c * ENNReal.ofReal |dipSym χ β lam 30 E F c| := by
      apply sum_le_sum
      intro F _
      exact lintegral_anchor_abs_reversalAverage_le id root (measurable_dipSym hχ hlam β 30 E F)
        (dipSym_translate E F)
    _ ≤ ∑ F ∈ E.edgeFinset.powerset, ENNReal.ofReal (A F * lam ^ ((4 - β) * Fintype.card I - 2)) :=
      sum_le_sum fun F hF => ha F hF lam hlam root
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun F hF => mul_nonneg (hA F hF) (by positivity)), sum_mul]

/-- The displayed `∫ |G'|` estimate on its literal fixed-origin carrier. -/
theorem exists_lintegral_Gprime_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hI : 2 ≤ Fintype.card I) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (E : SimpleGraph I) (hE : E.Connected) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ p : RelativeCoordinates root, ENNReal.ofReal |Gprime χ β lam E root p|) ≤
        ENNReal.ofReal (A * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  obtain ⟨A, hA, ha⟩ := exists_lintegral_singletonBox_le hχ hβ hI hk E hE
  refine ⟨A, hA, fun lam hlam root => ?_⟩
  have hm : Measurable (fun c => ENNReal.ofReal |singletonBox χ β lam E c|) := by
    simpa only [Real.norm_eq_abs] using (measurable_singletonBox hχ hlam E).norm.ennreal_ofReal
  dsimp only [Gprime, GdoublePrime]
  rw [← lintegral_anchor_eq_relative root hm
    (fun a c => by rw [singletonBox_translate])]
  exact ha lam hlam root

/-- The displayed `∫ |G''|` estimate on its literal fixed-origin carrier. -/
theorem exists_lintegral_GdoublePrime_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) (hI : 2 ≤ Fintype.card I) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hconn : (E ⊔ sameBlockGraph blk).Connected) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ p : RelativeCoordinates root, ENNReal.ofReal |GdoublePrime χ β lam M blk E root p|) ≤
        ENNReal.ofReal (A * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  obtain ⟨A, hA, ha⟩ := exists_lintegral_symBox_le hχ hβ hM hI hk blk hblk E hconn
  refine ⟨A, hA, fun lam hlam root => ?_⟩
  have hm : Measurable (fun c => ENNReal.ofReal |symBox χ β lam M blk E c|) := by
    simpa only [Real.norm_eq_abs] using (measurable_symBox hχ hlam blk E).norm.ennreal_ofReal
  dsimp only [Gprime, GdoublePrime]
  rw [← lintegral_anchor_eq_relative root hm
    (fun a c => by rw [symBox_translate])]
  exact ha lam hlam root

end MultipoleBKT.Limits.RouteDirect

end
