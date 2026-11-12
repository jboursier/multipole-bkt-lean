/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.TailExpansion
public import MultipoleBKT.Appendix.GeneralExpansion.CutoffTail

/-!
# The singleton extension of the frozen cutoff statement

See Lemma A.7. The paper assumes at least two labels. The stronger frozen
statement also includes a singleton. Its far family is empty,
and its cutoff error is a single planar radial tail.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset Limits Hierarchical Multipole Parity SmallIntegral
open scoped Classical ENNReal

/-- Separate singleton branch, outside the paper's at-least-two range. -/
theorem singleton_cluster_cutoff_bound {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ min eps 1 →
      ∀ (S : Finset ℕ), S.card = 1 → ∀ (B : Type*) [Fintype B] [DecidableEq B],
      Fintype.card B ≤ 1 → ∀ (blk : S → B) (Dn Dz : Finset (Sym2 S)) (N : ℕ),
      |∫ c in boxConfig S N, clusterBox χ β lam M blk Dn Dz ∅ c *
        (cutInd (eps*truncationScale p₀ β lam) c-1)| ≤
        C*N*lam^((2-β)*1)*truncationScale p₀ β lam^(-2 : ℝ) := by
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨A,hA,hb⟩ := GeneralExpansion.lintegral_cutoff_tail_le hχ hβ (k := 1)
    (by omega) (by norm_num; linarith) (zero_le_one.trans hM) p₀
  let W := pairWeightBound hχ hβ0
  have hW : 1 ≤ W := one_le_pairWeightBound hχ hβ0
  let C := W*A*eps^(GeneralExpansion.tailExp p₀ β 1)
  have hC : 0 < C := by dsimp [C]; exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one hW) hA) (Real.rpow_pos_of_pos heps _)
  refine ⟨C,hC,?_⟩
  intro lam hlam hlε S hS B _ _ hB blk Dn Dz N
  have hSc : Fintype.card S = 1 := by simpa only [Fintype.card_coe] using hS
  have : Nonempty S := Fintype.card_pos_iff.1 (by omega)
  have : Subsingleton S := Fintype.card_le_one_iff_subsingleton.1 hSc.le
  let i₀ : S := Classical.arbitrary S
  let h := eps*truncationScale p₀ β lam
  have hlh : lam ≤ h := (hlε.trans (min_le_left _ _)).trans (le_mul_of_one_le_right heps.le
    (Appendix.one_le_truncationScale (p₀ := p₀) hβ hlam (hlε.trans (min_le_right _ _))))
  have hpt (c : S → ℂ × ℂ) :
      |clusterBox χ β lam M blk Dn Dz ∅ c| ≤ W*(∏ i, pairDensity χ β lam (c i)) := by
    have hw := abs_prod_blockW_le (M := M) hχ hβ0 hlam blk c
    have hwp : |∏ b, blockW χ β lam M blk b c| ≤ W := by
      rw [hSc] at hw
      have hp : W^(1*1*Fintype.card B) ≤ W := by
        simpa only [one_mul,pow_one] using pow_le_pow_right₀ hW hB
      exact hw.trans ((by split_ifs <;> first | simpa only [mul_one] using hp | (simp only [mul_zero]; linarith [hW])) : _ ≤ W)
    have hz : |∏ e ∈ Dz, farInd M lam c e| ≤ 1 := abs_prod_farInd_le Dz c
    have hn : |∏ e ∈ Dn, -linkIndE M lam c e| ≤ 1 := (abs_prod_linkIndE_le Dn c).trans (by split_ifs <;> norm_num)
    unfold clusterBox
    simp only [Finset.prod_empty,mul_one,abs_mul,abs_of_nonneg (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le)]
    calc _ ≤ W*1*1*(∏ i, pairDensity χ β lam (c i)) := by
           gcongr
           exact prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le
         _ = _ := by ring
  have hcut (c : S → ℂ × ℂ) : |cutInd h c-1| =
      {u : ℂ | h < ‖u‖}.indicator (1 : ℂ → ℝ) ((c i₀).1-(c i₀).2) := by
    have hc : cutInd h c = if ‖(c i₀).1-(c i₀).2‖ ≤ h then (1 : ℝ) else 0 := by
      unfold cutInd
      simp_rw [show ∀ i : S, c i = c i₀ from fun i => congrArg c (Subsingleton.elim i i₀)]
      rw [prod_const,card_univ,hSc,pow_one]
    rw [hc]
    by_cases ht : ‖(c i₀).1-(c i₀).2‖ ≤ h
    · simp [ht,Set.indicator,not_lt.2 ht]
    · simp [ht,Set.indicator,lt_of_not_ge ht]
  have hconn (c : S → ℂ × ℂ) : GeneralExpansion.connInd M lam c = 1 := by
    unfold GeneralExpansion.connInd
    exact ite_eq_left (SimpleGraph.Connected.of_subsingleton)
  have hi := hb eps lam heps hlam (hlε.trans (min_le_right _ _)) hlh N S hS i₀
  have hmaj : (∫⁻ c in boxConfig S N, ENNReal.ofReal |clusterBox χ β lam M blk Dn Dz ∅ c * (cutInd h c-1)|) ≤
      ENNReal.ofReal W * ENNReal.ofReal (A*eps^(GeneralExpansion.tailExp p₀ β 1)*N*
        (lam^((2-β)*1)*truncationScale p₀ β lam^(-2 : ℝ))) := by
    refine (setLIntegral_mono' (g := fun c : S → ℂ × ℂ => ENNReal.ofReal
      (W*(∏ i, pairDensity χ β lam (c i))*{u : ℂ | h < ‖u‖}.indicator (1 : ℂ → ℝ) ((c i₀).1-(c i₀).2)))
      (measurableSet_boxConfig N) (fun c _ => ?_)).trans ?_
    · rw [abs_mul,hcut]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hpt c) (indicator_nonneg (fun _ _ => zero_le_one) _))
    · rw [← lintegral_indicator (measurableSet_boxConfig N)]
      have he (c : S → ℂ × ℂ) : (boxConfig S N).indicator (fun c => ENNReal.ofReal
          (W*(∏ i, pairDensity χ β lam (c i))*{u : ℂ | h < ‖u‖}.indicator (1 : ℂ → ℝ) ((c i₀).1-(c i₀).2))) c =
          ENNReal.ofReal W * ((boxConfig S N).indicator
            (fun c => GeneralExpansion.connInd M lam c * ∏ i, ENNReal.ofReal (Real.exp (β*smearedKernel χ lam ((c i).1-(c i).2)))) c *
              {u : ℂ | h < ‖u‖}.indicator 1 ((c i₀).1-(c i₀).2)) := by
        by_cases hc : c ∈ boxConfig S N
        · rw [indicator_of_mem hc,indicator_of_mem hc,hconn,one_mul]
          simp only [pairDensity]
          by_cases ht : h < ‖(c i₀).1-(c i₀).2‖
          · simp only [indicator_of_mem (show (c i₀).1-(c i₀).2 ∈ {u : ℂ | h < ‖u‖} from ht),Pi.one_apply,mul_one,ENNReal.ofReal_mul (zero_le_one.trans hW),ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
          · simp only [indicator_of_notMem (show (c i₀).1-(c i₀).2 ∉ {u : ℂ | h < ‖u‖} from ht),mul_zero,ENNReal.ofReal_zero]
        · simp only [indicator_of_notMem hc,zero_mul,mul_zero]
      simp_rw [he]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (by simpa only [boxConfig,Nat.cast_one] using hi)
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal (by positivity) ?_)
  simp only [Real.norm_eq_abs]
  refine hmaj.trans_eq ?_
  rw [← ENNReal.ofReal_mul (zero_le_one.trans hW)]
  congr 1
  dsimp [C]
  ring

end MultipoleBKT.ExpansionK.RouteAssembly

end
