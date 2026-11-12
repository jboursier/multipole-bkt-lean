/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailVector
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailAbsorption

/-!
# Largest-radius sectors for the logarithmic case-F vector integral

See Step 4 of
the proof of Lemma A.7. The maximal-radius label is
summed before polar coordinates. All inner cores remain present.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset Limits SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

private theorem minRho_omit_tail (lam : ℝ) (k : ℕ) (i₀ : Fin (k + 2))
    (v : Fin (k + 2) → ℂ) (hmax : ∀ i, ‖v i‖ ≤ ‖v i₀‖) :
    minRho lam v = minRho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)) := by
  apply le_antisymm
  · exact (le_inf'_iff _ _).mpr fun j _ => minRho_le_rho lam v _
  · apply (le_inf'_iff _ _).mpr
    intro i _
    rcases i₀.eq_self_or_eq_succAbove i with hi | ⟨j, hi⟩
    · rw [hi]
      exact (minRho_le_rho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)) 0).trans
        (max_le_max (hmax _) le_rfl)
    · rw [hi]
      exact minRho_le_rho lam _ j

/-- The literal largest-radius sectors transport the unordered vector tail
to the ordered integral with all `k+1` inner vectors still unrestricted below
the maximal one. Ties only enlarge the finite sum. -/
theorem lintegral_logRadialWeight_tail_le (β : ℝ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) (k q : ℕ) :
    (∫⁻ v in {v : Fin (k + 2) → ℂ | h < maxRho lam v},
      ENNReal.ofReal (logRadialWeight β lam q v)) ≤
      (k + 2) * (ENNReal.ofReal (2 * Real.pi) ^ (k + 2) * orderedTail β lam h k q) := by
  have hS : MeasurableSet {v : Fin (k + 2) → ℂ | h < maxRho lam v} :=
    measurableSet_lt measurable_const (measurable_maxRho lam)
  rw [← lintegral_indicator hS]
  have hpoint (v : Fin (k + 2) → ℂ) :
      {v : Fin (k + 2) → ℂ | h < maxRho lam v}.indicator
        (fun v => ENNReal.ofReal (logRadialWeight β lam q v)) v ≤
          ∑ i₀, orderedVectorTerm (Ioi h) β lam k q i₀ v := by
    by_cases hv : h < maxRho lam v
    · rw [indicator_of_mem (show v ∈ {v : Fin (k + 2) → ℂ | h < maxRho lam v} from hv)]
      obtain ⟨i₀, _, hi₀⟩ := exists_max_image univ (fun i => ‖v i‖) univ_nonempty
      have hmax : ∀ i, ‖v i‖ ≤ ‖v i₀‖ := fun i => hi₀ i (mem_univ _)
      have hR : maxRho lam v = rho lam (v i₀) := by
        apply le_antisymm
        · exact (fold_max_le _).mpr ⟨lam_le_rho lam _, fun i _ => max_le_max (hmax i) le_rfl⟩
        · exact rho_le_maxRho lam v i₀
      have heq : ENNReal.ofReal (logRadialWeight β lam q v) = orderedVectorTerm (Ioi h) β lam k q i₀ v := by
        unfold orderedVectorTerm
        rw [indicator_of_mem (show v ∈ {v : Fin (k + 2) → ℂ | ‖v i₀‖ ∈ Ioi h ∧ ∀ j, ‖v (i₀.succAbove j)‖ ≤ ‖v i₀‖} from
          ⟨by
            rw [hR] at hv
            exact (lt_max_iff.1 hv).resolve_right (not_lt.2 hlh), fun j => hmax _⟩)]
        unfold logRadialWeight
        rw [hR, minRho_omit_tail lam k i₀ v hmax, Fin.prod_univ_succAbove _ i₀]
        have hr := rho_pos hlam (v i₀)
        have hpower : rho lam (v i₀) ^ (-2 : ℝ) * rho lam (v i₀) ^ (2 - β) =
            rho lam (v i₀) ^ (-β) := by
          rw [← Real.rpow_add hr]
          congr 1
          ring
        rw [← mul_assoc (rho lam (v i₀) ^ (-2 : ℝ)) (rho lam (v i₀) ^ (2 - β)), hpower]
        have hpow0 : 0 ≤ rho lam (v i₀) ^ (-β) := Real.rpow_nonneg hr.le _
        have hlog0 : 0 ≤ (1 + Real.log (rho lam (v i₀) /
            minRho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)))) ^ q := by
          apply pow_nonneg
          have hp := minRho_pos hlam (fun j : Fin (k + 1) => v (i₀.succAbove j))
          have hm : minRho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)) ≤ rho lam (v i₀) := (minRho_le_rho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)) 0).trans
            (max_le_max (hmax _) le_rfl)
          have := Real.log_nonneg ((one_le_div hp).mpr hm)
          linarith
        rw [ENNReal.ofReal_mul hlog0, ENNReal.ofReal_mul hpow0,
          ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg (rho_pos hlam _).le _)]
        ring
      rw [heq]
      exact single_le_sum (f := fun i => orderedVectorTerm (Ioi h) β lam k q i v)
        (fun _ _ => bot_le) (mem_univ i₀)
    · rw [indicator_of_notMem (show v ∉ {v : Fin (k + 2) → ℂ | h < maxRho lam v} from hv)]
      exact bot_le
  have hm (i₀ : Fin (k + 2)) : Measurable (orderedVectorTerm (Ioi h) β lam k q i₀) := by
    unfold orderedVectorTerm
    apply Measurable.indicator
    · have hm : Measurable (fun v : Fin (k + 2) → ℂ =>
        minRho lam (fun j : Fin (k + 1) => v (i₀.succAbove j))) :=
        (measurable_minRho lam).comp (by fun_prop)
      unfold rho
      fun_prop
    · change MeasurableSet ({v : Fin (k + 2) → ℂ | ‖v i₀‖ ∈ Ioi h} ∩
        {v | ∀ j, ‖v (i₀.succAbove j)‖ ≤ ‖v i₀‖})
      apply MeasurableSet.inter
      · exact measurableSet_Ioi.preimage (by fun_prop)
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun j => measurableSet_le
          (show Measurable (fun v : Fin (k + 2) → ℂ => ‖v (i₀.succAbove j)‖) by fun_prop)
          (by fun_prop)

  calc
    _ ≤ ∫⁻ v, ∑ i₀, orderedVectorTerm (Ioi h) β lam k q i₀ v := lintegral_mono hpoint
    _ = ∑ i₀, ∫⁻ v, orderedVectorTerm (Ioi h) β lam k q i₀ v :=
      lintegral_finsetSum _ fun i₀ _ => hm i₀
    _ = (k + 2) * ∫⁻ v in {v : ℂ | h < ‖v‖},
        ENNReal.ofReal (rho lam v ^ (-β)) * innerVector β lam k q ‖v‖ := by
      simp_rw [lintegral_orderedVectorTerm (Ioi h) measurableSet_Ioi β lam k q]
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
      rfl
    _ = _ := by rw [orderedVectorTail_eq β hlam hlh]

/-- The finite largest-label count and the exact angular factor. -/
noncomputable def tailSectorCoefficient (k : ℕ) : ℝ :=
  ((k + 2 : ℕ) : ℝ) * (2 * Real.pi) ^ (k + 2)

private theorem tailSectorCoefficient_pos (k : ℕ) : 0 < tailSectorCoefficient k := by
  unfold tailSectorCoefficient
  positivity

/-- The unordered logarithmic vector tail before applying a temperature regime. -/
theorem vector_tail_le_ordered (β : ℝ) {lam h : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) (k q : ℕ) :
    (∫⁻ v in {v : Fin (k + 2) → ℂ | h < maxRho lam v},
      ENNReal.ofReal (logRadialWeight β lam q v)) ≤
      ENNReal.ofReal (tailSectorCoefficient k) * orderedTail β lam h k q := by
  refine (lintegral_logRadialWeight_tail_le β hlam hlh k q).trans_eq ?_
  unfold tailSectorCoefficient
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast, mul_assoc]
  simp only [Nat.cast_add,Nat.cast_ofNat]

/-- The actual unordered vector-tail display below four. -/
theorem caseF_vector_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4) (k q : ℕ)
    (hsize : (4 - β) * (k + 2) < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      (∫⁻ v in {v : Fin (k + 2) → ℂ | h < maxRho lam v},
        ENNReal.ofReal (logRadialWeight β lam q v)) ≤
        ENNReal.ofReal (C * h ^ ((4 - β) * (k + 2) - 2)) := by
  obtain ⟨A,hA,hb⟩ := orderedTail_lt_four hβ hβ4 k q hsize
  refine ⟨tailSectorCoefficient k * A,mul_pos (tailSectorCoefficient_pos k) hA,?_⟩
  intro lam h hlam hlh
  refine (vector_tail_le_ordered β hlam hlh k q).trans ?_
  exact (mul_le_mul' le_rfl (hb lam h hlam hlh)).trans_eq
    (by rw [← ENNReal.ofReal_mul (tailSectorCoefficient_pos k).le]; congr 1; ring)

/-- The actual unordered vector-tail display at four, retaining the printed
logarithmic power `2(k+2)` before final absorption. -/
theorem caseF_vector_four (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      (∫⁻ v in {v : Fin (k + 2) → ℂ | h < maxRho lam v},
        ENNReal.ofReal (logRadialWeight 4 lam (k + 2) v)) ≤
        ENNReal.ofReal (C * h ^ (-2 : ℝ) * (1 + Real.log (h / lam)) ^ (2 * (k + 2))) := by
  obtain ⟨A,hA,hb⟩ := caseF_four k
  refine ⟨tailSectorCoefficient k * A,mul_pos (tailSectorCoefficient_pos k) hA,?_⟩
  intro lam h hlam hlh
  refine (vector_tail_le_ordered 4 hlam hlh k (k + 2)).trans ?_
  exact (mul_le_mul' le_rfl (hb lam h hlam hlh)).trans_eq
    (by rw [← ENNReal.ofReal_mul (tailSectorCoefficient_pos k).le]; congr 1; ring)

/-- The actual unordered vector-tail display above four. -/
theorem caseF_vector_gt_four {β : ℝ} (hβ : 4 < β) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      (∫⁻ v in {v : Fin (k + 2) → ℂ | h < maxRho lam v},
        ENNReal.ofReal (logRadialWeight β lam (k + 2) v)) ≤
        ENNReal.ofReal (C * h ^ (2 - β) * lam ^ ((4 - β) * (k + 1)) *
          (1 + Real.log (h / lam)) ^ (k + 2)) := by
  obtain ⟨A,hA,hb⟩ := orderedTail_gt_four hβ k (k + 2)
  refine ⟨tailSectorCoefficient k * A,mul_pos (tailSectorCoefficient_pos k) hA,?_⟩
  intro lam h hlam hlh
  refine (vector_tail_le_ordered β hlam hlh k (k + 2)).trans ?_
  exact (mul_le_mul' le_rfl (hb lam h hlam hlh)).trans_eq
    (by rw [← ENNReal.ofReal_mul (tailSectorCoefficient_pos k).le]; congr 1; ring)

/-- The unordered vector-tail integral after the three displayed regimes.
The cutoff-dependent coefficient is chosen before lambda. -/
theorem caseF_vector_bound {β : ℝ} (hβ : 2 < β) (p₀ k : ℕ)
    (hkp : ((k + 2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ eps →
      (∫⁻ v in {v : Fin (k + 2) → ℂ | eps * truncationScale p₀ β lam < maxRho lam v},
        ENNReal.ofReal (logRadialWeight β lam (k + 2) v)) ≤
        ENNReal.ofReal (C * lam ^ ((2 - β) * (k + 2)) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  intro eps heps heps1
  obtain ⟨A,hA,hb⟩ := caseF_bound hβ p₀ k hkp eps heps heps1
  refine ⟨tailSectorCoefficient k * A,mul_pos (tailSectorCoefficient_pos k) hA,?_⟩
  intro lam hlam hle
  have hlh : lam ≤ eps * truncationScale p₀ β lam := hle.trans
    (le_mul_of_one_le_right heps.le (Appendix.one_le_truncationScale hβ hlam (hle.trans heps1)))
  refine (vector_tail_le_ordered β hlam hlh k (k + 2)).trans ?_
  exact (mul_le_mul' le_rfl (hb lam hlam hle)).trans_eq
    (by rw [← ENNReal.ofReal_mul (tailSectorCoefficient_pos k).le]; congr 1; ring)

end MultipoleBKT.ExpansionK.RouteSpatial

end
