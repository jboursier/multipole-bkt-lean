/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Radial

/-!
# The omitted radial bound for every positive epsilon

See (A.42) and Lemma A.7. For epsilon above one the same radial moments retain an
additional epsilon power or logarithmic polynomial in the coefficient.
Lambda stays at most one, as at the screened model of Lemma A.7.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory GeneralExpansion SmallIntegral.RouteJext
open scoped ENNReal

/-- The large-epsilon scalar moments, with epsilon fixed before the coefficient.
The three temperature regimes are integrated before logarithmic absorption. -/
theorem internal_moment_product_large {β eps : ℝ} (hβ : 2 < β) (heps : 1 ≤ eps)
    (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      RouteLog.radialLogMoment (4-β) lam (eps*truncationScale p₀ β lam) q *
        RouteLog.radialLogMoment (4-β) lam (eps*truncationScale p₀ β lam) 0 ^ (k-1) ≤
      C * lam ^ ((2-β)*k) := by
  have heps0 : 0 < eps := zero_lt_one.trans_le heps
  by_cases hβ4 : β < 4
  · obtain ⟨A,hA,hb⟩ := moment_product_lt_four hβ hβ4 hk q
    refine ⟨A*eps^((4-β)*k),by positivity,?_⟩
    intro lam hlam hlam1
    have hlh : lam ≤ eps*truncationScale p₀ β lam := hlam1.trans
      (one_le_mul_of_one_le_of_one_le heps (Appendix.one_le_truncationScale hβ hlam hlam1))
    have hs := hb lam _ hlam hlh
    rw [Real.mul_rpow heps0.le (Appendix.truncationScale_pos hlam).le,
      Appendix.rpow_truncationScale_mul_of_lt hlam hβ4] at hs
    exact hs.trans_eq (by ring)
  · have hge : 4 ≤ β := le_of_not_gt hβ4
    have hreg : ∃ A : ℝ, 0 < A ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
        RouteLog.radialLogMoment (4-β) lam h q *
          RouteLog.radialLogMoment (4-β) lam h 0 ^ (k-1) ≤
        A*lam^((4-β)*k)*(1+Real.log (h/lam))^(k+q) := by
      by_cases heq : β = 4
      · subst β
        obtain ⟨A,hA,hb⟩ := moment_product_four hk q
        refine ⟨A,hA,fun lam h hlam hlh => ?_⟩
        simpa only [sub_self,zero_mul,Real.rpow_zero,mul_one] using hb lam h hlam hlh
      · obtain ⟨A,hA,hb⟩ := moment_product_gt_four (lt_of_le_of_ne hge (Ne.symm heq)) hk q
        refine ⟨A,hA,fun lam h hlam hlh => (hb lam h hlam hlh).trans ?_⟩
        have hL : 1 ≤ 1+Real.log (h/lam) := by
          have := Real.log_nonneg ((one_le_div hlam).2 hlh)
          linarith
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (Nat.le_add_left q k)) (by positivity)
    obtain ⟨A,hA,hb⟩ := hreg
    obtain ⟨B,hB,hlog⟩ := power_log_uniform
      (show (0:ℝ) < 2*k by exact mul_pos (by norm_num) (by exact_mod_cast hk))
      (show (0:ℝ) ≤ 2*p₀+1 by positivity) (k+q)
    have heL : 0 ≤ Real.log eps := Real.log_nonneg heps
    refine ⟨A*B*(1+Real.log eps)^(k+q),by positivity,?_⟩
    intro lam hlam hlam1
    have hR := Appendix.one_le_truncationScale (p₀ := p₀) hβ hlam hlam1
    have hlh : lam ≤ eps*truncationScale p₀ β lam := hlam1.trans
      (one_le_mul_of_one_le_of_one_le heps hR)
    have hL : 0 ≤ 1+Real.log (eps*truncationScale p₀ β lam/lam) := by
      have := Real.log_nonneg ((one_le_div hlam).2 hlh)
      linarith
    have hcut := RouteLog.log_cutoff_le (p₀ := p₀) hge hlam hlam1 one_pos le_rfl
    rw [one_mul] at hcut
    have hsplit : Real.log (eps*truncationScale p₀ β lam/lam) =
        Real.log eps + Real.log (truncationScale p₀ β lam/lam) := by
      rw [mul_div_assoc,Real.log_mul heps0.ne' (div_pos (Appendix.truncationScale_pos hlam) hlam).ne']
    have hpoly : 1+Real.log (eps*truncationScale p₀ β lam/lam) ≤
        (1+Real.log eps)*(1+(2*(p₀:ℝ)+1)*|Real.log lam|) := by
      rw [hsplit]
      nlinarith [mul_nonneg heL (show 0 ≤ (2*(p₀:ℝ)+1)*|Real.log lam| by positivity)]
    have hp := pow_le_pow_left₀ hL hpoly (k+q)
    rw [mul_pow] at hp
    have habs := (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hlam.le (2*k))).trans
      (show lam^(2*(k:ℝ))*((1+Real.log eps)^(k+q)*(1+(2*(p₀:ℝ)+1)*|Real.log lam|)^(k+q)) ≤
        (1+Real.log eps)^(k+q)*B by
          nlinarith [mul_le_mul_of_nonneg_left (hlog lam hlam hlam1)
            (pow_nonneg (by linarith : 0 ≤ 1+Real.log eps) (k+q))])
    have he : lam^((4-β)*k) = lam^((2-β)*k)*lam^(2*(k:ℝ)) := by
      rw [← Real.rpow_add hlam]
      congr 1
      ring
    calc
      _ ≤ A*lam^((4-β)*k)*(1+Real.log (eps*truncationScale p₀ β lam/lam))^(k+q) := hb lam _ hlam hlh
      _ = A*lam^((2-β)*k)*(lam^(2*(k:ℝ))*(1+Real.log (eps*truncationScale p₀ β lam/lam))^(k+q)) := by rw [he]; ring
      _ ≤ A*lam^((2-β)*k)*((1+Real.log eps)^(k+q)*B) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
      _ = _ := by ring

/-- The original cutoff vector integral for any fixed positive epsilon.
Its coefficient is uniform over label carriers of cardinality `k`. -/
theorem vectorWeight_bound_at {χ : ℂ → ℝ} {β eps : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (heps : 0 < eps) (p₀ : ℕ)
    {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I],
      Fintype.card I = k → ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      (∫⁻ u : I → ℂ, vectorWeight χ β lam (eps*truncationScale p₀ β lam) q u) ≤
        ENNReal.ofReal (C*lam^((2-β)*k)) := by
  by_cases heps1 : eps ≤ 1
  · obtain ⟨C,hC,hb⟩ := vectorWeight_gain hχ hβ p₀ hk q
    refine ⟨C,hC,fun I _ _ _ hI lam hlam hle _ => ?_⟩
    refine (hb I hI eps lam hlam hle heps1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hα : 0 ≤ alphaExponent β*k := by
      have : 0 ≤ alphaExponent β := by unfold alphaExponent; split_ifs <;> linarith
      positivity
    have hp := Real.rpow_le_one heps.le heps1 hα
    calc
      _ ≤ C*1*lam^((2-β)*k) := by gcongr
      _ = _ := by ring
  · obtain ⟨C,hC,hb⟩ := internal_moment_product_large hβ (le_of_not_ge heps1) p₀ hk q
    let D := (k:ℝ)*(1+Real.log 17)^q*(2*Real.pi*Real.exp (β*MultipoleIntegral.kernelConst χ))^k
    have hD : 0 < D := by
      have hk0 : (0:ℝ) < k := by exact_mod_cast hk
      have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 17)
      dsimp only [D]
      positivity
    refine ⟨D*C,mul_pos hD hC,fun I _ _ _ hI lam hlam hle hlam1 => ?_⟩
    have hlh : lam ≤ eps*truncationScale p₀ β lam := hle.trans
      (le_mul_of_one_le_right heps.le (Appendix.one_le_truncationScale hβ hlam hlam1))
    have hv := lintegral_vectorWeight_le (I := I) (β := β) hχ (by linarith) hlam hlh q
    rw [hI] at hv
    exact hv.trans (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_left (hb lam hlam hlam1) hD.le).trans_eq (by ring)))

end MultipoleBKT.ExpansionK.RouteOmitted

end
