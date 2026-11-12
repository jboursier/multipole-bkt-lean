/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.JointConfiguration

/-!
# The logarithmic case-F displays for the configuration tree integral

See Step 4 of
the proof of Lemma A.7. The actual configuration tree
integral is reduced to the unordered vector tail before its three regimes
and final cutoff absorption.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

/-- The configuration integral with its full joint odd tail is bounded by the
unordered logarithmic radial integral, with all regularized cores present. -/
theorem jointTree_tail_le_radial_any {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k+2 →
      ∀ lam h : ℝ, 0 < lam →
      ∀ (T : SimpleGraph W), T.IsTree →
      ∀ (A E N : Finset (Sym2 W)), A ∪ (E ∪ N) = T.edgeFinset →
      Disjoint A (E ∪ N) → Disjoint E N → ∀ n : ℕ,
      (∫⁻ c in boxConfig W n ∩ {c : W → ℂ × ℂ | h < maxRad lam c},
        jointTreeDensity χ β M lam A E N c) ≤
          ENNReal.ofReal (C * n) * ∫⁻ u in {u : W → ℂ | h < maxRho lam u},
            ENNReal.ofReal (logRadialWeight β lam (k+2) u) := by
  obtain ⟨C,hC,hb⟩ := jointTree_tail_le_vectors hM (k+1)
  obtain ⟨Cg,hCg,hg⟩ := exists_logDensityWeight_le hχ hβ
  refine ⟨C * Cg^(k+2),by positivity,?_⟩
  intro W _ _ _ hW lam h hlam T hT A E N hpart hA hEN n
  have hv := hb W (by omega) T hT A E N hpart hA hEN hχ β lam h hlam n
  have hp (u : W → ℂ) : ENNReal.ofReal (logDensityWeight χ β lam (k+1) u) ≤
      ENNReal.ofReal (Cg^(k+2)) * ENNReal.ofReal (logRadialWeight β lam (k+2) u) := by
    have hg' := hg W lam hlam (k+1) u
    rw [hW] at hg'
    refine (ENNReal.ofReal_le_ofReal hg').trans ?_
    rw [← ENNReal.ofReal_mul (pow_nonneg hCg.le _)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hCg.le _)
    unfold logRadialWeight
    apply mul_le_mul_of_nonneg_right
    · apply pow_le_pow_right₀
      · have hh := Real.log_nonneg ((one_le_div (SmallIntegral.minRho_pos hlam u)).2
          ((SmallIntegral.minRho_le_rho lam u (Classical.arbitrary W)).trans (SmallIntegral.rho_le_maxRho lam u (Classical.arbitrary W))))
        exact le_add_of_nonneg_right hh
      · omega
    · exact mul_nonneg (Real.rpow_nonneg (SmallIntegral.maxRho_pos hlam u).le _)
        (prod_nonneg fun _ _ => Real.rpow_nonneg (rho_pos hlam _).le _)

  refine hv.trans ?_
  calc
    _ ≤ ENNReal.ofReal (C*n) * ∫⁻ u in {u : W → ℂ | h < SmallIntegral.maxRho lam u},
        ENNReal.ofReal (Cg^(k+2)) * ENNReal.ofReal (logRadialWeight β lam (k+2) u) :=
      mul_le_mul' le_rfl (lintegral_mono hp)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,
        ← ENNReal.ofReal_mul (mul_nonneg hC.le (Nat.cast_nonneg _))]
      congr 1
      congr 1
      ring

/-- The configuration integral with its full joint odd tail is bounded by the
unordered logarithmic radial integral, with all regularized cores present. -/
theorem jointTree_tail_le_radial {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam →
      ∀ (T : SimpleGraph (Fin (k+2))), T.IsTree →
      ∀ (A E N : Finset (Sym2 (Fin (k+2)))), A ∪ (E ∪ N) = T.edgeFinset →
      Disjoint A (E ∪ N) → Disjoint E N → ∀ n : ℕ,
      (∫⁻ c in boxConfig (Fin (k+2)) n ∩ {c : Fin (k+2) → ℂ × ℂ | h < maxRad lam c},
        jointTreeDensity χ β M lam A E N c) ≤
          ENNReal.ofReal (C * n) * ∫⁻ u in {u : Fin (k+2) → ℂ | h < maxRho lam u},
            ENNReal.ofReal (logRadialWeight β lam (k+2) u) := by
  obtain ⟨C,hC,hb⟩ := jointTree_tail_le_radial_any hχ hβ hM k
  exact ⟨C,hC,hb (Fin (k+2)) (by simp)⟩

end MultipoleBKT.ExpansionK.RouteSpatial

end
