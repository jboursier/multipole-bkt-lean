/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.Pointwise
public import MultipoleBKT.Limits.RouteDirect.LogAbsorption
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Density
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Measurability

/-!
# Integrating the retained majorants of the limiting integrals

See Lemma 4.26 of the paper. Integrate the mixed spatial tree first. The radii and
single-dipole densities are then bounded by the written logarithmic majorant.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph
open SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- One retained tree majorant, including its original single-dipole densities. -/
noncomputable def limitingTreeTerm (χ : ℂ → ℝ) (β lam M : ℝ)
    (NT A B : Finset (Sym2 I)) (c : I → ℂ × ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ i, pairDensity χ β lam (c i)) * radialFactor lam c) *
    treeProfile M lam A B NT c

/-- Measurability of the complete retained majorant. -/
theorem measurable_limitingTreeTerm {χ : ℂ → ℝ} {β lam M : ℝ}
    (hχ : IsMollifier χ) (hlam : 0 < lam) (NT A B : Finset (Sym2 I)) :
    Measurable (limitingTreeTerm χ β lam M NT A B) := by
  have hedge (e : Sym2 I) (ev : Bool) : Measurable fun c : I → ℂ × ℂ => edgeProfile ev M lam c e := by
    induction e using Sym2.ind with
    | h i j =>
      change Measurable fun c : I → ℂ × ℂ => spatialProfile ev M
        (min (rhoD lam (c i)) (rhoD lam (c j)))
        (max (rhoD lam (c i)) (rhoD lam (c j))) (dipoleDist (c i) (c j)) /
          min (rhoD lam (c i)) (rhoD lam (c j)) ^ 2
      have hd : Measurable fun c : I → ℂ × ℂ => dipoleDist (c i) (c j) :=
        measurable_dipoleDist.comp
          (show Measurable (fun c : I → ℂ × ℂ => (c i, c j)) by fun_prop)
      have hi : Measurable (fun c : I → ℂ × ℂ => rhoD lam (c i)) :=
        (measurable_rhoD lam).comp (measurable_pi_apply i)
      have hj : Measurable (fun c : I → ℂ × ℂ => rhoD lam (c j)) :=
        (measurable_rhoD lam).comp (measurable_pi_apply j)
      unfold spatialProfile MultipoleBKT.RouteLog.evenEdgeProfile
      split_ifs <;> first
        | fun_prop
        | exact (Measurable.ite (measurableSet_le hd ((hi.min hj).const_mul M))
            measurable_const (by fun_prop)).div (by fun_prop)
  have hrad : Measurable (radialFactor (V := I) lam) := by
    unfold radialFactor
    exact (Finset.measurable_prod _ fun i _ =>
      ((measurable_rhoD lam).comp (measurable_pi_apply i)).pow_const 2).mul
        ((measurable_maxRad lam).pow_const (-2 : ℝ))
  have hdist : Measurable fun c : I → ℂ × ℂ => fun e : A => (Peeling.dipoleDistOn c e : ℂ) := by
    refine measurable_pi_iff.mpr fun e => ?_
    induction e.val using Sym2.ind with
    | h i j => exact Complex.measurable_ofReal.comp (measurable_dipoleDist.comp
          (show Measurable (fun c : I → ℂ × ℂ => (c i, c j)) by fun_prop))
  unfold limitingTreeTerm treeProfile
  exact ((Finset.measurable_prod _ fun i _ =>
    (measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i)).mul hrad).ennreal_ofReal.mul
      ((measurable_jointOdd_comp _ _ _ (measurable_minRad lam) (measurable_maxRad lam) hdist).mul
        ((Finset.measurable_prod _ fun e _ => (hedge e true).ennreal_ofReal).mul
          (Finset.measurable_prod _ fun e _ => (hedge e false).ennreal_ofReal)))

/-- The exact logarithmic configuration-to-vector comparison for a retained
mixed tree. Integrate the joint odd family and the even annuli. -/
theorem lintegral_limitingTreeTerm_le {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      ∀ (T : SimpleGraph I), T.IsTree → Fintype.card I = k + 1 →
      ∀ (NT A B : Finset (Sym2 I)), A ∪ (B ∪ NT) = T.edgeFinset →
      Disjoint A (B ∪ NT) → Disjoint B NT → ∀ root : I,
      (∫⁻ c, anchor root c * limitingTreeTerm χ β lam M NT A B c) ≤
        ENNReal.ofReal C * ∫⁻ u : I → ℂ, ENNReal.ofReal (logRadialWeight β lam k u) := by
  obtain ⟨Cs, hCs, hs⟩ := lintegral_treeProfile hM k
  obtain ⟨Cg, hCg, hg⟩ := exists_logDensityWeight_le hχ hβ
  refine ⟨Cs * Cg ^ Fintype.card I, by positivity,
    fun lam hlam T hT hI NT A B hpart hA hB root => ?_⟩
  have hm : Measurable (fun c => anchor root c * limitingTreeTerm χ β lam M NT A B c) :=
    (measurable_anchor root).mul (measurable_limitingTreeTerm (β := β) (M := M) hχ hlam NT A B)
  rw [lintegral_eq_lintegral_pos_vec _ hm]
  have hpoint (u : I → ℂ) :
      (∫⁻ x : I → ℂ, anchor root (ofPosVec x u) * limitingTreeTerm χ β lam M NT A B (ofPosVec x u)) ≤
        ENNReal.ofReal Cs * ENNReal.ofReal (logDensityWeight χ β lam k u) := by
    let P : ℝ := (∏ i, Real.exp (β * smearedKernel χ lam (u i))) *
      radialFactor lam (ofPosVec (fun _ => 0) u)
    have hP : 0 ≤ P := mul_nonneg (prod_nonneg fun _ _ => (Real.exp_pos _).le)
      (by unfold radialFactor
          exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
            (Real.rpow_nonneg (hlam.le.trans (lam_le_maxRad lam _)) _))
    have heq (x : I → ℂ) : anchor root (ofPosVec x u) * limitingTreeTerm χ β lam M NT A B (ofPosVec x u) =
        ENNReal.ofReal P * (anchor root (ofPosVec x u) * treeProfile M lam A B NT (ofPosVec x u)) := by
      dsimp only [limitingTreeTerm, P, radialFactor]
      simp only [ofPosVec_apply, pairDensity_mk hχ, rhoD_mk, maxRad_ofPosVec_eq]
      ring
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hsp := hs I hI T hT A B NT hpart hA hB root u lam hlam 1
    simp only [Nat.cast_one, mul_one] at hsp
    exact (mul_le_mul_right hsp _).trans_eq (by
      rw [← ENNReal.ofReal_mul hP, ← ENNReal.ofReal_mul (by positivity : 0 ≤ Cs)]
      congr 1
      unfold P logDensityWeight
      ring)
  refine (lintegral_mono hpoint).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal Cs * ∫⁻ u : I → ℂ,
        ENNReal.ofReal (Cg ^ Fintype.card I) * ENNReal.ofReal (logRadialWeight β lam k u) := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro u
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hg I lam hlam k u)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
        ← ENNReal.ofReal_mul hCs.le]

/-- Integrability of a full retained-tree majorant, with the final power
absorption performed only after the spatial logarithms. -/
theorem lintegral_limitingTreeTerm_lt_top {χ : ℂ → ℝ} {β lam M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam) (hM : 1 ≤ M)
    (hk : (Fintype.card I : ℕ∞) ≤ pStar β) (T : SimpleGraph I) (hT : T.IsTree)
    (NT A B : Finset (Sym2 I)) (hpart : A ∪ (B ∪ NT) = T.edgeFinset)
    (hA : Disjoint A (B ∪ NT)) (hB : Disjoint B NT) (root : I) :
    ∫⁻ c, anchor root c * limitingTreeTerm χ β lam M NT A B c < ∞ := by
  obtain ⟨C, _, hb⟩ := lintegral_limitingTreeTerm_le (I := I) (β := β) (M := M) hχ (by linarith) hM (Fintype.card I - 1)
  exact (hb lam hlam T hT (by have := Fintype.card_pos (α := I); omega)
    NT A B hpart hA hB root).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_logRadialWeight_lt_top hβ hlam hk _))

end MultipoleBKT.Limits.RouteDirect

end
