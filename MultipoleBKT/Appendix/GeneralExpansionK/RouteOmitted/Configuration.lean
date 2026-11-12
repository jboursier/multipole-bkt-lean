/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.LongProfile
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.RadialEpsilon

/-!
# Omitted configuration integrals before radial absorption

See Lemma A.7. Position integration leaves
`N/h²` times the written cutoff radial integral with its logarithm.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open GeneralExpansion
open scoped Classical ENNReal

/-- Tonelli followed by the coupled spatial integration. Both original
omitted alternatives retain the exact inverse-square cutoff. -/
theorem omittedTree_le_vectors {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W],
      Fintype.card W ≤ k+1 → ∀ (T : SimpleGraph W), T.IsTree →
      ∀ (A E N : Finset (Sym2 W)), A ∪ (E ∪ N) = T.edgeFinset →
      Disjoint A (E ∪ N) → Disjoint E N → ∀ mark : Option (Sym2 W),
      (∀ m, mark = some m → m ∈ E) → ∀ {χ : ℂ → ℝ}, IsMollifier χ →
      ∀ (β lam h : ℝ), 0 < lam → lam ≤ h → ∀ n : ℕ,
      (∫⁻ c in boxConfig W n,
        omittedTree M lam (17*h) A E N mark c * activityDensity χ β lam h c) ≤
        ENNReal.ofReal (C*n/h^2) * ∫⁻ u : W → ℂ, vectorWeight χ β lam h k u := by
  obtain ⟨C,hC,hb⟩ := lintegral_omittedTree hM k
  refine ⟨C,hC,?_⟩
  intro W _ _ _ hW T hT A E N hpart hA hEN mark hm χ hχ β lam h hlam hlh n
  let root : W := Classical.arbitrary W
  let G (c : W → ℂ × ℂ) := (TwoComponentCoulomb.box n).indicator (1 : ℂ → ℝ≥0∞) (c root).1 *
    omittedTree M lam (17*h) A E N mark c * activityDensity χ β lam h c
  have hG : Measurable G := (((measurable_const.indicator (TwoComponentCoulomb.measurableSet_box n)).comp
    (measurable_fst.comp (measurable_pi_apply root))).mul (measurable_omittedTree _ _ _ _ _ _ _)).mul
    (measurable_activityDensity hχ hlam _ _)
  have hbox : (∫⁻ c in boxConfig W n, omittedTree M lam (17*h) A E N mark c *
      activityDensity χ β lam h c) ≤ ∫⁻ c, G c := by
    rw [← lintegral_indicator (measurableSet_boxConfig n)]
    apply lintegral_mono
    intro c
    by_cases hc : c ∈ boxConfig W n
    · rw [indicator_of_mem hc]
      simp only [G,indicator_of_mem (((Set.mem_univ_pi.mp hc) root).1),Pi.one_apply,one_mul,le_refl]
    · rw [indicator_of_notMem hc]
      exact bot_le
  refine hbox.trans ?_
  rw [lintegral_eq_lintegral_pos_vec G hG,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro u
  let dens := ∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i)^2)
  have hre (x : W → ℂ) : G (ofPosVec x u) =
      ((TwoComponentCoulomb.box n).indicator 1 (x root) *
        omittedTree M lam (17*h) A E N mark (ofPosVec x u)) * dens := by
    dsimp only [G,ofPosVec_apply]
    rw [activityDensity_ofPosVec hχ]
  change (∫⁻ x : W → ℂ, G (ofPosVec x u)) ≤ _
  simp_rw [hre]
  have hdens : dens ≠ ⊤ := ENNReal.prod_ne_top fun _ _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [lintegral_mul_const' _ _ hdens]
  by_cases hu : ∀ i, ‖u i‖ ≤ h
  · have hh : 0 < h := hlam.trans_le hlh
    have hH : h ≤ 17*h := by linarith
    have hs := hb W hW T hT A E N hpart hA hEN mark hm root u lam (17*h) hlam
      (fun i => (max_le (hu i) hlh).trans hH) n
    have hL : 0 ≤ 1 + Real.log (17*h/minRho lam u) := by
      have := Real.log_nonneg ((one_le_div (minRho_pos hlam u)).2
        ((minRho_le_rho lam u root).trans ((max_le (hu root) hlh).trans hH)))
      linarith
    have hs' : (∫⁻ x : W → ℂ, (TwoComponentCoulomb.box n).indicator 1 (x root) *
        omittedTree M lam (17*h) A E N mark (ofPosVec x u)) ≤
        ENNReal.ofReal (C*n/h^2*(1+Real.log (17*h/minRho lam u))^k) := by
      refine hs.trans (ENNReal.ofReal_le_ofReal ?_)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL _)
      exact div_le_div_of_nonneg_left (mul_nonneg hC.le (Nat.cast_nonneg _))
        (pow_pos hh 2) (pow_le_pow_left₀ hh.le hH 2)
    refine (mul_le_mul' hs' le_rfl).trans_eq ?_
    unfold vectorWeight
    dsimp only [dens]
    change ENNReal.ofReal (C*n/h^2*(1+Real.log (17*h/SmallIntegral.minRho lam u))^k) * _ = _
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C*n/h^2)]
    ring
  · push Not at hu
    obtain ⟨i,hi⟩ := hu
    have hz : cutWeight χ β lam h (u i) = 0 := by
      unfold cutWeight
      rw [indicator_of_notMem (show u i ∉ Metric.closedBall (0 : ℂ) h by
        intro hx
        exact (not_le.mpr hi) (mem_closedBall_zero_iff.mp hx)),ENNReal.ofReal_zero]
    have hd : dens = 0 := prod_eq_zero (mem_univ i) (by rw [hz,zero_mul])
    change _ * dens ≤ ENNReal.ofReal (C*n/h^2) * (ENNReal.ofReal _ * dens)
    simp only [hd,mul_zero,le_refl]

/-- Apply the radial cutoff gain only after the spatial logarithm is present. -/
theorem omittedTree_bound {χ : ℂ → ℝ} {β M : ℝ} (hχ : IsMollifier χ)
    (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k →
      ∀ (T : SimpleGraph W), T.IsTree → ∀ (A E N : Finset (Sym2 W)),
      A ∪ (E ∪ N) = T.edgeFinset → Disjoint A (E ∪ N) → Disjoint E N →
      ∀ mark : Option (Sym2 W), (∀ m, mark = some m → m ∈ E) → ∀ n : ℕ,
      (∫⁻ c in boxConfig W n,
        omittedTree M lam (17*(eps*truncationScale p₀ β lam)) A E N mark c *
          activityDensity χ β lam (eps*truncationScale p₀ β lam) c) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*n*lam^((2-β)*k)*truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨A,hA,ha⟩ := omittedTree_le_vectors hM (k-1)
  obtain ⟨B,hB,hb⟩ := vectorWeight_gain hχ hβ p₀ hk (k-1)
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro eps lam hlam hle heps W _ _ _ hW T hT Ao E N hpart hAo hEN mark hm n
  have heps0 := hlam.trans_le hle
  have ht := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hlh : lam ≤ eps*truncationScale p₀ β lam := hle.trans (le_mul_of_one_le_right heps0.le
    (Appendix.one_le_truncationScale hβ hlam (hle.trans heps)))
  have hα : 0 ≤ alphaExponent β*k := by
    have : 0 ≤ alphaExponent β := by unfold alphaExponent; split_ifs <;> linarith
    positivity
  have hv := hb W hW eps lam hlam hle heps
  have hv' : (∫⁻ u : W → ℂ, vectorWeight χ β lam (eps*truncationScale p₀ β lam) (k-1) u) ≤
      ENNReal.ofReal (B*lam^((2-β)*k)) := by
    refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
    have := Real.rpow_le_one heps0.le heps hα
    calc
      _ ≤ B*1*lam^((2-β)*k) := by gcongr
      _ = _ := by ring
  have hs := ha W (by omega) T hT Ao E N hpart hAo hEN mark hm hχ β lam _ hlam hlh n
  refine hs.trans ((mul_le_mul' le_rfl hv').trans_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_neg heps0.le,Real.rpow_two,Real.rpow_neg ht.le,Real.rpow_two,mul_pow]
  ring

/-- The same omitted tree bound for an arbitrary fixed positive epsilon. -/
theorem omittedTree_bound_at {χ : ℂ → ℝ} {β M : ℝ} (hχ : IsMollifier χ)
    (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k →
      ∀ (T : SimpleGraph W), T.IsTree → ∀ (A E N : Finset (Sym2 W)),
      A ∪ (E ∪ N) = T.edgeFinset → Disjoint A (E ∪ N) → Disjoint E N →
      ∀ mark : Option (Sym2 W), (∀ m, mark = some m → m ∈ E) → ∀ n : ℕ,
      (∫⁻ c in boxConfig W n,
        omittedTree M lam (17*(eps*truncationScale p₀ β lam)) A E N mark c *
          activityDensity χ β lam (eps*truncationScale p₀ β lam) c) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*n*lam^((2-β)*k)*truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨A,hA,ha⟩ := omittedTree_le_vectors hM (k-1)
  obtain ⟨B,hB,hb⟩ := vectorWeight_bound_at hχ hβ heps p₀ hk (k-1)
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro lam hlam hle hlam1 W _ _ _ hW T hT Ao E N hpart hAo hEN mark hm n
  have heps0 := hlam.trans_le hle
  have ht := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hlh : lam ≤ eps*truncationScale p₀ β lam := hle.trans (le_mul_of_one_le_right heps0.le
    (Appendix.one_le_truncationScale hβ hlam hlam1))
  have hv := hb W hW lam hlam hle hlam1
  have hs := ha W (by omega) T hT Ao E N hpart hAo hEN mark hm hχ β lam _ hlam hlh n
  refine hs.trans ((mul_le_mul' le_rfl hv).trans_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_neg heps0.le,Real.rpow_two,Real.rpow_neg ht.le,Real.rpow_two,mul_pow]
  ring

end MultipoleBKT.ExpansionK.RouteOmitted

end
