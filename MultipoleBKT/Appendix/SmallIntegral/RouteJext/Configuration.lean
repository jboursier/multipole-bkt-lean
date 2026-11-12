/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Core
public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Radial

/-!
# Configuration integration and the cancellation of the largest radius

See Lemma A.4. Apply the common translation
estimate at fixed displacements, integrate the tree coordinates, and cancel
its squared largest radius against (A.25) before radial integration.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJext

open MeasureTheory Set Finset SimpleGraph Limits Peeling RouteJ GeneralExpansion
open TwoComponentCoulomb (box)
open scoped Classical ENNReal

/-- One retained tree and one dipole carrying the external root gain. -/
noncomputable def term {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (χ : ℂ → ℝ) (β lam M eps : ℝ) (p₀ : ℕ) {N : ℕ}
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ)
    (A E F : Finset (Sym2 W)) (root : W) (c : W → ℂ × ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (gainW p₀ β lam eps V Z (maxRad lam c) (c root)) *
    ENNReal.ofReal (radialFactor lam c) *
      cutTree M lam (eps * truncationScale p₀ β lam) A E F c *
        ∏ i, ENNReal.ofReal (cutDens χ β lam (eps * truncationScale p₀ β lam) (c i))

theorem measurable_term {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam M eps : ℝ} (hlam : 0 < lam)
    (p₀ : ℕ) {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ)
    (A E F : Finset (Sym2 W)) (root : W) :
    Measurable (term χ β lam M eps p₀ V Z A E F root) := by
  have hg : Measurable fun c : W → ℂ × ℂ => gainW p₀ β lam eps V Z (maxRad lam c) (c root) := by
    unfold gainW
    exact measurable_const.min (((measurable_maxRad lam).pow_const 2).div
      (((continuous_badDistZ' p₀ β lam eps V Z).measurable.comp (measurable_pi_apply root)).pow_const 2))
  have hr : Measurable (radialFactor (V := W) lam) := by
    unfold radialFactor
    exact (Finset.measurable_prod _ fun i _ =>
      ((measurable_rhoD lam).comp (measurable_pi_apply i)).pow_const 2).mul
        ((measurable_maxRad lam).pow_const (-2 : ℝ))
  exact ((hg.ennreal_ofReal.mul hr.ennreal_ofReal).mul (measurable_cutTree M lam _ A E F)).mul
    (Finset.measurable_prod _ fun i _ => ((measurable_cutDens hχ hlam β _).comp
      (measurable_pi_apply i)).ennreal_ofReal)

/-- The actual cut density becomes the cut displacement weight. -/
theorem cutDens_ofPosVec {W : Type*} {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    (β lam h : ℝ) (x u : W → ℂ) (i : W) :
    ENNReal.ofReal (cutDens χ β lam h (ofPosVec x u i)) = cutWeight χ β lam h (u i) := by
  unfold cutDens cutWeight
  rw [pairDensity_ofPosVec hχ, norm_ofPosVec_sub]
  by_cases hu : ‖u i‖ ≤ h
  · rw [indicator_of_mem (show ‖u i‖ ∈ Iic h from hu), Pi.one_apply, mul_one,
      indicator_of_mem (mem_closedBall_zero_iff.mpr hu)]
  · rw [indicator_of_notMem (show ‖u i‖ ∉ Iic h from hu), mul_zero,
      indicator_of_notMem (fun hx => hu (mem_closedBall_zero_iff.mp hx)), ENNReal.ofReal_zero]

/-- At fixed vectors the root square cancels exactly against the radius
allocation, leaving the product of squared regularized dipole radii. -/
theorem radius_cancel {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W] {lam : ℝ}
    (hlam : 0 < lam) (u : W → ℂ) (A B C L : ℝ) (q : ℕ) :
    (maxRho lam u ^ 2 * (A + B * L) * (C * L ^ q)) *
        radialFactor lam (ofPosVec (fun _ => 0) u) =
      C * (A * L ^ q + B * L ^ (q + 1)) * ∏ i, rho lam (u i) ^ 2 := by
  unfold radialFactor
  simp only [ofPosVec_apply, rhoD_mk, maxRad_ofPosVec_eq]
  rw [Real.rpow_neg (maxRho_pos hlam u).le, Real.rpow_two, pow_succ]
  field_simp [(maxRho_pos hlam u).ne']
  ring

/-- Full configuration comparison for a retained tree. The two terms are kept
separate so only the area coefficient may later depend on epsilon_0. -/
theorem lintegral_term_le_vectors {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam M eps : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (p₀ : ℕ) {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ)
    (A E F : Finset (Sym2 W)) (hT : (fromEdgeSet ((F ∪ (A ∪ E) : Finset (Sym2 W)) : Set (Sym2 W))).IsTree)
    (hTE : (fromEdgeSet ((F ∪ (A ∪ E) : Finset (Sym2 W)) : Set (Sym2 W))).edgeFinset = F ∪ (A ∪ E))
    (hlh : lam ≤ eps * truncationScale p₀ β lam) (root : W) :
    (∫⁻ c in boxConfig W N, term χ β lam M eps p₀ V Z A E F root c) ≤
      ENNReal.ofReal ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1)) *
        (ENNReal.ofReal (N / (16 * (eps * truncationScale p₀ β lam) ^ 2)) *
          (∫⁻ u : W → ℂ, vectorWeight χ β lam (eps * truncationScale p₀ β lam) (Fintype.card W - 1) u) +
        ENNReal.ofReal (8 * Real.pi * V.card) *
          ∫⁻ u : W → ℂ, vectorWeight χ β lam (eps * truncationScale p₀ β lam) (Fintype.card W) u) := by
  let h := eps * truncationScale p₀ β lam
  let C := (4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1)
  let a : ℝ := N / (16 * h ^ 2)
  let b : ℝ := 8 * Real.pi * V.card
  let q := Fintype.card W - 1
  have hq : q + 1 = Fintype.card W := Nat.sub_add_cancel (Fintype.card_pos : 0 < Fintype.card W)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  let G (c : W → ℂ × ℂ) := (box N).indicator (1 : ℂ → ℝ≥0∞) (c root).1 *
    term χ β lam M eps p₀ V Z A E F root c
  have hG : Measurable G :=
    (((measurable_const.indicator (TwoComponentCoulomb.measurableSet_box N)).comp
      (measurable_fst.comp (measurable_pi_apply root))).mul (measurable_term hχ hlam p₀ V Z A E F root))
  have hbox : (∫⁻ c in boxConfig W N, term χ β lam M eps p₀ V Z A E F root c) ≤ ∫⁻ c, G c := by
    rw [← lintegral_indicator (measurableSet_boxConfig N)]
    apply lintegral_mono
    intro c
    by_cases hc : c ∈ boxConfig W N
    · rw [indicator_of_mem hc]
      have hr := ((Set.mem_univ_pi.mp hc) root).1
      simp only [G, indicator_of_mem hr, Pi.one_apply, one_mul, le_refl]
    · rw [indicator_of_notMem hc]
      exact bot_le
  refine hbox.trans ?_
  rw [lintegral_eq_lintegral_pos_vec G hG]
  have hpt (u : W → ℂ) : (∫⁻ x : W → ℂ, G (ofPosVec x u)) ≤ ENNReal.ofReal C *
      (ENNReal.ofReal a * vectorWeight χ β lam h q u +
        ENNReal.ofReal b * vectorWeight χ β lam h (q + 1) u) := by
    let dens := ∏ i, cutWeight χ β lam h (u i)
    let rad := radialFactor lam (ofPosVec (fun _ : W => 0) u)
    have hre (x : W → ℂ) : G (ofPosVec x u) =
        ((box N).indicator 1 (x root) * ENNReal.ofReal
          (gainW p₀ β lam eps V Z (maxRho lam u) (ofPosVec x u root)) *
            cutTree M lam h A E F (ofPosVec x u)) * ENNReal.ofReal rad * dens := by
      dsimp only [G, term]
      simp_rw [cutDens_ofPosVec hχ]
      have hr : radialFactor lam (ofPosVec x u) = rad := by
        unfold rad radialFactor
        simp only [ofPosVec_apply, rhoD_mk, maxRad_ofPosVec_eq]
      rw [hr, maxRad_ofPosVec_eq]
      simp only [ofPosVec_apply]
      dsimp only [h, dens]
      ring
    simp_rw [hre]
    rw [lintegral_mul_const' _ _ (show dens ≠ ⊤ from ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top),
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    by_cases hu : ∀ i, ‖u i‖ ≤ h
    · have hu' (i) : rho lam (u i) ≤ h := max_le (hu i) hlh
      let T := fromEdgeSet ((F ∪ (A ∪ E) : Finset (Sym2 W)) : Set (Sym2 W))
      have hs := lintegral_cutTree_gain_le hM hlam u hu' T hT A E root V Z
      have hs0 : (∫⁻ x : W → ℂ, (box N).indicator 1 (x root) *
          ENNReal.ofReal (gainW p₀ β lam eps V Z (maxRho lam u) (ofPosVec x u root)) *
            cutTree M lam h A E F (ofPosVec x u)) ≤
          ENNReal.ofReal (maxRho lam u ^ 2 *
            (a + b * (1 + Real.log (17 * h / minRho lam u))) *
              (C * (1 + Real.log (17 * h / minRho lam u)) ^ q)) := by
        convert! hs using 1
        apply lintegral_congr
        intro x
        congr 1
        unfold cutTree
        rw [vectors_ofPosVec]
        apply prod_congr _ (fun _ _ => rfl)
        convert! hTE.symm using 1
        congr 1
        exact Subsingleton.elim _ _
      refine (mul_le_mul' (mul_le_mul' hs0 le_rfl) le_rfl).trans_eq ?_
      let L := 1 + Real.log (17 * h / minRho lam u)
      have hL : 0 ≤ L := by
        have ham := minRho_pos hlam u
        have hah := (minRho_le_rho lam u root).trans (hu' root)
        have := Real.log_nonneg ((one_le_div ham).2 (show minRho lam u ≤ 17 * h by linarith))
        dsimp only [L]
        linarith
      rw [← ENNReal.ofReal_mul (by positivity), radius_cancel hlam u a b C L q]
      unfold vectorWeight dens
      have hD : 0 ≤ a * L ^ q + b * L ^ (q + 1) := by positivity
      rw [ENNReal.ofReal_mul (mul_nonneg hC hD), ENNReal.ofReal_mul hC,
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb,
        ENNReal.ofReal_prod_of_nonneg (fun i _ => sq_nonneg _)]
      rw [prod_mul_distrib]
      ring
    · push Not at hu
      obtain ⟨i, hi⟩ := hu
      have hd : dens = 0 := by
        apply prod_eq_zero (mem_univ i)
        unfold cutWeight
        rw [indicator_of_notMem (fun hx => (not_le.mpr hi) (mem_closedBall_zero_iff.mp hx)), ENNReal.ofReal_zero]
      rw [hd, mul_zero]
      exact bot_le
  refine (lintegral_mono hpt).trans_eq ?_
  have hm (r : ℕ) : Measurable (vectorWeight (I := W) χ β lam h r) := by
    unfold vectorWeight
    exact ((measurable_const.div (measurable_minRho lam)).log.const_add 1 |>.pow_const r |>.ennreal_ofReal).mul
      (Finset.measurable_prod _ fun i _ => ((measurable_cutWeight hχ hlam β h).comp (measurable_pi_apply i)).mul (by unfold rho; fun_prop))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left (f := fun u : W → ℂ => ENNReal.ofReal a * vectorWeight χ β lam h q u)
      (g := fun u : W → ℂ => ENNReal.ofReal b * vectorWeight χ β lam h (q + 1) u)
      (measurable_const.mul (hm q)),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hq]

end MultipoleBKT.SmallIntegral.RouteJext

end
