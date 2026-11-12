/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegralZ.RouteSingleton.Geometry
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Basic

/-!
# Integration on the singleton disk

See Proposition 5.18.
Integrate the positive root and the displacement in a disk independently.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegralZ.RouteSingleton

open MeasureTheory Set Metric Finset MultipoleIntegral
open scoped ENNReal
open TwoComponentCoulomb (box)

/-- The product indicator for roots in `B` and displacements in the closed disk `r ≤ λ`. -/
noncomputable def diskWeight {ι : Type*} [Fintype ι] (lam : ℝ) (B : Set ℂ)
    (c : ι → ℂ × ℂ) : ℝ≥0∞ :=
  ∏ i, B.indicator (1 : ℂ → ℝ≥0∞) (c i).1 *
    (closedBall (0 : ℂ) lam).indicator (1 : ℂ → ℝ≥0∞) ((c i).2 - (c i).1)

/-- A singleton disk contributes `|B| π λ²`, with root `x` and displacement `y-x`. -/
theorem lintegral_diskWeight {ι : Type*} [Fintype ι] {lam : ℝ} (hlam : 0 ≤ lam)
    {B : Set ℂ} (hB : MeasurableSet B) (hι : Fintype.card ι = 1) :
    ∫⁻ c : ι → ℂ × ℂ, diskWeight lam B c = volume B * ENNReal.ofReal (Real.pi * lam ^ 2) := by
  classical
  let f : ℂ × ℂ → ℝ≥0∞ := fun e => B.indicator (1 : ℂ → ℝ≥0∞) e.1 *
    (closedBall (0 : ℂ) lam).indicator (1 : ℂ → ℝ≥0∞) (e.2 - e.1)
  have hf : Measurable f := (measurable_const.indicator hB).comp measurable_fst |>.mul
    ((measurable_const.indicator measurableSet_closedBall).comp (measurable_snd.sub measurable_fst))
  change (∫⁻ c : ι → ℂ × ℂ, ∏ i, f (c i)) = _
  rw [volume_pi, lintegral_pi_prod_eq' (0 : ℂ × ℂ) (fun _ : ι => volume) (fun _ => f) (fun _ => hf), prod_const, card_univ, hι, pow_one]
  rw [Measure.volume_eq_prod, lintegral_prod _ hf.aemeasurable]
  have ht (x : ℂ) : ∫⁻ y : ℂ, f (x, y) =
      B.indicator (1 : ℂ → ℝ≥0∞) x * volume (closedBall (0 : ℂ) lam) := by
    dsimp [f]
    rw [lintegral_const_mul' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top (indicator_one_le_one _ _)),
      lintegral_sub_right_eq_self, lintegral_indicator_one measurableSet_closedBall]
  simp_rw [ht]
  have hBi : Measurable (B.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hB
  rw [lintegral_mul_const _ hBi, lintegral_indicator_one hB]
  congr 1
  rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hlam, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- The integrand on the singleton disk is bounded below by
`exp(-|L|) (3λ)^{-β}`. There are no internal pair interactions, and `τ^Z ≥ λ`
controls the external weight. See Proposition 5.18. -/
theorem le_plusIntegrand_of_disk {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam M ε₀ L : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) {N p₀ : ℕ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} {S : Finset ℕ} (hS : S.card = 1) (hM : 0 ≤ M)
    (hh : lam ≤ ε₀ * truncationScale p₀ β lam) {c : S → ℂ × ℂ}
    (hr : ∀ i, ‖(c i).1 - (c i).2‖ ≤ lam)
    (hx : ∀ i, (c i).1 ∉ badNbhd V Z ((M + 1) * lam)) :
    Real.exp (-|L|) * (3 * lam) ^ (-β) ≤ plusIntegrand χ p₀ β lam M ε₀ L V Z c := by
  classical
  have hcard : Fintype.card S = 1 := by simpa using hS
  have : Subsingleton S := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have : Nonempty S := Fintype.card_pos_iff.mp (by omega)
  have hconn : (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected :=
    SimpleGraph.Connected.of_subsingleton
  have hpair : ∀ i j : S, ¬ i < j := fun i j => by rw [Subsingleton.elim i j]; exact lt_irrefl _
  unfold plusIntegrand
  simp only [hconn, ↓reduceIte, hpair, prod_const_one, mul_one, one_mul]
  have hdip (i : S) : Real.exp (-|L|) * (3 * lam) ^ (-β) ≤
      UpperBound.dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2) := by
    rw [indicator_of_mem (show (c i).1 - (c i).2 ∈ closedBall (0 : ℂ)
        (ε₀ * truncationScale p₀ β lam) from mem_closedBall_zero_iff.mpr ((hr i).trans hh))]
    unfold UpperBound.dipoleWeightZ
    simp only [isGoodZ_of_disk hM (hr i) (hx i), ↓reduceIte, mul_one]
    have hτ := UpperBound.lam_le_goodRadiusZ (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V) (Z := Z) (c i)
    have hτ0 : 0 < UpperBound.goodRadiusZ p₀ β lam ε₀ V Z (c i) := hlam.trans_le hτ
    have hq : 0 ≤ ‖(c i).1 - (c i).2‖ / UpperBound.goodRadiusZ p₀ β lam ε₀ V Z (c i) ∧
        ‖(c i).1 - (c i).2‖ / UpperBound.goodRadiusZ p₀ β lam ε₀ V Z (c i) ≤ 1 :=
      ⟨by positivity, (div_le_one hτ0).mpr ((hr i).trans hτ)⟩
    have hweight : -|L| ≤ L * (‖(c i).1 - (c i).2‖ /
        UpperBound.goodRadiusZ p₀ β lam ε₀ V Z (c i)) ^ 2 := by
      have hsq : (‖(c i).1 - (c i).2‖ / UpperBound.goodRadiusZ p₀ β lam ε₀ V Z (c i)) ^ 2 ≤ 1 := by
        nlinarith [hq.1, hq.2]
      nlinarith [neg_abs_le L, abs_nonneg L,
        sq_nonneg (‖(c i).1 - (c i).2‖ / UpperBound.goodRadiusZ p₀ β lam ε₀ V Z (c i))]
    refine mul_le_mul (Real.exp_le_exp.mpr hweight) ?_ (by positivity) (by positivity)
    have hk := neg_log_add_le_smearedKernel hχ hlam ((c i).1 - (c i).2)
    have hlog := Real.log_le_log (by positivity : 0 < ‖(c i).1 - (c i).2‖ + 2 * lam)
      (show ‖(c i).1 - (c i).2‖ + 2 * lam ≤ 3 * lam by linarith [hr i])
    rw [Real.rpow_def_of_pos (by positivity : 0 < 3 * lam)]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc _ = ∏ _i : S, Real.exp (-|L|) * (3 * lam) ^ (-β) := by
        rw [prod_const, card_univ, hcard, pow_one]
       _ ≤ _ := prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hdip i)

/-- Restriction to the singleton disk, followed by the root and disk integrations.
The pointwise estimate is an internal interface for the actual frozen integrand. -/
theorem le_integral_of_disk {S : Finset ℕ} (hS : S.card = 1) {N : ℕ} {lam : ℝ}
    (hlam : 0 < lam) {B : Set ℂ} (hBm : MeasurableSet B)
    (hB : B ⊆ innerBox N (2 * lam)) {b A : ℝ} (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hvol : ENNReal.ofReal b ≤ volume B) {F : (S → ℂ × ℂ) → ℝ}
    (hFm : Measurable F) (hF0 : ∀ c, 0 ≤ F c)
    (hfin : ∫⁻ c in univ.pi (fun _ : S => box N ×ˢ box N), ENNReal.ofReal (F c) ≠ ⊤)
    (hF : ∀ c, (∀ i, (c i).1 ∈ B ∧ ‖(c i).1 - (c i).2‖ ≤ lam) → A ≤ F c) :
    A * b * (Real.pi * lam ^ 2) ≤ ∫ c in univ.pi (fun _ : S => box N ×ˢ box N), F c := by
  classical
  have hc : Fintype.card S = 1 := by simpa using hS
  have hpoint (c : S → ℂ × ℂ) : ENNReal.ofReal A * diskWeight lam B c ≤
      (univ.pi (fun _ : S => box N ×ˢ box N)).indicator (fun c => ENNReal.ofReal (F c)) c := by
    by_cases hz : diskWeight lam B c = 0
    · rw [hz, mul_zero]; exact zero_le
    have he : ∀ i, (c i).1 ∈ B ∧ ‖(c i).1 - (c i).2‖ ≤ lam := by
      intro i
      have hi := (prod_ne_zero_iff.mp hz) i (mem_univ i)
      obtain ⟨hx, hr⟩ := mul_ne_zero_iff.mp hi
      refine ⟨mem_of_indicator_one_ne_zero hx, ?_⟩
      have := mem_of_indicator_one_ne_zero hr
      simpa only [mem_closedBall_zero_iff, norm_sub_rev] using this
    rw [indicator_of_mem (mem_univ_pi.mpr fun i => mem_box_of_disk hlam (hB (he i).1) (he i).2)]
    calc ENNReal.ofReal A * diskWeight lam B c ≤ ENNReal.ofReal A * 1 := by
          gcongr
          exact prod_le_one fun i _ => mul_le_one' (indicator_one_le_one _ _) (indicator_one_le_one _ _)
         _ = ENNReal.ofReal A := mul_one _
         _ ≤ _ := ENNReal.ofReal_le_ofReal (hF c he)
  have hint : ENNReal.ofReal (A * b * (Real.pi * lam ^ 2)) ≤
      ∫⁻ c in univ.pi (fun _ : S => box N ×ˢ box N), ENNReal.ofReal (F c) := by
    rw [← lintegral_indicator (measurableSet_pi_box_prod N)]
    calc _ = ENNReal.ofReal A * (ENNReal.ofReal b * ENNReal.ofReal (Real.pi * lam ^ 2)) := by
          rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul hA]; congr 1; ring
         _ ≤ ENNReal.ofReal A * (volume B * ENNReal.ofReal (Real.pi * lam ^ 2)) := by gcongr
         _ = ENNReal.ofReal A * ∫⁻ c : S → ℂ × ℂ, diskWeight lam B c := by
          rw [lintegral_diskWeight hlam.le hBm hc]
         _ = ∫⁻ c : S → ℂ × ℂ, ENNReal.ofReal A * diskWeight lam B c :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
         _ ≤ _ := lintegral_mono hpoint
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hFm.aestronglyMeasurable]
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hint

end MultipoleBKT.MultipoleIntegralZ.RouteSingleton

end
