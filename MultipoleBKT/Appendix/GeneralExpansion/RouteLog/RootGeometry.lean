/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.FrozenRoot
public import MultipoleBKT.Appendix.RouteLog.Root
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Logarithmic integration in the actual frozen-root geometry

See (A.41). Keep the truncated inverse-square kernel until its planar
integral has been evaluated. The four translated endpoints are those seen
by the negative endpoint of the root dipole.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral UpperBound MultipoleIntegralZ

variable {N p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- The pointwise root estimate before the logarithmic integration.
The first term is the cutoff cap and the last term covers bad roots. -/
theorem rootZ_log_le (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V) {w : ℂ} (hw : ‖w‖ ≤ ε₀ * truncationScale p₀ β lam) (y : ℂ) :
    rootZ p₀ β lam M ε₀ V Z w y ≤
      (box N).indicator 1 y *
          ENNReal.ofReal (max ‖w‖ lam ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2) +
        ∑ j ∈ V, ∑ l : Fin 4,
          (ENNReal.ofReal (16 * max ‖w‖ lam ^ 2) *
              (ball (rootCentre (Z j) w l) (4 * (ε₀ * truncationScale p₀ β lam))).indicator
                (fun y' => ENNReal.ofReal ((max ‖y' - rootCentre (Z j) w l‖ (max ‖w‖ lam) ^ 2)⁻¹)) y +
            (closedBall (rootCentre (Z j) w l) (M * max ‖w‖ lam)).indicator 1 y) := by
  classical
  unfold rootZ
  set h := ε₀ * truncationScale p₀ β lam with hh_def
  have hh0 : 0 < h := hlam.trans_le hlamh
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  set m := max ‖w‖ lam with hm_def
  have hm0 : 0 < m := lt_max_of_lt_right hlam
  set e : ℂ × ℂ := (y + w, y) with he_def
  have hew : e.1 - e.2 = w := by simp [e]
  set S := ∑ j ∈ V, ∑ l : Fin 4,
          (ENNReal.ofReal (16 * m ^ 2) *
              (ball (rootCentre (Z j) w l) (4 * h)).indicator
                (fun y' => ENNReal.ofReal ((max ‖y' - rootCentre (Z j) w l‖ (max ‖w‖ lam) ^ 2)⁻¹)) y +
            (closedBall (rootCentre (Z j) w l) (M * m)).indicator 1 y)
  by_cases hy : y ∈ box N
  · rw [indicator_of_mem hy, Pi.one_apply, one_mul, one_mul]
    by_cases hg : IsGoodZ p₀ β lam M ε₀ V Z e
    · simp only [hg, ↓reduceIte, add_zero]
      set τ := goodRadiusZ p₀ β lam ε₀ V Z e
      have hτm : m / 4 ≤ τ := by
        have := goodRadiusZ_ge hlam (by linarith) hM hV hg (by rw [hew]; linarith)
        rwa [hew] at this
      have hτ0 : 0 < τ := by linarith [div_pos hm0 (by norm_num : (0 : ℝ) < 4)]
      set D := badDistZ p₀ β lam ε₀ V Z e
      have hτD : D / 4 ≤ τ := le_max_left _ _
      by_cases hD : 4 * h ≤ D
      · -- far from the bad charges: the cap
        refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
        have hτh : h ≤ τ := by linarith
        have h1 : ‖w‖ / τ ≤ m / h := div_le_div₀ hm0.le (le_max_left _ _) hh0 hτh
        have h2 : 0 ≤ ‖w‖ / τ := by positivity
        calc (‖w‖ / τ) ^ 2 ≤ (m / h) ^ 2 := pow_le_pow_left₀ h2 h1 2
          _ = m ^ 2 / h ^ 2 := by rw [div_pow]
      · -- near a bad charge
        push Not at hD
        have hVne : V.Nonempty := by
          by_contra hVe
          rw [Finset.not_nonempty_iff_eq_empty] at hVe
          have : 4 * h ≤ D := le_badDistZ le_rfl (by simp [hVe])
          linarith
        obtain ⟨j, hjV, hjmin⟩ := V.exists_min_image (fun j => dipoleDist e (Z j)) hVne
        have hDj : D = dipoleDist e (Z j) := by
          refine le_antisymm (badDistZ_le_dipoleDist e hjV) ?_
          by_contra hlt
          push Not at hlt
          have : min (4 * h) (dipoleDist e (Z j)) ≤ D :=
            le_badDistZ (min_le_left _ _) fun j' hj' => (min_le_right _ _).trans (hjmin j' hj')
          rcases min_choice (4 * h) (dipoleDist e (Z j)) with hc | hc <;> rw [hc] at this <;>
            linarith
        obtain ⟨l, hl⟩ := exists_dipoleDist_root_eq (Z j) w y
        set d := dipoleDist e (Z j)
        set q := rootCentre (Z j) w l
        have hdq : d = ‖y - q‖ := hl
        have hτmax : max m d / 4 ≤ τ := by
          have hτd : d / 4 ≤ τ := hDj ▸ hτD
          rw [div_le_iff₀ (by norm_num)]
          exact max_le (by linarith) (by linarith)
        have hbound : (‖w‖ / τ) ^ 2 ≤ 16 * m ^ 2 * (max d m ^ 2)⁻¹ := by
          have hmax0 : 0 < max m d := lt_max_of_lt_left hm0
          have h1 : ‖w‖ / τ ≤ m / (max m d / 4) :=
            div_le_div₀ hm0.le (le_max_left _ _) (by positivity) hτmax
          have h2 : 0 ≤ ‖w‖ / τ := by positivity
          calc (‖w‖ / τ) ^ 2 ≤ (m / (max m d / 4)) ^ 2 := pow_le_pow_left₀ h2 h1 2
            _ = 16 * (m ^ 2 / max m d ^ 2) := by field_simp; ring
            _ = 16 * m ^ 2 * (max d m ^ 2)⁻¹ := by
                rw [max_comm m d, div_eq_mul_inv]
                ring
        have hyq : y ∈ ball q (4 * h) := by
          rw [mem_ball, dist_eq_norm, ← hdq, ← hDj]
          exact hD
        refine le_add_left ?_
        refine le_trans ?_ (single_le_sum (f := fun j => ∑ l : Fin 4,
          (ENNReal.ofReal (16 * m ^ 2) *
              (ball (rootCentre (Z j) w l) (4 * h)).indicator
                (fun y' => ENNReal.ofReal ((max ‖y' - rootCentre (Z j) w l‖ (max ‖w‖ lam) ^ 2)⁻¹)) y +
            (closedBall (rootCentre (Z j) w l) (M * m)).indicator 1 y))
          (fun _ _ => zero_le) hjV)
        refine le_trans ?_ (single_le_sum (fun _ _ => zero_le) (mem_univ l))
        refine le_add_right ?_
        rw [indicator_of_mem hyq, ← ENNReal.ofReal_mul (by positivity), ← hdq]
        exact ENNReal.ofReal_le_ofReal hbound
    · simp only [hg, ↓reduceIte, zero_add]
      obtain ⟨j, hjV, hjd⟩ := exists_near_of_not_isGoodZ hM0 hg
      obtain ⟨l, hl⟩ := exists_dipoleDist_root_eq (Z j) w y
      rw [hew] at hjd
      have hyq : y ∈ closedBall (rootCentre (Z j) w l) (M * m) := by
        rw [mem_closedBall, dist_eq_norm, ← hl]
        exact hjd
      refine le_add_left ?_
      refine le_trans ?_ (single_le_sum (f := fun j => ∑ l : Fin 4,
          (ENNReal.ofReal (16 * m ^ 2) *
              (ball (rootCentre (Z j) w l) (4 * h)).indicator
                (fun y' => ENNReal.ofReal ((max ‖y' - rootCentre (Z j) w l‖ (max ‖w‖ lam) ^ 2)⁻¹)) y +
            (closedBall (rootCentre (Z j) w l) (M * m)).indicator 1 y))
          (fun _ _ => zero_le) hjV)
      refine le_trans ?_ (single_le_sum (fun _ _ => zero_le) (mem_univ l))
      refine le_add_left ?_
      rw [indicator_of_mem hyq, Pi.one_apply]
  · rw [indicator_of_notMem hy, zero_mul]
    exact zero_le

/-- The actual root defect satisfies (A.41) with its
logarithm retained. Four translated endpoints per frozen dipole suffice. -/
theorem lintegral_rootZ_log_le (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V) {w : ℂ} (hw : ‖w‖ ≤ ε₀ * truncationScale p₀ β lam) :
    ∫⁻ y, rootZ p₀ β lam M ε₀ V Z w y ≤
      ENNReal.ofReal (N * (max ‖w‖ lam ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2) +
        4 * V.card * (16 * max ‖w‖ lam ^ 2 *
          (2 * Real.pi * (1 / 2 + Real.log (4 * (ε₀ * truncationScale p₀ β lam) / max ‖w‖ lam))) +
            Real.pi * (M * max ‖w‖ lam) ^ 2)) := by
  set h := ε₀ * truncationScale p₀ β lam with hh_def
  have hh0 : 0 < h := hlam.trans_le hlamh
  have hM0 : 0 ≤ M := zero_le_one.trans ((one_le_pow₀ (by norm_num)).trans hM)
  set m := max ‖w‖ lam with hm_def
  have hm0 : 0 < m := lt_max_of_lt_right hlam
  set a : ℝ := m ^ 2 / h ^ 2
  set b : ℝ := 16 * m ^ 2
  set s : ℝ := 2 * Real.pi * (1 / 2 + Real.log (4 * h / m))
  set v : ℝ := Real.pi * (M * m) ^ 2
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hm4 : m ≤ 4 * h := by
    have hmh : m ≤ h := max_le hw hlamh
    linarith
  have hs : 0 ≤ s := by
    have := Real.log_nonneg ((one_le_div hm0).2 hm4)
    dsimp only [s]
    positivity
  have hv : 0 ≤ v := by positivity
  set f₁ : ℂ → ℝ≥0∞ := fun y => (box N).indicator 1 y * ENNReal.ofReal a
  set g : Fin N → Fin 4 → ℂ → ℝ≥0∞ := fun j l y =>
    ENNReal.ofReal b * (ball (rootCentre (Z j) w l) (4 * h)).indicator
        (fun y' => ENNReal.ofReal ((max ‖y' - rootCentre (Z j) w l‖ m ^ 2)⁻¹)) y +
      (closedBall (rootCentre (Z j) w l) (M * m)).indicator 1 y
  have hf₁ : Measurable f₁ :=
    (measurable_one.indicator (TwoComponentCoulomb.measurableSet_box N)).mul measurable_const
  have hg : ∀ j l, Measurable (g j l) := by
    intro j l
    refine (measurable_const.mul (Measurable.indicator ?_ measurableSet_ball)).add
      (measurable_one.indicator measurableSet_closedBall)
    exact ENNReal.measurable_ofReal.comp (((measurable_id.sub measurable_const).norm.max measurable_const).pow_const 2).inv
  have hgint : ∀ j l, ∫⁻ y, g j l y ≤ ENNReal.ofReal (b * s + v) := by
    intro j l
    simp only [g]
    set q := rootCentre (Z j) w l
    have hu : Measurable fun y : ℂ => (ball q (4 * h)).indicator
        (fun y' => ENNReal.ofReal ((max ‖y' - q‖ m ^ 2)⁻¹)) y :=
      Measurable.indicator (ENNReal.measurable_ofReal.comp
        (((measurable_id.sub measurable_const).norm.max measurable_const).pow_const 2).inv) measurableSet_ball
    have hbu : Measurable fun y : ℂ => ENNReal.ofReal b * (ball q (4 * h)).indicator
        (fun y' => ENNReal.ofReal ((max ‖y' - q‖ m ^ 2)⁻¹)) y := measurable_const.mul hu
    rw [lintegral_add_left hbu, lintegral_const_mul _ hu,
      lintegral_indicator_one measurableSet_closedBall,
      Complex.volume_closedBall, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal b * (∫⁻ y, (ball q (4 * h)).indicator
          (fun y' => ENNReal.ofReal ((max ‖y' - q‖ m ^ 2)⁻¹)) y) +
          ENNReal.ofReal ((M * m) ^ 2 * Real.pi)
        ≤ ENNReal.ofReal b * ENNReal.ofReal s + ENNReal.ofReal v := by
          gcongr
          · have he : (∫⁻ y, (ball q (4 * h)).indicator
                (fun y' => ENNReal.ofReal ((max ‖y' - q‖ m ^ 2)⁻¹)) y) ≤
                ∫⁻ y, (closedBall q (4 * h)).indicator
                  (fun y' => ENNReal.ofReal ((max ‖y' - q‖ m ^ 2)⁻¹)) y :=
              lintegral_mono fun y => indicator_le_indicator_of_subset ball_subset_closedBall
                (fun _ => zero_le) y
            refine he.trans (le_of_eq ?_)
            have hshift : (fun y : ℂ => (closedBall q (4 * h)).indicator
                (fun y' => ENNReal.ofReal ((max ‖y' - q‖ m ^ 2)⁻¹)) y) =
                fun y : ℂ => (closedBall (0 : ℂ) (4 * h)).indicator
                  (fun y' => ENNReal.ofReal ((max ‖y'‖ m ^ 2)⁻¹)) (y - q) := by
              funext y
              by_cases hy : ‖y - q‖ ≤ 4 * h <;>
                simp [Set.indicator, mem_closedBall, dist_eq_norm, hy]
            rw [hshift, lintegral_sub_right_eq_self, lintegral_indicator measurableSet_closedBall]
            rw [show closedBall (0 : ℂ) (4 * h) = {z : ℂ | ‖z‖ ≤ 4 * h} by
              ext z
              simp only [mem_closedBall_zero_iff, mem_ofPred_eq]]
            exact
              RouteLog.lintegral_planar_truncated_inverse_square hm0 hm4
          · exact le_of_eq (by simp only [v]; ring_nf)
      _ = ENNReal.ofReal (b * s + v) := by
          rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_add (by positivity) hv]
  calc ∫⁻ y, rootZ p₀ β lam M ε₀ V Z w y
      ≤ ∫⁻ y, (f₁ y + ∑ j ∈ V, ∑ l : Fin 4, g j l y) :=
        lintegral_mono fun y => rootZ_log_le hlam hlamh hM hV hw y
    _ = (∫⁻ y, f₁ y) + ∑ j ∈ V, ∑ l : Fin 4, ∫⁻ y, g j l y := by
        rw [lintegral_add_left hf₁, lintegral_finsetSum _ fun j _ =>
          Finset.measurable_sum _ fun l _ => hg j l]
        congr 1
        exact sum_congr rfl fun j _ => lintegral_finsetSum _ fun l _ => hg j l
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal a + ∑ _j ∈ V, ∑ _l : Fin 4, ENNReal.ofReal (b * s + v) := by
        gcongr with j _ l _
        · simp only [f₁]
          rw [lintegral_mul_const _ (measurable_one.indicator
            (TwoComponentCoulomb.measurableSet_box N)),
            lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box N),
            TwoComponentCoulomb.volume_box]
        · exact hgint j l
    _ = ENNReal.ofReal (N * a + 4 * V.card * (b * s + v)) := by
        rw [sum_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring

end MultipoleBKT.GeneralExpansion

end
