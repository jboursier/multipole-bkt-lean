/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Definitions
public import MultipoleBKT.Appendix.RouteLog.Root

/-!
# The logarithmic common translation for J_ext

See Lemma A.4. The cap gives the area term.
Each of the four translated endpoints gives a truncated inverse-square integral.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJext

open MeasureTheory Set Finset Metric Limits MultipoleIntegral UpperBound GeneralExpansion
open TwoComponentCoulomb (box)
open scoped ENNReal

variable {N p₀ : ℕ} {β lam ε₀ : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- The capped root gain before evaluating its disc and annular integrals. -/
theorem gainW_log_le {R : ℝ} (hR : 0 < R) (Dbox : Set ℂ) (u t : ℂ) :
    Dbox.indicator 1 t * ENNReal.ofReal (gainW p₀ β lam ε₀ V Z R (t, t + u)) ≤
      Dbox.indicator 1 t *
          ENNReal.ofReal (R ^ 2 / (16 * (ε₀ * truncationScale p₀ β lam) ^ 2)) +
        ∑ j ∈ V, ∑ l : Fin 4, ENNReal.ofReal (R ^ 2) *
          (ball (gainCentre (Z j) u l) (4 * (ε₀ * truncationScale p₀ β lam))).indicator
            (fun y => ENNReal.ofReal ((max ‖y - gainCentre (Z j) u l‖ R ^ 2)⁻¹)) t := by
  classical
  set h := ε₀ * truncationScale p₀ β lam with hh_def
  set e : ℂ × ℂ := (t, t + u) with he
  set D := badDistZ p₀ β lam ε₀ V Z e with hD_def
  have hDcap : D ≤ 4 * h := badDistZ_le_cap e
  by_cases hD : 4 * h ≤ D
  · -- far from the bad charges: the cap
    refine le_add_right ?_
    by_cases ht : t ∈ Dbox
    · rw [indicator_of_mem ht, Pi.one_apply, one_mul, one_mul]
      refine ENNReal.ofReal_le_ofReal ?_
      have hD4 : D = 4 * h := le_antisymm hDcap hD
      unfold gainW
      rw [← hD_def, hD4]
      refine (min_le_right _ _).trans (le_of_eq ?_)
      ring
    · rw [indicator_of_notMem ht, zero_mul, zero_mul]
  · -- near a bad charge
    push Not at hD
    refine le_add_left ?_
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
    obtain ⟨l, hl⟩ := exists_dipoleDist_gain_eq (Z j) u t
    set q := gainCentre (Z j) u l
    have hDq : D = ‖t - q‖ := hDj.trans hl
    have hmem : t ∈ ball q (4 * h) := by
      rw [mem_ball, dist_eq_norm, ← hDq]
      exact hD
    have hle1 : Dbox.indicator 1 t * ENNReal.ofReal (gainW p₀ β lam ε₀ V Z R e) ≤
        ENNReal.ofReal (gainW p₀ β lam ε₀ V Z R e) := by
      by_cases ht : t ∈ Dbox
      · rw [indicator_of_mem ht, Pi.one_apply, one_mul]
      · rw [indicator_of_notMem ht, zero_mul]; exact zero_le
    refine hle1.trans ?_
    refine le_trans ?_ (single_le_sum (f := fun j => ∑ l : Fin 4, ENNReal.ofReal (R ^ 2) *
        (ball (gainCentre (Z j) u l) (4 * h)).indicator
          (fun y => ENNReal.ofReal ((max ‖y - gainCentre (Z j) u l‖ R ^ 2)⁻¹)) t)
      (fun _ _ => zero_le) hjV)
    refine le_trans ?_ (single_le_sum (fun _ _ => zero_le) (mem_univ l))
    rw [indicator_of_mem hmem, ← ENNReal.ofReal_mul (sq_nonneg R)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold gainW
    rw [← hD_def, hDq]
    rcases le_total ‖t - q‖ R with hdR | hRd
    · rw [max_eq_right hdR, mul_inv_cancel₀ (sq_pos_of_pos hR).ne']
      exact min_le_left _ _
    · rw [max_eq_left hRd, ← div_eq_mul_inv]
      exact min_le_right _ _

/-- The common translation retains its logarithm. The coefficient of `V.card`
is uniform in the cutoff. -/
theorem lintegral_gainW_shift_log_le (hh : 0 < ε₀ * truncationScale p₀ β lam) {R : ℝ} (hR : 0 < R)
    (hRh : R ≤ ε₀ * truncationScale p₀ β lam) (v u : ℂ) :
    ∫⁻ t, (box N).indicator 1 t * ENNReal.ofReal (gainW p₀ β lam ε₀ V Z R (t + v, t + v + u)) ≤
      ENNReal.ofReal (N * (R ^ 2 / (16 * (ε₀ * truncationScale p₀ β lam) ^ 2)) +
        4 * V.card * (R ^ 2 *
          (2 * Real.pi * (1 / 2 + Real.log (4 * (ε₀ * truncationScale p₀ β lam) / R))))) := by
  set h := ε₀ * truncationScale p₀ β lam with hh_def
  set A : ℝ := R ^ 2 / (16 * h ^ 2)
  set b : ℝ := R ^ 2
  set s : ℝ := 2 * Real.pi * (1 / 2 + Real.log (4 * h / R))
  have hA : 0 ≤ A := by positivity
  have hb : 0 ≤ b := sq_nonneg R
  have hR4 : R ≤ 4 * h := by dsimp only [h]; linarith
  have hs : 0 ≤ s := by
    have := Real.log_nonneg ((one_le_div hR).2 hR4)
    dsimp only [s]
    positivity
  set f₁ : ℂ → ℝ≥0∞ := fun t => (box N).indicator 1 t * ENNReal.ofReal A
  set g : Fin N → Fin 4 → ℂ → ℝ≥0∞ := fun j l t =>
    ENNReal.ofReal b * (ball ((gainCentre (Z j) u l - v)) (4 * h)).indicator
      (fun y => ENNReal.ofReal ((max ‖y - (gainCentre (Z j) u l - v)‖ R ^ 2)⁻¹)) t
  have hf₁ : Measurable f₁ :=
    (measurable_one.indicator (TwoComponentCoulomb.measurableSet_box N)).mul measurable_const
  have hg : ∀ j l, Measurable (g j l) := by
    intro j l
    refine measurable_const.mul (Measurable.indicator ?_ measurableSet_ball)
    exact ENNReal.measurable_ofReal.comp (((measurable_id.sub measurable_const).norm.max measurable_const).pow_const 2).inv
  have hgint : ∀ j l, ∫⁻ t, g j l t ≤ ENNReal.ofReal (b * s) := by
    intro j l
    simp only [g]
    have hu : Measurable fun t : ℂ => (ball ((gainCentre (Z j) u l - v)) (4 * h)).indicator
        (fun y => ENNReal.ofReal ((max ‖y - (gainCentre (Z j) u l - v)‖ R ^ 2)⁻¹)) t :=
      Measurable.indicator (ENNReal.measurable_ofReal.comp
        (((measurable_id.sub measurable_const).norm.max measurable_const).pow_const 2).inv) measurableSet_ball
    rw [lintegral_const_mul _ hu, ENNReal.ofReal_mul hb]
    gcongr
    rw [lintegral_indicator measurableSet_ball]
    have hsub : ball ((gainCentre (Z j) u l - v)) (4 * h) ⊆
        {y : ℂ | ‖y - (gainCentre (Z j) u l - v)‖ ≤ 4 * h} :=
      fun y hy => by
        change ‖y - (gainCentre (Z j) u l - v)‖ ≤ 4 * h
        simpa only [dist_eq_norm] using (mem_ball.mp hy).le
    have ht := lintegral_mono_set (μ := volume) hsub
      (f := fun y : ℂ => ENNReal.ofReal ((max ‖y - (gainCentre (Z j) u l - v)‖ R ^ 2)⁻¹))
    refine ht.trans_eq ?_
    have he : (fun y : ℂ => {y : ℂ | ‖y - (gainCentre (Z j) u l - v)‖ ≤ 4 * h}.indicator
        (fun y => ENNReal.ofReal ((max ‖y - (gainCentre (Z j) u l - v)‖ R ^ 2)⁻¹)) y) =
        fun y : ℂ => {y : ℂ | ‖y‖ ≤ 4 * h}.indicator
          (fun y => ENNReal.ofReal ((max ‖y‖ R ^ 2)⁻¹)) (y - (gainCentre (Z j) u l - v)) := by
      funext y
      rfl
    rw [← lintegral_indicator (measurableSet_le (by fun_prop) measurable_const), he,
      lintegral_sub_right_eq_self,
      lintegral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    exact MultipoleBKT.RouteLog.lintegral_planar_truncated_inverse_square hR hR4
  calc ∫⁻ t, (box N).indicator 1 t * ENNReal.ofReal (gainW p₀ β lam ε₀ V Z R (t + v, t + v + u))
      ≤ ∫⁻ t, (f₁ t + ∑ j ∈ V, ∑ l : Fin 4, g j l t) :=
        lintegral_mono fun t => by
          have ht := gainW_log_le (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V) (Z := Z) hR {y : ℂ | y - v ∈ box N} u (t + v)
          have heq (q : ℂ) :
              (ball q (4 * h)).indicator
                (fun y => ENNReal.ofReal ((max ‖y - q‖ R ^ 2)⁻¹)) (t + v) =
              (ball (q - v) (4 * h)).indicator
                (fun y => ENNReal.ofReal ((max ‖y - (q - v)‖ R ^ 2)⁻¹)) t := by
            have he : t + v - q = t - (q - v) := by ring
            have hm : t + v ∈ ball q (4 * h) ↔ t ∈ ball (q - v) (4 * h) := by
              simp only [mem_ball, dist_eq_norm, he]
            by_cases htq : t ∈ ball (q - v) (4 * h)
            · rw [indicator_of_mem (hm.mpr htq), indicator_of_mem htq, he]
            · rw [indicator_of_notMem (fun hq => htq (hm.mp hq)), indicator_of_notMem htq]
          have hmem : t + v ∈ {y : ℂ | y - v ∈ box N} ↔ t ∈ box N := by
            change t + v - v ∈ box N ↔ t ∈ box N
            rw [show t + v - v = t by ring]
          have hi : {y : ℂ | y - v ∈ box N}.indicator (1 : ℂ → ℝ≥0∞) (t + v) =
              (box N).indicator 1 t := by
            by_cases htb : t ∈ box N
            · rw [indicator_of_mem (hmem.mpr htb), indicator_of_mem htb]
              rfl
            · rw [indicator_of_notMem (fun hm => htb (hmem.mp hm)), indicator_of_notMem htb]
          rw [hi] at ht
          dsimp only [h] at heq
          simp_rw [heq] at ht
          exact ht
    _ = (∫⁻ t, f₁ t) + ∑ j ∈ V, ∑ l : Fin 4, ∫⁻ t, g j l t := by
        rw [lintegral_add_left hf₁, lintegral_finsetSum _ fun j _ =>
          Finset.measurable_sum _ fun l _ => hg j l]
        congr 1
        exact sum_congr rfl fun j _ => lintegral_finsetSum _ fun l _ => hg j l
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal A + ∑ _j ∈ V, ∑ _l : Fin 4, ENNReal.ofReal (b * s) := by
        gcongr with j _ l _
        · simp only [f₁]
          rw [lintegral_mul_const _ (measurable_one.indicator
            (TwoComponentCoulomb.measurableSet_box N)),
            lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box N),
            TwoComponentCoulomb.volume_box]
        · exact hgint j l
    _ = ENNReal.ofReal (N * A + 4 * V.card * (b * s)) := by
        rw [sum_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring


/-- The root at its own first endpoint. This is the translated estimate with
zero shift, used in the marked-root sum for the full configuration integral. -/
theorem lintegral_gainW_log_le (hh : 0 < ε₀ * truncationScale p₀ β lam) {R : ℝ} (hR : 0 < R)
    (hRh : R ≤ ε₀ * truncationScale p₀ β lam) (u : ℂ) :
    ∫⁻ t, (box N).indicator 1 t * ENNReal.ofReal (gainW p₀ β lam ε₀ V Z R (t, t + u)) ≤
      ENNReal.ofReal (N * (R ^ 2 / (16 * (ε₀ * truncationScale p₀ β lam) ^ 2)) +
        4 * V.card * (R ^ 2 *
          (2 * Real.pi * (1 / 2 + Real.log (4 * (ε₀ * truncationScale p₀ β lam) / R))))) := by
  simpa only [add_zero] using lintegral_gainW_shift_log_le hh hR hRh 0 u (V := V) (Z := Z)

/-- The common-translation logarithmic bound for all dipoles simultaneously.
The translated endpoint count is at most four times the label count times
the bad-dipole count, as in the first display of (A.20), the proof of Lemma A.4. -/
theorem lintegral_common_translation_log_le {W : Type*} [Fintype W] [Nonempty W]
    (hh : 0 < ε₀ * truncationScale p₀ β lam) {R : ℝ} (hR : 0 < R)
    (hRh : R ≤ ε₀ * truncationScale p₀ β lam) (x u : W → ℂ) :
    (∫⁻ t, (box N).indicator 1 t * ENNReal.ofReal
      (min 1 (R ^ 2 / minBadDist p₀ β lam ε₀ V Z (fun i => (t + x i, t + x i + u i)) ^ 2))) ≤
      (Fintype.card W : ℝ≥0∞) * ENNReal.ofReal
        (N * (R ^ 2 / (16 * (ε₀ * truncationScale p₀ β lam) ^ 2)) +
          4 * V.card * (R ^ 2 *
            (2 * Real.pi * (1 / 2 + Real.log (4 * (ε₀ * truncationScale p₀ β lam) / R))))) := by
  classical
  let f (i : W) (t : ℂ) := (box N).indicator (1 : ℂ → ℝ≥0∞) t *
    ENNReal.ofReal (gainW p₀ β lam ε₀ V Z R (t + x i, t + x i + u i))
  have hf (i : W) : Measurable (f i) :=
    (measurable_const.indicator (TwoComponentCoulomb.measurableSet_box N)).mul
      (((measurable_gainW R).comp (by fun_prop)).ennreal_ofReal)
  have hp (t : ℂ) : (box N).indicator 1 t * ENNReal.ofReal
      (min 1 (R ^ 2 / minBadDist p₀ β lam ε₀ V Z (fun i => (t + x i, t + x i + u i)) ^ 2)) ≤ ∑ i, f i t := by
    obtain ⟨j, hj⟩ := exists_minBadDist_eq (p₀ := p₀) (β := β) (lam := lam)
      (ε₀ := ε₀) (V := V) (Z := Z) (fun i => (t + x i, t + x i + u i))
    have hg : min 1 (R ^ 2 / minBadDist p₀ β lam ε₀ V Z
        (fun i => (t + x i, t + x i + u i)) ^ 2) ≤
        ∑ i : W, gainW p₀ β lam ε₀ V Z R (t + x i, t + x i + u i) := by
      rw [hj]
      exact single_le_sum (f := fun i : W => gainW p₀ β lam ε₀ V Z R (t + x i, t + x i + u i))
        (fun i _ => gainW_nonneg _ _) (mem_univ j)
    rw [← mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => gainW_nonneg _ _)]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hg)
  refine (lintegral_mono hp).trans ?_
  rw [lintegral_finsetSum _ (fun i _ => hf i)]
  calc
    _ ≤ ∑ _i : W, ENNReal.ofReal
        (N * (R ^ 2 / (16 * (ε₀ * truncationScale p₀ β lam) ^ 2)) +
          4 * V.card * (R ^ 2 *
            (2 * Real.pi * (1 / 2 + Real.log (4 * (ε₀ * truncationScale p₀ β lam) / R))))) :=
      sum_le_sum fun i _ => lintegral_gainW_shift_log_le hh hR hRh (x i) (u i)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]


end MultipoleBKT.SmallIntegral.RouteJext

end
