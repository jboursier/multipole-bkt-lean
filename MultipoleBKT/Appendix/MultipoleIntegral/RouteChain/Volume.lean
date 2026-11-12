/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Geometry

/-!
# Exact chain volume and positivity

See (A.15). There are `2k-1` independent endpoint balls and one root square.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral.RouteChain

open MeasureTheory Set Finset
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The chain indicator with the positive root in an arbitrary measurable set. -/
noncomputable def chainWeight (lam : ℝ) (σ : ι ≃ Fin k) (root : ι) (B : Set ℂ)
    (c : ι → ℂ × ℂ) : ℝ≥0∞ :=
  (B.indicator (1 : ℂ → ℝ≥0∞) (c root).1 *
    ∏ i ∈ univ.erase root, (Metric.ball ((9 / 2 * (σ i : ℕ) * lam : ℝ) : ℂ) (lam / 16)).indicator
      (1 : ℂ → ℝ≥0∞) ((c i).1 - (c root).1)) *
    ∏ i, (Metric.ball (((9 / 2 * (σ i : ℕ) + 3 / 2) * lam : ℝ) : ℂ) (lam / 16)).indicator
      (1 : ℂ → ℝ≥0∞) ((c i).2 - (c root).1)

theorem measurable_chainWeight (lam : ℝ) (σ : ι ≃ Fin k) (root : ι) {B : Set ℂ}
    (hB : MeasurableSet B) : Measurable (chainWeight lam σ root B) := by
  unfold chainWeight
  refine (((measurable_const.indicator hB).comp (by fun_prop)).mul ?_).mul ?_
  all_goals
    exact Finset.measurable_prod _ fun i _ =>
      (measurable_const.indicator measurableSet_ball).comp (by fun_prop)

theorem chainWeight_le_one (lam : ℝ) (σ : ι ≃ Fin k) (root : ι) (B : Set ℂ) (c : ι → ℂ × ℂ) :
    chainWeight lam σ root B c ≤ 1 := by
  exact mul_le_one' (mul_le_one' (indicator_one_le_one _ _)
    (prod_le_one fun _ _ => indicator_one_le_one _ _))
    (prod_le_one fun _ _ => indicator_one_le_one _ _)

/-- A nonzero chain indicator gives exactly the paper's chain. -/
theorem chain_of_weight_ne_zero {lam : ℝ} {σ : ι ≃ Fin k} {root : ι} {N : ℕ}
    {c : ι → ℂ × ℂ} (h : chainWeight lam σ root (innerBox N (5 * k * lam)) c ≠ 0) :
    Chain N lam σ root c := by
  obtain ⟨hxy, hy⟩ := mul_ne_zero_iff.mp h
  obtain ⟨hx0, hx⟩ := mul_ne_zero_iff.mp hxy
  rw [prod_ne_zero_iff] at hx hy
  refine ⟨mem_of_indicator_one_ne_zero hx0, ?_, ?_⟩
  · intro i hi
    have := mem_of_indicator_one_ne_zero (hx i (mem_erase.mpr ⟨hi, mem_univ i⟩))
    rw [Metric.mem_ball, dist_eq_norm] at this
    convert this using 1
    dsimp [centre]
    congr 1
    ring
  · intro i
    have := mem_of_indicator_one_ne_zero (hy i (mem_univ i))
    rw [Metric.mem_ball, dist_eq_norm] at this
    convert this using 1
    dsimp [centre]
    congr 1
    push_cast
    ring

omit [DecidableEq ι] in
/-- Fubini in the literal positive and negative endpoint coordinates. -/
theorem lintegral_endpoint_coords {F : (ι → ℂ × ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ c, F c = ∫⁻ x : ι → ℂ, ∫⁻ y : ι → ℂ, F (fun i => (x i, y i)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℂ ℂ ι
  have hmp := measurePreserving_arrowProdEquivProdArrow ℂ ℂ ι (fun _ => (volume : Measure ℂ))
    (fun _ => (volume : Measure ℂ))
  have hvol : (volume : Measure (ι → ℂ × ℂ)) =
      Measure.pi fun _ : ι => (volume : Measure ℂ).prod volume := by rw [volume_pi]; rfl
  have he : ∫⁻ c, F c = ∫⁻ p : (ι → ℂ) × (ι → ℂ), F (e.symm p)
      ∂(Measure.pi fun _ : ι => (volume : Measure ℂ)).prod
        (Measure.pi fun _ : ι => (volume : Measure ℂ)) := by
    rw [hvol, ← hmp.lintegral_comp_emb e.measurableEmbedding]
    simp [e]
  rw [he]
  calc _ = ∫⁻ x : ι → ℂ, ∫⁻ y : ι → ℂ, F (e.symm (x, y))
        ∂Measure.pi (fun _ : ι => (volume : Measure ℂ))
        ∂Measure.pi (fun _ : ι => (volume : Measure ℂ)) :=
      lintegral_prod (fun p => F (e.symm p)) (hF.comp e.symm.measurable).aemeasurable
    _ = _ := by
      rw [← volume_pi]
      rfl

/-- The Jacobian-one star coordinates evaluate the chain volume exactly. -/
theorem lintegral_chainWeight {lam : ℝ} (hlam : 0 ≤ lam) (σ : ι ≃ Fin k) (root : ι)
    {B : Set ℂ} (hB : MeasurableSet B) :
    ∫⁻ c, chainWeight lam σ root B c =
      volume B * ENNReal.ofReal (Real.pi * (lam / 16) ^ 2) ^ (2 * Fintype.card ι - 1) := by
  let V := ENNReal.ofReal (Real.pi * (lam / 16) ^ 2)
  let A (i : ι) := Metric.ball ((9 / 2 * (σ i : ℕ) * lam : ℝ) : ℂ) (lam / 16)
  let D (i : ι) := Metric.ball (((9 / 2 * (σ i : ℕ) + 3 / 2) * lam : ℝ) : ℂ) (lam / 16)
  have hv (i : ι) (X : ℂ) : ∫⁻ y : ℂ, (D i).indicator (1 : ℂ → ℝ≥0∞) (y - X) = V := by
    rw [lintegral_sub_right_eq_self, lintegral_indicator_one measurableSet_ball,
      volume_ball_eq _ (by positivity)]
  have hx : Measurable (fun x : ι → ℂ => B.indicator (1 : ℂ → ℝ≥0∞) (x root) *
      ∏ i ∈ univ.erase root, (A i).indicator (1 : ℂ → ℝ≥0∞) (x i - x root)) := by
    refine ((measurable_const.indicator hB).comp (measurable_pi_apply root)).mul ?_
    exact Finset.measurable_prod _ fun i _ =>
      (measurable_const.indicator measurableSet_ball).comp (by fun_prop)
  rw [lintegral_endpoint_coords (measurable_chainWeight lam σ root hB)]
  change (∫⁻ x : ι → ℂ, ∫⁻ y : ι → ℂ,
    (B.indicator (1 : ℂ → ℝ≥0∞) (x root) *
      ∏ i ∈ univ.erase root, (A i).indicator (1 : ℂ → ℝ≥0∞) (x i - x root)) *
      ∏ i, (D i).indicator (1 : ℂ → ℝ≥0∞) (y i - x root)) = _
  have hi (x : ι → ℂ) : (∫⁻ y : ι → ℂ,
      (B.indicator (1 : ℂ → ℝ≥0∞) (x root) *
        ∏ i ∈ univ.erase root, (A i).indicator (1 : ℂ → ℝ≥0∞) (x i - x root)) *
        ∏ i, (D i).indicator (1 : ℂ → ℝ≥0∞) (y i - x root)) =
      (B.indicator (1 : ℂ → ℝ≥0∞) (x root) *
        ∏ i ∈ univ.erase root, (A i).indicator (1 : ℂ → ℝ≥0∞) (x i - x root)) *
        V ^ Fintype.card ι := by
    rw [lintegral_const_mul _ (by
      exact Finset.measurable_prod _ fun i _ =>
        (measurable_const.indicator measurableSet_ball).comp (by fun_prop))]
    rw [lintegral_pi_prod_eq (fun i t => (D i).indicator (1 : ℂ → ℝ≥0∞) (t - x root))
      (fun i => (measurable_const.indicator measurableSet_ball).comp (measurable_id.sub_const _))]
    simp_rw [hv]
    rw [prod_const, card_univ]
  simp_rw [hi]
  rw [lintegral_mul_const _ hx]
  have hpar : IsParentMap root (fun _ => root) :=
    ⟨fun i => if i = root then 0 else 1, fun i hi => by simp [hi]⟩
  have hstar := lintegral_parent_eq hpar
    (fun i t s => (A i).indicator (1 : ℂ → ℝ≥0∞) (t - s))
    (fun i => (measurable_const.indicator measurableSet_ball).comp (measurable_fst.sub measurable_snd))
    (fun _ => V)
    (fun i _ s => by rw [lintegral_sub_right_eq_self, lintegral_indicator_one measurableSet_ball,
      volume_ball_eq _ (by positivity)])
    (B.indicator (1 : ℂ → ℝ≥0∞)) (measurable_const.indicator hB)
  rw [hstar, lintegral_indicator_one hB, prod_const, card_erase_of_mem (mem_univ root), card_univ]
  rw [mul_assoc, ← pow_add]
  congr 2
  have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨root⟩
  omega

/-- The quantitative chain volume in (A.15). -/
theorem chain_volume_lower {lam : ℝ} (hlam : 0 < lam) (σ : ι ≃ Fin k) (root : ι) (N : ℕ)
    (hN : 4 * (5 * k * lam) ≤ Real.sqrt N) :
    ENNReal.ofReal (N / 4) * ENNReal.ofReal (Real.pi * (lam / 16) ^ 2) ^ (2 * k - 1) ≤
      ∫⁻ c, chainWeight lam σ root (innerBox N (5 * k * lam)) c := by
  rw [lintegral_chainWeight hlam.le σ root (measurableSet_innerBox N _), Fintype.card_congr σ,
    Fintype.card_fin]
  exact mul_le_mul' (ofReal_quarter_le_volume_innerBox (by positivity) hN) le_rfl

/-- Chain positivity exported for the limit with one fixed dipole proof. -/
theorem chain_integral_pos {lam : ℝ} (hlam : 0 < lam) (σ : ι ≃ Fin k) (root : ι) {N : ℕ}
    (hN : 0 < N) (hbox : 4 * (5 * k * lam) ≤ Real.sqrt N) :
    0 < ∫⁻ c, chainWeight lam σ root (innerBox N (5 * k * lam)) c := by
  apply lt_of_lt_of_le _ (chain_volume_lower hlam σ root N hbox)
  apply (pos_iff_ne_zero).mpr
  apply mul_ne_zero
  · exact (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < N / 4)).ne'
  · exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by positivity)).ne'

end MultipoleBKT.MultipoleIntegral.RouteChain

end
