/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Radial
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.TreeUnion

/-!
# Polar reduction below the largest radius

See (A.12) and (A.13). First use Tonelli with the largest radius fixed. Then
integrate the other dipole vectors in polar coordinates up to that radius.
This gives the literal nested integral, before any temperature estimate.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set Finset Function
open scoped ENNReal

/-- Polar coordinates for a nonnegative radial function on the plane. -/
theorem lintegral_norm_eq (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z : ℂ, f ‖z‖ = ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * f r := by
  have he := TwoComponentCoulomb.lintegral_radial_set univ MeasurableSet.univ f hf
  simp only [mem_univ, ofPred_true, Measure.restrict_univ, indicator_univ] at he
  rw [he, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r _
  ring

/-- The polar integral over a disc, with no change to the regularization
at `λ`. -/
theorem lintegral_radial_disc {lam : ℝ} (hlam : 0 < lam) (a u : ℝ) :
    ∫⁻ z : ℂ, (Metric.closedBall (0 : ℂ) u).indicator
        (fun z => ENNReal.ofReal (max ‖z‖ lam ^ a)) z =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ t in Ioc (0 : ℝ) u, ENNReal.ofReal (t * max t lam ^ a) := by
  let f (t : ℝ) := (Iic u).indicator (fun t => ENNReal.ofReal (max t lam ^ a)) t
  have hf : Measurable f := by
    apply Measurable.indicator _ measurableSet_Iic
    exact ENNReal.measurable_ofReal.comp
      ((continuous_id.max continuous_const).rpow_const
        (fun t => Or.inl (lt_max_of_lt_right hlam).ne')).measurable
  have heq : ∀ z : ℂ, (Metric.closedBall (0 : ℂ) u).indicator
      (fun z => ENNReal.ofReal (max ‖z‖ lam ^ a)) z = f ‖z‖ := by
    intro z
    by_cases hz : ‖z‖ ≤ u <;> simp [f, Metric.mem_closedBall, dist_zero_right, hz]
  simp_rw [heq]
  rw [lintegral_norm_eq f hf]
  congr 1
  have hpt : ∀ t : ℝ, ENNReal.ofReal t * f t =
      (Iic u).indicator (fun t => ENNReal.ofReal (t * max t lam ^ a)) t := by
    intro t
    by_cases ht : t ≤ u
    · dsimp only [f]
      rw [Set.indicator_of_mem (show t ∈ Iic u from ht), Set.indicator_of_mem (show t ∈ Iic u from ht)]
      exact (ENNReal.ofReal_mul' (Real.rpow_nonneg (lt_max_of_lt_right hlam).le _)).symm
    · simp [f, ht]
  simp_rw [hpt]
  rw [setLIntegral_indicator measurableSet_Iic, Set.inter_comm, Ioi_inter_Iic]

/-- Tonelli with a distinguished root. The inner one-variable integral
still depends on the root, rather than being replaced by an independent
moment. -/
theorem lintegral_root_fiber_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (root : ι) {F : ℂ → ℝ≥0∞} (hF : Measurable F)
    {G : ℂ → ℂ → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) :
    ∫⁻ x : ι → ℂ, F (x root) * ∏ c ∈ univ.erase root, G (x c) (x root) =
      ∫⁻ t, F t * (∫⁻ s, G s t) ^ (Fintype.card ι - 1) := by
  let μ : ι → Measure ℂ := fun _ => volume
  let s := univ.erase root
  have hr : root ∉ s := notMem_erase root univ
  have hP : Measurable fun x : ι → ℂ => ∏ c ∈ s, G (x c) (x root) :=
    Finset.measurable_prod _ fun c _ => hG.comp (f := fun x : ι → ℂ => (x c, x root))
      ((measurable_pi_apply c).prodMk (measurable_pi_apply root))
  have hm : Measurable fun x : ι → ℂ => F (x root) * ∏ c ∈ s, G (x c) (x root) :=
    (hF.comp (measurable_pi_apply root)).mul hP
  have hinner : ∀ z : ι → ℂ,
      (∫⋯∫⁻_s, (fun x => F (x root) * ∏ c ∈ s, G (x c) (x root)) ∂μ) z =
      F (z root) * (∫⁻ u, G u (z root)) ^ (Fintype.card ι - 1) := by
    intro z
    rw [lmarginal_mul_left_of_indep (fun x => F (x root)) _ hP
      (fun x y hxy => by rw [hxy root hr])]
    congr 1
    have heq : (∫⋯∫⁻_s, (fun x => ∏ c ∈ s, G (x c) (x root)) ∂μ) z =
        (∫⋯∫⁻_s, (fun x => ∏ c ∈ s, G (x c) (z root)) ∂μ) z := by
      unfold lmarginal
      apply lintegral_congr
      intro w
      apply prod_congr rfl
      intro c _
      simp [Function.updateFinset_def, hr]
    rw [heq, lmarginal_prod_eq (fun c u => G u (z root))
      (fun c => hG.comp (measurable_id.prodMk measurable_const)) s z]
    simp only [μ]
    rw [prod_const, card_erase_of_mem (mem_univ root), card_univ]
  have huniv : insert root s = (univ : Finset ι) := insert_erase (mem_univ root)
  change (∫⁻ x : ι → ℂ, F (x root) * ∏ c ∈ s, G (x c) (x root)) = _
  rw [volume_pi, lintegral_eq_lmarginal_univ (μ := μ) (fun _ => (0 : ℂ)), ← huniv,
    lmarginal_insert _ hm hr]
  simp_rw [hinner, Function.update_self]
  rfl

/-- The ordered sector after the ordering-tree estimate. -/
noncomputable def orderedSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β lam h : ℝ) (root : ι) (x : ι → ℂ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : ℂ) h).indicator
    (fun z => ENNReal.ofReal (max ‖z‖ lam ^ (-β))) (x root) *
      ∏ c ∈ univ.erase root, (Metric.closedBall (0 : ℂ) ‖x root‖).indicator
        (fun z => ENNReal.ofReal (max ‖z‖ lam ^ (2 - β))) (x c)

/-- The exact ordered polar integral (A.13), including all angular factors.
There is no assumption on `β` at this reduction step. -/
theorem lintegral_orderedSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {lam : ℝ} (hlam : 0 < lam) (β h : ℝ) (root : ι) :
    ∫⁻ x : ι → ℂ, orderedSector β lam h root x =
      ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
        orderedRadial β lam (Ioc 0 h) (Fintype.card ι - 1) := by
  let P (a : ℝ) (z : ℂ) := ENNReal.ofReal (max ‖z‖ lam ^ a)
  have hP (a : ℝ) : Measurable (P a) := ENNReal.measurable_ofReal.comp
    ((continuous_norm.max continuous_const).rpow_const
      (fun z => Or.inl (lt_max_of_lt_right hlam).ne')).measurable
  let F := (Metric.closedBall (0 : ℂ) h).indicator (P (-β))
  let G (s t : ℂ) := (Metric.closedBall (0 : ℂ) ‖t‖).indicator (P (2 - β)) s
  have hG : Measurable (Function.uncurry G) := by
    have heq : Function.uncurry G = fun p : ℂ × ℂ =>
        if ‖p.1‖ ≤ ‖p.2‖ then P (2 - β) p.1 else 0 := by
      funext p
      simp [G, Function.uncurry_def, Set.indicator, Metric.mem_closedBall, dist_zero_right]
    rw [heq]
    exact Measurable.ite (measurableSet_le measurable_fst.norm measurable_snd.norm)
      ((hP _).comp measurable_fst) measurable_const
  change (∫⁻ x : ι → ℂ, F (x root) * ∏ c ∈ univ.erase root, G (x c) (x root)) = _
  rw [lintegral_root_fiber_eq root ((hP _).indicator measurableSet_closedBall) hG]
  have hinner (t : ℂ) : ∫⁻ s, G s t = ENNReal.ofReal (2 * Real.pi) * orderedInner β lam ‖t‖ :=
    lintegral_radial_disc hlam (2 - β) ‖t‖
  simp_rw [hinner, mul_pow]
  let q := Fintype.card ι - 1
  have heq : ∀ t : ℂ, F t * (ENNReal.ofReal (2 * Real.pi) ^ q * orderedInner β lam ‖t‖ ^ q) =
      ENNReal.ofReal (2 * Real.pi) ^ q *
        ((Iic h).indicator (fun r => ENNReal.ofReal (max r lam ^ (-β)) * orderedInner β lam r ^ q)) ‖t‖ := by
    intro t
    by_cases ht : ‖t‖ ≤ h
    · simp [F, P, ht, Metric.mem_closedBall, dist_zero_right]
      ring
    · simp [F, P, ht, Metric.mem_closedBall, dist_zero_right]
  change (∫⁻ t, F t * (ENNReal.ofReal (2 * Real.pi) ^ q * orderedInner β lam ‖t‖ ^ q)) = _
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), lintegral_norm_eq]
  · have hpt : ∀ r : ℝ, ENNReal.ofReal r *
        ((Iic h).indicator (fun r => ENNReal.ofReal (max r lam ^ (-β)) * orderedInner β lam r ^ q)) r =
        (Iic h).indicator (fun r => ENNReal.ofReal (r * max r lam ^ (-β)) * orderedInner β lam r ^ q) r := by
      intro r
      by_cases hr : r ≤ h
      · rw [Set.indicator_of_mem (show r ∈ Iic h from hr), Set.indicator_of_mem (show r ∈ Iic h from hr), ← mul_assoc,
          ← ENNReal.ofReal_mul' (Real.rpow_nonneg (lt_max_of_lt_right hlam).le _)]
      · simp [hr]
    simp_rw [hpt]
    rw [setLIntegral_indicator measurableSet_Iic, Set.inter_comm, Ioi_inter_Iic,
      ← mul_assoc, ← pow_succ]
    have hcard : Fintype.card ι - 1 + 1 = Fintype.card ι :=
      Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨root⟩)
    change ENNReal.ofReal (2 * Real.pi) ^ (Fintype.card ι - 1 + 1) *
      orderedRadial β lam (Ioc 0 h) (Fintype.card ι - 1) = _
    rw [hcard]
  · apply Measurable.indicator _ measurableSet_Iic
    exact (ENNReal.measurable_ofReal.comp
      ((continuous_id.max continuous_const).rpow_const
        (fun r => Or.inl (lt_max_of_lt_right hlam).ne')).measurable).mul
      ((orderedInner_mono β lam).measurable.pow_const q)

end MultipoleBKT.MultipoleIntegral

end
