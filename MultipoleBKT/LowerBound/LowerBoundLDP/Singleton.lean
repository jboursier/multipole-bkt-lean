/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.LowerBoundLDP.Bounds
public import MultipoleBKT.LowerBound.LowerBoundLDP.Scales
public import MultipoleBKT.LowerBound.Hierarchical.Model
public import MultipoleBKT.Appendix.GeneralExpansion.RootBound
public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.SquareMoment
import Mathlib.MeasureTheory.Integral.Pi
import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Polar

/-!
# Direct singleton damping in the LDP lower bound

Proposition 4.62,
the display after (4.142). A singleton has no interaction. Its defect is the expectation
of `1 - exp (-L r²/h²)` under the cut dipole probability measure. The inequality
`1 - exp (-t) ≤ t`, planar integration and the radial square moment give a
coefficient chosen before `M`. At the paper's choice `L = β/64` it depends only
on the mollifier, `β`, `p₀` and `ε₀`.
-/

@[expose] public section

namespace MultipoleBKT.LowerBoundLDP

open MeasureTheory Set Finset Filter Topology Metric
open Hierarchical
open MultipoleIntegral (kernelConst exp_smearedKernel_le)
open TwoComponentCoulomb (box)
open scoped ENNReal

variable {χ : ℂ → ℝ}

/-- The singleton partition function is the expectation of its Gaussian damping.
Proposition 4.62, the display after (4.142). -/
theorem minus_singleton_eq_integral (hχ : IsMollifier χ) {N p₀ : ℕ} {β lam ε₀ : ℝ}
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (L M : ℝ) (i : ℕ) :
    minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} =
      ∫ d, gaussianWeight p₀ β lam ε₀ L d ∂cutoffDipoleMeasure χ N p₀ β lam ε₀ := by
  classical
  let := isProbabilityMeasure_cutoffDipoleMeasure (p₀ := p₀) hχ hlam β hε₀ hN
  have : Subsingleton ({i} : Finset ℕ) :=
    Finset.card_le_one_iff_subsingleton_coe.1 (by simp)
  let a : ({i} : Finset ℕ) := ⟨i, mem_singleton_self i⟩
  have hconn (c : ({i} : Finset ℕ) → ℂ × ℂ) :
      (SimpleGraph.fromRel fun u v => MultipoleLinked M lam (c u) (c v)).Connected :=
    (SimpleGraph.connected_iff _).2
      ⟨fun u v => by rw [Subsingleton.elim u v], ⟨a⟩⟩
  have hprod (c : ({i} : Finset ℕ) → ℂ × ℂ) :
      (∏ u, ∏ v, if u < v then
        (if IsStableDipolePair (c u) (c v) then
          Real.exp (-β * upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam) (c u) (c v))
          else 0) else 1) = 1 := by
    apply prod_eq_one
    intro u _
    apply prod_eq_one
    intro v _
    simp [Subsingleton.elim u v]
  rw [minusPartitionFunction, Finset.prod_singleton, modelPartitionFunction]
  simp only [hconn, ↓reduceIte, hprod, one_mul]
  have hp (c : ({i} : Finset ℕ) → ℂ × ℂ) :
      (∏ u, gaussianWeight p₀ β lam ε₀ L (c u)) = gaussianWeight p₀ β lam ε₀ L (c a) := by
    have hu : (Finset.univ : Finset ({i} : Finset ℕ)) = {a} := by
      ext u
      simp only [Finset.mem_univ, Finset.mem_singleton, Subsingleton.elim u a, iff_self]
    rw [hu, Finset.prod_singleton]
  simp_rw [hp]
  apply integral_comp_eval
  exact (by unfold gaussianWeight; fun_prop :
    Measurable (gaussianWeight p₀ β lam ε₀ L)).aestronglyMeasurable

/-- Direct damping defect before radial estimation. Proposition 4.62,
the display after (4.142). The finite-box overlap is bounded by one. -/
theorem singleton_defect_le_plane (hχ : IsMollifier χ) {N p₀ : ℕ} {β lam ε₀ L : ℝ}
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hL : 0 ≤ L) (M : ℝ) (i : ℕ) :
    0 ≤ 1 - minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} ∧
      1 - minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} ≤
        (cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
          (L / (ε₀ * truncationScale p₀ β lam) ^ 2) *
          ∫ w in closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam),
            Real.exp (β * smearedKernel χ lam w) * ‖w‖ ^ 2 := by
  let μ := cutoffDipoleMeasure χ N p₀ β lam ε₀
  let h := ε₀ * truncationScale p₀ β lam
  let ψ := gaussianWeight p₀ β lam ε₀ L
  let f : ℂ → ℝ := (closedBall (0 : ℂ) h).indicator
    (fun w => Real.exp (β * smearedKernel χ lam w) * (1 - Real.exp (-L * (‖w‖ ^ 2 / h ^ 2))))
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hCe : 0 < cutoffDipoleNormalization χ N p₀ β lam ε₀ :=
    (mul_pos_iff_of_pos_left hN0).1 hC
  let := isProbabilityMeasure_cutoffDipoleMeasure (p₀ := p₀) hχ hlam β hε₀ hN
  have hψm : Measurable ψ := by dsimp only [ψ]; unfold gaussianWeight; fun_prop
  have hψ0 (d : ℂ × ℂ) : 0 ≤ ψ d := (Real.exp_pos _).le
  have hψ1 (d : ℂ × ℂ) : ψ d ≤ 1 := by
    apply Real.exp_le_one_iff.2
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hL) (by positivity)
  have hψi : Integrable ψ μ := Integrable.of_bound hψm.aestronglyMeasurable 1
    (Eventually.of_forall fun d => by rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 d)]; exact hψ1 d)
  have hdef : 1 - minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} = ∫ d, (1 - ψ d) ∂μ := by
    rw [minus_singleton_eq_integral hχ hlam hε₀ hN]
    rw [integral_sub (integrable_const 1) hψi, integral_const]
    simp [μ, ψ]
  have hf0 (w : ℂ) : 0 ≤ f w := indicator_nonneg
    (fun w _ => mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hL) (by positivity))))) w
  have hcont : Continuous (fun w : ℂ => Real.exp (β * smearedKernel χ lam w) *
      (1 - Real.exp (-L * (‖w‖ ^ 2 / h ^ 2)))) :=
    (continuous_exp_smearedKernel hχ hlam β).mul (by fun_prop)
  have hfi : Integrable f := (integrable_indicator_iff measurableSet_closedBall).2
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 h))
  have hfm : Measurable f := hcont.measurable.indicator measurableSet_closedBall
  have heq : (∫ d, (1 - ψ d) ∂μ) =
      (cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        ((1 / (N : ℝ)) * ∫ d in box N ×ˢ box N, f (d.1 - d.2)) := by
    change (∫ d, (1 - ψ d) ∂(volume.restrict (box N ×ˢ box N)).withDensity
      (ENNReal.ofReal ∘ fun d : ℂ × ℂ =>
        ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
          (closedBall (0 : ℂ) h).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
            (d.1 - d.2))) = _
    rw [integral_withDensity_eq_integral_toReal_smul
      ((ENNReal.measurable_ofReal.comp ((measurable_cutoffDensity hχ hlam β h).const_mul ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹)))
      (Eventually.of_forall fun d => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul]
    have hp (d : ℂ × ℂ) :
        (ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
          (closedBall (0 : ℂ) h).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
            (d.1 - d.2))).toReal * (1 - ψ d) =
        (N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ * f (d.1 - d.2) := by
      rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hC.le) (cutoffDensity_nonneg β h d))]
      dsimp [f, ψ, gaussianWeight, h]
      by_cases hd : d.1 - d.2 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)
      · simp only [indicator_of_mem hd]; ring
      · simp only [indicator_of_notMem hd, mul_zero, zero_mul]
    simp_rw [Function.comp_apply, hp]
    rw [integral_const_mul]
    field_simp
  rw [hdef]
  refine ⟨integral_nonneg fun d => sub_nonneg.2 (hψ1 d), ?_⟩
  rw [heq]
  have hb := integral_box_prod_sub_le N hfm hf0 hfi
  have hm : IntegrableOn (fun w : ℂ => Real.exp (β * smearedKernel χ lam w) * ‖w‖ ^ 2)
      (closedBall (0 : ℂ) h) :=
    ((continuous_exp_smearedKernel hχ hlam β).mul (by fun_prop)).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 h)
  have hplane : ∫ w, f w ≤ L / h ^ 2 *
      ∫ w in closedBall (0 : ℂ) h, Real.exp (β * smearedKernel χ lam w) * ‖w‖ ^ 2 := by
    rw [show (∫ w, f w) = ∫ w in closedBall (0 : ℂ) h,
      Real.exp (β * smearedKernel χ lam w) * (1 - Real.exp (-L * (‖w‖ ^ 2 / h ^ 2))) from
        integral_indicator measurableSet_closedBall, ← integral_const_mul]
    apply integral_mono (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 h))
      (hm.const_mul _)
    intro w
    have ht := Real.add_one_le_exp (-L * (‖w‖ ^ 2 / h ^ 2))
    have := mul_le_mul_of_nonneg_left (show 1 - Real.exp (-L * (‖w‖ ^ 2 / h ^ 2)) ≤
      L * (‖w‖ ^ 2 / h ^ 2) by linarith only [ht]) (Real.exp_pos (β * smearedKernel χ lam w)).le
    convert this using 1; ring
  exact (mul_le_mul_of_nonneg_left (hb.trans hplane) (inv_nonneg.2 hCe.le)).trans_eq (by ring)

/-- Polar coordinates give the literal cubic radial moment used in the paper.
proof of Proposition 4.62. -/
theorem singleton_square_le_radial (hχ : IsMollifier χ) {β lam h : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) (hh : 0 ≤ h) :
    (∫ w in closedBall (0 : ℂ) h, Real.exp (β * smearedKernel χ lam w) * ‖w‖ ^ 2) ≤
      2 * Real.pi * Real.exp (β * kernelConst χ) *
        ∫ r in (0 : ℝ)..h, r ^ 3 * max r lam ^ (-β) := by
  let g : ℝ → ℝ := fun r => r ^ 2 * max r lam ^ (-β)
  have hg : Continuous g := by
    exact (continuous_id.pow 2).mul ((continuous_id.max continuous_const).rpow_const
      fun r => Or.inl (lt_max_of_lt_right hlam).ne')
  have hc : Continuous (fun r : ℝ => r ^ 3 * max r lam ^ (-β)) :=
    (continuous_id.pow 3).mul ((continuous_id.max continuous_const).rpow_const
      fun r => Or.inl (lt_max_of_lt_right hlam).ne')
  have hpolar : (∫⁻ w in closedBall (0 : ℂ) h, ENNReal.ofReal (g ‖w‖)) =
      ENNReal.ofReal (2 * Real.pi * ∫ r in (0 : ℝ)..h, r ^ 3 * max r lam ^ (-β)) := by
    let f : ℝ → ℝ≥0∞ := (Iic h).indicator (fun r => ENNReal.ofReal (g r))
    have he : (fun w : ℂ => (closedBall (0 : ℂ) h).indicator
        (fun w => ENNReal.ofReal (g ‖w‖)) w) = fun w => f ‖w‖ := by
      funext w
      simp only [f, Set.indicator, mem_closedBall_zero_iff, Set.mem_Iic]
    rw [← lintegral_indicator measurableSet_closedBall, he,
      MultipoleIntegral.lintegral_norm_eq f
        ((ENNReal.measurable_ofReal.comp hg.measurable).indicator measurableSet_Iic)]
    have he' : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * f r =
        (Iic h).indicator (fun r => ENNReal.ofReal (r ^ 3 * max r lam ^ (-β))) r := by
      intro r hr
      by_cases hrh : r ≤ h
      · simp only [f, indicator_of_mem (show r ∈ Iic h from hrh)]
        rw [← ENNReal.ofReal_mul hr.le]
        congr 1
        dsimp only [g]
        ring
      · simp [f, hrh]
    rw [setLIntegral_congr_fun measurableSet_Ioi he', setLIntegral_indicator measurableSet_Iic,
      Set.inter_comm, Ioi_inter_Iic]
    have hint : IntegrableOn (fun r : ℝ => r ^ 3 * max r lam ^ (-β)) (Ioc 0 h) :=
      hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_mem measurableSet_Ioc |>.mono fun r hr => mul_nonneg
        (pow_nonneg hr.1.le 3) (Real.rpow_nonneg (lt_max_of_lt_right hlam).le _)),
      ← intervalIntegral.integral_of_le hh, ← ENNReal.ofReal_mul (by positivity)]
  have hb : (∫⁻ w in closedBall (0 : ℂ) h,
      ENNReal.ofReal (Real.exp (β * smearedKernel χ lam w) * ‖w‖ ^ 2)) ≤
      ENNReal.ofReal (Real.exp (β * kernelConst χ)) *
        ∫⁻ w in closedBall (0 : ℂ) h, ENNReal.ofReal (g ‖w‖) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro w
    dsimp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he := exp_smearedKernel_le hχ hβ hlam w
    dsimp only [g]
    nlinarith only [mul_le_mul_of_nonneg_right he (sq_nonneg ‖w‖)]
  rw [hpolar, ← ENNReal.ofReal_mul (by positivity)] at hb
  have hw : Continuous (fun w : ℂ => Real.exp (β * smearedKernel χ lam w) * ‖w‖ ^ 2) :=
    (continuous_exp_smearedKernel hχ hlam β).mul (by fun_prop)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w =>
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) hw.measurable.aestronglyMeasurable]
  have hr : 0 ≤ ∫ r in (0 : ℝ)..h, r ^ 3 * max r lam ^ (-β) :=
    intervalIntegral.integral_nonneg hh fun r hr => mul_nonneg (pow_nonneg hr.1 3)
      (Real.rpow_nonneg (lt_max_of_lt_right hlam).le _)
  have ht := ENNReal.toReal_le_of_le_ofReal (by positivity) hb
  convert ht using 1; ring

/-- The direct cubic radial defect estimate, before applying (4.12).
Proposition 4.62, the display after (4.142). -/
theorem singleton_defect_le_radial (hχ : IsMollifier χ) {N p₀ : ℕ} {β lam ε₀ L : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hL : 0 ≤ L)
    (M : ℝ) (i : ℕ) :
    0 ≤ 1 - minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} ∧
      1 - minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} ≤
        (cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
          (L / (ε₀ * truncationScale p₀ β lam) ^ 2) *
          (2 * Real.pi * Real.exp (β * kernelConst χ) *
            ∫ r in (0 : ℝ)..(ε₀ * truncationScale p₀ β lam), r ^ 3 * max r lam ^ (-β)) := by
  obtain ⟨h0, hb⟩ := singleton_defect_le_plane hχ hlam hε₀ hN hL M i
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hCe := (mul_pos_iff_of_pos_left hN0).1 hC
  refine ⟨h0, hb.trans (mul_le_mul_of_nonneg_left
    (singleton_square_le_radial hχ hβ hlam
      (mul_nonneg hε₀.le (Appendix.truncationScale_pos hlam).le)) ?_)⟩
  exact mul_nonneg (inv_nonneg.2 hCe.le) (div_nonneg hL (sq_nonneg _))

/-- The radial square moment after the three beta regimes have been evaluated.
proof of Proposition 4.62. -/
theorem singleton_radial_moment_bound {β : ℝ} (hβ : 2 < β)
    (p₀ : ℕ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      lam ≤ ε₀ * truncationScale p₀ β lam →
      (ε₀ * truncationScale p₀ β lam) ^ (-2 : ℝ) *
        (∫ r in (0 : ℝ)..(ε₀ * truncationScale p₀ β lam), r ^ 3 * max r lam ^ (-β)) ≤
        C * lam ^ (2 - β) * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  let σ := GeneralExpansion.tailSigma p₀ β 1
  obtain ⟨C, hC, hb⟩ := GeneralExpansion.radial_moment_zero_power hβ
    (GeneralExpansion.zero_lt_tailSigma (p₀ := p₀) (β := β) (by omega : 1 ≤ 1))
    (GeneralExpansion.four_sub_le_tailSigma (p₀ := p₀) (β := β) (by omega : 1 ≤ 1))
  refine ⟨C * ε₀ ^ (σ - 2), by positivity, fun lam hlam hlam1 hlh => ?_⟩
  let h := ε₀ * truncationScale p₀ β lam
  have hh : 0 < h := hlam.trans_le hlh
  have hm : Continuous (fun t : ℝ => t * max t lam ^ ((4 - β) - 2)) :=
    continuous_id.mul ((continuous_id.max continuous_const).rpow_const
      fun t => Or.inl (lt_max_of_lt_right hlam).ne')
  have hc : Continuous (fun t : ℝ => t ^ 3 * max t lam ^ (-β)) :=
    (continuous_id.pow 3).mul ((continuous_id.max continuous_const).rpow_const
      fun t => Or.inl (lt_max_of_lt_right hlam).ne')
  have hr : (∫ t in (0 : ℝ)..h, t ^ 3 * max t lam ^ (-β)) ≤
      RouteLog.radialLogMoment (4 - β) lam h 0 := by
    simp only [RouteLog.radialLogMoment, pow_zero, mul_one]
    apply intervalIntegral.integral_mono_on hh.le (hc.intervalIntegrable 0 h)
      (hm.intervalIntegrable 0 h)
    intro t ht
    have hp : max t lam ^ ((4 - β) - 2) = max t lam ^ (-β) * max t lam ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add (lt_max_of_lt_right hlam)]
      congr 1
      ring
    rw [hp]
    have hb' := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ ht.1 (le_max_left t lam) 2)
      (mul_nonneg ht.1 (Real.rpow_nonneg (show 0 ≤ max t lam from (lt_max_of_lt_right hlam).le) (-β)))
    nlinarith only [hb']
  have hj : (∫ t in (0 : ℝ)..h, t ^ 3 * max t lam ^ (-β)) ≤
      C * lam ^ (4 - β - σ) * h ^ σ := hr.trans (hb lam h hlam hlh)
  have hp := GeneralExpansion.cut_power_le (p₀ := p₀) (β := β) (by omega : 1 ≤ 1)
    hlam hlam1 hε₀
  simp only [Nat.cast_one, mul_one] at hp
  calc
    _ ≤ h ^ (-2 : ℝ) * (C * lam ^ (4 - β - σ) * h ^ σ) :=
      mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hh.le _)
    _ = C * (lam ^ (4 - β - σ) * h ^ (σ - 2)) := by
      rw [show σ - 2 = (-2 : ℝ) + σ by ring, Real.rpow_add hh]
      ring
    _ ≤ C * (ε₀ ^ (σ - 2) * (lam ^ (2 - β) * truncationScale p₀ β lam ^ (-2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hp hC.le
    _ = _ := by ring

/-- The first displayed singleton bound with `C λ^(β-2)` and the literal cubic
radial integral. The coefficient is quantified before `M`.
Proposition 4.62, the display after (4.142), using (4.12). -/
theorem singleton_damping_radial_bound (hχ : IsMollifier χ) {β : ℝ} (hβ : 2 < β)
    (p₀ : ℕ) {ε₀ L : ℝ} (hε₀ : 0 < ε₀) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (M : ℝ) (i : ℕ),
          0 ≤ 1 - minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} ∧
          1 - minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} ≤
            C * lam ^ (β - 2) * (ε₀ * truncationScale p₀ β lam) ^ (-2 : ℝ) *
              ∫ r in (0 : ℝ)..(ε₀ * truncationScale p₀ β lam), r ^ 3 * max r lam ^ (-β) := by
  obtain ⟨l, hl, hnorm⟩ := lem411_lower hχ hβ hε₀
  let Z := dipoleConstant χ β
  let K := 2 * Real.pi * Real.exp (β * kernelConst χ)
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨2 * L * K / Z + 1, by positivity, min l 1, lt_min hl one_pos,
    min_le_right _ _, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hnorm p₀ lam hlam (hlt.trans_le (min_le_left _ _))).and
    (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN M i => ?_⟩
  obtain ⟨hCe, hN1⟩ := hN₀ N hN
  obtain ⟨h0, hb⟩ := singleton_defect_le_radial hχ (by linarith only [hβ]) hlam hε₀ hN1 hL M i
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hCe0 : 0 < cutoffDipoleNormalization χ N p₀ β lam ε₀ :=
    lt_of_lt_of_le (by positivity) hCe
  have hinv : (cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ≤ 2 / (Z * lam ^ (2 - β)) := by
    apply (le_div_iff₀ (mul_pos hZ hℓ)).2
    apply (inv_mul_le_iff₀ hCe0).2
    dsimp only [Z]
    linarith only [hCe]
  let h := ε₀ * truncationScale p₀ β lam
  let J := ∫ r in (0 : ℝ)..h, r ^ 3 * max r lam ^ (-β)
  have hh : 0 < h := mul_pos hε₀ (Appendix.truncationScale_pos hlam)
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg hh.le fun r hr =>
    mul_nonneg (pow_nonneg hr.1 3) (Real.rpow_nonneg (lt_max_of_lt_right hlam).le _)
  have he : (lam ^ (2 - β))⁻¹ = lam ^ (β - 2) := by
    rw [← Real.rpow_neg hlam.le]
    congr 1
    ring
  refine ⟨h0, hb.trans ?_⟩
  change (cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ * (L / h ^ 2) * (K * J) ≤ _
  calc
    _ ≤ (2 / (Z * lam ^ (2 - β))) * (L / h ^ 2) * (K * J) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinv (div_nonneg hL (sq_nonneg _))) (mul_nonneg hK.le hJ)
    _ = (2 * L * K / Z) * lam ^ (β - 2) * h ^ (-2 : ℝ) * J := by
      rw [div_eq_mul_inv (2 : ℝ), mul_inv, he, Real.rpow_neg hh.le, Real.rpow_two]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hJ
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hh.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlam.le _)
      exact le_add_of_nonneg_right (by norm_num)

/-- The singleton defect is `O(R̄⁻²)`, with its coefficient and lambda threshold
chosen before `M`. Proposition 4.62, the display after (4.142). -/
theorem singleton_damping_bound (hχ : IsMollifier χ) {β : ℝ} (hβ : 2 < β)
    (p₀ : ℕ) {ε₀ L : ℝ} (hε₀ : 0 < ε₀) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (M : ℝ) (i : ℕ),
          0 ≤ 1 - minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} ∧
          1 - minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} ≤
            C * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  obtain ⟨A, hA, hrad⟩ := singleton_radial_moment_bound hβ p₀ hε₀
  obtain ⟨C, hC, l, hl, hl1, hb⟩ := singleton_damping_radial_bound hχ hβ p₀ hε₀ hL
  refine ⟨C * A, mul_pos hC hA, min l (ε₀ / 2), lt_min hl (by positivity),
    (min_le_left _ _).trans hl1, fun lam hlam hlt => ?_⟩
  have hlam1 : lam ≤ 1 := ((hlt.trans_le (min_le_left _ _)).trans_le hl1).le
  have hlh : lam ≤ ε₀ * truncationScale p₀ β lam := by
    have hr := Appendix.one_le_truncationScale (p₀ := p₀) hβ hlam hlam1
    exact (hlt.trans_le (min_le_right _ _)).le.trans
      ((by linarith only [hε₀] : ε₀ / 2 ≤ ε₀).trans (le_mul_of_one_le_right hε₀.le hr))
  obtain ⟨N₀, hN₀⟩ := hb lam hlam (hlt.trans_le (min_le_left _ _))
  refine ⟨N₀, fun N hN M i => ?_⟩
  obtain ⟨h0, hd⟩ := hN₀ N hN M i
  refine ⟨h0, hd.trans ?_⟩
  have hj := mul_le_mul_of_nonneg_left (hrad lam hlam hlam1 hlh)
    (mul_nonneg hC.le (Real.rpow_nonneg hlam.le (β - 2)))
  have he : lam ^ (β - 2) * lam ^ (2 - β) = 1 := by
    rw [← Real.rpow_add hlam, show β - 2 + (2 - β) = 0 by ring, Real.rpow_zero]
  convert hj using 1
  · ring
  · calc
      C * A * truncationScale p₀ β lam ^ (-2 : ℝ) =
          C * A * truncationScale p₀ β lam ^ (-2 : ℝ) *
            (lam ^ (β - 2) * lam ^ (2 - β)) := by rw [he, mul_one]
      _ = _ := by ring

/-- The logarithm of the singleton factor is `O(R̄⁻²)`, uniformly in `M`.
proof of Proposition 4.62. -/
theorem singleton_damping_log_bound (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    {β : ℝ} (hβ : 2 < β) {ε₀ L : ℝ} (hε₀ : 0 < ε₀) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (M : ℝ) (i : ℕ),
          0 < minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} ∧
          |Real.log (minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}})| ≤
            C * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  obtain ⟨C, hC, l, hl, hl1, hb⟩ := singleton_damping_bound hχ hβ p₀ hε₀ hL
  obtain ⟨l', hl', -, hr⟩ := exists_rpow_neg_two_truncationScale_le hp₀ hβ
    (show 0 < 1 / (2 * (C + 1)) by positivity)
  refine ⟨2 * C, by positivity, min l l', lt_min hl hl', (min_le_left _ _).trans hl1,
    fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hb lam hlam (hlt.trans_le (min_le_left _ _))
  refine ⟨N₀, fun N hN M i => ?_⟩
  obtain ⟨h0, hd⟩ := hN₀ N hN M i
  let R := truncationScale p₀ β lam ^ (-2 : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg (Appendix.truncationScale_pos hlam).le _
  have hsmall : C * R ≤ 1 / 2 := by
    have hpow : (lam ^ 2) ^ (pBeta p₀ β - 1) ≤ 1 := pow_le_one₀ (sq_nonneg _)
      (pow_le_one₀ hlam.le ((hlt.trans_le (min_le_left _ _)).trans_le hl1).le)
    have hr' := (hr lam hlam (hlt.trans_le (min_le_right _ _))).trans
      (mul_le_of_le_one_right (by positivity) hpow)
    have hh : C / (2 * (C + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith only [hC]
    exact (mul_le_mul_of_nonneg_left hr' hC.le).trans (by simpa only [mul_one_div] using hh)
  have hpos : 0 < minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} := by
    linarith only [hd, hsmall]
  have hu : Real.log (minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}}) ≤ 0 :=
    Real.log_nonpos hpos.le (by linarith only [h0])
  have hlower := Real.log_le_log (show 0 < 1 - C * R by linarith only [hsmall])
    (show 1 - C * R ≤ minusPartitionFunction χ N p₀ β lam M ε₀ L {{i}} by linarith only [hd])
  have ht := neg_two_mul_le_log_one_sub (mul_nonneg hC.le hR) hsmall
  refine ⟨hpos, ?_⟩
  rw [abs_of_nonpos hu]
  dsimp only [R] at ht hlower
  linarith only [ht, hlower]

end MultipoleBKT.LowerBoundLDP
