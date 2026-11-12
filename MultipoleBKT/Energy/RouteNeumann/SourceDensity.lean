/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.Variational

/-!
# The L² source for the screened Neumann problem

The right side of (3.16) is a bounded density with support in the inner quarter disc.
This module identifies its L² pairing with integration against the two charges.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace

namespace MultipoleBKT.RouteNeumann

variable {χ : ℂ → ℝ} {lam τ : ℝ} {d : ℂ × ℂ}

/-- The real density of a smeared charge. -/
noncomputable def chargeDensity (χ : ℂ → ℝ) (lam : ℝ) (a w : ℂ) : ℝ :=
  (smearedDensity χ a lam w).toReal

/-- A charge density is L² on the bounded screening disc. -/
theorem memLp_chargeDensity (hχ : IsMollifier χ) (hlam : 0 < lam) (a z : ℂ) (τ : ℝ) :
    MemLp (chargeDensity χ lam a) 2 (volume.restrict (ball z τ)) := by
  let : IsFiniteMeasure (volume.restrict (ball z τ)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := volume) (x := z) (r := τ))⟩
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hM0 := hχ.nonneg_of_le hM
  apply MemLp.of_bound ((measurable_smearedDensity hχ a lam).ennreal_toReal.aestronglyMeasurable)
    (M / lam ^ 2)
  filter_upwards with w
  change ‖(smearedDensity χ a lam w).toReal‖ ≤ M / lam ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hle := smearedDensity_le (z := a) hM hlam w
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
    ENNReal.ofReal_ne_top).mpr hle |>.trans_eq (ENNReal.toReal_ofReal (by positivity))

/-- The L² right side of (3.16). -/
noncomputable def sourceLp (hχ : IsMollifier χ) (hlam : 0 < lam) (τ : ℝ) (d : ℂ × ℂ) :
    Lp ℝ 2 (volume.restrict (ball (dipoleMidpoint d) τ)) :=
  (2 * Real.pi) • ((memLp_chargeDensity hχ hlam d.1 (dipoleMidpoint d) τ).toLp
    (chargeDensity χ lam d.1) -
    (memLp_chargeDensity hχ hlam d.2 (dipoleMidpoint d) τ).toLp (chargeDensity χ lam d.2))

/-- L² pairing is integration of the product of the specified representatives. -/
theorem inner_toLp_real {μ : Measure ℂ} {f g : ℂ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ w, f w * g w ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
  simp only [hfw, hgw, RCLike.inner_apply, conj_trivial]
  ring

/-- Pairing a charge density with a test equals integration against that charge.
The support calculation includes every test reaching the boundary. -/
theorem inner_chargeDensity_test (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {a : ℂ}
    (ha : ‖a - dipoleMidpoint d‖ = ‖d.2 - d.1‖ / 2)
    {u : ℂ → ℝ} (hu : MemLp u 2 (volume.restrict (ball (dipoleMidpoint d) τ))) :
    inner ℝ ((memLp_chargeDensity hχ hlam a (dipoleMidpoint d) τ).toLp
      (chargeDensity χ lam a)) (hu.toLp u) = ∫ w, u w ∂smearedCharge χ a lam := by
  rw [inner_toLp_real, smearedCharge_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul (measurable_smearedDensity hχ a lam)
      (Eventually.of_forall fun w => by simp [smearedDensity])]
  simp only [smul_eq_mul]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro w hw
  have hr := norm_le_of_screening hτ
  have hl := lam_le_of_screening hτ
  have ht := pos_of_screening hlam hτ
  have hwa : w ∉ closedBall a lam := by
    intro hw'
    rw [mem_closedBall, dist_eq_norm] at hw'
    apply hw
    rw [mem_ball, dist_eq_norm]
    have := norm_sub_le_norm_sub_add_norm_sub w a (dipoleMidpoint d)
    rw [ha] at this
    linarith
  simp [chargeDensity, smearedDensity_eq_zero hχ hlam hwa]

/-- The variational source is exactly the two smeared charges of (3.16). -/
theorem inner_sourceLp_test (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {u : ℂ → ℝ}
    (hu : MemLp u 2 (volume.restrict (ball (dipoleMidpoint d) τ))) :
    inner ℝ (sourceLp hχ hlam τ d) (hu.toLp u) =
      2 * Real.pi * ((∫ w, u w ∂smearedCharge χ d.1 lam) -
        ∫ w, u w ∂smearedCharge χ d.2 lam) := by
  rw [sourceLp, real_inner_smul_left, inner_sub_left,
    inner_chargeDensity_test hχ hlam hτ (norm_fst_sub_dipoleMidpoint d),
    inner_chargeDensity_test hχ hlam hτ (norm_snd_sub_dipoleMidpoint d)]

end MultipoleBKT.RouteNeumann
