/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.SourceDensity
public import MultipoleBKT.Energy.RouteNeumann.GreenAverage

/-!
# Identification and uniqueness of the screened solution

The Green representation and uniqueness argument for (3.16) identify
the existing screened field with the gradient of the Green average in the
finite-energy class. The mean is subtracted from the potential only.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace

namespace MultipoleBKT.RouteNeumann

variable {χ : ℂ → ℝ} {lam τ : ℝ} {d : ℂ × ℂ}

/-- Regularity of the concrete potential near the closed screening disc. -/
theorem contDiffOn_screenedPotential (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ContDiffOn ℝ 1 (screenedPotential χ lam τ d) (ball (dipoleMidpoint d) (2 * τ)) :=
  (contDiff_dipolePotential hχ hlam d).contDiffOn.add
    (contDiffOn_screenedCorrection hlam hτ)

/-- The concrete potential is in L² on the screening disc. -/
theorem memLp_screenedPotential (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    MemLp (screenedPotential χ lam τ d) 2 (volume.restrict (ball (dipoleMidpoint d) τ)) := by
  apply memLp_of_continuousOn_closedBall
  exact (contDiffOn_screenedPotential hχ hlam hτ).continuousOn.mono
    (closedBall_subset_ball (by linarith [pos_of_screening hlam hτ]))

/-- The concrete field has finite energy on the screening disc. -/
theorem memLp_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    MemLp (screenedField χ lam τ d) 2 (volume.restrict (ball (dipoleMidpoint d) τ)) := by
  apply memLp_of_continuousOn_closedBall
  exact (continuousOn_screenedField hχ hlam hτ).mono
    (closedBall_subset_ball (by linarith [pos_of_screening hlam hτ]))

/-- L² pairing of fields is their Dirichlet pairing. -/
theorem inner_toLp_field {μ : Measure ℂ} {F G : ℂ → ℂ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    inner ℝ (hF.toLp F) (hG.toLp G) = ∫ w, inner ℝ (F w) (G w) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with w hFw hGw
  rw [hFw, hGw]

/-- Subtracting the Green average's spatial mean fixes its additive constant,
equation (3.16). -/
noncomputable def normalizedGreenAverage (χ : ℂ → ℝ) (lam τ : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℝ :=
  greenAverage χ lam τ d w - (volume.real (ball (dipoleMidpoint d) τ))⁻¹ *
    ∫ v in ball (dipoleMidpoint d) τ, greenAverage χ lam τ d v

/-- The Green average is L², by its identification with the concrete potential. -/
theorem memLp_greenAverage (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    MemLp (greenAverage χ lam τ d) 2 (volume.restrict (ball (dipoleMidpoint d) τ)) := by
  apply (memLp_screenedPotential hχ hlam hτ).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  exact (greenAverage_eq_screenedPotential hχ hlam hτ
    (by simpa [dist_eq_norm] using (mem_ball.mp hw).le)).symm

/-- The Green gradient is L². The explicit computation is used only for
regularity of the integral, equation (3.19). -/
theorem memLp_greenField (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    MemLp (greenField χ lam τ d) 2 (volume.restrict (ball (dipoleMidpoint d) τ)) := by
  apply (memLp_screenedField hχ hlam hτ).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  exact (greenField_eq_screenedField hχ hlam hτ
    (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le)).symm

/-- The energy pair is constructed from the Green potential and field
integrals, equation (3.19). -/
noncomputable def greenPair (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) : EnergyPair (dipoleMidpoint d) τ :=
  ((memLp_greenAverage hχ hlam hτ).toLp (greenAverage χ lam τ d),
    (memLp_greenField hχ hlam hτ).toLp (greenField χ lam τ d))

/-- The Green pair has a classical extension near the closed disc, by
computing the integral. This step imposes no source equation. -/
theorem greenPair_mem_classicalPairs (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    greenPair hχ hlam hτ ∈ classicalPairs (dipoleMidpoint d) τ := by
  refine ⟨screenedPotential χ lam τ d, screenedField χ lam τ d, 2 * τ,
    by linarith [pos_of_screening hlam hτ], contDiffOn_screenedPotential hχ hlam hτ,
    ?_, memLp_screenedPotential hχ hlam hτ, memLp_screenedField hχ hlam hτ, ?_⟩
  · intro w hw
    exact hasGradientAt_screenedPotential hχ hlam hτ (by simpa [mem_ball, dist_eq_norm] using hw)
  · apply Prod.ext
    · apply Lp.ext
      filter_upwards [(memLp_greenAverage hχ hlam hτ).coeFn_toLp,
        (memLp_screenedPotential hχ hlam hτ).coeFn_toLp,
        ae_restrict_mem measurableSet_ball] with w hwg hwp hw
      exact hwg.trans ((greenAverage_eq_screenedPotential hχ hlam hτ
        (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le)).trans hwp.symm)
    · apply Lp.ext
      filter_upwards [(memLp_greenField hχ hlam hτ).coeFn_toLp,
        (memLp_screenedField hχ hlam hτ).coeFn_toLp,
        ae_restrict_mem measurableSet_ball] with w hwg hwf hw
      exact hwg.trans ((greenField_eq_screenedField hχ hlam hτ
        (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le)).trans hwf.symm)

private theorem green_test (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {V : EnergyPair (dipoleMidpoint d) τ}
    (hV : V ∈ classicalPairs (dipoleMidpoint d) τ) :
    inner ℝ (greenPair hχ hlam hτ).2 V.2 = inner ℝ (sourceLp hχ hlam τ d) V.1 := by
  obtain ⟨φ, F, ρ, hρ, hφ, hgrad, hp, hF, rfl⟩ := hV
  rw [greenPair, inner_toLp_field, inner_sourceLp_test hχ hlam hτ]
  calc (∫ w in ball (dipoleMidpoint d) τ, inner ℝ (greenField χ lam τ d w) (F w)) =
      ∫ w in ball (dipoleMidpoint d) τ, fderiv ℝ φ w (greenField χ lam τ d w) := by
        apply setIntegral_congr_fun measurableSet_ball
        intro w hw
        dsimp only
        rw [(hgrad w (ball_subset_ball hρ.le hw)).hasFDerivAt.fderiv,
          toDual_apply_apply, real_inner_comm]
    _ = _ := integral_greenField_classical hχ hlam hτ hρ hφ

/-- The Green superposition is a finite-energy weak Neumann solution.
Its equation follows from `disc_source`, the Green problem preceding (3.19). -/
theorem greenPair_isWeakSolution (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    IsWeakSolution (dipoleMidpoint d) τ (sourceLp hχ hlam τ d) (greenPair hχ hlam hτ) :=
  ⟨subset_closure (greenPair_mem_classicalPairs hχ hlam hτ),
    fun _ hV => green_test hχ hlam hτ hV⟩

/-- Every finite-energy weak solution has the computed Green gradient,
as in the discussion after (3.19). Identify it by zero Neumann gradient uniqueness. -/
theorem weakSolution_gradient_eq_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {U : EnergyPair (dipoleMidpoint d) τ}
    (hU : IsWeakSolution (dipoleMidpoint d) τ (sourceLp hχ hlam τ d) U) :
    U.2 =ᵐ[volume.restrict (ball (dipoleMidpoint d) τ)] screenedField χ lam τ d := by
  have he := gradient_unique hU (greenPair_isWeakSolution hχ hlam hτ)
  rw [he]
  apply (memLp_greenField hχ hlam hτ).coeFn_toLp.trans
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  exact greenField_eq_screenedField hχ hlam hτ
    (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le)

/-- The represented potential has zero mean on the disc, equation (3.16). -/
theorem integral_normalizedGreenAverage (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ∫ w in ball (dipoleMidpoint d) τ, normalizedGreenAverage χ lam τ d w = 0 := by
  have ht := pos_of_screening hlam hτ
  let : IsFiniteMeasure (volume.restrict (ball (dipoleMidpoint d) τ)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := volume) (x := dipoleMidpoint d) (r := τ))⟩
  have hi := (memLp_greenAverage hχ hlam hτ).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hv : volume.real (ball (dipoleMidpoint d) τ) ≠ 0 := by
    rw [volume_real_ball_complex _ ht.le]
    positivity
  simp only [normalizedGreenAverage]
  rw [integral_sub hi (integrable_const _), setIntegral_const, smul_eq_mul]
  field_simp
  ring

/-- Mean subtraction leaves the Green gradient unchanged, equation (3.19). -/
theorem hasGradientAt_normalizedGreenAverage (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ}
    (hw : w ∈ ball (dipoleMidpoint d) τ) :
    HasGradientAt (normalizedGreenAverage χ lam τ d) (screenedField χ lam τ d w) w := by
  exact (hasGradientAt_greenAverage hχ hlam hτ hw).sub_const _

/-- The zero-mean Green representation belongs to the finite-energy weak
solution class. No boundary testing or density assertion is assumed. -/
theorem exists_normalized_green_solution (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ∃ U : EnergyPair (dipoleMidpoint d) τ,
      IsWeakSolution (dipoleMidpoint d) τ (sourceLp hχ hlam τ d) U ∧
      U.1 =ᵐ[volume.restrict (ball (dipoleMidpoint d) τ)] normalizedGreenAverage χ lam τ d ∧
      U.2 =ᵐ[volume.restrict (ball (dipoleMidpoint d) τ)] screenedField χ lam τ d := by
  have ht := pos_of_screening hlam hτ
  let : IsFiniteMeasure (volume.restrict (ball (dipoleMidpoint d) τ)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := volume) (x := dipoleMidpoint d) (r := τ))⟩
  let c := (volume.real (ball (dipoleMidpoint d) τ))⁻¹ *
    ∫ v in ball (dipoleMidpoint d) τ, greenAverage χ lam τ d v
  let u := normalizedGreenAverage χ lam τ d
  have hu : MemLp u 2 (volume.restrict (ball (dipoleMidpoint d) τ)) :=
    (memLp_greenAverage hχ hlam hτ).sub (memLp_const c)
  let U : EnergyPair (dipoleMidpoint d) τ :=
    (hu.toLp u, (memLp_greenField hχ hlam hτ).toLp (greenField χ lam τ d))
  have hclass : U ∈ classicalPairs (dipoleMidpoint d) τ := by
    let v : ℂ → ℝ := fun w => screenedPotential χ lam τ d w - c
    have hv : MemLp v 2 (volume.restrict (ball (dipoleMidpoint d) τ)) :=
      (memLp_screenedPotential hχ hlam hτ).sub (memLp_const c)
    refine ⟨v, screenedField χ lam τ d, 2 * τ, by linarith,
      (contDiffOn_screenedPotential hχ hlam hτ).sub contDiffOn_const,
      ?_, hv, memLp_screenedField hχ hlam hτ, ?_⟩
    · intro w hw
      exact (hasGradientAt_screenedPotential hχ hlam hτ
        (by simpa [mem_ball, dist_eq_norm] using hw)).sub_const c
    · apply Prod.ext
      · apply Lp.ext
        filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp,
          ae_restrict_mem measurableSet_ball] with w hwu hwv hw
        rw [hwu, hwv]
        dsimp only [u, v, normalizedGreenAverage, c]
        rw [greenAverage_eq_screenedPotential hχ hlam hτ
          (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le)]
      · apply Lp.ext
        filter_upwards [(memLp_greenField hχ hlam hτ).coeFn_toLp,
          (memLp_screenedField hχ hlam hτ).coeFn_toLp,
          ae_restrict_mem measurableSet_ball] with w hwg hwf hw
        exact hwg.trans ((greenField_eq_screenedField hχ hlam hτ
          (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le)).trans hwf.symm)
  refine ⟨U, ⟨subset_closure hclass, fun V hV => green_test hχ hlam hτ hV⟩,
    hu.coeFn_toLp, ?_⟩
  exact weakSolution_gradient_eq_screenedField hχ hlam hτ
    ⟨subset_closure hclass, fun V hV => green_test hχ hlam hτ hV⟩

/-- Every weak solution has the gradient of the zero-mean Green average,
equation (3.19). -/
theorem weakSolution_gradient_eq_greenAverage (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {U : EnergyPair (dipoleMidpoint d) τ}
    (hU : IsWeakSolution (dipoleMidpoint d) τ (sourceLp hχ hlam τ d) U) :
    U.2 =ᵐ[volume.restrict (ball (dipoleMidpoint d) τ)]
      gradient (normalizedGreenAverage χ lam τ d) := by
  apply (weakSolution_gradient_eq_screenedField hχ hlam hτ hU).trans
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  exact (hasGradientAt_normalizedGreenAverage hχ hlam hτ hw).gradient.symm

end MultipoleBKT.RouteNeumann
