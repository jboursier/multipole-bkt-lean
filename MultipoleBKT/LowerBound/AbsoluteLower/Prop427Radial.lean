/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.RadialCalculation
public import MultipoleBKT.Limits.Radial
public import MultipoleBKT.Limits.TreeIntegral
public import MultipoleBKT.UpperBound.BadPointTypes.Radial
public import MultipoleBKT.Appendix.SmallIntegral.Radial
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Symmetric radial integration for the fixed-group tree bound

The proof of Lemma 4.58, equations (A.68)–(A.69).

Write `ρᵢ = max(rᵢ, λ)` and `k` for the number of labels. In both
radial regimes the missing maximum square is distributed symmetrically:
`∏ ρᵢ² / max ρ² ≤ ∏ ρᵢ^(2 - 2/k)`.

The one-radius bounds split at `λ`. `RouteFixedGroups.RadialCalculation`
identifies the planar moments with the radial moments and applies the
positive and negative bounds. Products of these one-radius integrals
give the uniform estimates for `2 < β < 4` and `β ≥ 4`.

The weight `dipoleWeight` uses dilated radii.
`RoutePosition.sourceWeight` carries the paper's radial power.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open MeasureTheory Set Finset Limits
open scoped ENNReal

variable {lam h a E : ℝ}

/-! ### One dipole -/

/-- `∫_{|u| ≤ λ} |u|^{-a} du ≤ 2π λ^{2-a}/(2-a)` for `0 ≤ a < 2`. -/
theorem lintegral_ball_rpow_neg_le (hlam : 0 < lam) (ha : a < 2) :
    ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) lam).indicator
        (fun u => ENNReal.ofReal (‖u‖ ^ (-a))) u ≤
      ENNReal.ofReal (2 * Real.pi * (lam ^ (2 - a) / (2 - a))) := by
  set f : ℝ → ℝ := (Iic lam).indicator (fun r => r ^ (-a)) with hf
  have hf0 : ∀ r, 0 ≤ r → 0 ≤ f r := fun r hr => by
    simp only [hf]
    by_cases hr' : r ∈ Iic lam
    · rw [Set.indicator_of_mem hr']
      exact Real.rpow_nonneg hr _
    · rw [Set.indicator_of_notMem hr']
  have hpt : ∀ u : ℂ, (Metric.closedBall (0 : ℂ) lam).indicator
      (fun u => ENNReal.ofReal (‖u‖ ^ (-a))) u = ENNReal.ofReal (f ‖u‖) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) lam
    · have hu' : ‖u‖ ∈ Iic lam := by
        rw [Metric.mem_closedBall, dist_zero_right] at hu
        exact hu
      rw [Set.indicator_of_mem hu, hf, Set.indicator_of_mem hu']
    · have hu' : ‖u‖ ∉ Iic lam := by
        rw [Metric.mem_closedBall, dist_zero_right] at hu
        exact hu
      rw [Set.indicator_of_notMem hu, hf, Set.indicator_of_notMem hu', ENNReal.ofReal_zero]
  simp_rw [hpt]
  -- the radial integrand
  have hrad : ∀ r ∈ Ioi (0 : ℝ), f r * r = (Ioc 0 lam).indicator (fun r => r ^ (1 - a)) r := by
    intro r hr
    have hr0 : 0 < r := hr
    by_cases hrl : r ≤ lam
    · have h1 : r ∈ Iic lam := hrl
      have h2 : r ∈ Ioc 0 lam := ⟨hr0, hrl⟩
      simp only [hf, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      rw [show (1 - a) = (-a) + 1 by ring, Real.rpow_add_one hr0.ne']
    · have h1 : r ∉ Iic lam := hrl
      have h2 : r ∉ Ioc 0 lam := fun h => hrl h.2
      simp only [hf, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, zero_mul]
  have hint_rad : IntegrableOn (fun r => (Ioc 0 lam).indicator (fun r => r ^ (1 - a)) r)
      (Ioi 0) := by
    unfold IntegrableOn
    rw [integrable_indicator_iff measurableSet_Ioc]
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := lam) (r := 1 - a)
      (by linarith))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlam.le] at this
    exact this.mono_measure Measure.restrict_le_self
  have hint_rad' : IntegrableOn (fun r => f r * r) (Ioi 0) :=
    hint_rad.congr_fun (fun r hr => (hrad r hr).symm) measurableSet_Ioi
  have hint : Integrable fun u : ℂ => f ‖u‖ := (integrable_fun_norm_complex_iff f).2 hint_rad'
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun u => hf0 _ (norm_nonneg _)),
    integral_fun_norm_complex f]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi hrad, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioi, max_self,
    ← intervalIntegral.integral_of_le hlam.le, integral_rpow (Or.inl (by linarith))]
  rw [show (1 - a) + 1 = 2 - a by ring, Real.zero_rpow (by linarith)]
  ring

/-- `ρ(u)^E (h/|u|)^a ≤ h^a (ρ(u)^{E-a} + λ^E 𝟙_{|u| ≤ λ} |u|^{-a})` for `a > 0`. -/
theorem rho_rpow_mul_le (hlam : 0 < lam) (hh : 0 ≤ h) (ha : 0 < a) (u : ℂ) :
    rho lam u ^ E * (h / ‖u‖) ^ a ≤
      h ^ a * (rho lam u ^ (E - a) +
        lam ^ E * (Metric.closedBall (0 : ℂ) lam).indicator (fun u => ‖u‖ ^ (-a)) u) := by
  have hρ := rho_pos hlam u
  have hind : 0 ≤ (Metric.closedBall (0 : ℂ) lam).indicator (fun u => ‖u‖ ^ (-a)) u :=
    indicator_nonneg (fun _ _ => by positivity) u
  have hrhs : 0 ≤ h ^ a * (rho lam u ^ (E - a) +
      lam ^ E * (Metric.closedBall (0 : ℂ) lam).indicator (fun u => ‖u‖ ^ (-a)) u) := by
    positivity
  rcases (norm_nonneg u).eq_or_lt with h0 | hu0
  · rw [← h0, div_zero, Real.zero_rpow ha.ne', mul_zero]
    exact hrhs
  have hdiv : (h / ‖u‖) ^ a = h ^ a * ‖u‖ ^ (-a) := by
    rw [Real.div_rpow hh hu0.le, Real.rpow_neg hu0.le, div_eq_mul_inv]
  rw [hdiv]
  by_cases hu : lam ≤ ‖u‖
  · have hρu : rho lam u = ‖u‖ := max_eq_left hu
    have h1 : rho lam u ^ E * (h ^ a * ‖u‖ ^ (-a)) = h ^ a * rho lam u ^ (E - a) := by
      rw [hρu, Real.rpow_sub hu0, Real.rpow_neg hu0.le]
      field_simp
    rw [h1]
    refine mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ?_) (by positivity)
    exact mul_nonneg (by positivity) hind
  · push Not at hu
    have hρu : rho lam u = lam := max_eq_right hu.le
    have hmem : u ∈ Metric.closedBall (0 : ℂ) lam := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hu.le
    rw [Set.indicator_of_mem hmem, hρu]
    have : 0 ≤ h ^ a * lam ^ (E - a) := by positivity
    nlinarith [Real.rpow_nonneg hu0.le (-a), Real.rpow_nonneg hh a, Real.rpow_nonneg hlam.le E]

/-- `∫_{|u| ≤ h} ρ(u)^E (h/|u|)^a du ≤ h^a (2π (1 + 1/(E-a+2)) h^{E-a+2} + 2π λ^{E-a+2}/(2-a))`
for `0 < λ ≤ h`, `0 < a < 2` and `E - a + 2 > 0`. -/
theorem lintegral_cutoff_rho_rpow_le_of_pos (hlam : 0 < lam) (hlh : lam ≤ h) (ha : 0 < a)
    (ha2 : a < 2) (hE : 0 < E - a + 2) :
    ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (rho lam u ^ E * (h / ‖u‖) ^ a)) u ≤
      ENNReal.ofReal (h ^ a * (2 * Real.pi * ((1 + 1 / (E - a + 2)) * h ^ (E - a + 2)) +
        lam ^ E * (2 * Real.pi * (lam ^ (2 - a) / (2 - a))))) := by
  have hh : 0 ≤ h := hlam.le.trans hlh
  have hpt : ∀ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (rho lam u ^ E * (h / ‖u‖) ^ a)) u ≤
      ENNReal.ofReal (h ^ a) * ((Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (E - a))) u +
        ENNReal.ofReal (lam ^ E) * (Metric.closedBall (0 : ℂ) lam).indicator
          (fun u => ENNReal.ofReal (‖u‖ ^ (-a))) u) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) h
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      have h1 := rho_rpow_mul_le (E := E) hlam hh ha u
      have h2 : ENNReal.ofReal ((Metric.closedBall (0 : ℂ) lam).indicator
          (fun u => ‖u‖ ^ (-a)) u) = (Metric.closedBall (0 : ℂ) lam).indicator
          (fun u => ENNReal.ofReal (‖u‖ ^ (-a))) u := by
        by_cases hu' : u ∈ Metric.closedBall (0 : ℂ) lam
        · rw [Set.indicator_of_mem hu', Set.indicator_of_mem hu']
        · rw [Set.indicator_of_notMem hu', Set.indicator_of_notMem hu', ENNReal.ofReal_zero]
      refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (Real.rpow_nonneg
        (rho_pos hlam u).le _) (mul_nonneg (by positivity)
          (indicator_nonneg (fun _ _ => by positivity) u)),
        ENNReal.ofReal_mul (by positivity), h2]
      rfl
    · rw [Set.indicator_of_notMem hu]
      exact bot_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hm1 : Measurable fun u : ℂ => (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (E - a))) u :=
    (ENNReal.measurable_ofReal.comp ((continuous_rho lam).measurable.pow_const _)).indicator
      measurableSet_closedBall
  rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hI1 := RouteFixedGroups.planar_max_moment_le_of_pos (E := E - a) hlam hlh
    (by linarith)
  have hI2 := lintegral_ball_rpow_neg_le hlam ha2
  have hA : (0 : ℝ) ≤ 2 * Real.pi * ((1 + 1 / (E - a + 2)) * h ^ (E - a + 2)) := by
    have : 0 < 1 + 1 / (E - a + 2) := by positivity
    positivity
  calc ENNReal.ofReal (h ^ a) * ((∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (E - a))) u) +
        ENNReal.ofReal (lam ^ E) * ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) lam).indicator
          (fun u => ENNReal.ofReal (‖u‖ ^ (-a))) u)
      ≤ ENNReal.ofReal (h ^ a) * (ENNReal.ofReal (2 * Real.pi *
          ((1 + 1 / (E - a + 2)) * h ^ (E - a + 2))) + ENNReal.ofReal (lam ^ E) *
          ENNReal.ofReal (2 * Real.pi * (lam ^ (2 - a) / (2 - a)))) := by
        refine mul_le_mul' le_rfl (add_le_add ?_ (mul_le_mul' le_rfl hI2))
        convert hI1 using 4
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hA (by
          have : 0 < 2 - a := by linarith
          positivity), ← ENNReal.ofReal_mul (by positivity)]

/-- `∫_{|u| ≤ h} ρ(u)^E (h/|u|)^a du ≤ h^a λ^{E-a+2} 2π (1 + 1/|E-a+2| + 1/(2-a))` for
`0 < λ ≤ h`, `0 < a < 2` and `E - a + 2 < 0`. -/
theorem lintegral_cutoff_rho_rpow_le_of_neg (hlam : 0 < lam) (hlh : lam ≤ h) (ha : 0 < a)
    (ha2 : a < 2) (hE : E - a + 2 < 0) :
    ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (rho lam u ^ E * (h / ‖u‖) ^ a)) u ≤
      ENNReal.ofReal (h ^ a * (lam ^ (E - a + 2) *
        (2 * Real.pi * (1 + 1 / (-(E - a + 2)) + 1 / (2 - a))))) := by
  have hh : 0 ≤ h := hlam.le.trans hlh
  have hpt : ∀ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (rho lam u ^ E * (h / ‖u‖) ^ a)) u ≤
      ENNReal.ofReal (h ^ a) * ((Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (E - a))) u +
        ENNReal.ofReal (lam ^ E) * (Metric.closedBall (0 : ℂ) lam).indicator
          (fun u => ENNReal.ofReal (‖u‖ ^ (-a))) u) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) h
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      have h1 := rho_rpow_mul_le (E := E) hlam hh ha u
      have h2 : ENNReal.ofReal ((Metric.closedBall (0 : ℂ) lam).indicator
          (fun u => ‖u‖ ^ (-a)) u) = (Metric.closedBall (0 : ℂ) lam).indicator
          (fun u => ENNReal.ofReal (‖u‖ ^ (-a))) u := by
        by_cases hu' : u ∈ Metric.closedBall (0 : ℂ) lam
        · rw [Set.indicator_of_mem hu', Set.indicator_of_mem hu']
        · rw [Set.indicator_of_notMem hu', Set.indicator_of_notMem hu', ENNReal.ofReal_zero]
      refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (Real.rpow_nonneg
        (rho_pos hlam u).le _) (mul_nonneg (by positivity)
          (indicator_nonneg (fun _ _ => by positivity) u)),
        ENNReal.ofReal_mul (by positivity), h2]
      rfl
    · rw [Set.indicator_of_notMem hu]
      exact bot_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hm1 : Measurable fun u : ℂ => (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (E - a))) u :=
    (ENNReal.measurable_ofReal.comp ((continuous_rho lam).measurable.pow_const _)).indicator
      measurableSet_closedBall
  rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hI1 : (∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (E - a))) u) ≤
      ENNReal.ofReal (2 * Real.pi * ((1 + 1 / (-(E - a + 2))) * lam ^ (E - a + 2))) := by
    refine (RouteFixedGroups.planar_max_moment_le_of_neg (E := E - a) hlam hlh hE).trans ?_
    apply ENNReal.ofReal_le_ofReal
    gcongr
    norm_num
  have hI2 := lintegral_ball_rpow_neg_le hlam ha2
  have ha2' : 0 < 2 - a := by linarith
  have hA : (0 : ℝ) ≤ 2 * Real.pi * ((1 + 1 / (-(E - a + 2))) * lam ^ (E - a + 2)) := by
    have : 0 < 1 + 1 / (-(E - a + 2)) := by
      have : 0 < -(E - a + 2) := by linarith
      positivity
    positivity
  calc ENNReal.ofReal (h ^ a) * ((∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (E - a))) u) +
        ENNReal.ofReal (lam ^ E) * ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) lam).indicator
          (fun u => ENNReal.ofReal (‖u‖ ^ (-a))) u)
      ≤ ENNReal.ofReal (h ^ a) * (ENNReal.ofReal (2 * Real.pi *
          ((1 + 1 / (-(E - a + 2))) * lam ^ (E - a + 2))) + ENNReal.ofReal (lam ^ E) *
          ENNReal.ofReal (2 * Real.pi * (lam ^ (2 - a) / (2 - a)))) := by
        refine mul_le_mul' le_rfl (add_le_add ?_ (mul_le_mul' le_rfl hI2))
        convert hI1 using 4
    _ = ENNReal.ofReal (h ^ a * (2 * Real.pi *
          ((1 + 1 / (-(E - a + 2))) * lam ^ (E - a + 2)) +
          lam ^ E * (2 * Real.pi * (lam ^ (2 - a) / (2 - a))))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hA (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ = _ := by
        congr 1
        have hl : lam ^ E * lam ^ (2 - a) = lam ^ (E - a + 2) := by
          rw [← Real.rpow_add hlam]
          ring_nf
        rw [show lam ^ E * (2 * Real.pi * (lam ^ (2 - a) / (2 - a))) =
          (lam ^ E * lam ^ (2 - a)) * (2 * Real.pi / (2 - a)) by ring, hl]
        field_simp

/-! ### The dipole weight -/

/-- The weight of one dipole vector after the position integrals (display (A.68)):
`Ψ(u) = e^{β g_λ(u)} 𝟙_{|u| ≤ h} (17 h/|u|)^a`. -/
noncomputable def dipoleWeight (χ : ℂ → ℝ) (β lam h a : ℝ) (u : ℂ) : ℝ :=
  Real.exp (β * smearedKernel χ lam u) *
    (Metric.closedBall (0 : ℂ) h).indicator (fun u => (17 * h / ‖u‖) ^ a) u

theorem dipoleWeight_nonneg (χ : ℂ → ℝ) (β lam : ℝ) {h a : ℝ} (hh : 0 ≤ h) (u : ℂ) :
    0 ≤ dipoleWeight χ β lam h a u :=
  mul_nonneg (Real.exp_pos _).le (indicator_nonneg (fun _ _ => by positivity) u)

theorem measurable_dipoleWeight {χ : ℂ → ℝ} (hχ : IsMollifier χ) {lam : ℝ} (hlam : 0 < lam)
    (β h a : ℝ) : Measurable (dipoleWeight χ β lam h a) :=
  (measurable_exp_smearedKernel hχ hlam β).mul
    ((((measurable_const.div measurable_norm).pow_const a)).indicator measurableSet_closedBall)

/-- `Ψ(u) ρ(u)^s ≤ C_χ 17^a 𝟙_{|u| ≤ h} ρ(u)^{s-β} (h/|u|)^a`. -/
theorem dipoleWeight_mul_rpow_le {χ : ℂ → ℝ} {β Cχ lam h a : ℝ} (hlam : 0 < lam) (hh : 0 ≤ h)
    (hCχ : ∀ u : ℂ, Real.exp (β * smearedKernel χ lam u) ≤ Cχ * rho lam u ^ (-β))
    (s : ℝ) (u : ℂ) :
    dipoleWeight χ β lam h a u * rho lam u ^ s ≤
      Cχ * 17 ^ a * (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => rho lam u ^ (s - β) * (h / ‖u‖) ^ a) u := by
  have hρ := rho_pos hlam u
  unfold dipoleWeight
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) h
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    have h17 : (17 * h / ‖u‖) ^ a = 17 ^ a * (h / ‖u‖) ^ a := by
      rw [mul_div_assoc, Real.mul_rpow (by norm_num) (by positivity)]
    rw [h17]
    have hs : rho lam u ^ (s - β) = rho lam u ^ (-β) * rho lam u ^ s := by
      rw [← Real.rpow_add hρ]
      ring_nf
    rw [hs]
    have h1 := hCχ u
    have h2 : 0 ≤ 17 ^ a * (h / ‖u‖) ^ a * rho lam u ^ s := by positivity
    calc Real.exp (β * smearedKernel χ lam u) * (17 ^ a * (h / ‖u‖) ^ a) * rho lam u ^ s
        = Real.exp (β * smearedKernel χ lam u) * (17 ^ a * (h / ‖u‖) ^ a * rho lam u ^ s) := by
          ring
      _ ≤ Cχ * rho lam u ^ (-β) * (17 ^ a * (h / ‖u‖) ^ a * rho lam u ^ s) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero, zero_mul, mul_zero]

/-! ### The product over the dipoles -/

/-- The radius factor `∏ᵢ ρᵢ² / max ρ²` (the right-hand side of eq. (A.67)), with
`ρᵢ = max(|uᵢ|, λ)` and `max ρ = SmallIntegral.maxRho λ u`. -/
noncomputable def radiusFactor {ι : Type*} [Fintype ι] (lam : ℝ) (u : ι → ℂ) : ℝ :=
  (∏ i, rho lam (u i) ^ (2 : ℝ)) * SmallIntegral.maxRho lam u ^ (-(2 : ℝ))

theorem radiusFactor_nonneg {ι : Type*} [Fintype ι] {lam : ℝ} (hlam : 0 < lam)
    (u : ι → ℂ) : 0 ≤ radiusFactor lam u :=
  mul_nonneg (prod_nonneg fun _ _ => Real.rpow_nonneg (rho_pos hlam _).le _)
    (Real.rpow_nonneg (SmallIntegral.maxRho_pos hlam u).le _)

/-- `∏ ρᵢ²/max ρ² ≤ ∏ ρᵢ^{2 - 2/k}`. -/
theorem radiusFactor_le {ι : Type*} [Fintype ι] [Nonempty ι] {lam : ℝ} (hlam : 0 < lam)
    (u : ι → ℂ) :
    radiusFactor lam u ≤ ∏ i, rho lam (u i) ^ (2 - 2 / (Fintype.card ι : ℝ)) := by
  unfold radiusFactor
  rw [mul_comm]
  exact prod_rpow_mul_rpow_neg_le (fun i => rho lam (u i)) (fun _ => rho_pos hlam _)
    (fun i => SmallIntegral.rho_le_maxRho lam u i) zero_le_two

/-- **The integral (A.68) for `β ∈ (2,4)`** ((A.68) in the proof of Lemma 4.58): for `k = |ι|` with
`4 - β - 2/k - a ≥ (4-β)/4`, `∫ ∏ᵢ Ψ(uᵢ) ∏ ρᵢ²/max ρ² ≤ (C h^{4-β-2/k})^k`, with `C` depending
only on `χ` and `β`. -/
theorem lintegral_large_lt_four {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β : ℝ} (hβ : 2 < β)
    (hβ4 : β < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam h a : ℝ), 0 < lam → lam ≤ h → 0 < a → a ≤ 1 →
      ∀ {ι : Type} [Fintype ι] [Nonempty ι],
        (4 - β) / 4 ≤ 4 - β - 2 / Fintype.card ι - a →
        ∫⁻ u : ι → ℂ, (∏ i, ENNReal.ofReal (dipoleWeight χ β lam h a (u i))) *
            ENNReal.ofReal (radiusFactor lam u) ≤
          ENNReal.ofReal ((C * h ^ (4 - β - 2 / Fintype.card ι)) ^ Fintype.card ι) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_exp_smearedKernel_le hχ (by linarith : (0 : ℝ) ≤ β)
  have h4β : 0 < 4 - β := by linarith
  set C : ℝ := Cχ * 17 * (2 * Real.pi * (1 + 4 / (4 - β) + 1)) with hC
  refine ⟨C, by positivity, fun lam h a hlam hlh ha ha1 ι _ _ hk => ?_⟩
  classical
  have hh : 0 ≤ h := hlam.le.trans hlh
  set k := Fintype.card ι with hkdef
  set s : ℝ := 2 - 2 / k with hs
  -- the single-dipole integral
  have hsingle : ∫⁻ t : ℂ, ENNReal.ofReal (dipoleWeight χ β lam h a t * rho lam t ^ s) ≤
      ENNReal.ofReal (C * h ^ (4 - β - 2 / k)) := by
    have hpt : ∀ t : ℂ, ENNReal.ofReal (dipoleWeight χ β lam h a t * rho lam t ^ s) ≤
        ENNReal.ofReal (Cχ * 17 ^ a) * (Metric.closedBall (0 : ℂ) h).indicator
          (fun u => ENNReal.ofReal (rho lam u ^ (s - β) * (h / ‖u‖) ^ a)) t := by
      intro t
      refine (ENNReal.ofReal_le_ofReal (dipoleWeight_mul_rpow_le hlam hh (hCχ lam hlam) s t)).trans
        (le_of_eq ?_)
      by_cases ht : t ∈ Metric.closedBall (0 : ℂ) h
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, ENNReal.ofReal_mul (by positivity)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero, mul_zero,
          ENNReal.ofReal_zero]
    have hE : (4 - β) / 4 ≤ s - β - a + 2 := by
      simp only [hs]
      linarith
    have hEpos : 0 < s - β - a + 2 := lt_of_lt_of_le (by positivity) hE
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl (lintegral_cutoff_rho_rpow_le_of_pos (E := s - β) hlam hlh ha
      (by linarith) (by linarith))).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- the algebra
    have hinv : 1 / (s - β - a + 2) ≤ 4 / (4 - β) := by
      rw [div_le_div_iff₀ hEpos h4β]
      linarith
    have h2a : 1 / (2 - a) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hlh' : lam ^ (s - β - a + 2) ≤ h ^ (s - β - a + 2) :=
      Real.rpow_le_rpow hlam.le hlh hEpos.le
    have hl2 : lam ^ (s - β) * (2 * Real.pi * (lam ^ (2 - a) / (2 - a))) =
        lam ^ (s - β - a + 2) * (2 * Real.pi * (1 / (2 - a))) := by
      rw [show s - β - a + 2 = (s - β) + (2 - a) by ring, Real.rpow_add hlam]
      ring
    have hha : h ^ a * h ^ (s - β - a + 2) = h ^ (4 - β - 2 / k) := by
      rw [← Real.rpow_add' hh (by simp only [hs]; linarith)]
      congr 1
      simp only [hs]
      ring
    have h17 : (17 : ℝ) ^ a ≤ 17 := by
      calc (17 : ℝ) ^ a ≤ 17 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
        _ = 17 := Real.rpow_one 17
    rw [hl2]
    have hpos1 : 0 ≤ h ^ (s - β - a + 2) := Real.rpow_nonneg hh _
    have hpos2 : 0 ≤ h ^ a := Real.rpow_nonneg hh _
    calc Cχ * 17 ^ a * (h ^ a * (2 * Real.pi * ((1 + 1 / (s - β - a + 2)) *
          h ^ (s - β - a + 2)) + lam ^ (s - β - a + 2) * (2 * Real.pi * (1 / (2 - a)))))
        ≤ Cχ * 17 * (h ^ a * (2 * Real.pi * ((1 + 4 / (4 - β)) * h ^ (s - β - a + 2)) +
          h ^ (s - β - a + 2) * (2 * Real.pi * 1))) := by
          have hx0 : 0 ≤ 1 / (s - β - a + 2) := by positivity
          have hy0 : 0 ≤ 1 / (2 - a) := by
            have : 0 < 2 - a := by linarith
            positivity
          have hpi := Real.pi_pos
          have hA : 2 * Real.pi * ((1 + 1 / (s - β - a + 2)) * h ^ (s - β - a + 2)) ≤
              2 * Real.pi * ((1 + 4 / (4 - β)) * h ^ (s - β - a + 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hpos1)
              (by positivity)
          have hB : lam ^ (s - β - a + 2) * (2 * Real.pi * (1 / (2 - a))) ≤
              h ^ (s - β - a + 2) * (2 * Real.pi * 1) :=
            mul_le_mul hlh' (mul_le_mul_of_nonneg_left h2a (by positivity)) (by positivity) hpos1
          have hS : 0 ≤ h ^ a * (2 * Real.pi * ((1 + 1 / (s - β - a + 2)) *
              h ^ (s - β - a + 2)) + lam ^ (s - β - a + 2) * (2 * Real.pi * (1 / (2 - a)))) := by
            have : 0 ≤ lam ^ (s - β - a + 2) := Real.rpow_nonneg hlam.le _
            positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left h17 hCχ0.le)
            (mul_le_mul_of_nonneg_left (add_le_add hA hB) hpos2) hS (by positivity)
      _ = C * (h ^ a * h ^ (s - β - a + 2)) := by
          rw [hC]
          ring
      _ = C * h ^ (4 - β - 2 / k) := by rw [hha]
  -- the product
  have hpt : ∀ u : ι → ℂ, (∏ i, ENNReal.ofReal (dipoleWeight χ β lam h a (u i))) *
      ENNReal.ofReal (radiusFactor lam u) ≤
      ∏ i, ENNReal.ofReal (dipoleWeight χ β lam h a (u i) * rho lam (u i) ^ s) := by
    intro u
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => dipoleWeight_nonneg χ β lam hh _),
      ← ENNReal.ofReal_mul (prod_nonneg fun i _ => dipoleWeight_nonneg χ β lam hh _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (dipoleWeight_nonneg χ β lam hh _)
        (Real.rpow_nonneg (rho_pos hlam _).le _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [prod_mul_distrib]
    exact mul_le_mul_of_nonneg_left (radiusFactor_le hlam u)
      (prod_nonneg fun i _ => dipoleWeight_nonneg χ β lam hh _)
  refine (lintegral_mono hpt).trans ?_
  have hmeas : ∀ i : ι, Measurable fun t : ℂ =>
      ENNReal.ofReal (dipoleWeight χ β lam h a t * rho lam t ^ s) := fun i =>
    ENNReal.measurable_ofReal.comp ((measurable_dipoleWeight hχ hlam β h a).mul
      ((continuous_rho lam).measurable.pow_const _))
  rw [volume_pi, lintegral_pi_prod (fun _ : ι => (volume : Measure ℂ))
    (fun _ t => ENNReal.ofReal (dipoleWeight χ β lam h a t * rho lam t ^ s)) hmeas,
    prod_const, card_univ]
  refine (pow_le_pow_left' hsingle k).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_pow (by positivity)]

/-- One dipole for `β ≥ 4`: `∫ Ψ(u) ρ(u)^s du ≤ C_χ 17 · 2π (2 + 1/a) λ^{s+2-β} (h/λ)^a` for
`s - β - a + 2 < 0` and `β - 2 - s ≥ 0` (here `s = 2 - 2/k`). -/
theorem lintegral_dipoleWeight_le_of_neg {χ : ℂ → ℝ} {β Cχ lam h a s : ℝ}
    (hlam : 0 < lam) (hlh : lam ≤ h) (ha : 0 < a) (ha1 : a ≤ 1) (hCχ0 : 0 < Cχ)
    (hCχ : ∀ u : ℂ, Real.exp (β * smearedKernel χ lam u) ≤ Cχ * rho lam u ^ (-β))
    (hs : a ≤ -(s - β - a + 2)) :
    ∫⁻ t : ℂ, ENNReal.ofReal (dipoleWeight χ β lam h a t * rho lam t ^ s) ≤
      ENNReal.ofReal (Cχ * 17 * (2 * Real.pi * (2 + 1 / a)) *
        (lam ^ (s - β + 2) * (h / lam) ^ a)) := by
  have hh : 0 ≤ h := hlam.le.trans hlh
  have hEneg : s - β - a + 2 < 0 := by linarith
  have hpt : ∀ t : ℂ, ENNReal.ofReal (dipoleWeight χ β lam h a t * rho lam t ^ s) ≤
      ENNReal.ofReal (Cχ * 17 ^ a) * (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (rho lam u ^ (s - β) * (h / ‖u‖) ^ a)) t := by
    intro t
    refine (ENNReal.ofReal_le_ofReal (dipoleWeight_mul_rpow_le hlam hh hCχ s t)).trans
      (le_of_eq ?_)
    by_cases ht : t ∈ Metric.closedBall (0 : ℂ) h
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, ENNReal.ofReal_mul (by positivity)]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero, mul_zero,
        ENNReal.ofReal_zero]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl (lintegral_cutoff_rho_rpow_le_of_neg (E := s - β) hlam hlh ha
    (by linarith) hEneg)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hinv : 1 / (-(s - β - a + 2)) ≤ 1 / a := one_div_le_one_div_of_le ha hs
  have h2a : 1 / (2 - a) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h17 : (17 : ℝ) ^ a ≤ 17 := by
    calc (17 : ℝ) ^ a ≤ 17 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
      _ = 17 := Real.rpow_one 17
  have hpow : h ^ a * lam ^ (s - β - a + 2) = lam ^ (s - β + 2) * (h / lam) ^ a := by
    rw [Real.div_rpow hh hlam.le, show s - β - a + 2 = (s - β + 2) - a by ring,
      Real.rpow_sub hlam]
    field_simp
  have hx0 : 0 ≤ 1 / (-(s - β - a + 2)) := by
    have : 0 < -(s - β - a + 2) := by linarith
    positivity
  have hy0 : 0 ≤ 1 / (2 - a) := by
    have : 0 < 2 - a := by linarith
    positivity
  have hP : 0 ≤ lam ^ (s - β + 2) * (h / lam) ^ a := by positivity
  calc Cχ * 17 ^ a * (h ^ a * (lam ^ (s - β - a + 2) * (2 * Real.pi *
        (1 + 1 / (-(s - β - a + 2)) + 1 / (2 - a)))))
      = Cχ * 17 ^ a * (2 * Real.pi * (1 + 1 / (-(s - β - a + 2)) + 1 / (2 - a))) *
          (h ^ a * lam ^ (s - β - a + 2)) := by ring
    _ ≤ Cχ * 17 * (2 * Real.pi * (2 + 1 / a)) * (h ^ a * lam ^ (s - β - a + 2)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h17 hCχ0.le)
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)
          (by positivity)) (by positivity)
    _ = _ := by rw [hpow]

/-- **The integral (A.69) for `β ≥ 4`** ((A.69) in the proof of Lemma 4.58): for `k = |ι| ≥ 1`,
`∫ ∏ᵢ Ψ(uᵢ) ∏ ρᵢ²/max ρ² ≤ (C (2 + 1/a))^k λ^{(4-β)k-2} (h/λ)^{ak}`, `C` depending only on `χ`. -/
theorem lintegral_large_ge_four {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β : ℝ} (hβ4 : 4 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam h a : ℝ), 0 < lam → lam ≤ h → 0 < a → a ≤ 1 →
      ∀ {ι : Type} [Fintype ι] [Nonempty ι],
        ∫⁻ u : ι → ℂ, (∏ i, ENNReal.ofReal (dipoleWeight χ β lam h a (u i))) *
            ENNReal.ofReal (radiusFactor lam u) ≤
          ENNReal.ofReal ((C * (2 + 1 / a)) ^ Fintype.card ι *
            lam ^ ((4 - β) * Fintype.card ι - 2) * (h / lam) ^ (a * Fintype.card ι)) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_exp_smearedKernel_le hχ (by linarith : (0 : ℝ) ≤ β)
  set C : ℝ := Cχ * 17 * (2 * Real.pi) with hC
  refine ⟨C, by positivity, fun lam h a hlam hlh ha ha1 ι _ _ => ?_⟩
  classical
  have hh : 0 ≤ h := hlam.le.trans hlh
  set k := Fintype.card ι with hkdef
  set s : ℝ := 2 - 2 / k with hs
  -- the pointwise bound
  have hpt : ∀ u : ι → ℂ, (∏ i, ENNReal.ofReal (dipoleWeight χ β lam h a (u i))) *
      ENNReal.ofReal (radiusFactor lam u) ≤
      ∏ i, ENNReal.ofReal (dipoleWeight χ β lam h a (u i) * rho lam (u i) ^ s) := by
    intro u
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => dipoleWeight_nonneg χ β lam hh _),
      ← ENNReal.ofReal_mul (prod_nonneg fun i _ => dipoleWeight_nonneg χ β lam hh _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (dipoleWeight_nonneg χ β lam hh _)
        (Real.rpow_nonneg (rho_pos hlam _).le _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [prod_mul_distrib]
    exact mul_le_mul_of_nonneg_left (radiusFactor_le hlam u)
      (prod_nonneg fun i _ => dipoleWeight_nonneg χ β lam hh _)
  refine (lintegral_mono hpt).trans ?_
  have hmeas : ∀ i : ι, Measurable fun t : ℂ =>
      ENNReal.ofReal (dipoleWeight χ β lam h a t * rho lam t ^ s) := fun i =>
    ENNReal.measurable_ofReal.comp ((measurable_dipoleWeight hχ hlam β h a).mul
      ((continuous_rho lam).measurable.pow_const _))
  rw [volume_pi, lintegral_pi_prod (fun _ : ι => (volume : Measure ℂ))
    (fun i t => ENNReal.ofReal (dipoleWeight χ β lam h a t * rho lam t ^ s)) hmeas]
  -- each factor
  have hfac : ∀ _i : ι, ∫⁻ t : ℂ, ENNReal.ofReal (dipoleWeight χ β lam h a t * rho lam t ^ s) ≤
      ENNReal.ofReal (C * (2 + 1 / a) * (lam ^ (s - β + 2) * (h / lam) ^ a)) := by
    intro i
    have hsi : a ≤ -(s - β - a + 2) := by
      dsimp only [s]
      have : (0 : ℝ) ≤ 2 / k := by positivity
      linarith
    have := lintegral_dipoleWeight_le_of_neg hlam hlh ha ha1 hCχ0 (hCχ lam hlam) hsi
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [hC]
    ring
  refine (prod_le_prod fun i _ => hfac i).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_pos.ne' : Fintype.card ι ≠ 0)
  have hsum : ∑ _i : ι, (s - β + 2) = (4 - β) * k - 2 := by
    rw [sum_const, card_univ, ← hkdef, nsmul_eq_mul]
    dsimp only [s]
    field_simp
    ring
  simp_rw [prod_mul_distrib]
  rw [← Real.rpow_sum_of_pos hlam, hsum]
  simp only [prod_const, card_univ, ← hkdef]
  rw [← Real.rpow_natCast ((h / lam) ^ a), ← Real.rpow_mul (by positivity), mul_pow C (2 + 1 / a)]
  ring

end AbsoluteLower

end MultipoleBKT

end
