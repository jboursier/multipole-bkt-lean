/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.Regularity
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TwoComponentCoulomb.Potential.ElectricDecay
import TwoComponentCoulomb.Potential.Fundamental
import TwoComponentCoulomb.Potential.SmearedCharge

/-!
# The electric potential and field of radial smeared charges

For an admissible mollifier `χ` (`IsMollifier χ`), real charges `dᵢ`, centres `zᵢ` and radii
`αᵢ > 0`, the electric potential of equation (3.2)
(equation (2.55) is the case `αᵢ = λ`) is

`h_α = g * (Σᵢ dᵢ δ_{zᵢ}^{(αᵢ)}) = Σᵢ dᵢ U_{zᵢ,αᵢ}`,   `U_{z,α}(x) = ∫ g(x - y) dδ_z^{(α)}(y)`,

with `g = logKernel` and `δ_z^{(α)} = smearedCharge χ z α`. Since
`U_{z,α}(x) = (g * δ₀^{(α)})(x - z)`, its gradient is the field of the enclosed mass
`smearedField χ α (x - z) = -δ₀^{(α)}(B(0, |x - z|)) (x - z) / |x - z|²`
(`MultipoleBKT.Potential.Regularity`). This file proves that `h_α` is `C¹`
with gradient `electricField χ d z α`, the weak form of
`-Δh_α = 2π Σᵢ dᵢ δ_{zᵢ}^{(αᵢ)}` (equation (3.1); equation (2.56)), and
the decay at infinity of a neutral configuration. The energy identity is in
`MultipoleBKT.Potential.ElectricEnergy`.

* `electricPotential χ d z α`, `electricField χ d z α x = Σᵢ dᵢ smearedField χ αᵢ (x - zᵢ)`.
* `hasGradientAt_integral_logKernel_sub_smearedCharge` : `∇U_{z,α}(x) = smearedField χ α (x - z)`.
* `integral_gradLogKernel_sub_smearedCharge` : **Newton's theorem for the field**,
  `∫ -(x - y) / |x - y|² dδ_z^{(α)}(y) = smearedField χ α (x - z)` (rotation averaging);
  `smearedField_of_lt` : outside `B̄(0, α)` the field is that of a point charge.
* `hasGradientAt_electricPotential`, `gradient_electricPotential`, `contDiff_electricPotential`,
  `continuous_electricField`, `norm_electricField_le` : `∇h_α = electricField χ d z α`, `h_α` is
  `C¹`, and its field is bounded by `Σᵢ |dᵢ| √(π M) / αᵢ` (`M` a bound for `χ`).
* `integral_fderiv_apply_smearedField`, `integral_fderiv_apply_electricField` : the Green identity
  `∫ ∇ξ · ∇h_α = 2π Σᵢ dᵢ ∫ ξ dδ_{zᵢ}^{(αᵢ)}` for `ξ` of class `C¹` with compact support, from the
  point-charge identity of `TwoComponentCoulomb` (`TwoComponentCoulomb.integral_fderiv_apply_gradLogKernel`) by
  Fubini.
* `exists_decay_electric`, `integrable_norm_sq_electricField` : for a neutral configuration
  (`Σᵢ dᵢ = 0`), `|h_α(x)| ≤ C / |x|` and `|∇h_α(x)| ≤ C / |x|²` for `|x|` large, hence
  `|∇h_α|² ∈ L¹`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

/-- The electric potential `h_α = g * (Σᵢ dᵢ δ_{zᵢ}^{(αᵢ)})` (equation (3.2);
equation (2.55), for `αᵢ = λ`), expanded linearly as
`Σᵢ dᵢ ∫ g(x - y) dδ_{zᵢ}^{(αᵢ)}(y)`. -/
noncomputable def electricPotential (χ : ℂ → ℝ) {ι : Type*} [Fintype ι] (d : ι → ℝ) (z : ι → ℂ)
    (α : ι → ℝ) (x : ℂ) : ℝ :=
  ∑ i, d i * ∫ y, logKernel (x - y) ∂smearedCharge χ (z i) (α i)

/-- The electric field `Σᵢ dᵢ ∇(g * δ₀^{(αᵢ)})(x - zᵢ)`; it is `∇h_α`
(`hasGradientAt_electricPotential`). -/
noncomputable def electricField (χ : ℂ → ℝ) {ι : Type*} [Fintype ι] (d : ι → ℝ) (z : ι → ℂ)
    (α : ι → ℝ) (x : ℂ) : ℂ :=
  ∑ i, d i • smearedField χ (α i) (x - z i)

variable {χ : ℂ → ℝ} {α : ℝ}

/-! ### Null spheres and integrability against a smeared charge -/

/-- Circles about the centre are null for `δ_z^{(α)}`: almost every `y` has `|y - z| ≠ r`. -/
theorem ae_norm_sub_ne_smearedCharge (χ : ℂ → ℝ) (z : ℂ) (α r : ℝ) :
    ∀ᵐ y ∂smearedCharge χ z α, ‖y - z‖ ≠ r := by
  have h1 : smearedCharge χ z α (sphere z r) = 0 :=
    smearedCharge_absolutelyContinuous χ z α (Measure.addHaar_sphere volume z r)
  rw [ae_iff]
  have h2 : {y : ℂ | ¬‖y - z‖ ≠ r} = sphere z r := by
    ext y
    simp
  rw [h2]
  exact h1

/-- The point field `y ↦ -(x - y) / |x - y|²` is integrable for `δ_z^{(α)}`, `α > 0`. -/
theorem integrable_gradLogKernel_sub_smearedCharge (hχ : IsMollifier χ) (x z : ℂ) (hα : 0 < α) :
    Integrable (fun y : ℂ => -((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y)) (smearedCharge χ z α) :=
  RouteFlux.integrable_gradLogKernel_sub_smearedCharge hχ x z hα

/-! ### The field of one smeared charge -/

/-- `∇(g * δ₀^{(α)})(u) = δ₀^{(α)}(B(0, |u|)) • (-u / |u|²)`. -/
theorem smearedField_eq_smul (χ : ℂ → ℝ) (α : ℝ) (u : ℂ) :
    smearedField χ α u = (smearedCharge χ 0 α).real (ball 0 ‖u‖) • (-((‖u‖ ^ 2)⁻¹ : ℝ) • u) := by
  rw [smearedField, smul_smul]
  congr 1
  ring

/-- Outside `B̄(0, α)` the field of `δ₀^{(α)}` is that of a unit point charge at `0`. -/
theorem smearedField_of_lt (hχ : IsMollifier χ) (hα : 0 < α) {u : ℂ} (h : α < ‖u‖) :
    smearedField χ α u = -((‖u‖ ^ 2)⁻¹ : ℝ) • u := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  have hnull : smearedCharge χ 0 α (ball 0 ‖u‖)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (closedBall_subset_ball h))
      (smearedCharge_compl_closedBall hχ hα)
  have hm : (smearedCharge χ 0 α).real (ball 0 ‖u‖) = 1 := by
    rw [measureReal_def, (prob_compl_eq_zero_iff measurableSet_ball).1 hnull, ENNReal.toReal_one]
  rw [smearedField_eq_smul, hm, one_smul]

/-- **The field of one smeared charge** (the proof of Lemma 3.1, for a general centre): for `α > 0`
the potential `U_{z,α}(x) = ∫ g(x - y) dδ_z^{(α)}(y) = (g * δ₀^{(α)})(x - z)` is differentiable
everywhere with gradient
`smearedField χ α (x - z) = -δ₀^{(α)}(B(0, |x - z|)) (x - z) / |x - z|²`. -/
theorem hasGradientAt_integral_logKernel_sub_smearedCharge (hχ : IsMollifier χ) (z : ℂ)
    (hα : 0 < α) (x₀ : ℂ) :
    HasGradientAt (fun x => ∫ y, logKernel (x - y) ∂smearedCharge χ z α)
      (smearedField χ α (x₀ - z)) x₀ := by
  have h : (fun x => ∫ y, logKernel (x - y) ∂smearedCharge χ z α) =
      fun x => smearedPotential χ α (x - z) :=
    funext fun x => integral_logKernel_sub_smearedCharge_eq_smearedPotential χ x z α
  rw [h, hasGradientAt_iff_hasFDerivAt]
  have := (hasFDerivAt_smearedPotential hχ hα (x₀ - z)).comp x₀ ((hasFDerivAt_id x₀).sub_const z)
  rw [ContinuousLinearMap.comp_id] at this
  exact this

/-! ### Newton's theorem for the field -/

/-- Rotations about the centre preserve integrability against `δ_z^{(α)}` (vector-valued form). -/
theorem integrable_comp_rotate_smearedCharge_iff' {E : Type*} [NormedAddCommGroup E]
    (hχ : IsMollifier χ) (z : ℂ) (α : ℝ) {u : ℂ} (hu : ‖u‖ = 1) (f : ℂ → E) :
    Integrable (fun y => f (z + u * (y - z))) (smearedCharge χ z α) ↔
      Integrable f (smearedCharge χ z α) := by
  conv_rhs => rw [← map_rotate_smearedCharge hχ z α hu]
  rw [(measurableEmbedding_rotate z hu).integrable_map_iff]
  rfl

/-- `∫_{-π}^{π} f(e^{iθ} w) dθ = ∫_{-π}^{π} f(circleMap 0 |w| θ) dθ` (periodicity). -/
theorem integral_Ioo_comp_exp_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (w : ℂ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, f (Complex.exp (θ * Complex.I) * w) =
      ∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap 0 ‖w‖ θ) := by
  set h : ℝ → E := fun t => f (circleMap 0 ‖w‖ t) with hh
  have hper : Function.Periodic h (2 * Real.pi) := fun t => by
    simp only [hh, periodic_circleMap 0 ‖w‖ t]
  have hfun : ∀ θ : ℝ, f (Complex.exp (θ * Complex.I) * w) = h (θ + Complex.arg w) := by
    intro θ
    have : Complex.exp (θ * Complex.I) * w = circleMap 0 ‖w‖ (θ + Complex.arg w) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
      simp only [circleMap, zero_add, Complex.ofReal_add, add_mul, Complex.exp_add]
      ring
    rw [this]
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simp_rw [hfun]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi,
    intervalIntegral.integral_comp_add_right]
  have h1 := hper.intervalIntegral_add_eq (-Real.pi + Complex.arg w) (-Real.pi)
  have e1 : -Real.pi + Complex.arg w + 2 * Real.pi = Real.pi + Complex.arg w := by ring
  have e2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [e1, e2] at h1
  rw [h1, intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo]

/-- Newton's theorem for the field, with the enclosed mass `δ_z^{(α)}(B(z, |x - z|))`: the
average over `y ∼ δ_z^{(α)}` of the point field `-(x - y) / |x - y|²` is
`δ_z^{(α)}(B(z, |x - z|)) • (-(x - z) / |x - z|²)`. The proof averages over the rotations about `z`,
which preserve `δ_z^{(α)}` since `χ` is radial; the circle average of the point field is the field
of the centre outside the circle and `0` inside. -/
theorem integral_gradLogKernel_sub_smearedCharge_eq_smul (hχ : IsMollifier χ) (x z : ℂ)
    (hα : 0 < α) :
    ∫ y, -((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y) ∂smearedCharge χ z α =
      (smearedCharge χ z α).real (ball z ‖x - z‖) • (-((‖x - z‖ ^ 2)⁻¹ : ℝ) • (x - z)) := by
  have hfin := isFiniteMeasure_smearedCharge hχ z α
  set μ := smearedCharge χ z α with hμ
  set K : ℂ → ℂ := fun w => -((‖w‖ ^ 2)⁻¹ : ℝ) • w with hK
  set f : ℂ → ℂ := fun y => K (x - y) with hf
  set G : ℝ → ℂ → ℂ := fun θ y => K ((x - z) - Complex.exp (θ * Complex.I) * (y - z)) with hG
  have hu : ∀ θ : ℝ, ‖Complex.exp (θ * Complex.I)‖ = 1 := fun θ => Complex.norm_exp_ofReal_mul_I θ
  have hGθ : ∀ θ : ℝ, G θ = fun y => f (z + Complex.exp (θ * Complex.I) * (y - z)) := by
    intro θ
    funext y
    simp only [hG, hf]
    congr 1
    ring
  have hint0 : Integrable f μ := integrable_gradLogKernel_sub_smearedCharge hχ x z hα
  have hrot : ∀ θ : ℝ, ∫ y, G θ y ∂μ = ∫ y, f y ∂μ := fun θ => by
    rw [hGθ θ, integral_comp_rotate_smearedCharge' hχ z α (hu θ)]
  have hGint : ∀ θ : ℝ, Integrable (G θ) μ := fun θ => by
    rw [hGθ θ]
    exact (integrable_comp_rotate_smearedCharge_iff' hχ z α (hu θ) f).2 hint0
  have hGnorm : ∀ θ : ℝ, ∫ y, ‖G θ y‖ ∂μ = ∫ y, ‖f y‖ ∂μ := fun θ => by
    rw [hGθ θ]
    exact integral_comp_rotate_smearedCharge' hχ z α (hu θ) (fun v => ‖f v‖)
  have hmeas : Measurable (Function.uncurry G) :=
    TwoComponentCoulomb.measurable_gradLogKernel.comp
      (by fun_prop : Continuous fun p : ℝ × ℂ =>
        (x - z) - Complex.exp (p.1 * Complex.I) * (p.2 - z)).measurable
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioo (-Real.pi) Real.pi)).prod μ) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun θ => hGint θ, ?_⟩
    simp only [Function.uncurry_apply_pair, hGnorm]
    exact integrable_const _
  have hswap := integral_integral_swap hint
  simp only [hrot] at hswap
  rw [setIntegral_const, Real.volume_real_Ioo, max_eq_left (by linarith [Real.pi_pos]),
    show Real.pi - -Real.pi = 2 * Real.pi by ring] at hswap
  have hin : ∀ᵐ y ∂μ, ∫ θ in Ioo (-Real.pi) Real.pi, G θ y =
      (ball z ‖x - z‖).indicator (fun _ => (2 * Real.pi) • K (x - z)) y := by
    filter_upwards [ae_ne_smearedCharge χ z z α, ae_norm_sub_ne_smearedCharge χ z α ‖x - z‖]
      with y hy hyr
    have hr : 0 < ‖y - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
    simp only [hG]
    rw [integral_Ioo_comp_exp_mul (fun v => K ((x - z) - v)) (y - z)]
    rcases lt_or_gt_of_ne hyr with h | h
    · rw [indicator_of_mem (by rwa [mem_ball, dist_eq_norm])]
      exact TwoComponentCoulomb.integral_Ioo_gradLogKernel_sub_circleMap_of_lt hr h
    · rw [indicator_of_notMem (by rw [mem_ball, dist_eq_norm, not_lt]; exact h.le)]
      exact TwoComponentCoulomb.integral_Ioo_gradLogKernel_sub_circleMap_of_gt hr h
  rw [integral_congr_ae hin, integral_indicator_const _ measurableSet_ball, smul_comm] at hswap
  exact smul_right_injective ℂ (by positivity : (2 * Real.pi) ≠ 0) hswap

/-- **Newton's theorem for the field**: the average over `y ∼ δ_z^{(α)}` of the point field
`-(x - y) / |x - y|²` is the field `smearedField χ α (x - z)` of the enclosed mass. -/
theorem integral_gradLogKernel_sub_smearedCharge (hχ : IsMollifier χ) (x z : ℂ) (hα : 0 < α) :
    ∫ y, -((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y) ∂smearedCharge χ z α = smearedField χ α (x - z) := by
  have h := map_add_right_smearedCharge χ 0 z α
  rw [zero_add] at h
  rw [← h, (measurableEmbedding_addRight z).integral_map]
  have e : ∀ y : ℂ, x - (y + z) = (x - z) - y := fun y => by ring
  simp_rw [e]
  rw [integral_gradLogKernel_sub_smearedCharge_eq_smul hχ (x - z) 0 hα, smearedField_eq_smul,
    sub_zero]

/-! ### The potential and the field of a configuration -/

section Configuration

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-- **`∇h_α = Σᵢ dᵢ ∇(g * δ₀^{(αᵢ)})(· - zᵢ)`** (radii `αᵢ > 0`). -/
theorem hasGradientAt_electricPotential (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i) (x : ℂ) :
    HasGradientAt (electricPotential χ d z α) (electricField χ d z α x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : ∀ i ∈ Finset.univ, HasFDerivAt
      (fun y => d i * ∫ w, logKernel (y - w) ∂smearedCharge χ (z i) (α i))
      (d i • toDual ℝ ℂ (smearedField χ (α i) (x - z i))) x := fun i _ => by
    have := (hasGradientAt_integral_logKernel_sub_smearedCharge hχ (z i) (hα i) x).hasFDerivAt
    simpa using this.const_mul (d i)
  have h2 := HasFDerivAt.fun_sum h
  have e2 : toDual ℝ ℂ (electricField χ d z α x) =
      ∑ i, d i • toDual ℝ ℂ (smearedField χ (α i) (x - z i)) := by
    rw [electricField, map_sum]
    simp_rw [map_smul]
  rw [e2]
  exact h2

/-- `∇h_α(x) · v = ⟪E_α(x), v⟫`. -/
theorem fderiv_electricPotential_apply (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i) (x v : ℂ) :
    fderiv ℝ (electricPotential χ d z α) x v = inner ℝ (electricField χ d z α x) v := by
  rw [(hasGradientAt_electricPotential hχ hα x).hasFDerivAt.fderiv, toDual_apply_apply]

/-- `gradient h_α = E_α`. -/
theorem gradient_electricPotential (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i) (x : ℂ) :
    gradient (electricPotential χ d z α) x = electricField χ d z α x :=
  (hasGradientAt_electricPotential hχ hα x).gradient

/-- The electric field is continuous. -/
theorem continuous_electricField (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i) :
    Continuous (electricField χ d z α) := by
  unfold electricField
  exact continuous_finsetSum _ fun i _ => (continuous_const (y := d i)).smul
    ((continuous_smearedField hχ (hα i)).comp (continuous_sub_right (z i)))

/-- The electric potential is continuous. -/
theorem continuous_electricPotential (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i) :
    Continuous (electricPotential χ d z α) := by
  unfold electricPotential
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_integral_logKernel_sub_smearedCharge hχ (z i) (hα i))

/-- The electric potential is of class `C¹`. -/
theorem contDiff_electricPotential (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i) :
    ContDiff ℝ 1 (electricPotential χ d z α) := by
  refine contDiff_one_iff_fderiv.2
    ⟨fun x => (hasGradientAt_electricPotential hχ hα x).differentiableAt, ?_⟩
  have : fderiv ℝ (electricPotential χ d z α) =
      fun x => toDual ℝ ℂ (electricField χ d z α x) :=
    funext fun x => (hasGradientAt_electricPotential hχ hα x).hasFDerivAt.fderiv
  rw [this]
  exact (toDual ℝ ℂ).continuous.comp (continuous_electricField hχ hα)

/-- **The field is bounded**: `|E_α(x)| ≤ Σᵢ |dᵢ| √(π M) / αᵢ` when `χ ≤ M`. -/
theorem norm_electricField_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hα : ∀ i, 0 < α i) (x : ℂ) :
    ‖electricField χ d z α x‖ ≤ ∑ i, |d i| * (Real.sqrt (Real.pi * M) / α i) := by
  unfold electricField
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_smearedField_le hχ hM (hα i) _) (abs_nonneg _)

end Configuration

/-! ### The Green identity -/

/-- Integrability of `(x, y) ↦ ∇ξ(x) · ∇g(x - y)` for `volume ⊗ δ_z^{(α)}` (`ξ` of class `C¹` with
compact support): domination of `δ_z^{(α)}` by a multiple of Lebesgue measure on a disc reduces it
to the uniform-disc case of `TwoComponentCoulomb`. -/
theorem integrable_fderiv_apply_gradLogKernel_sub_prod_smearedCharge (hχ : IsMollifier χ)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (z : ℂ) (hα : 0 < α) :
    Integrable (fun p : ℂ × ℂ => fderiv ℝ ξ p.1 (-((‖p.1 - p.2‖ ^ 2)⁻¹ : ℝ) • (p.1 - p.2)))
      (volume.prod (smearedCharge χ z α)) :=
  RouteFlux.integrable_fderiv_apply_gradLogKernel_sub_prod_smearedCharge hχ hξ hc z hα

/-- **The Green identity for one smeared charge**: `∫ ∇ξ · ∇U_{z,α} = 2π ∫ ξ dδ_z^{(α)}` for `ξ` of
class `C¹` with compact support, i.e. `-ΔU_{z,α} = 2π δ_z^{(α)}` in the weak sense (equation (3.1); Stokes's formula of Lemma 3.1). -/
theorem integral_fderiv_apply_smearedField (hχ : IsMollifier χ) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (z : ℂ) (hα : 0 < α) :
    ∫ x, fderiv ℝ ξ x (smearedField χ α (x - z)) =
      2 * Real.pi * ∫ y, ξ y ∂smearedCharge χ z α := by
  have h := RouteFlux.weakPoisson_convolvedField hχ hξ hc z hα
  simpa only [RouteFlux.convolvedField, RouteFlux.pointField,
    integral_gradLogKernel_sub_smearedCharge hχ _ z hα] using h

section ConfigurationGreen

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-- **The Green identity for a configuration** (equation (3.1), weak form; no
neutrality needed): `∫ ∇ξ · ∇h_α = 2π Σᵢ dᵢ ∫ ξ dδ_{zᵢ}^{(αᵢ)}` for `ξ` of class `C¹` with
compact support. -/
theorem integral_fderiv_apply_electricField (hχ : IsMollifier χ) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (hα : ∀ i, 0 < α i) :
    ∫ x, fderiv ℝ ξ x (electricField χ d z α x) =
      2 * Real.pi * ∑ i, d i * ∫ y, ξ y ∂smearedCharge χ (z i) (α i) := by
  have h1 : ∀ x : ℂ, fderiv ℝ ξ x (electricField χ d z α x) =
      ∑ i, d i * fderiv ℝ ξ x (smearedField χ (α i) (x - z i)) := fun x => by
    rw [electricField, map_sum]
    simp_rw [map_smul, smul_eq_mul]
  have hint : ∀ i, Integrable (fun x : ℂ => fderiv ℝ ξ x (smearedField χ (α i) (x - z i))) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hξ.continuous_fderiv one_ne_zero).clm_apply
        ((continuous_smearedField hχ (hα i)).comp (continuous_sub_right (z i)))
    · refine (hc.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ ?_
      intro h0
      exact hx (by simp [h0])
  simp_rw [h1]
  rw [integral_finsetSum _ fun i _ => (hint i).const_mul (d i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_fderiv_apply_smearedField hχ hξ hc (z i) (hα i)]
  ring

end ConfigurationGreen

/-! ### Decay of a neutral configuration -/

section Decay

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-- `|-log |x - z| + log |x|| ≤ 2 |z| / |x|` for `2 |z| ≤ |x|`, `x ≠ 0`. -/
theorem abs_neg_log_norm_sub_add_log_le {x z : ℂ} (hz : 2 * ‖z‖ ≤ ‖x‖) (hx : 0 < ‖x‖) :
    |-Real.log ‖x - z‖ + Real.log ‖x‖| ≤ 2 * ‖z‖ / ‖x‖ := by
  have hs : 0 < ‖x - z‖ := by
    have := norm_sub_norm_le x z
    linarith [norm_nonneg z]
  have h := TwoComponentCoulomb.abs_discPotential_add_log_le hs hz hx le_rfl
  rwa [TwoComponentCoulomb.discPotential_of_le hs le_rfl] at h

/-- `|-(x - z)/|x - z|² + x/|x|²| ≤ 2 |z| / |x|²` for `2 |z| ≤ |x|`, `x ≠ 0`. -/
theorem norm_gradLogKernel_sub_sub_le {x z : ℂ} (hz : 2 * ‖z‖ ≤ ‖x‖) (hx : 0 < ‖x‖) :
    ‖-((‖x - z‖ ^ 2)⁻¹ : ℝ) • (x - z) - (-((‖x‖ ^ 2)⁻¹ : ℝ) • x)‖ ≤ 2 * ‖z‖ / ‖x‖ ^ 2 := by
  have h := TwoComponentCoulomb.norm_discField_sub_le (a := 0) hz hx (norm_nonneg _)
  rwa [TwoComponentCoulomb.discField_of_le (norm_nonneg _)] at h

/-- **Decay of a neutral configuration** (`Σᵢ dᵢ = 0`): for `|x|` large, `|h_α(x)| ≤ C / |x|` and
`|∇h_α(x)| ≤ C / |x|²`. Outside all discs `h_α(x) = -Σᵢ dᵢ log |x - zᵢ|` and
`∇h_α(x) = -Σᵢ dᵢ (x - zᵢ) / |x - zᵢ|²` (Newton's theorem); neutrality removes the monopole
terms. -/
theorem exists_decay_electric (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i) (hn : ∑ i, d i = 0) :
    ∃ R₀ C : ℝ, 0 < R₀ ∧ 0 ≤ C ∧ ∀ x : ℂ, R₀ ≤ ‖x‖ →
      |electricPotential χ d z α x| ≤ C / ‖x‖ ∧ ‖electricField χ d z α x‖ ≤ C / ‖x‖ ^ 2 := by
  set S : ℝ := ∑ j, (‖z j‖ + α j) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => add_nonneg (norm_nonneg _) (hα j).le
  have hSi : ∀ i, ‖z i‖ + α i ≤ S := fun i =>
    Finset.single_le_sum (f := fun j => ‖z j‖ + α j)
      (fun j _ => add_nonneg (norm_nonneg _) (hα j).le) (Finset.mem_univ i)
  refine ⟨2 * S + 1, ∑ i, |d i| * (2 * ‖z i‖), by linarith,
    Finset.sum_nonneg fun i _ => by positivity, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := by linarith
  have hzx : ∀ i, 2 * ‖z i‖ ≤ ‖x‖ := fun i => by
    have := hSi i
    have := hα i
    linarith
  have hax : ∀ i, α i < ‖x - z i‖ := fun i => by
    have := hSi i
    have := norm_sub_norm_le x (z i)
    linarith
  constructor
  · have e : electricPotential χ d z α x =
        ∑ i, d i * (-Real.log ‖x - z i‖ + Real.log ‖x‖) := by
      have h0 : ∑ i, d i * Real.log ‖x‖ = 0 := by rw [← Finset.sum_mul, hn, zero_mul]
      simp only [mul_add, Finset.sum_add_distrib, h0, add_zero]
      unfold electricPotential
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_logKernel_sub_smearedCharge_of_le hχ (hα i) (hax i).le]
      rfl
    rw [e, Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (abs_neg_log_norm_sub_add_log_le (hzx i) hxpos) (abs_nonneg _)
  · have e : electricField χ d z α x =
        ∑ i, d i • (-((‖x - z i‖ ^ 2)⁻¹ : ℝ) • (x - z i) - (-((‖x‖ ^ 2)⁻¹ : ℝ) • x)) := by
      have h0 : ∑ i, d i • (-((‖x‖ ^ 2)⁻¹ : ℝ) • x) = 0 := by
        rw [← Finset.sum_smul, hn, zero_smul]
      calc electricField χ d z α x = ∑ i, d i • (-((‖x - z i‖ ^ 2)⁻¹ : ℝ) • (x - z i)) :=
            Finset.sum_congr rfl fun i _ => by rw [smearedField_of_lt hχ (hα i) (hax i)]
        _ = ∑ i, d i • (-((‖x - z i‖ ^ 2)⁻¹ : ℝ) • (x - z i)) -
              ∑ i, d i • (-((‖x‖ ^ 2)⁻¹ : ℝ) • x) := by rw [h0, sub_zero]
        _ = _ := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm
    rw [e, Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (norm_gradLogKernel_sub_sub_le (hzx i) hxpos) (abs_nonneg _)

/-- **Finite Dirichlet energy**: for a neutral configuration `|∇h_α|²` is integrable. -/
theorem integrable_norm_sq_electricField (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i)
    (hn : ∑ i, d i = 0) : Integrable fun x => ‖electricField χ d z α x‖ ^ 2 := by
  obtain ⟨R₀, C, hR₀, hC, hdec⟩ := exists_decay_electric (d := d) (z := z) hχ hα hn
  refine TwoComponentCoulomb.integrable_of_decay ((continuous_electricField hχ hα).norm.pow 2)
    (R₀ := R₀) (C := C ^ 2) (sq_nonneg C) fun x hx => ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  calc ‖electricField χ d z α x‖ ^ 2 ≤ (C / ‖x‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hdec x hx).2 2
    _ = C ^ 2 / ‖x‖ ^ 4 := by rw [div_pow, ← pow_mul]

end Decay

end MultipoleBKT

end
