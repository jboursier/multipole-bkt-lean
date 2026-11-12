/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import MultipoleBKT.Frozen.IsMollifier
public import MultipoleBKT.Frozen.Kappa
public import MultipoleBKT.Frozen.SmearedCharge
public import MultipoleBKT.Frozen.SmearedKernel
public import TwoComponentCoulomb.Frozen.LogKernel
import TwoComponentCoulomb.Potential.DiscPotential

/-!
# API for the smeared charge of a general mollifier

Basic measure-theoretic facts about `δ_z^{(λ)} = smearedCharge χ z lam`, the measure on `ℂ` with
density `λ⁻² χ((· - z) / λ)` with respect to Lebesgue measure (Section 2.1), for an admissible mollifier `χ` (`IsMollifier χ`).

* `IsMollifier.measurable`, `.nonneg`, `.radial`, `.exists_bound`, `.eq_zero_of_one_lt`,
  `.integral_eq_one`, `.integrable` : the six components of `IsMollifier`, unpacked.
* `smearedDensity` : the density, with `smearedCharge_eq_withDensity : smearedCharge χ z lam =
  volume.withDensity (smearedDensity χ z lam)` (by `rfl`).
* `measurable_smearedDensity`, `smearedDensity_le`, `smearedDensity_eq_zero` : the density is
  measurable, bounded by `M / λ²` (`M` a bound for `χ`) and vanishes off the closed disc `B̄(z, λ)`.
* `smearedCharge_le_smul_restrict` : domination `δ_z^{(λ)} ≤ (M / λ²) • volume|_{B̄(z, λ)}`.
* `smearedCharge_compl_closedBall`, `ae_mem_closedBall_smearedCharge` : the support.
* `smearedCharge_eq_map` and `integral_smearedCharge_eq_integral_one` : change of variables
  `δ_z^{(λ)} = (x ↦ z + λ x)_* δ_0^{(1)}`.
* `isProbabilityMeasure_smearedCharge` : `δ_z^{(λ)}` is a probability measure for `λ > 0`; for every
  real `λ` it is finite (`isFiniteMeasure_smearedCharge`), is `0` for `λ = 0` and agrees with the
  measure of radius `|λ|` (`smearedCharge_eq_abs`).
* `map_rotate_smearedCharge` : invariance under rotations about the centre `z` (`χ` is radial).
* `integrable_logKernel_sub_smearedCharge` and `integrable_logKernel_prod_smearedCharge` :
  integrability of the logarithmic kernel `g = logKernel` against one, respectively two, smeared
  charges.
* `map_add_right_smearedCharge`, `map_neg_smearedCharge` : behaviour under translations and under
  the antipodal map.
* `integrable_smearedCharge_of_continuous` and `ae_prod_smearedCharge_ne` : continuous functions
  are integrable, and the diagonal is null for a product of two smeared charges.
* `kappa_eq_smearedKernel` : `κ = g_1(0)`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

/-! ### Unpacking `IsMollifier` -/

namespace IsMollifier

variable {χ : ℂ → ℝ}

theorem measurable (hχ : IsMollifier χ) : Measurable χ := hχ.1

theorem nonneg (hχ : IsMollifier χ) (x : ℂ) : 0 ≤ χ x := hχ.2.1 x

theorem radial (hχ : IsMollifier χ) {x y : ℂ} (h : ‖x‖ = ‖y‖) : χ x = χ y := hχ.2.2.1 x y h

theorem exists_bound (hχ : IsMollifier χ) : ∃ M : ℝ, ∀ x, χ x ≤ M := by
  obtain ⟨M, hM⟩ := hχ.2.2.2.1
  exact ⟨M, fun x => hM ⟨x, rfl⟩⟩

theorem eq_zero_of_one_lt (hχ : IsMollifier χ) {x : ℂ} (hx : 1 < ‖x‖) : χ x = 0 :=
  hχ.2.2.2.2.1 x hx

theorem integral_eq_one (hχ : IsMollifier χ) : ∫ x, χ x = 1 := hχ.2.2.2.2.2

theorem integrable (hχ : IsMollifier χ) : Integrable χ :=
  Integrable.of_integral_ne_zero (by rw [hχ.integral_eq_one]; exact one_ne_zero)

/-- A bound for `χ` is nonnegative. -/
theorem nonneg_of_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) : 0 ≤ M :=
  (hχ.nonneg 0).trans (hM 0)

end IsMollifier

variable {χ : ℂ → ℝ} {z : ℂ} {lam : ℝ}

/-- The norm of `(x - z) / λ` for a real `λ`. -/
theorem norm_sub_div_ofReal (x z : ℂ) (lam : ℝ) : ‖(x - z) / (lam : ℂ)‖ = ‖x - z‖ / |lam| := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]

/-! ### The density -/

/-- The density of `smearedCharge χ z lam` with respect to Lebesgue measure. -/
noncomputable def smearedDensity (χ : ℂ → ℝ) (z : ℂ) (lam : ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((lam ^ 2)⁻¹ * χ ((x - z) / lam))

theorem smearedCharge_eq_withDensity (χ : ℂ → ℝ) (z : ℂ) (lam : ℝ) :
    smearedCharge χ z lam = volume.withDensity (smearedDensity χ z lam) := rfl

theorem measurable_smearedDensity (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) :
    Measurable (smearedDensity χ z lam) := by
  unfold smearedDensity
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul
    (hχ.measurable.comp ((measurable_id.sub_const z).div_const (lam : ℂ))))

/-- The density is bounded by `M / λ²` when `χ ≤ M` and `λ > 0`. -/
theorem smearedDensity_le {M : ℝ} (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam) (x : ℂ) : smearedDensity χ z lam x ≤ ENNReal.ofReal (M / lam ^ 2) := by
  unfold smearedDensity
  refine ENNReal.ofReal_le_ofReal ?_
  have h : M / lam ^ 2 = (lam ^ 2)⁻¹ * M := div_eq_inv_mul _ _
  rw [h]
  exact mul_le_mul_of_nonneg_left (hM _) (by positivity)

/-- The density vanishes outside the closed disc `B̄(z, λ)` when `λ > 0`. -/
theorem smearedDensity_eq_zero (hχ : IsMollifier χ) (hlam : 0 < lam) {x : ℂ}
    (hx : x ∉ closedBall z lam) : smearedDensity χ z lam x = 0 := by
  have h1 : lam < ‖x - z‖ := by
    rw [mem_closedBall, not_le, dist_eq_norm] at hx
    exact hx
  have h2 : 1 < ‖(x - z) / (lam : ℂ)‖ := by
    rw [norm_sub_div_ofReal, abs_of_pos hlam]
    exact (one_lt_div hlam).2 h1
  unfold smearedDensity
  rw [hχ.eq_zero_of_one_lt h2, mul_zero, ENNReal.ofReal_zero]

/-- The density is bounded by the indicator of the closed disc `B̄(z, λ)` times `M / λ²`. -/
theorem smearedDensity_le_indicator (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (x : ℂ) :
    smearedDensity χ z lam x ≤
      (closedBall z lam).indicator (fun _ => ENNReal.ofReal (M / lam ^ 2)) x := by
  by_cases hx : x ∈ closedBall z lam
  · rw [indicator_of_mem hx]
    exact smearedDensity_le hM hlam x
  · rw [smearedDensity_eq_zero hχ hlam hx]
    exact zero_le

/-! ### Domination and support -/

/-- **Domination**: `δ_z^{(λ)} ≤ (M / λ²) • volume|_{B̄(z, λ)}` when `χ ≤ M` and `λ > 0`. -/
theorem smearedCharge_le_smul_restrict (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) :
    smearedCharge χ z lam ≤
      ENNReal.ofReal (M / lam ^ 2) • (volume : Measure ℂ).restrict (closedBall z lam) := by
  calc smearedCharge χ z lam
      ≤ volume.withDensity ((closedBall z lam).indicator fun _ => ENNReal.ofReal (M / lam ^ 2)) :=
        withDensity_mono (Filter.Eventually.of_forall (smearedDensity_le_indicator hχ hM hlam))
    _ = (volume.restrict (closedBall z lam)).withDensity fun _ => ENNReal.ofReal (M / lam ^ 2) :=
        withDensity_indicator measurableSet_closedBall _
    _ = ENNReal.ofReal (M / lam ^ 2) • (volume : Measure ℂ).restrict (closedBall z lam) :=
        withDensity_const _

/-- The complement of the closed disc `B̄(z, λ)` is `δ_z^{(λ)}`-null when `λ > 0`. -/
theorem smearedCharge_compl_closedBall (hχ : IsMollifier χ) (hlam : 0 < lam) :
    smearedCharge χ z lam (closedBall z lam)ᶜ = 0 := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  refine le_antisymm ((smearedCharge_le_smul_restrict hχ hM hlam _).trans ?_) zero_le
  simp [Measure.restrict_apply measurableSet_closedBall.compl]

/-- Almost every point for `δ_z^{(λ)}` lies in the closed disc `B̄(z, λ)` (for `λ > 0`). -/
theorem ae_mem_closedBall_smearedCharge (hχ : IsMollifier χ) (hlam : 0 < lam) :
    ∀ᵐ x ∂smearedCharge χ z lam, x ∈ closedBall z lam :=
  ae_iff.2 (smearedCharge_compl_closedBall hχ hlam)

theorem smearedCharge_absolutelyContinuous (χ : ℂ → ℝ) (z : ℂ) (lam : ℝ) :
    smearedCharge χ z lam ≪ volume :=
  withDensity_absolutelyContinuous _ _

/-- `δ_z^{(λ)}` has no atoms. -/
theorem smearedCharge_singleton (χ : ℂ → ℝ) (z x : ℂ) (lam : ℝ) :
    smearedCharge χ z lam {x} = 0 :=
  smearedCharge_absolutelyContinuous χ z lam (measure_singleton x)

/-! ### Change of variables -/

/-- Pushing `μ.withDensity g` forward along a measurable embedding `f` with `μ.map f = ν` and
`g = h ∘ f` gives `ν.withDensity h`. -/
theorem map_withDensity_of_measurableEmbedding {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurableEmbedding f)
    (hmap : μ.map f = ν) {g : α → ℝ≥0∞} {h : β → ℝ≥0∞} (hg : ∀ x, g x = h (f x)) :
    (μ.withDensity g).map f = ν.withDensity h := by
  subst hmap
  ext s hs
  rw [hf.map_apply, withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs,
    hf.restrict_map, hf.lintegral_map]
  exact lintegral_congr hg

/-- The affine map `x ↦ z + λ x` pushes Lebesgue measure to `λ⁻² • volume`, for `λ > 0`. -/
theorem map_affine_volume (z : ℂ) (hlam : 0 < lam) :
    (volume : Measure ℂ).map (fun x : ℂ => z + (lam : ℂ) * x) =
      ENNReal.ofReal (lam ^ 2)⁻¹ • volume := by
  have hlam0 : lam ≠ 0 := hlam.ne'
  have h1 : (volume : Measure ℂ).map (fun x : ℂ => (lam : ℂ) * x) =
      ENNReal.ofReal (lam ^ 2)⁻¹ • volume := by
    have h := Measure.map_addHaar_smul (volume : Measure ℂ) hlam0
    rw [Complex.finrank_real_complex, abs_of_pos (by positivity)] at h
    exact h
  have h2 : (fun x : ℂ => z + (lam : ℂ) * x) = (fun y => z + y) ∘ (fun x => (lam : ℂ) * x) := rfl
  rw [h2, ← Measure.map_map (measurable_const_add z) (by fun_prop), h1,
    Measure.map_smul _ (measurable_const_add z).aemeasurable, map_add_left_eq_self]

theorem measurableEmbedding_affine (z : ℂ) (hlam : 0 < lam) :
    MeasurableEmbedding (fun x : ℂ => z + (lam : ℂ) * x) :=
  (measurableEmbedding_addLeft z).comp
    (measurableEmbedding_mulLeft₀ (Complex.ofReal_ne_zero.2 hlam.ne'))

/-- **Change of variables**: for `λ > 0`, `δ_z^{(λ)}` is the pushforward of `δ_0^{(1)}` under
`x ↦ z + λ x`. -/
theorem smearedCharge_eq_map (hχ : IsMollifier χ) (z : ℂ) (hlam : 0 < lam) :
    smearedCharge χ z lam = (smearedCharge χ 0 1).map (fun x : ℂ => z + (lam : ℂ) * x) := by
  have hlam0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam.ne'
  have hmeas : Measurable fun y : ℂ => ENNReal.ofReal (χ ((y - z) / lam)) :=
    ENNReal.measurable_ofReal.comp
      (hχ.measurable.comp ((measurable_id.sub_const z).div_const (lam : ℂ)))
  have hg : ∀ x : ℂ, smearedDensity χ 0 1 x =
      (fun y : ℂ => ENNReal.ofReal (χ ((y - z) / lam))) (z + (lam : ℂ) * x) := by
    intro x
    have : (z + (lam : ℂ) * x - z) / lam = x := by field_simp; ring
    show _ = ENNReal.ofReal (χ ((z + (lam : ℂ) * x - z) / lam))
    rw [this]
    simp [smearedDensity]
  rw [smearedCharge_eq_withDensity χ 0 1,
    map_withDensity_of_measurableEmbedding (measurableEmbedding_affine z hlam)
      (map_affine_volume z hlam) (h := fun y : ℂ => ENNReal.ofReal (χ ((y - z) / lam))) hg, withDensity_smul_measure, ← withDensity_smul _ hmeas,
    smearedCharge_eq_withDensity]
  congr 1
  funext x
  simp only [smearedDensity, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_mul (by positivity)]


/-! ### Total mass, finiteness and the symmetry `λ ↦ -λ` -/

instance sFinite_smearedCharge (χ : ℂ → ℝ) (z : ℂ) (lam : ℝ) : SFinite (smearedCharge χ z lam) := by
  unfold smearedCharge
  infer_instance

/-- The unit-scale measure `δ_0^{(1)}` has total mass `∫ χ = 1`. -/
theorem smearedCharge_one_univ (hχ : IsMollifier χ) : smearedCharge χ 0 1 univ = 1 := by
  have h : ∀ x : ℂ, smearedDensity χ 0 1 x = ENNReal.ofReal (χ x) := fun x => by
    simp [smearedDensity]
  rw [smearedCharge_eq_withDensity, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [h]
  rw [← ofReal_integral_eq_lintegral_ofReal hχ.integrable (Filter.Eventually.of_forall hχ.nonneg),
    hχ.integral_eq_one, ENNReal.ofReal_one]

/-- For `λ > 0`, `δ_z^{(λ)}` is a probability measure. -/
theorem isProbabilityMeasure_smearedCharge (hχ : IsMollifier χ) (z : ℂ) (hlam : 0 < lam) :
    IsProbabilityMeasure (smearedCharge χ z lam) := by
  have : IsProbabilityMeasure (smearedCharge χ 0 1) := ⟨smearedCharge_one_univ hχ⟩
  rw [smearedCharge_eq_map hχ z hlam]
  infer_instance

/-- For `λ = 0` the density vanishes (as `0⁻¹ = 0`) and `δ_z^{(0)} = 0`. -/
theorem smearedCharge_zero (χ : ℂ → ℝ) (z : ℂ) : smearedCharge χ z 0 = 0 := by
  have h : smearedDensity χ z 0 = 0 := by
    funext x
    simp [smearedDensity]
  rw [smearedCharge_eq_withDensity, h, withDensity_zero]

/-- The measure only depends on `|λ|` since `χ` is radial. -/
theorem smearedCharge_neg (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) :
    smearedCharge χ z (-lam) = smearedCharge χ z lam := by
  rw [smearedCharge_eq_withDensity, smearedCharge_eq_withDensity]
  congr 1
  funext x
  have h : χ ((x - z) / ((-lam : ℝ) : ℂ)) = χ ((x - z) / (lam : ℂ)) :=
    hχ.radial (by rw [norm_sub_div_ofReal, norm_sub_div_ofReal, abs_neg])
  unfold smearedDensity
  rw [h, neg_sq]

theorem smearedCharge_eq_abs (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) :
    smearedCharge χ z lam = smearedCharge χ z |lam| := by
  rcases le_or_gt 0 lam with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, smearedCharge_neg hχ]

/-- `δ_z^{(λ)}` is a finite measure for every real `λ`. -/
theorem isFiniteMeasure_smearedCharge (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) :
    IsFiniteMeasure (smearedCharge χ z lam) := by
  rcases eq_or_ne lam 0 with rfl | h0
  · rw [smearedCharge_zero]
    infer_instance
  · rw [smearedCharge_eq_abs hχ]
    have := isProbabilityMeasure_smearedCharge hχ z (abs_pos.2 h0)
    infer_instance

/-! ### Invariance under rotations about the centre -/

theorem measurePreserving_rotate (z : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    MeasurePreserving (fun x : ℂ => z + u * (x - z)) volume volume := by
  have hrot := LinearIsometryEquiv.measurePreserving
    (rotation (⟨u, mem_sphere_zero_iff_norm.2 hu⟩ : Circle))
  have hfun : ⇑(rotation (⟨u, mem_sphere_zero_iff_norm.2 hu⟩ : Circle)) =
      fun x : ℂ => u * x := funext (rotation_apply _)
  rw [hfun] at hrot
  exact (measurePreserving_add_left volume z).comp (hrot.comp (measurePreserving_sub_right volume z))

theorem measurableEmbedding_rotate (z : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    MeasurableEmbedding (fun x : ℂ => z + u * (x - z)) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  exact (measurableEmbedding_addLeft z).comp
    ((measurableEmbedding_mulLeft₀ hu0).comp (MeasurableEquiv.subRight z).measurableEmbedding)

/-- **Radial invariance**: for `‖u‖ = 1`, the rotation `x ↦ z + u (x - z)` about the centre `z`
preserves `δ_z^{(λ)}`, since `χ` is radial. -/
theorem map_rotate_smearedCharge (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) {u : ℂ} (hu : ‖u‖ = 1) :
    (smearedCharge χ z lam).map (fun x : ℂ => z + u * (x - z)) = smearedCharge χ z lam := by
  rw [smearedCharge_eq_withDensity]
  refine map_withDensity_of_measurableEmbedding (measurableEmbedding_rotate z hu)
    (measurePreserving_rotate z hu).map_eq (h := smearedDensity χ z lam) fun x => ?_
  have h : χ ((z + u * (x - z) - z) / (lam : ℂ)) = χ ((x - z) / (lam : ℂ)) :=
    hχ.radial (by simp [hu])
  show _ = ENNReal.ofReal ((lam ^ 2)⁻¹ * χ ((z + u * (x - z) - z) / (lam : ℂ)))
  rw [h]
  rfl

/-! ### Integrals -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrals against `δ_z^{(λ)}` are integrals against the density `λ⁻² χ((· - z) / λ)`. -/
theorem integral_smearedCharge (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) (f : ℂ → E) :
    ∫ x, f x ∂smearedCharge χ z lam = ∫ x, ((lam ^ 2)⁻¹ * χ ((x - z) / lam)) • f x := by
  rw [smearedCharge_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    (measurable_smearedDensity hχ z lam) (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
  congr 1
  funext x
  unfold smearedDensity
  rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (hχ.nonneg _))]

/-- Change of variables for integrals: `∫ f dδ_z^{(λ)} = ∫ f(z + λ x) dδ_0^{(1)}(x)` for `λ > 0`. -/
theorem integral_smearedCharge_eq_integral_one (hχ : IsMollifier χ) (z : ℂ) (hlam : 0 < lam)
    (f : ℂ → E) :
    ∫ x, f x ∂smearedCharge χ z lam = ∫ x, f (z + (lam : ℂ) * x) ∂smearedCharge χ 0 1 := by
  rw [smearedCharge_eq_map hχ z hlam, (measurableEmbedding_affine z hlam).integral_map]

end Integral

/-! ### Integrability of the logarithmic kernel -/

/-- The logarithmic kernel `x ↦ g(x - y)` is integrable for `δ_z^{(λ)}`, for `λ > 0`. -/
theorem integrable_logKernel_sub_smearedCharge_of_pos (hχ : IsMollifier χ) (y z : ℂ)
    (hlam : 0 < lam) :
    Integrable (fun x : ℂ => logKernel (x - y)) (smearedCharge χ z lam) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have h1 : IntegrableOn (fun x : ℂ => logKernel (x - y)) (ball z (lam + 1)) := by
    have := (TwoComponentCoulomb.integrableOn_log_norm_sub_ball y z (lam + 1)).neg
    refine this.congr_fun (fun x _ => ?_) measurableSet_ball
    simp [logKernel, norm_sub_rev]
  have h2 : IntegrableOn (fun x : ℂ => logKernel (x - y)) (closedBall z lam) :=
    h1.mono_set (closedBall_subset_ball (lt_add_one lam))
  exact (Integrable.smul_measure h2 ENNReal.ofReal_ne_top).mono_measure
    (smearedCharge_le_smul_restrict hχ hM hlam)

/-- The logarithmic kernel `x ↦ g(x - y)` is integrable for `δ_z^{(λ)}`, for every real `λ`. -/
theorem integrable_logKernel_sub_smearedCharge (hχ : IsMollifier χ) (y z : ℂ) (lam : ℝ) :
    Integrable (fun x : ℂ => logKernel (x - y)) (smearedCharge χ z lam) := by
  rcases eq_or_ne lam 0 with rfl | h0
  · rw [smearedCharge_zero]
    exact integrable_zero_measure
  · rw [smearedCharge_eq_abs hχ]
    exact integrable_logKernel_sub_smearedCharge_of_pos hχ y z (abs_pos.2 h0)

/-- The kernel `g(x - y)` is integrable for the product of two smeared charges, for positive
`λ` and `μ`. -/
theorem integrable_logKernel_prod_smearedCharge_of_pos (hχ : IsMollifier χ) (a b : ℂ) {mu : ℝ}
    (hlam : 0 < lam) (hmu : 0 < mu) :
    Integrable (fun p : ℂ × ℂ => logKernel (p.1 - p.2))
      ((smearedCharge χ a lam).prod (smearedCharge χ b mu)) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hint : Integrable (fun p : ℂ × ℂ => logKernel (p.1 - p.2))
      ((volume.restrict (closedBall a lam)).prod (volume.restrict (closedBall b mu))) :=
    (TwoComponentCoulomb.integrable_log_norm_sub_prod_ball a b (lam + 1) (mu + 1)).neg.mono_measure
      (Measure.prod_mono
        (Measure.restrict_mono (closedBall_subset_ball (lt_add_one lam)) le_rfl)
        (Measure.restrict_mono (closedBall_subset_ball (lt_add_one mu)) le_rfl))
  have hle := Measure.prod_mono (smearedCharge_le_smul_restrict (z := a) hχ hM hlam)
    (smearedCharge_le_smul_restrict (z := b) hχ hM hmu)
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at hle
  exact (Integrable.smul_measure hint
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).mono_measure hle

/-- The kernel `g(x - y)` is integrable for the product of two smeared charges, for all real
radii `λ` and `μ`. -/
theorem integrable_logKernel_prod_smearedCharge (hχ : IsMollifier χ) (a b : ℂ) (lam mu : ℝ) :
    Integrable (fun p : ℂ × ℂ => logKernel (p.1 - p.2))
      ((smearedCharge χ a lam).prod (smearedCharge χ b mu)) := by
  rcases eq_or_ne lam 0 with rfl | h0
  · rw [smearedCharge_zero, Measure.zero_prod]
    exact integrable_zero_measure
  rcases eq_or_ne mu 0 with rfl | h1
  · rw [smearedCharge_zero (z := b), Measure.prod_zero]
    exact integrable_zero_measure
  rw [smearedCharge_eq_abs hχ a lam, smearedCharge_eq_abs hχ b mu]
  exact integrable_logKernel_prod_smearedCharge_of_pos hχ a b (abs_pos.2 h0) (abs_pos.2 h1)

/-! ### Translations and the antipodal map -/

/-- Translation: `(· + w)` pushes `δ_z^{(λ)}` to `δ_{z+w}^{(λ)}`. -/
theorem map_add_right_smearedCharge (χ : ℂ → ℝ) (z w : ℂ) (lam : ℝ) :
    (smearedCharge χ z lam).map (· + w) = smearedCharge χ (z + w) lam := by
  rw [smearedCharge_eq_withDensity, smearedCharge_eq_withDensity]
  refine map_withDensity_of_measurableEmbedding (measurableEmbedding_addRight w)
    (map_add_right_eq_self volume w) fun x => ?_
  simp [smearedDensity]

/-- Antipodal map: `x ↦ -x` pushes `δ_z^{(λ)}` to `δ_{-z}^{(λ)}`. -/
theorem map_neg_smearedCharge (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) :
    (smearedCharge χ z lam).map Neg.neg = smearedCharge χ (-z) lam := by
  rw [smearedCharge_eq_withDensity, smearedCharge_eq_withDensity]
  refine map_withDensity_of_measurableEmbedding measurableEmbedding_neg
    (Measure.map_neg_eq_self volume) fun x => ?_
  have h : χ ((-x - -z) / (lam : ℂ)) = χ ((x - z) / (lam : ℂ)) :=
    hχ.radial (by rw [← norm_neg]; congr 1; ring)
  show _ = ENNReal.ofReal ((lam ^ 2)⁻¹ * χ ((-x - -z) / (lam : ℂ)))
  rw [h]
  rfl

/-! ### Continuous functions and the diagonal -/

/-- Continuous functions are integrable for `δ_z^{(λ)}`. -/
theorem integrable_smearedCharge_of_continuous (hχ : IsMollifier χ) {f : ℂ → ℝ}
    (hf : Continuous f) (z : ℂ) (lam : ℝ) : Integrable f (smearedCharge χ z lam) := by
  rcases eq_or_ne lam 0 with rfl | h0
  · rw [smearedCharge_zero]
    exact integrable_zero_measure
  rw [smearedCharge_eq_abs hχ]
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have h : IntegrableOn f (closedBall z |lam|) :=
    hf.continuousOn.integrableOn_compact (isCompact_closedBall z |lam|)
  exact (Integrable.smul_measure h ENNReal.ofReal_ne_top).mono_measure
    (smearedCharge_le_smul_restrict hχ hM (abs_pos.2 h0))

/-- The diagonal is a null set for the product of two smeared charges. -/
theorem ae_prod_smearedCharge_ne (χ : ℂ → ℝ) (z w : ℂ) (lam mu : ℝ) :
    ∀ᵐ p ∂(smearedCharge χ z lam).prod (smearedCharge χ w mu), p.1 ≠ p.2 := by
  have hm : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} := isClosed_diagonal.measurableSet
  rw [ae_iff]
  have : {p : ℂ × ℂ | ¬p.1 ≠ p.2} = {p : ℂ × ℂ | p.1 = p.2} := by simp
  rw [this, Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall fun x => ?_
  have : Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {x} := by
    ext y; simp [eq_comm]
  simp [this, smearedCharge_singleton]

/-! ### The constant `κ` -/

/-- `κ = g_1(0)` (equations (2.3)–(2.4)). -/
theorem kappa_eq_smearedKernel (χ : ℂ → ℝ) : kappa χ = smearedKernel χ 1 0 := rfl

end MultipoleBKT

end
