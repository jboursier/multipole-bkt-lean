/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.PartitionFunction
public import MultipoleBKT.Frozen.GibbsMeasure
public import MultipoleBKT.Frozen.DipoleNormalization
public import MultipoleBKT.Frozen.DipoleMeasure
public import MultipoleBKT.Frozen.DipoleInteraction
public import MultipoleBKT.Frozen.IsMollifier
public import MultipoleBKT.Potential.Kernel
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Plumbing for the Gibbs measure and the dipole measure

Elementary facts on the frozen objects `energy`, `partitionFunction`, `gibbsMeasure`,
`dipoleNormalization`, `dipoleMeasure` and `dipoleInteraction` of
the paper (eq. (2.5); eq. (2.8); eq. (2.9); eq. (2.31); eq. (2.30)), used by
every later proof. Throughout, `χ` is an admissible mollifier and `λ > 0`, so that
`g_λ = smearedKernel χ lam` is continuous (`continuous_smearedKernel`).

* `isCompact_box`, `volume_box_prod`, `volume_pi_box_prod`: the box `Λ = [0, √N]²`, the square
  `Λ²` (the space of one dipole) and `(Λ²)^ι` (compact, measurable, of volume `(N²)^|ι|`).
* `energy_eq_sum_smearedKernel`, `continuous_energy`, `measurable_energy`: the energy
  `F_λ` is the explicit finite sum of values of `g_λ`; it is continuous in the configuration.
* `continuous_dipoleInteraction`, `measurable_dipoleInteraction_apply`: `v_ij` is continuous.
* `integrableOn_exp_smearedKernel_box`, `dipoleNormalization_pos`, `dipoleNormalization_mul`,
 `isProbabilityMeasure_dipoleMeasure`: `0 < C_{β,λ}` and `μ_{β,λ}` is a probability measure
  (for `N ≥ 1`).
* `ae_mem_box_dipoleMeasure`, `ae_pi_dipoleMeasure_mem_box`: `μ_{β,λ}` and its finite powers
  live on `Λ²` (resp. `(Λ²)^ι`).
* `partitionFunction_pos`, `partitionFunction_lt_top`, `gibbsMeasure_univ`,
 `isProbabilityMeasure_gibbsMeasure_of_ne_top`, `isProbabilityMeasure_gibbsMeasure`:
  `0 < Z_{N,β}^λ < ∞` and `ℙ_{N,β}^λ` is a probability measure. The finiteness of `Z` is
  elementary here because `λ > 0` makes `F_λ` a continuous function on a compact set.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open TwoComponentCoulomb (box logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam β : ℝ} {N : ℕ}

/-! ### The box and the square -/

theorem isCompact_box (N : ℕ) : IsCompact (box N) :=
  isCompact_Icc.reProdIm isCompact_Icc

/-- The square `Λ² = Λ × Λ`, the space of one dipole `(x, y)`, is compact. -/
theorem isCompact_box_prod (N : ℕ) : IsCompact (box N ×ˢ box N) :=
  (isCompact_box N).prod (isCompact_box N)

theorem measurableSet_box_prod (N : ℕ) : MeasurableSet (box N ×ˢ box N) :=
  (TwoComponentCoulomb.measurableSet_box N).prod (TwoComponentCoulomb.measurableSet_box N)

/-- The square `Λ²` has volume `N²`. -/
theorem volume_box_prod (N : ℕ) : volume (box N ×ˢ box N) = (N : ℝ≥0∞) ^ 2 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, TwoComponentCoulomb.volume_box, sq]

theorem volume_box_prod_pos (hN : 1 ≤ N) : 0 < volume (box N ×ˢ box N) := by
  rw [volume_box_prod]
  exact ENNReal.pow_pos (by exact_mod_cast hN) _

theorem volume_box_prod_lt_top (N : ℕ) : volume (box N ×ˢ box N) < ∞ := by
  rw [volume_box_prod]
  exact ENNReal.pow_lt_top (ENNReal.natCast_lt_top N)

/-- The configuration space `(Λ²)^ι` is compact. -/
theorem isCompact_pi_box_prod (ι : Type*) (N : ℕ) :
    IsCompact (Set.univ.pi fun _ : ι => box N ×ˢ box N) :=
  isCompact_univ_pi fun _ => isCompact_box_prod N

theorem measurableSet_pi_box_prod {ι : Type*} [Countable ι] (N : ℕ) :
    MeasurableSet (Set.univ.pi fun _ : ι => box N ×ˢ box N) :=
  MeasurableSet.univ_pi fun _ => measurableSet_box_prod N

/-- The configuration space `(Λ²)^ι` has volume `(N²)^|ι|`. -/
theorem volume_pi_box_prod {ι : Type*} [Fintype ι] (N : ℕ) :
    volume (Set.univ.pi fun _ : ι => box N ×ˢ box N) = ((N : ℝ≥0∞) ^ 2) ^ Fintype.card ι := by
  rw [volume_pi_pi]
  simp [volume_box_prod, Finset.prod_const]

theorem volume_pi_box_prod_pos {ι : Type*} [Fintype ι] (hN : 1 ≤ N) :
    0 < volume (Set.univ.pi fun _ : ι => box N ×ˢ box N) := by
  rw [volume_pi_box_prod]
  exact ENNReal.pow_pos (ENNReal.pow_pos (by exact_mod_cast hN) _) _

theorem volume_pi_box_prod_lt_top {ι : Type*} [Fintype ι] (N : ℕ) :
    volume (Set.univ.pi fun _ : ι => box N ×ˢ box N) < ∞ := by
  rw [volume_pi_box_prod]
  exact ENNReal.pow_lt_top (ENNReal.pow_lt_top (ENNReal.natCast_lt_top N))

/-! ### Continuity of the energy and of the dipole interaction -/

/-- The energy `F_λ` (eq. (2.5)) as an explicit finite sum of values of `g_λ`. -/
theorem energy_eq_sum_smearedKernel (χ : ℂ → ℝ) (lam : ℝ) (c : Fin N → ℂ × ℂ) :
    energy χ lam c = (1 / 2) * ∑ i, ∑ j,
        (smearedKernel χ lam ((c j).1 - (c i).1) - smearedKernel χ lam ((c j).2 - (c i).1)
          - smearedKernel χ lam ((c j).1 - (c i).2) + smearedKernel χ lam ((c j).2 - (c i).2))
      - N * (logKernel lam + kappa χ) := by
  simp only [energy, integral_logKernel_prod_smearedCharge]

/-- The energy `F_λ` is continuous on the configuration space, for `λ > 0`. -/
theorem continuous_energy (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Continuous (energy χ lam : (Fin N → ℂ × ℂ) → ℝ) := by
  have hg := continuous_smearedKernel hχ hlam
  have h : (energy χ lam : (Fin N → ℂ × ℂ) → ℝ) = fun c => (1 / 2) * ∑ i, ∑ j,
        (smearedKernel χ lam ((c j).1 - (c i).1) - smearedKernel χ lam ((c j).2 - (c i).1)
          - smearedKernel χ lam ((c j).1 - (c i).2) + smearedKernel χ lam ((c j).2 - (c i).2))
      - N * (logKernel lam + kappa χ) :=
    funext (energy_eq_sum_smearedKernel χ lam)
  rw [h]
  fun_prop

/-- The energy `F_λ` is measurable on the configuration space, for `λ > 0`. -/
theorem measurable_energy (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Measurable (energy χ lam : (Fin N → ℂ × ℂ) → ℝ) :=
  (continuous_energy hχ hlam).measurable

/-- The dipole--dipole interaction `v_ij` is continuous in the pair of dipoles, for `λ > 0`. -/
theorem continuous_dipoleInteraction (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Continuous fun q : (ℂ × ℂ) × (ℂ × ℂ) => dipoleInteraction χ lam q.1 q.2 := by
  have hg := continuous_smearedKernel hχ hlam
  unfold dipoleInteraction
  fun_prop

theorem measurable_dipoleInteraction (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => dipoleInteraction χ lam q.1 q.2 :=
  (continuous_dipoleInteraction hχ hlam).measurable

/-- `c ↦ v_ij(c_i, c_j)` is continuous on any configuration space `ι → ℂ × ℂ`. -/
theorem continuous_dipoleInteraction_apply (hχ : IsMollifier χ) (hlam : 0 < lam) {ι : Type*}
    (i j : ι) : Continuous fun c : ι → ℂ × ℂ => dipoleInteraction χ lam (c i) (c j) := by
  have h := continuous_dipoleInteraction hχ hlam
  fun_prop

/-- `c ↦ v_ij(c_i, c_j)` is measurable on any configuration space `ι → ℂ × ℂ` (with the product
σ-algebra). -/
theorem measurable_dipoleInteraction_apply (hχ : IsMollifier χ) (hlam : 0 < lam) {ι : Type*}
    (i j : ι) : Measurable fun c : ι → ℂ × ℂ => dipoleInteraction χ lam (c i) (c j) := by
  have h := measurable_dipoleInteraction hχ hlam
  fun_prop

/-! ### The dipole normalization and the dipole measure -/

theorem continuous_exp_smearedKernel_sub (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) :
    Continuous fun p : ℂ × ℂ => Real.exp (β * smearedKernel χ lam (p.1 - p.2)) := by
  have hg := continuous_smearedKernel hχ hlam
  fun_prop

theorem integrableOn_exp_smearedKernel_box (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (N : ℕ) :
    IntegrableOn (fun p : ℂ × ℂ => Real.exp (β * smearedKernel χ lam (p.1 - p.2)))
      (box N ×ˢ box N) :=
  (continuous_exp_smearedKernel_sub hχ hlam β).continuousOn.integrableOn_compact
    (isCompact_box_prod N)

/-- `∫_{Λ²} e^{β g_λ(x - y)} dx dy > 0` for `N ≥ 1`. -/
theorem integral_exp_smearedKernel_box_pos (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) :
    0 < ∫ p in box N ×ˢ box N, Real.exp (β * smearedKernel χ lam (p.1 - p.2)) := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun p => (Real.exp_pos _).le)
    (integrableOn_exp_smearedKernel_box hχ hlam β N)]
  have : Function.support (fun p : ℂ × ℂ => Real.exp (β * smearedKernel χ lam (p.1 - p.2))) =
      Set.univ := by
    ext p
    simp [Function.mem_support]
  rw [this, Set.univ_inter]
  exact volume_box_prod_pos hN

/-- `C_{β,λ} > 0` for `N ≥ 1` (it is a real number, so finite). -/
theorem dipoleNormalization_pos (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hN : 1 ≤ N) :
    0 < dipoleNormalization χ N β lam := by
  unfold dipoleNormalization
  have : (0 : ℝ) < N := by exact_mod_cast hN
  exact mul_pos (by positivity) (integral_exp_smearedKernel_box_pos hχ hlam β hN)

/-- `N C_{β,λ} = ∫_{Λ²} e^{β g_λ(x - y)} dx dy`. -/
theorem natCast_mul_dipoleNormalization (χ : ℂ → ℝ) (β lam : ℝ) (hN : 1 ≤ N) :
    (N : ℝ) * dipoleNormalization χ N β lam =
      ∫ p in box N ×ˢ box N, Real.exp (β * smearedKernel χ lam (p.1 - p.2)) := by
  have : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  unfold dipoleNormalization
  field_simp

theorem natCast_mul_dipoleNormalization_pos (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) : 0 < (N : ℝ) * dipoleNormalization χ N β lam := by
  rw [natCast_mul_dipoleNormalization χ β lam hN]
  exact integral_exp_smearedKernel_box_pos hχ hlam β hN

/-- The dipole measure `μ_{β,λ}` has total mass one, for `N ≥ 1`. -/
theorem dipoleMeasure_univ (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hN : 1 ≤ N) :
    dipoleMeasure χ N β lam univ = 1 := by
  unfold dipoleMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint := integrableOn_exp_smearedKernel_box hχ hlam β N
  have hpos := natCast_mul_dipoleNormalization_pos hχ hlam β hN
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (Filter.Eventually.of_forall fun p => by positivity)]
  rw [integral_const_mul, ← natCast_mul_dipoleNormalization χ β lam hN, inv_mul_cancel₀ hpos.ne']
  simp

/-- `μ_{β,λ}` is a probability measure, for `N ≥ 1` (eq. (2.30)). -/
theorem isProbabilityMeasure_dipoleMeasure (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) : IsProbabilityMeasure (dipoleMeasure χ N β lam) :=
  ⟨dipoleMeasure_univ hχ hlam β hN⟩

/-- The dipole measure is concentrated on `Λ²`. -/
theorem ae_mem_box_dipoleMeasure (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) :
    ∀ᵐ p ∂dipoleMeasure χ N β lam, p ∈ box N ×ˢ box N :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_box_prod N))

/-- The `ι`-fold power of the dipole measure is concentrated on `(Λ²)^ι`: almost every
configuration has all its dipoles in `Λ²`. -/
theorem ae_pi_dipoleMeasure_mem_box (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hN : 1 ≤ N)
    {ι : Type*} [Fintype ι] :
    ∀ᵐ c ∂Measure.pi fun _ : ι => dipoleMeasure χ N β lam, ∀ i, c i ∈ box N ×ˢ box N := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  rw [ae_all_iff]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_mem_box_dipoleMeasure χ N β lam)

/-! ### The partition function and the Gibbs measure -/

theorem measurable_ofReal_exp_neg_mul_energy (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) :
    Measurable fun c : Fin N → ℂ × ℂ => ENNReal.ofReal (Real.exp (-β * energy χ lam c)) :=
  ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp ((measurable_energy hχ hlam).const_mul (-β)))

/-- `Z_{N,β}^λ > 0` for `N ≥ 1` (eq. (2.9)): the Boltzmann weight is positive and `(Λ²)^N`
has positive volume. -/
theorem partitionFunction_pos (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hN : 1 ≤ N) :
    0 < partitionFunction χ N β lam := by
  unfold partitionFunction
  rw [lintegral_pos_iff_support (measurable_ofReal_exp_neg_mul_energy hχ hlam β)]
  have : Function.support (fun c : Fin N → ℂ × ℂ =>
      ENNReal.ofReal (Real.exp (-β * energy χ lam c))) = Set.univ := by
    ext c
    simp [Function.mem_support, Real.exp_pos]
  rw [this, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact volume_pi_box_prod_pos hN

/-- `Z_{N,β}^λ < ∞` for `λ > 0`: the energy `F_λ` is continuous, hence bounded on the compact
set `(Λ²)^N`. -/
theorem partitionFunction_lt_top (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (N : ℕ) :
    partitionFunction χ N β lam < ∞ := by
  unfold partitionFunction
  have hc : Continuous fun c : Fin N → ℂ × ℂ => Real.exp (-β * energy χ lam c) := by
    have := continuous_energy (N := N) hχ hlam
    fun_prop
  have hint : IntegrableOn (fun c : Fin N → ℂ × ℂ => Real.exp (-β * energy χ lam c))
      (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) :=
    hc.continuousOn.integrableOn_compact (isCompact_pi_box_prod (Fin N) N)
  exact hint.lintegral_lt_top

/-- The mass of the whole space under the Gibbs measure is `Z⁻¹ Z`. -/
theorem gibbsMeasure_univ (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) :
    gibbsMeasure χ N β lam univ = (partitionFunction χ N β lam)⁻¹ * partitionFunction χ N β lam := by
  unfold gibbsMeasure
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rfl

/-- Conditional form: `ℙ_{N,β}^λ` is a probability measure as soon as `Z_{N,β}^λ < ∞`. (The
finiteness is in fact elementary for `λ > 0`, see `partitionFunction_lt_top` and
`isProbabilityMeasure_gibbsMeasure`; this form is kept for callers that already have it.) -/
theorem isProbabilityMeasure_gibbsMeasure_of_ne_top (hχ : IsMollifier χ) (hlam : 0 < lam)
    (β : ℝ) (hN : 1 ≤ N) (hZ : partitionFunction χ N β lam ≠ ∞) :
    IsProbabilityMeasure (gibbsMeasure χ N β lam) :=
  ⟨by rw [gibbsMeasure_univ, ENNReal.inv_mul_cancel (partitionFunction_pos hχ hlam β hN).ne' hZ]⟩

/-- The Gibbs measure `ℙ_{N,β}^λ` (eq. (2.8)) is a probability measure for
`N ≥ 1` and `λ > 0`. -/
theorem isProbabilityMeasure_gibbsMeasure (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) : IsProbabilityMeasure (gibbsMeasure χ N β lam) :=
  isProbabilityMeasure_gibbsMeasure_of_ne_top hχ hlam β hN
    (partitionFunction_lt_top hχ hlam β N).ne

end MultipoleBKT

end
