/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.DipoleConstant
public import MultipoleBKT.Gibbs.Activities
public import MultipoleBKT.Appendix.RadialIntegral
public import MultipoleBKT.Frozen.TruncationScale
public import MultipoleBKT.LowerBound.Parity.Cancellation
public import Mathlib.MeasureTheory.Integral.Marginal

/-!
# The truncated dipole measure `μ_{β,λ,ε₀}` (Definition 4.11) and Lemma 4.12

Definition 4.11 and Lemma 4.12. Throughout, `R̄ = R̄_{β,λ} = truncationScale p₀ β λ` (Definition 2.18) and `Λ = box N`.

* `cutoffDipoleNormalization χ N p₀ β λ ε₀ = C_{β,λ,ε₀}
  = (1/N) ∫_{Λ²} e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ ε₀ R̄} dx dy` (eq. (4.10)); it is the
  helper `truncatedDipoleNormalization` of `MultipoleBKT.Potential.DipoleConstant` at the
  truncation length `R = ε₀ R̄` (`cutoffDipoleNormalization_eq`).
* `cutoffDipoleMeasure χ N p₀ β λ ε₀ = μ_{β,λ,ε₀}`, the measure on `(ℂ × ℂ)` with density
  `(C_{β,λ,ε₀} N)⁻¹ e^{β g_λ(x - y)} 𝟙_{x, y ∈ Λ} 𝟙_{|x - y| ≤ ε₀ R̄}` (eq. (4.9)): a
  probability measure for `N ≥ 1`, `λ > 0`, `ε₀ > 0` (`isProbabilityMeasure_cutoffDipoleMeasure`),
  concentrated on `Λ² ∩ {|x - y| ≤ ε₀ R̄}` (`ae_cutoffDipoleMeasure`), invariant under the
  reversal `(x, y) ↦ (y, x)` (`measurePreserving_swap_cutoffDipoleMeasure`), and its finite powers
  have the product density with respect to Lebesgue measure (`pi_cutoffDipoleMeasure_eq`).
* For `ε₀ = ∞` the paper sets `μ_{β,λ,∞} = μ_{β,λ}` and `C_{β,λ,∞} = C_{β,λ}` (Definition 4.11): these are
  the frozen `dipoleMeasure` and `dipoleNormalization`, which the generic constructions of
  `MultipoleBKT.LowerBound.Hierarchical.Model` take as their base measure. When the cutoff exceeds
  the diameter of `Λ`, the truncated objects are the frozen ones
  (`cutoffDipoleNormalization_eq_of_le`, `cutoffDipoleMeasure_eq_of_le`).

**Lemma 4.12**, for `β > 2`:

* `lem411_devtCbeta` (eq. (4.11)): there is `C > 0` depending only on `β` (and `χ`) such
  that for all `ε₀ ∈ (0, 1)`, `λ ∈ (0, 1)`, `C_{β,λ,ε₀}` converges as `N → ∞` to a limit `L` with
  `|L - λ^{2-β} 𝒵_β| ≤ λ^{2-β} C (ε₀ R̄)^{-2}`; `lem411_devtCbeta_eventually` gives the
  same bound (constant `2C`) for all large `N`;
* `lem411_lower` (eq. (4.12)): given `ε₀ > 0` there is `λ₀` such that for
  `λ < λ₀`, `C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β} / 2` for all large `N`;
* `lem411_compare` (eq. (4.13)): there is `C > 0` depending only on `β` such
  that, given `ε₀ ∈ (0, 1)`, for `λ < λ₀ = min(1, ε₀/2)` and all large `N`,
  `|C_{β,λ,ε₀} - C_{β,λ}| / C_{β,λ} ≤ C (ε₀ R̄)^{-2}`.

The estimates (4.12) and (4.13), like (4.11), hold as `N → ∞` (the paper derives them from
(4.11)); the constants do not depend on `p₀`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace Hierarchical

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam ε₀ : ℝ}

/-! ### Definition 4.11 -/

/-- **The normalization** `C_{β,λ,ε₀} = (1/N) ∫_{Λ²} e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ ε₀ R̄_{β,λ}}
dx dy`, eq. (4.10) (Definition 4.11). -/
noncomputable def cutoffDipoleNormalization (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ) : ℝ :=
  (1 / N) * ∫ p in box N ×ˢ box N,
    (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
      (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2)

/-- **The truncated dipole measure** `μ_{β,λ,ε₀}` on `(ℝ²)² = ℂ × ℂ`, with density
`(C_{β,λ,ε₀} N)⁻¹ e^{β g_λ(x - y)} 𝟙_{x, y ∈ Λ} 𝟙_{|x - y| ≤ ε₀ R̄_{β,λ}}`, eq. (4.9)
(Definition 4.11). -/
noncomputable def cutoffDipoleMeasure (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ) :
    Measure (ℂ × ℂ) :=
  (volume.restrict (box N ×ˢ box N)).withDensity fun p =>
    ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
      (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
        (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2))

/-- `C_{β,λ,ε₀}` is the truncated normalization `C_{β,λ,R}` at the length `R = ε₀ R̄_{β,λ}`. -/
theorem cutoffDipoleNormalization_eq (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ) :
    cutoffDipoleNormalization χ N p₀ β lam ε₀ =
      truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam) := rfl

/-! ### The density -/

/-- The cutoff pair density `𝟙_{|x - y| ≤ R} e^{β g_λ(x - y)}`. -/
theorem measurable_cutoffDensity (hχ : IsMollifier χ) (hlam : 0 < lam) (β R : ℝ) :
    Measurable fun p : ℂ × ℂ =>
      (closedBall (0 : ℂ) R).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
        (p.1 - p.2) :=
  ((measurable_exp_smearedKernel hχ hlam β).indicator measurableSet_closedBall).comp
    (measurable_fst.sub measurable_snd)

theorem cutoffDensity_nonneg (β R : ℝ) (p : ℂ × ℂ) :
    0 ≤ (closedBall (0 : ℂ) R).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
      (p.1 - p.2) :=
  indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

theorem cutoffDensity_le (β R : ℝ) (p : ℂ × ℂ) :
    (closedBall (0 : ℂ) R).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
      (p.1 - p.2) ≤ Real.exp (β * smearedKernel χ lam (p.1 - p.2)) :=
  indicator_le_self' (fun _ _ => (Real.exp_pos _).le) _

theorem integrableOn_cutoffDensity_box (hχ : IsMollifier χ) (hlam : 0 < lam) (β R : ℝ)
    (N : ℕ) :
    IntegrableOn (fun p : ℂ × ℂ =>
      (closedBall (0 : ℂ) R).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
        (p.1 - p.2)) (box N ×ˢ box N) := by
  refine (integrableOn_exp_smearedKernel_box hχ hlam β N).mono'
    (measurable_cutoffDensity hχ hlam β R).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoffDensity_nonneg β R p)]
  exact cutoffDensity_le β R p

/-- `N C_{β,λ,ε₀} = ∫_{Λ²} e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ ε₀ R̄}`. -/
theorem natCast_mul_cutoffDipoleNormalization (χ : ℂ → ℝ) (p₀ : ℕ) (β lam ε₀ : ℝ)
    (hN : 1 ≤ N) :
    (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ =
      ∫ p in box N ×ˢ box N,
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2) := by
  have : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  unfold cutoffDipoleNormalization
  field_simp

/-- A product of two discs of radius `δ` about the centre of `Λ` lies in `Λ²`, and its pairs are
at distance less than `2δ`. -/
theorem volume_cutoff_pos (hN : 1 ≤ N) {R : ℝ} (hR : 0 < R) :
    0 < volume ((box N ×ˢ box N) ∩ {p : ℂ × ℂ | p.1 - p.2 ∈ closedBall (0 : ℂ) R}) := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  set δ : ℝ := min (R / 2) (Real.sqrt N / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδR : δ ≤ R / 2 := min_le_left _ _
  have hδN : δ ≤ Real.sqrt N / 2 := min_le_right _ _
  set z : ℂ := ⟨Real.sqrt N / 2, Real.sqrt N / 2⟩ with hz
  have hball : ball z δ ⊆ box N :=
    ball_subset_box (by simp [hz]; linarith) (by simp [hz]; linarith) (by simp [hz]; linarith)
      (by simp [hz]; linarith)
  have hsub : ball z δ ×ˢ ball z δ ⊆
      (box N ×ˢ box N) ∩ {p : ℂ × ℂ | p.1 - p.2 ∈ closedBall (0 : ℂ) R} := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine ⟨⟨hball ha, hball hb⟩, ?_⟩
    simp only [mem_ofPred_eq, mem_closedBall, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at ha hb
    have := norm_sub_le (a - z) (b - z)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_pos (measure_ball_pos volume z hδ0).ne' (measure_ball_pos volume z hδ0).ne'

/-- `C_{β,λ,ε₀} > 0` for `N ≥ 1`, `λ > 0`, `ε₀ > 0`. -/
theorem cutoffDipoleNormalization_pos (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) : 0 < cutoffDipoleNormalization χ N p₀ β lam ε₀ := by
  have hR : 0 < ε₀ * truncationScale p₀ β lam := mul_pos hε₀ (Appendix.truncationScale_pos hlam)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hint := integrableOn_cutoffDensity_box hχ hlam β (ε₀ * truncationScale p₀ β lam) N
  have hpos : 0 < ∫ p in box N ×ˢ box N,
      (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
        (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun p => cutoffDensity_nonneg β _ p) hint]
    have hsupp : Function.support (fun p : ℂ × ℂ =>
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2)) =
        {p : ℂ × ℂ | p.1 - p.2 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)} := by
      ext p
      simp only [Function.mem_support, mem_ofPred_eq]
      by_cases h : p.1 - p.2 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)
      · simp [(Real.exp_pos _).ne', h]
      · simp [h]
    rw [hsupp, inter_comm]
    exact volume_cutoff_pos hN hR
  unfold cutoffDipoleNormalization
  exact mul_pos (by positivity) hpos

theorem natCast_mul_cutoffDipoleNormalization_pos (hχ : IsMollifier χ) (hlam : 0 < lam)
    (β : ℝ) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) :
    0 < (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ :=
  mul_pos (by exact_mod_cast hN) (cutoffDipoleNormalization_pos hχ hlam β hε₀ hN)

/-! ### The measure -/

section Marginal

variable {δ : Type*} [DecidableEq δ] {X : δ → Type*} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, Measure (X i)}

/-- A factor that does not depend on the coordinates in `s` comes out of the marginal integral
over `s`. -/
theorem lmarginal_mul_left_of_indep {s : Finset δ} (g h : (∀ i, X i) → ℝ≥0∞)
    (hh : Measurable h) (hg : ∀ x y, (∀ i ∉ s, x i = y i) → g x = g y) (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun y => g y * h y) ∂μ) x = g x * (∫⋯∫⁻_s, h ∂μ) x := by
  unfold lmarginal
  have : ∀ y : ∀ i : s, X i, g (Function.updateFinset x s y) = g x := fun y =>
    hg _ _ fun i hi => by simp [Function.updateFinset_def, hi]
  simp_rw [this]
  exact lintegral_const_mul _ (hh.comp measurable_updateFinset)

variable [∀ i, SigmaFinite (μ i)]

/-- The marginal integral over `s` of `∏_{i ∈ s} fᵢ(yᵢ)` is `∏_{i ∈ s} ∫ fᵢ`. -/
theorem lmarginal_prod_eq (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (s : Finset δ)
    (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun y => ∏ i ∈ s, f i (y i)) ∂μ) x = ∏ i ∈ s, ∫⁻ t, f i t ∂μ i := by
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert a s ha ih =>
    have hm : ∀ t : Finset δ, Measurable fun y : ∀ i, X i => ∏ i ∈ t, f i (y i) := fun t =>
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    rw [lmarginal_insert _ (hm _) ha]
    simp_rw [Finset.prod_insert ha]
    have key : ∀ z : ∀ i, X i,
        (∫⋯∫⁻_s, (fun y => f a (y a) * ∏ i ∈ s, f i (y i)) ∂μ) z =
          f a (z a) * ∏ i ∈ s, ∫⁻ t, f i t ∂μ i := by
      intro z
      rw [lmarginal_mul_left_of_indep (fun y => f a (y a)) _ (hm s)
        (fun x y hxy => by rw [hxy a ha]), ih]
    simp_rw [key, Function.update_self]
    exact lintegral_mul_const _ (hf a)

end Marginal

/-- `∫ ∏ᵢ fᵢ(xᵢ) d(⊗ᵢ μᵢ) = ∏ᵢ ∫ fᵢ dμᵢ` for `x : ι → α`, `α` inhabited. -/
theorem lintegral_pi_prod_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    [MeasurableSpace α] (a : α) (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (f : ι → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → α, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i := by
  rw [lintegral_eq_lmarginal_univ (fun _ => a), lmarginal_prod_eq f hf]

/-- `μ_{β,λ,ε₀}` has total mass one. -/
theorem cutoffDipoleMeasure_univ (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) : cutoffDipoleMeasure χ N p₀ β lam ε₀ univ = 1 := by
  unfold cutoffDipoleMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint := integrableOn_cutoffDensity_box hχ hlam β (ε₀ * truncationScale p₀ β lam) N
  have hpos := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (Filter.Eventually.of_forall fun p => mul_nonneg (inv_nonneg.2 hpos.le)
      (cutoffDensity_nonneg β _ p))]
  rw [integral_const_mul, ← natCast_mul_cutoffDipoleNormalization χ p₀ β lam ε₀ hN,
    inv_mul_cancel₀ hpos.ne']
  simp

/-- `μ_{β,λ,ε₀}` is a probability measure (eq. (4.9), Definition 4.11). -/
theorem isProbabilityMeasure_cutoffDipoleMeasure (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) : IsProbabilityMeasure (cutoffDipoleMeasure χ N p₀ β lam ε₀) :=
  ⟨cutoffDipoleMeasure_univ hχ hlam β hε₀ hN⟩

/-- `μ_{β,λ,ε₀}` is concentrated on the dipoles of `Λ²` of length at most `ε₀ R̄`. -/
theorem ae_cutoffDipoleMeasure (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ) :
    ∀ᵐ p ∂cutoffDipoleMeasure χ N p₀ β lam ε₀,
      p ∈ box N ×ˢ box N ∧ ‖p.1 - p.2‖ ≤ ε₀ * truncationScale p₀ β lam := by
  have h1 : ∀ᵐ p ∂cutoffDipoleMeasure χ N p₀ β lam ε₀, p ∈ box N ×ˢ box N :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_box_prod N))
  have h2 : ∀ᵐ p ∂cutoffDipoleMeasure χ N p₀ β lam ε₀,
      ‖p.1 - p.2‖ ≤ ε₀ * truncationScale p₀ β lam := by
    rw [ae_iff]
    have hmeas : MeasurableSet {p : ℂ × ℂ | ¬‖p.1 - p.2‖ ≤ ε₀ * truncationScale p₀ β lam} :=
      (measurableSet_le ((measurable_fst.sub measurable_snd).norm) measurable_const).compl
    unfold cutoffDipoleMeasure
    rw [withDensity_apply _ hmeas]
    refine setLIntegral_eq_zero hmeas fun p hp => ?_
    have hp' : p.1 - p.2 ∉ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam) := by
      simpa [mem_closedBall, dist_zero_right] using hp
    simp [indicator_of_notMem hp']
  filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩

/-- `μ_{β,λ,ε₀}` is invariant under the reversal `(x, y) ↦ (y, x)` of the dipole. -/
theorem measurePreserving_swap_cutoffDipoleMeasure (hχ : IsMollifier χ) (N p₀ : ℕ)
    (β lam ε₀ : ℝ) :
    MeasurePreserving Prod.swap (cutoffDipoleMeasure χ N p₀ β lam ε₀)
      (cutoffDipoleMeasure χ N p₀ β lam ε₀) := by
  have hvol : MeasurePreserving (Prod.swap : ℂ × ℂ → ℂ × ℂ) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hres := hvol.restrict_preimage (measurableSet_box_prod N)
  rw [Set.preimage_swap_prod] at hres
  refine Parity.measurePreserving_withDensity_of_comp hres MeasurableEquiv.prodComm.measurableEmbedding
    fun p => ?_
  have hmem : p.2 - p.1 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam) ↔
      p.1 - p.2 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam) := by
    simp only [mem_closedBall, dist_zero_right, norm_sub_rev]
  simp only [Prod.fst_swap, Prod.snd_swap]
  by_cases h : p.1 - p.2 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)
  · rw [indicator_of_mem h, indicator_of_mem (hmem.2 h), ← smearedKernel_neg hχ lam (p.2 - p.1),
      neg_sub]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.1 h'))]

/-- The finite powers of `μ_{β,λ,ε₀}`, as a density with respect to Lebesgue measure on
`(Λ²)^ι`. -/
theorem pi_cutoffDipoleMeasure_eq (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => cutoffDipoleMeasure χ N p₀ β lam ε₀) =
      (volume.restrict (Set.univ.pi fun _ : ι => box N ×ˢ box N)).withDensity fun c =>
        ∏ i, ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
          (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
            (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) := by
  classical
  have := isProbabilityMeasure_cutoffDipoleMeasure (p₀ := p₀) hχ hlam β hε₀ hN
  have hd : Measurable fun p : ℂ × ℂ =>
      ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_cutoffDensity hχ hlam β _).const_mul _)
  refine Measure.pi_eq (μ := fun _ : ι => cutoffDipoleMeasure χ N p₀ β lam ε₀) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    Measure.restrict_restrict (MeasurableSet.univ_pi hs), ← Set.pi_inter_distrib,
    volume_pi, Measure.restrict_pi_pi, lintegral_pi_prod_eq ((0 : ℂ), (0 : ℂ))
      (fun i => (volume : Measure (ℂ × ℂ)).restrict (s i ∩ box N ×ˢ box N)) _ (fun _ => hd)]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold cutoffDipoleMeasure
  rw [withDensity_apply _ (hs i), Measure.restrict_restrict (hs i)]

/-! ### The cutoff `ε₀ = ∞` -/

/-- Dipoles of `Λ²` have length at most `2 √N`. -/
theorem norm_sub_le_of_mem_box {p : ℂ × ℂ} (hp : p ∈ box N ×ˢ box N) :
    ‖p.1 - p.2‖ ≤ 2 * Real.sqrt N := by
  obtain ⟨h1, h2⟩ := hp
  rw [box, Complex.mem_reProdIm] at h1 h2
  have hre : |(p.1 - p.2).re| ≤ Real.sqrt N := by
    rw [Complex.sub_re, abs_le]
    constructor <;> linarith [h1.1.1, h1.1.2, h2.1.1, h2.1.2]
  have him : |(p.1 - p.2).im| ≤ Real.sqrt N := by
    rw [Complex.sub_im, abs_le]
    constructor <;> linarith [h1.2.1, h1.2.2, h2.2.1, h2.2.2]
  calc ‖p.1 - p.2‖ ≤ |(p.1 - p.2).re| + |(p.1 - p.2).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * Real.sqrt N := by linarith

/-- If the cutoff `ε₀ R̄` exceeds `2 √N` (the cutoff is vacuous on `Λ²`), then
`C_{β,λ,ε₀} = C_{β,λ}`: the convention `C_{β,λ,∞} = C_{β,λ}` of Definition 4.11. -/
theorem cutoffDipoleNormalization_eq_of_le (hle : 2 * Real.sqrt N ≤ ε₀ * truncationScale p₀ β lam) :
    cutoffDipoleNormalization χ N p₀ β lam ε₀ = dipoleNormalization χ N β lam := by
  unfold cutoffDipoleNormalization dipoleNormalization
  congr 1
  refine setIntegral_congr_fun (measurableSet_box_prod N) fun p hp => ?_
  have : p.1 - p.2 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam) := by
    rw [mem_closedBall, dist_zero_right]
    exact (norm_sub_le_of_mem_box hp).trans hle
  simp only [indicator_of_mem this]

/-- If the cutoff `ε₀ R̄` exceeds `2 √N`, then `μ_{β,λ,ε₀} = μ_{β,λ}`: the convention
`μ_{β,λ,∞} = μ_{β,λ}` of Definition 4.11. -/
theorem cutoffDipoleMeasure_eq_of_le (hle : 2 * Real.sqrt N ≤ ε₀ * truncationScale p₀ β lam) :
    cutoffDipoleMeasure χ N p₀ β lam ε₀ = dipoleMeasure χ N β lam := by
  unfold cutoffDipoleMeasure dipoleMeasure
  rw [cutoffDipoleNormalization_eq_of_le hle]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_box_prod N)] with p hp
  have : p.1 - p.2 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam) := by
    rw [mem_closedBall, dist_zero_right]
    exact (norm_sub_le_of_mem_box hp).trans hle
  simp only [indicator_of_mem this]

/-! ### Lemma 4.12 -/

/-- `ε₀ R̄_{β,λ} ≤ R_{β,λ}` for `ε₀ ≤ 1` (proof of Lemma 4.12). -/
theorem ofReal_cutoff_le_criticalScale (hlam : 0 < lam) (hε₁ : ε₀ ≤ 1) :
    ENNReal.ofReal (ε₀ * truncationScale p₀ β lam) ≤ criticalScale β lam := by
  by_cases hβ : β < 4
  · rw [criticalScale, ite_eq_left hβ]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Appendix.truncationScale_of_lt hβ hlam]
    have : 0 ≤ lam ^ (-(β - 2) / (4 - β)) := Real.rpow_nonneg hlam.le _
    nlinarith
  · rw [criticalScale, ite_eq_right hβ]
    exact le_top

/-- The limit of `C_{β,λ,ε₀}` lies in `[0, λ^{2-β} 𝒵_β]`. -/
theorem setIntegral_closedBall_exp_smearedKernel_mem (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (R : ℝ) :
    0 ≤ ∫ w in closedBall (0 : ℂ) R, Real.exp (β * smearedKernel χ lam w) ∧
      ∫ w in closedBall (0 : ℂ) R, Real.exp (β * smearedKernel χ lam w) ≤
        lam ^ (2 - β) * dipoleConstant χ β := by
  refine ⟨setIntegral_nonneg measurableSet_closedBall fun w _ => (Real.exp_pos _).le, ?_⟩
  rw [← integral_exp_smearedKernel hχ hlam β]
  exact setIntegral_le_integral (integrable_exp_smearedKernel hχ hlam hβ)
    (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)

/-- **Lemma 4.12, eq. (4.11)** (Lemma 4.12): for `β > 2` there is
`C > 0`, depending only on `β` (and the fixed mollifier), such that for every `ε₀ ∈ (0, 1)` and
`λ ∈ (0, 1)`, `C_{β,λ,ε₀} = λ^{2-β} (𝒵_β + O((ε₀ R̄_{β,λ})^{-2}))` as `N → ∞`: `C_{β,λ,ε₀}`
converges to a limit `L` with `|L - λ^{2-β} 𝒵_β| ≤ λ^{2-β} C (ε₀ R̄_{β,λ})^{-2}`. -/
theorem lem411_devtCbeta (hχ : IsMollifier χ) (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p₀ : ℕ) (ε₀ lam : ℝ), 0 < ε₀ → ε₀ < 1 → 0 < lam → lam < 1 →
      ∃ L : ℝ, Tendsto (fun N : ℕ => cutoffDipoleNormalization χ N p₀ β lam ε₀) atTop (𝓝 L) ∧
        |L - lam ^ (2 - β) * dipoleConstant χ β| ≤
          lam ^ (2 - β) * (C * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹) := by
  have hZ := dipoleConstant_pos hχ hβ
  refine ⟨max (2 * Real.pi / (β - 2)) (4 * dipoleConstant χ β),
    lt_max_of_lt_right (by positivity), fun p₀ ε₀ lam hε₀ hε₁ hlam hlam1 => ?_⟩
  set R := ε₀ * truncationScale p₀ β lam with hR
  have hR0 : 0 < R := mul_pos hε₀ (Appendix.truncationScale_pos hlam)
  have hl : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hRinv : 0 ≤ (R ^ 2)⁻¹ := by positivity
  by_cases h2 : 2 * lam ≤ R
  · obtain ⟨L, hL, hbound⟩ := truncatedDipoleNormalization_asymptotics hχ hβ hlam hlam1.le h2
      (ofReal_cutoff_le_criticalScale hlam hε₁.le)
    refine ⟨L, hL, hbound.trans ?_⟩
    gcongr
    exact le_max_left _ _
  · refine ⟨_, tendsto_truncatedDipoleNormalization hχ hlam β R, ?_⟩
    obtain ⟨hI0, hI1⟩ := setIntegral_closedBall_exp_smearedKernel_mem hχ hβ hlam R
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have hR2 : R ^ 2 ≤ 4 := by nlinarith
    have h4 : 1 ≤ 4 * (R ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    calc lam ^ (2 - β) * dipoleConstant χ β -
          ∫ w in closedBall (0 : ℂ) R, Real.exp (β * smearedKernel χ lam w)
        ≤ lam ^ (2 - β) * (dipoleConstant χ β * 1) := by linarith
      _ ≤ lam ^ (2 - β) * (dipoleConstant χ β * (4 * (R ^ 2)⁻¹)) := by gcongr
      _ = lam ^ (2 - β) * (4 * dipoleConstant χ β * (R ^ 2)⁻¹) := by ring
      _ ≤ lam ^ (2 - β) * (max (2 * Real.pi / (β - 2)) (4 * dipoleConstant χ β) *
            (R ^ 2)⁻¹) := by
          gcongr
          exact le_max_right _ _

/-- **Lemma 4.12, eq. (4.11)**, for all large `N`: with the constant `2C`,
`|C_{β,λ,ε₀} - λ^{2-β} 𝒵_β| ≤ λ^{2-β} 2C (ε₀ R̄_{β,λ})^{-2}` for all large `N`. -/
theorem lem411_devtCbeta_eventually (hχ : IsMollifier χ) (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p₀ : ℕ) (ε₀ lam : ℝ), 0 < ε₀ → ε₀ < 1 → 0 < lam → lam < 1 →
      ∀ᶠ N : ℕ in atTop, |cutoffDipoleNormalization χ N p₀ β lam ε₀ -
          lam ^ (2 - β) * dipoleConstant χ β| ≤
        lam ^ (2 - β) * (C * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹) := by
  obtain ⟨C, hC, h⟩ := lem411_devtCbeta hχ hβ
  refine ⟨2 * C, by positivity, fun p₀ ε₀ lam hε₀ hε₁ hlam hlam1 => ?_⟩
  obtain ⟨L, hL, hbound⟩ := h p₀ ε₀ lam hε₀ hε₁ hlam hlam1
  have hR0 : 0 < ε₀ * truncationScale p₀ β lam := mul_pos hε₀ (Appendix.truncationScale_pos hlam)
  set a := lam ^ (2 - β) * (C * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹) with ha
  have ha0 : 0 < a := by positivity
  have hball : ∀ᶠ N : ℕ in atTop, |cutoffDipoleNormalization χ N p₀ β lam ε₀ - L| < a :=
    (Metric.tendsto_nhds.1 hL) a ha0 |>.mono fun N hN => by rwa [Real.dist_eq] at hN
  filter_upwards [hball] with N hN
  calc |cutoffDipoleNormalization χ N p₀ β lam ε₀ - lam ^ (2 - β) * dipoleConstant χ β|
      ≤ |cutoffDipoleNormalization χ N p₀ β lam ε₀ - L| +
          |L - lam ^ (2 - β) * dipoleConstant χ β| := abs_sub_le _ _ _
    _ ≤ a + a := add_le_add hN.le hbound
    _ = lam ^ (2 - β) * (2 * C * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹) := by rw [ha]; ring

/-- **Lemma 4.12, eq. (4.12)** (Lemma 4.12): for `β > 2` and
`ε₀ > 0` there is `λ₀ > 0` (depending on `ε₀`, `β`) such that for `λ ∈ (0, λ₀)`,
`C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β} / 2` for all large `N`. -/
theorem lem411_lower (hχ : IsMollifier χ) (hβ : 2 < β) (hε₀ : 0 < ε₀) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ →
      ∀ᶠ N : ℕ in atTop,
        1 / 2 * dipoleConstant χ β * lam ^ (2 - β) ≤ cutoffDipoleNormalization χ N p₀ β lam ε₀ := by
  have hZ := dipoleConstant_pos hχ hβ
  have hb : 0 < β - 2 := by linarith
  set K : ℝ := 4 * Real.pi * ε₀ ^ (2 - β) / ((β - 2) * dipoleConstant χ β) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min (min 1 (ε₀ / 2)) (K ^ (1 / (2 - β))), lt_min (lt_min one_pos (by linarith))
    (Real.rpow_pos_of_pos hK0 _), fun p₀ lam hlam hlt => ?_⟩
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hlamε : lam < ε₀ / 2 := hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hlamK : lam < K ^ (1 / (2 - β)) := hlt.trans_le (min_le_right _ _)
  have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
  set R := ε₀ * truncationScale p₀ β lam with hR
  have hεR : ε₀ ≤ R := le_mul_of_one_le_right hε₀.le hR1
  refine eventually_half_le_truncatedDipoleNormalization hχ hβ hlam (by linarith) ?_
  have hRp : R ^ (2 - β) ≤ ε₀ ^ (2 - β) := Real.rpow_le_rpow_of_nonpos hε₀ hεR (by linarith)
  have hKl : K < lam ^ (2 - β) := by
    have := Real.rpow_lt_rpow_of_neg hlam hlamK (by linarith : 2 - β < 0)
    rwa [← Real.rpow_mul hK0.le, one_div_mul_cancel (by linarith : (2 - β) ≠ 0),
      Real.rpow_one] at this
  have hc : 0 ≤ 2 * Real.pi / (β - 2) := by positivity
  calc 2 * Real.pi / (β - 2) * R ^ (2 - β) ≤ 2 * Real.pi / (β - 2) * ε₀ ^ (2 - β) := by gcongr
    _ = 1 / 2 * dipoleConstant χ β * K := by
        rw [hK]
        field_simp
        ring
    _ < 1 / 2 * dipoleConstant χ β * lam ^ (2 - β) := by gcongr

/-- **Lemma 4.12, eq. (4.13)** (Lemma 4.12): for `β > 2` there
is `C > 0` depending only on `β` (and the fixed mollifier) such that, for every `ε₀ ∈ (0, 1)`,
there is `λ₀ > 0` with: for `λ ∈ (0, λ₀)`, for all large `N`,
`|C_{β,λ,ε₀} - C_{β,λ}| / C_{β,λ} ≤ C (ε₀ R̄_{β,λ})^{-2}`. -/
theorem lem411_compare (hχ : IsMollifier χ) (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop,
        |cutoffDipoleNormalization χ N p₀ β lam ε₀ - dipoleNormalization χ N β lam| /
            dipoleNormalization χ N β lam ≤
          C * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹ := by
  have hZ := dipoleConstant_pos hχ hβ
  have hb : 0 < β - 2 := by linarith
  refine ⟨4 * Real.pi / ((β - 2) * dipoleConstant χ β), by positivity,
    fun ε₀ hε₀ hε₁ => ⟨min 1 (ε₀ / 2), lt_min one_pos (by linarith),
      fun p₀ lam hlam hlt => ?_⟩⟩
  have hlam1 : lam ≤ 1 := (hlt.trans_le (min_le_left _ _)).le
  have hlamε : lam < ε₀ / 2 := hlt.trans_le (min_le_right _ _)
  have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
  have hεR : ε₀ ≤ ε₀ * truncationScale p₀ β lam := le_mul_of_one_le_right hε₀.le hR1
  exact eventually_abs_truncated_sub_div_le hχ hβ hlam hlam1 (by linarith)
    (ofReal_cutoff_le_criticalScale hlam hε₁.le)

end Hierarchical

end MultipoleBKT

end
