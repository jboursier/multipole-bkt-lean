/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.FrozenData
public import Mathlib.Topology.Algebra.Order.Group

/-!
# Measurability and bounds for the frozen-bad-point interactions

Analytic facts about the objects of `MultipoleBKT.UpperBound.Hierarchical.FrozenData` used to
integrate them against the dipole measure (the paper, Section 5.3,
Definitions 5.13–5.15): the radii `τ^Z` depend on the dipoles, so the kernels
`g * δ^{(α)} * δ^{(η)}` must be controlled jointly in the radii.

* `twoRadiusKernel_eq_integral_scaled`, `measurable_twoRadiusKernel_comp`: for positive radii,
  `(g * δ₀^{(α)} * δ₀^{(η)})(z) = ∬ g(z - α a - η b) dδ₀^{(1)}(a) dδ₀^{(1)}(b)`, hence the kernel is
  jointly measurable in `(α, η, z)` on `α, η > 0`;
* `neg_log_le_twoRadiusKernel`, `abs_twoRadiusKernel_le`: for radii in `[λ, R]` and `|z| ≤ D`,
  `-log(2R + D) ≤ (g * δ^{(α)} * δ^{(η)})(z) ≤ -log λ + c_χ`;
* `abs_pairInteraction_le`: the same bound for the interaction `v^Z`;
* `continuous_badDistZ`, `continuous_goodRadiusZ`, `measurable_interactionGoodZ`,
  `measurable_interactionExtZ`, `measurableSet_isGoodZ`, `measurable_dipoleWeightZ`,
  `measurable_hatDipoleWeightZ`: measurability in the good dipoles.
-/

@[expose] public section

open MeasureTheory Metric Set
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

namespace UpperBound

variable {N : ℕ} {χ : ℂ → ℝ}

/-! ### The two-radius kernel, jointly in the radii -/

section Kernel

theorem measurable_logKernel : Measurable logKernel := by
  unfold logKernel
  fun_prop

/-- For positive radii, the two-radius kernel is an integral against the fixed measure
`δ₀^{(1)} ⊗ δ₀^{(1)}`. -/
theorem twoRadiusKernel_eq_integral_scaled (hχ : IsMollifier χ) {α η : ℝ} (hα : 0 < α)
    (hη : 0 < η) (z : ℂ) :
    twoRadiusKernel χ α η z =
      ∫ p : ℂ × ℂ, logKernel (z - (α : ℂ) * p.1 - (η : ℂ) * p.2)
        ∂(smearedCharge χ 0 1).prod (smearedCharge χ 0 1) := by
  rw [twoRadiusKernel_eq_integral_conv hχ, smearedCharge_eq_map hχ 0 hα,
    smearedCharge_eq_map hχ 0 hη, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    integral_map (f := fun p : ℂ × ℂ => logKernel (z - p.1 - p.2)) (by fun_prop)
      (measurable_logKernel.comp (by fun_prop)).aestronglyMeasurable]
  simp only [Prod.map, zero_add]

/-- The scaled kernel, a jointly measurable function of `(α, η, z)`. -/
noncomputable def scaledKernel (χ : ℂ → ℝ) (x : ℝ × ℝ × ℂ) : ℝ :=
  ∫ p : ℂ × ℂ, logKernel (x.2.2 - (x.1 : ℂ) * p.1 - (x.2.1 : ℂ) * p.2)
    ∂(smearedCharge χ 0 1).prod (smearedCharge χ 0 1)

theorem measurable_scaledKernel : Measurable (scaledKernel χ) := by
  have h : StronglyMeasurable fun q : (ℝ × ℝ × ℂ) × (ℂ × ℂ) =>
      logKernel (q.1.2.2 - (q.1.1 : ℂ) * q.2.1 - (q.1.2.1 : ℂ) * q.2.2) :=
    (measurable_logKernel.comp (by fun_prop)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := (smearedCharge χ 0 1).prod (smearedCharge χ 0 1))).measurable

/-- **Joint measurability of the two-radius kernel** for positive measurable radii. -/
theorem measurable_twoRadiusKernel_comp (hχ : IsMollifier χ) {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} {z : X → ℂ} (ha : Measurable a) (hb : Measurable b) (hz : Measurable z)
    (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x) :
    Measurable fun x => twoRadiusKernel χ (a x) (b x) (z x) := by
  have : (fun x => twoRadiusKernel χ (a x) (b x) (z x)) =
      fun x => scaledKernel χ (a x, b x, z x) := by
    funext x
    rw [twoRadiusKernel_eq_integral_scaled hχ (ha0 x) (hb0 x)]
    rfl
  rw [this]
  exact measurable_scaledKernel.comp (ha.prodMk (hb.prodMk hz))

/-- The constant `c_χ = ∫ g dδ₀^{(1)}`. -/
noncomputable abbrev kernelConst (χ : ℂ → ℝ) : ℝ := ∫ y, logKernel y ∂smearedCharge χ 0 1

/-- **Lower bound**: `(g * δ₀^{(α)} * δ₀^{(η)})(z) ≥ -log(α + η + |z|)` for `α, η > 0`. -/
theorem neg_log_le_twoRadiusKernel (hχ : IsMollifier χ) {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (z : ℂ) : -Real.log (α + η + ‖z‖) ≤ twoRadiusKernel χ α η z := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  have := isProbabilityMeasure_smearedCharge hχ z hη
  unfold twoRadiusKernel
  have hae : ∀ᵐ p ∂(smearedCharge χ 0 α).prod (smearedCharge χ z η),
      -Real.log (α + η + ‖z‖) ≤ logKernel (p.1 - p.2) := by
    have h1 : ∀ᵐ p ∂(smearedCharge χ 0 α).prod (smearedCharge χ z η), p.1 ∈ closedBall (0 : ℂ) α :=
      (Measure.quasiMeasurePreserving_fst).ae (ae_mem_closedBall_smearedCharge hχ hα)
    have h2 : ∀ᵐ p ∂(smearedCharge χ 0 α).prod (smearedCharge χ z η), p.2 ∈ closedBall z η :=
      (Measure.quasiMeasurePreserving_snd).ae (ae_mem_closedBall_smearedCharge hχ hη)
    filter_upwards [h1, h2, ae_prod_smearedCharge_ne χ 0 z α η] with p hp1 hp2 hp3
    rw [mem_closedBall, dist_zero_right] at hp1
    rw [mem_closedBall, dist_eq_norm] at hp2
    have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp3)
    have hle : ‖p.1 - p.2‖ ≤ α + η + ‖z‖ := by
      calc ‖p.1 - p.2‖ = ‖p.1 - (p.2 - z) - z‖ := by congr 1; ring
        _ ≤ ‖p.1‖ + ‖p.2 - z‖ + ‖z‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
        _ ≤ α + η + ‖z‖ := by linarith
    unfold logKernel
    exact neg_le_neg (Real.log_le_log hpos hle)
  calc -Real.log (α + η + ‖z‖)
      = ∫ _p, -Real.log (α + η + ‖z‖) ∂(smearedCharge χ 0 α).prod (smearedCharge χ z η) := by
        rw [integral_const, probReal_univ, one_smul]
    _ ≤ _ := integral_mono_ae (integrable_const _)
        (integrable_logKernel_prod_smearedCharge hχ 0 z α η) hae

/-- **Two-sided bound**: for `λ ≤ α, η ≤ R` (`λ > 0`) and `|z| ≤ D`,
`|(g * δ₀^{(α)} * δ₀^{(η)})(z)| ≤ |log(2R + D)| + |log λ| + |c_χ|`. -/
theorem abs_twoRadiusKernel_le (hχ : IsMollifier χ) {lam α η R D : ℝ} (hlam : 0 < lam)
    (hα : lam ≤ α) (hη : lam ≤ η) (hαR : α ≤ R) (hηR : η ≤ R) {z : ℂ} (hz : ‖z‖ ≤ D) :
    |twoRadiusKernel χ α η z| ≤ |Real.log (2 * R + D)| + |Real.log lam| + |kernelConst χ| := by
  have hα0 : 0 < α := hlam.trans_le hα
  have hη0 : 0 < η := hlam.trans_le hη
  have hlo := neg_log_le_twoRadiusKernel hχ hα0 hη0 z
  have hhi := twoRadiusKernel_le_right hχ hα0 hη0 z
  have hlog : -Real.log (2 * R + D) ≤ -Real.log (α + η + ‖z‖) := by
    refine neg_le_neg (Real.log_le_log (by positivity) (by linarith))
  have hη' : logKernel (η : ℂ) ≤ -Real.log lam := by
    unfold logKernel
    rw [Complex.norm_real, Real.norm_of_nonneg hη0.le]
    exact neg_le_neg (Real.log_le_log hlam hη)
  rw [abs_le]
  constructor
  · have := le_abs_self (Real.log (2 * R + D))
    have := abs_nonneg (Real.log lam)
    have := abs_nonneg (kernelConst χ)
    linarith
  · have := neg_abs_le (Real.log lam)
    have := le_abs_self (kernelConst χ)
    have := abs_nonneg (Real.log (2 * R + D))
    linarith

/-- The bound of `abs_twoRadiusKernel_le`. -/
noncomputable def kernelBound (χ : ℂ → ℝ) (lam R D : ℝ) : ℝ :=
  |Real.log (2 * R + D)| + |Real.log lam| + |kernelConst χ|

/-- **Bound on the interaction** `v^Z`: if the four radii lie in `[λ, R]` and the four cross
differences have norm at most `D`, then `|v^Z| ≤ 8 (|log(2R + D)| + |log λ| + |c_χ|)`. -/
theorem abs_pairInteraction_le (hχ : IsMollifier χ) {lam R D : ℝ} (hlam : 0 < lam)
    (hlamR : lam ≤ R) {a b : ℂ × ℂ} {ta tb : ℝ × ℝ}
    (ha1 : lam ≤ ta.1 ∧ ta.1 ≤ R) (ha2 : lam ≤ ta.2 ∧ ta.2 ≤ R)
    (hb1 : lam ≤ tb.1 ∧ tb.1 ≤ R) (hb2 : lam ≤ tb.2 ∧ tb.2 ≤ R)
    (h11 : ‖a.1 - b.1‖ ≤ D) (h21 : ‖a.2 - b.1‖ ≤ D) (h12 : ‖a.1 - b.2‖ ≤ D)
    (h22 : ‖a.2 - b.2‖ ≤ D) :
    |pairInteraction χ lam a b ta tb| ≤ 8 * kernelBound χ lam R D := by
  have hg : ∀ {w : ℂ}, ‖w‖ ≤ D → |smearedKernel χ lam w| ≤ kernelBound χ lam R D := fun hw =>
    abs_twoRadiusKernel_le hχ hlam le_rfl le_rfl hlamR hlamR hw
  have hK : ∀ {α η : ℝ} {w : ℂ}, lam ≤ α ∧ α ≤ R → lam ≤ η ∧ η ≤ R → ‖w‖ ≤ D →
      |twoRadiusKernel χ α η w| ≤ kernelBound χ lam R D := fun hα hη hw =>
    abs_twoRadiusKernel_le hχ hlam hα.1 hη.1 hα.2 hη.2 hw
  unfold pairInteraction
  have e1 := hg h11
  have e2 := hg h21
  have e3 := hg h12
  have e4 := hg h22
  have f1 := hK ha1 hb1 h11
  have f2 := hK ha2 hb1 h21
  have f3 := hK ha1 hb2 h12
  have f4 := hK ha2 hb2 h22
  rw [abs_le] at e1 e2 e3 e4 f1 f2 f3 f4 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, f1.1, f1.2, f2.1,
    f2.2, f3.1, f3.2, f4.1, f4.2]

end Kernel

/-! ### Measurability in the good dipoles -/

section Measurability

variable (χ) (p₀ : ℕ) (β lam M ε₀ L : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ)

theorem continuous_dipoleDist_left (e : ℂ × ℂ) : Continuous fun d : ℂ × ℂ => dipoleDist d e := by
  unfold dipoleDist
  fun_prop

theorem continuous_badDistZ : Continuous (badDistZ p₀ β lam ε₀ V Z) := by
  classical
  unfold badDistZ
  induction V using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert j V hj ih =>
    simp only [Finset.fold_insert hj]
    exact (continuous_dipoleDist_left (Z j)).min ih

theorem continuous_goodRadiusZ : Continuous (goodRadiusZ p₀ β lam ε₀ V Z) := by
  unfold goodRadiusZ
  exact ((continuous_badDistZ p₀ β lam ε₀ V Z).div_const 4).max continuous_const

variable {χ}

/-- `v^Z` of two good dipoles is measurable in the pair. -/
theorem measurable_interactionGoodZ (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => interactionGoodZ χ p₀ β lam ε₀ V Z q.1 q.2 := by
  have hτ := (continuous_goodRadiusZ p₀ β lam ε₀ V Z).measurable
  have hτ1 : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => goodRadiusZ p₀ β lam ε₀ V Z q.1 :=
    hτ.comp measurable_fst
  have hτ2 : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => goodRadiusZ p₀ β lam ε₀ V Z q.2 :=
    hτ.comp measurable_snd
  have hpos : ∀ e, 0 < goodRadiusZ p₀ β lam ε₀ V Z e := fun e => goodRadiusZ_pos hlam e
  have hg := (continuous_smearedKernel hχ hlam).measurable
  have hK : ∀ {u v : (ℂ × ℂ) × (ℂ × ℂ) → ℝ} {w : (ℂ × ℂ) × (ℂ × ℂ) → ℂ}, Measurable u →
      Measurable v → Measurable w → (∀ q, 0 < u q) → (∀ q, 0 < v q) →
      Measurable fun q => twoRadiusKernel χ (u q) (v q) (w q) :=
    fun hu hv hw hu0 hv0 => measurable_twoRadiusKernel_comp hχ hu hv hw hu0 hv0
  unfold interactionGoodZ pairInteraction
  refine Measurable.sub (Measurable.sub (Measurable.sub (hg.comp (by fun_prop))
    (hK hτ1 hτ2 (by fun_prop) (fun q => hpos _) (fun q => hpos _)))
    (Measurable.sub (hg.comp (by fun_prop))
      (hK hτ1 hτ2 (by fun_prop) (fun q => hpos _) (fun q => hpos _))))
    (Measurable.sub (Measurable.sub (hg.comp (by fun_prop))
      (hK hτ1 hτ2 (by fun_prop) (fun q => hpos _) (fun q => hpos _)))
    (Measurable.sub (hg.comp (by fun_prop))
      (hK hτ1 hτ2 (by fun_prop) (fun q => hpos _) (fun q => hpos _))))

/-- `v^Z` of a good dipole with a bad label is measurable in the good dipole. -/
theorem measurable_interactionExtZ (hχ : IsMollifier χ) (hlam : 0 < lam) (j : Fin N) :
    Measurable fun d : ℂ × ℂ => interactionExtZ χ p₀ β lam ε₀ V Z d j := by
  have hτ := (continuous_goodRadiusZ p₀ β lam ε₀ V Z).measurable
  have hpos : ∀ e, 0 < goodRadiusZ p₀ β lam ε₀ V Z e := fun e => goodRadiusZ_pos hlam e
  have hb1 : 0 < (badRadiiZ p₀ β lam ε₀ V Z j).1 := hlam.trans_le (lam_le_badRadiusPlusOn j)
  have hb2 : 0 < (badRadiiZ p₀ β lam ε₀ V Z j).2 := hlam.trans_le (lam_le_badRadiusMinusOn j)
  have hg := (continuous_smearedKernel hχ hlam).measurable
  have hK : ∀ {u : ℂ × ℂ → ℝ} {v : ℝ} {w : ℂ × ℂ → ℂ}, Measurable u → Measurable w →
      (∀ q, 0 < u q) → 0 < v → Measurable fun q => twoRadiusKernel χ (u q) v (w q) :=
    fun hu hw hu0 hv0 => measurable_twoRadiusKernel_comp hχ hu measurable_const hw hu0
      (fun _ => hv0)
  unfold interactionExtZ pairInteraction
  refine Measurable.sub (Measurable.sub (Measurable.sub (hg.comp (by fun_prop))
    (hK hτ (by fun_prop) hpos hb1)) (Measurable.sub (hg.comp (by fun_prop))
      (hK hτ (by fun_prop) hpos hb1)))
    (Measurable.sub (Measurable.sub (hg.comp (by fun_prop))
      (hK hτ (by fun_prop) hpos hb2)) (Measurable.sub (hg.comp (by fun_prop))
      (hK hτ (by fun_prop) hpos hb2)))

theorem measurableSet_isGoodZ : MeasurableSet {e : ℂ × ℂ | IsGoodZ p₀ β lam M ε₀ V Z e} := by
  classical
  have h1 : ∀ j : Fin N, MeasurableSet {e : ℂ × ℂ | M * max ‖e.1 - e.2‖ lam < dipoleDist e (Z j)} :=
    fun j => measurableSet_lt (by fun_prop) (continuous_dipoleDist_left (Z j)).measurable
  have h3 : ∀ j : Fin N, MeasurableSet {e : ℂ × ℂ |
      M * max (min ‖e.1 - e.2‖ ‖(Z j).1 - (Z j).2‖) lam < dipoleDist e (Z j)} :=
    fun j => measurableSet_lt (by fun_prop) (continuous_dipoleDist_left (Z j)).measurable
  have hset : {e : ℂ × ℂ | IsGoodZ p₀ β lam M ε₀ V Z e} =
      (⋂ j ∈ ((typeOneOn p₀ β lam ε₀ V Z ∪ typeTwoOn p₀ β lam M ε₀ V Z : Finset (Fin N)) :
          Set (Fin N)), {e : ℂ × ℂ | M * max ‖e.1 - e.2‖ lam < dipoleDist e (Z j)}) ∩
        ⋂ j ∈ ((typeThreeOn p₀ β lam M ε₀ V Z : Finset (Fin N)) : Set (Fin N)),
          {e : ℂ × ℂ | M * max (min ‖e.1 - e.2‖ ‖(Z j).1 - (Z j).2‖) lam < dipoleDist e (Z j)} := by
    ext e
    simp [IsGoodZ]
  rw [hset]
  exact (MeasurableSet.biInter (Set.to_countable _) fun j _ => h1 j).inter
    (MeasurableSet.biInter (Set.to_countable _) fun j _ => h3 j)

theorem measurable_dipoleWeightZ : Measurable (dipoleWeightZ p₀ β lam M ε₀ L V Z) := by
  classical
  have hτ := (continuous_goodRadiusZ p₀ β lam ε₀ V Z).measurable
  unfold dipoleWeightZ
  refine Measurable.mul (Real.measurable_exp.comp (measurable_const.mul
    ((Measurable.div (by fun_prop) hτ).pow_const 2))) ?_
  exact Measurable.ite (measurableSet_isGoodZ p₀ β lam M ε₀ V Z) measurable_const
    measurable_const

theorem measurable_hatDipoleWeightZ (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Measurable (hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z) := by
  unfold hatDipoleWeightZ
  exact (measurable_dipoleWeightZ p₀ β lam M ε₀ L V Z).mul (Finset.measurable_prod _ fun j _ =>
    Real.measurable_exp.comp (measurable_const.mul
      (measurable_interactionExtZ p₀ β lam ε₀ V Z hχ hlam j)))

end Measurability

end UpperBound

end MultipoleBKT

end
