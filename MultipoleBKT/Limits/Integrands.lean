/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Radial

/-!
# Activity integrands as box integrals

See the proof of Lemma 4.26: the activities are
integrals against `μ_{β,λ}^{⊗ k}`, whose density with respect to Lebesgue measure on `(Λ²)^k` is
`(N C_{β,λ})^{-k} ∏ᵢ e^{β g_λ(xᵢ - yᵢ)}` (equation (2.30)).

* `integral_pi_dipoleMeasure`:
  `∫ F dμ^{⊗ ι} = (N C_{β,λ})^{-|ι|} ∫_{(Λ²)^ι} F(c) ∏ᵢ e^{β g_λ(xᵢ - yᵢ)} dc`;
* the translation invariance of the pair weights (`multipoleLinked_translate`,
  `isStableDipolePair_translate`, `dipoleInteraction_translate`, …).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

/-- The weight `e^{β g_λ(x - y)}` of a dipole `p = (x, y)`. -/
noncomputable def pairDensity (χ : ℂ → ℝ) (β lam : ℝ) (p : ℂ × ℂ) : ℝ :=
  Real.exp (β * smearedKernel χ lam (p.1 - p.2))

theorem pairDensity_pos (χ : ℂ → ℝ) (β lam : ℝ) (p : ℂ × ℂ) : 0 < pairDensity χ β lam p :=
  Real.exp_pos _

theorem measurable_pairDensity (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) :
    Measurable (pairDensity χ β lam) :=
  (measurable_exp_smearedKernel hχ hlam β).comp (measurable_fst.sub measurable_snd)

/-! ### Translation invariance -/

section Translation

variable (a : ℂ) (d e : ℂ × ℂ)

theorem add_diag_fst_sub_snd : (d + (a, a)).1 - (e + (a, a)).2 = d.1 - e.2 := by
  simp only [Prod.fst_add, Prod.snd_add]; ring

theorem add_diag_fst_sub_fst : (d + (a, a)).1 - (e + (a, a)).1 = d.1 - e.1 := by
  simp only [Prod.fst_add]; ring

theorem add_diag_snd_sub_snd : (d + (a, a)).2 - (e + (a, a)).2 = d.2 - e.2 := by
  simp only [Prod.snd_add]; ring

theorem add_diag_snd_sub_fst : (d + (a, a)).2 - (e + (a, a)).1 = d.2 - e.1 := by
  simp only [Prod.fst_add, Prod.snd_add]; ring

theorem multipoleLinked_translate (M lam : ℝ) :
    MultipoleLinked M lam (d + (a, a)) (e + (a, a)) ↔ MultipoleLinked M lam d e := by
  unfold MultipoleLinked
  rw [add_diag_fst_sub_fst, add_diag_fst_sub_snd, add_diag_snd_sub_fst, add_diag_snd_sub_snd,
    add_diag_fst_sub_snd a d d, add_diag_fst_sub_snd a e e]

theorem isStableDipolePair_translate :
    IsStableDipolePair (d + (a, a)) (e + (a, a)) ↔ IsStableDipolePair d e := by
  rw [isStableDipolePair_iff, isStableDipolePair_iff, add_diag_fst_sub_snd,
    add_diag_fst_sub_snd a d e, add_diag_fst_sub_snd a e d, add_diag_fst_sub_snd a e e]

theorem dipoleInteraction_translate (χ : ℂ → ℝ) (lam : ℝ) :
    dipoleInteraction χ lam (d + (a, a)) (e + (a, a)) = dipoleInteraction χ lam d e := by
  unfold dipoleInteraction
  rw [add_diag_fst_sub_fst, add_diag_snd_sub_snd, add_diag_fst_sub_snd, add_diag_fst_sub_snd]

theorem stablePairWeight_translate (χ : ℂ → ℝ) (β lam : ℝ) :
    stablePairWeight χ β lam (d + (a, a)) (e + (a, a)) = stablePairWeight χ β lam d e := by
  unfold stablePairWeight
  rw [dipoleInteraction_translate]
  congr 1
  exact propext (isStableDipolePair_translate a d e)

theorem unlinkedPairWeight_translate (χ : ℂ → ℝ) (β lam M : ℝ) :
    unlinkedPairWeight χ β lam M (d + (a, a)) (e + (a, a)) = unlinkedPairWeight χ β lam M d e := by
  unfold unlinkedPairWeight
  rw [dipoleInteraction_translate]
  congr 1
  exact propext (multipoleLinked_translate a d e M lam)

theorem pairDensity_translate (χ : ℂ → ℝ) (β lam : ℝ) :
    pairDensity χ β lam (d + (a, a)) = pairDensity χ β lam d := by
  unfold pairDensity
  rw [add_diag_fst_sub_snd]

end Translation

/-! ### Integrals against `μ^{⊗ ι}` as box integrals -/

section PiDensity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pi_dipoleMeasure_eq (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hN : 1 ≤ N) :
    Measure.pi (fun _ : ι => dipoleMeasure χ N β lam) =
      (volume.restrict (boxConfig ι N)).withDensity fun c =>
        ∏ i, ENNReal.ofReal ((N * dipoleNormalization χ N β lam)⁻¹ * pairDensity χ β lam (c i)) := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  have hd : Measurable fun p : ℂ × ℂ =>
      ENNReal.ofReal ((N * dipoleNormalization χ N β lam)⁻¹ * pairDensity χ β lam p) :=
    ENNReal.measurable_ofReal.comp ((measurable_pairDensity hχ hlam β).const_mul _)
  refine Measure.pi_eq (μ := fun _ : ι => dipoleMeasure χ N β lam) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    Measure.restrict_restrict (MeasurableSet.univ_pi hs), boxConfig, ← Set.pi_inter_distrib,
    volume_pi, Measure.restrict_pi_pi, lintegral_pi_prod
      (fun i => (volume : Measure (ℂ × ℂ)).restrict (s i ∩ box N ×ˢ box N))
      (fun _ p => ENNReal.ofReal ((N * dipoleNormalization χ N β lam)⁻¹ * pairDensity χ β lam p))
      (fun _ => hd)]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold dipoleMeasure
  rw [withDensity_apply _ (hs i), Measure.restrict_restrict (hs i)]
  rfl

/-- **Integrals against `μ^{⊗ ι}` as box integrals.**
`∫ F dμ^{⊗ ι} = (N C_{β,λ})^{-|ι|} ∫_{(Λ²)^ι} F(c) ∏ᵢ e^{β g_λ(xᵢ - yᵢ)} dc`. -/
theorem integral_pi_dipoleMeasure (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hN : 1 ≤ N)
    (F : (ι → ℂ × ℂ) → ℝ) :
    ∫ c, F c ∂Measure.pi (fun _ : ι => dipoleMeasure χ N β lam) =
      ((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ ^ Fintype.card ι *
        ∫ c in boxConfig ι N, F c * ∏ i, pairDensity χ β lam (c i) := by
  have hC := natCast_mul_dipoleNormalization_pos hχ hlam β hN
  have hd : Measurable fun c : ι → ℂ × ℂ =>
      ∏ i, ENNReal.ofReal ((N * dipoleNormalization χ N β lam)⁻¹ * pairDensity χ β lam (c i)) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      (((measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i)).const_mul _)
  rw [pi_dipoleMeasure_eq hχ hlam β hN, integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall fun c => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_prod]
  have : ∀ i, (ENNReal.ofReal ((N * dipoleNormalization χ N β lam)⁻¹ *
      pairDensity χ β lam (c i))).toReal =
      (N * dipoleNormalization χ N β lam)⁻¹ * pairDensity χ β lam (c i) := fun i =>
    ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hC.le) (pairDensity_pos χ β lam _).le)
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

end PiDensity

end Limits

end MultipoleBKT

end
