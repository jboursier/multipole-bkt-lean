/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.Algebra
public import MultipoleBKT.LowerBound.BoundedLowerEps.Multipole
public import MultipoleBKT.Appendix.MultipoleIntegral.CutoffModel
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Gate
public import MultipoleBKT.Limits.Integrands

/-!
# Normalizations for the control of activity errors (Proposition 4.24)

The proof of Proposition 4.24, and Lemma 4.12.

* `normalization_bounds`: the consequences of Lemma 4.12 used throughout: for `ε₀ ∈ (0, 1)`
  there are `C > 0` and `λ₀ ∈ (0, 1]` such that for `λ ∈ (0, λ₀)` and `N` large,
  `𝒵_β λ^{2-β}/2 ≤ C_{β,λ,ε₀}, C_{β,λ} ≤ 𝒵_β λ^{2-β}` and
  `|C_{β,λ}/C_{β,λ,ε₀} - 1| ≤ C R̄^{-2}` (from (4.13) and (4.12));
* `integral_pi_cutoffDipoleMeasure`: integrals against `μ_{β,λ,ε₀}^{⊗ ι}` as box integrals,
  `∫ F dμ_{β,λ,ε₀}^{⊗ ι} = (N C_{β,λ,ε₀})^{-|ι|} ∫_{(Λ²)^ι} F ∏_i e^{β g_λ(r_i)} 𝟙_{r_i ≤ ε₀ R̄}`;
* `cutoffWeight`: the dipole weight `e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ h}` of the truncated models;
* `zeroPartitionFunction_singleton_eq`: `𝖬^0_{ε₀}(S) = (N C_{β,λ,ε₀})^{-|S|} I^0_{mult,ε₀}(S)`;
* `modelPartitionFunction_singleton_one`: `𝖬({i}) = 1` for a model with `ψ = 1`.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionErrors

open MeasureTheory Set Finset Metric Filter
open TwoComponentCoulomb (box)
open Hierarchical Limits

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

/-- `R^{-2} = (R²)⁻¹` for `R > 0`. -/
theorem rpow_neg_two_eq {R : ℝ} (hR : 0 < R) : R ^ (-2 : ℝ) = (R ^ 2)⁻¹ := by
  rw [Real.rpow_neg hR.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The normalizations** (Lemma 4.12): for `β > 2`, `p₀` and
`ε₀ ∈ (0, 1)` there are `C > 0` and `λ₀ ∈ (0, 1]` such that for `λ ∈ (0, λ₀)` there is `N₀` with,
for `N ≥ N₀`: `N ≥ 1`, `2λ ≤ ε₀ R̄`, `𝒵_β λ^{2-β}/2 ≤ C_{β,λ,ε₀} ≤ 𝒵_β λ^{2-β}`,
`𝒵_β λ^{2-β}/2 ≤ C_{β,λ} ≤ 𝒵_β λ^{2-β}` and `|C_{β,λ}/C_{β,λ,ε₀} - 1| ≤ C R̄^{-2}`. -/
theorem normalization_bounds (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        1 ≤ N ∧ 2 * lam ≤ ε₀ * truncationScale p₀ β lam ∧
        1 / 2 * dipoleConstant χ β * lam ^ (2 - β) ≤ cutoffDipoleNormalization χ N p₀ β lam ε₀ ∧
        cutoffDipoleNormalization χ N p₀ β lam ε₀ ≤ lam ^ (2 - β) * dipoleConstant χ β ∧
        1 / 2 * dipoleConstant χ β * lam ^ (2 - β) ≤ dipoleNormalization χ N β lam ∧
        dipoleNormalization χ N β lam ≤ lam ^ (2 - β) * dipoleConstant χ β ∧
        |dipoleNormalization χ N β lam / cutoffDipoleNormalization χ N p₀ β lam ε₀ - 1| ≤
          C * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  intro ε₀ hε₀ hε₁
  obtain ⟨Cc, hCc, hcmp⟩ := lem411_compare hχ hβ
  obtain ⟨l₁, hl₁, hcmp'⟩ := hcmp ε₀ hε₀ hε₁
  obtain ⟨l₂, hl₂, hlow⟩ := lem411_lower hχ hβ hε₀
  have hZ := dipoleConstant_pos hχ hβ
  refine ⟨2 * Cc * (ε₀ ^ 2)⁻¹, by positivity, min (min l₁ l₂) (min 1 (ε₀ / 2)),
    lt_min (lt_min hl₁ hl₂) (lt_min one_pos (by linarith)),
    (min_le_right _ _).trans (min_le_left _ _), fun lam hlam hlt => ?_⟩
  have hlt₁ : lam < l₁ := hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hlt₂ : lam < l₂ := hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hlamε : lam ≤ ε₀ / 2 := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have h2 := BoundedLowerEps.two_mul_le_cutoff hβ hlam hlam1 hε₀ hlamε p₀
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hcmp' p₀ lam hlam hlt₁)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hlow p₀ lam hlam hlt₂)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (eventually_half_le_dipoleNormalization hχ hβ hlam)
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hc1 := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have hc2 := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hc3 := hN₃ N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have hc4 := MultipoleIntegralZ.cutoffDipoleNormalization_le_rpow hχ hβ hlam N p₀ ε₀
  have hc5 := dipoleNormalization_le hχ hβ hlam N
  refine ⟨hN1, h2, hc2, hc4, hc3, hc5, ?_⟩
  set Ce := cutoffDipoleNormalization χ N p₀ β lam ε₀
  set C := dipoleNormalization χ N β lam
  set R := truncationScale p₀ β lam
  have hR : 0 < R := Appendix.truncationScale_pos hlam
  have hl : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hCe : 0 < Ce := lt_of_lt_of_le (by positivity) hc2
  have hC : 0 < C := lt_of_lt_of_le (by positivity) hc3
  have hratio : C / Ce ≤ 2 := by
    rw [div_le_iff₀ hCe]
    nlinarith
  have heq : C / Ce - 1 = -((Ce - C) / C) * (C / Ce) := by
    field_simp
    ring
  rw [heq, abs_mul, abs_neg, abs_div, abs_of_pos hC, abs_of_pos (div_pos hC hCe),
    rpow_neg_two_eq hR]
  have h1 : |Ce - C| / C ≤ Cc * ((ε₀ * R) ^ 2)⁻¹ := hc1
  have hRR : ((ε₀ * R) ^ 2)⁻¹ = (ε₀ ^ 2)⁻¹ * (R ^ 2)⁻¹ := by rw [mul_pow, mul_inv]
  rw [hRR] at h1
  have h0 : 0 ≤ |Ce - C| / C := div_nonneg (abs_nonneg _) hC.le
  calc |Ce - C| / C * (C / Ce) ≤ Cc * ((ε₀ ^ 2)⁻¹ * (R ^ 2)⁻¹) * 2 :=
        mul_le_mul h1 hratio (div_pos hC hCe).le (by positivity)
    _ = 2 * Cc * (ε₀ ^ 2)⁻¹ * (R ^ 2)⁻¹ := by ring

/-- The cutoff dipole weight `e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ h}`. -/
noncomputable def cutoffWeight (χ : ℂ → ℝ) (β lam h : ℝ) (p : ℂ × ℂ) : ℝ :=
  Real.exp (β * smearedKernel χ lam (p.1 - p.2)) * (closedBall (0 : ℂ) h).indicator 1 (p.1 - p.2)

theorem cutoffWeight_eq_indicator (h : ℝ) (p : ℂ × ℂ) :
    cutoffWeight χ β lam h p =
      (closedBall (0 : ℂ) h).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
        (p.1 - p.2) := by
  unfold cutoffWeight
  by_cases hm : p.1 - p.2 ∈ closedBall (0 : ℂ) h
  · rw [indicator_of_mem hm, indicator_of_mem hm, Pi.one_apply, mul_one]
  · rw [indicator_of_notMem hm, indicator_of_notMem hm, mul_zero]

theorem cutoffWeight_nonneg (h : ℝ) (p : ℂ × ℂ) : 0 ≤ cutoffWeight χ β lam h p := by
  rw [cutoffWeight_eq_indicator]
  exact cutoffDensity_nonneg β h p

theorem measurable_cutoffWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β h : ℝ) :
    Measurable (cutoffWeight χ β lam h) := by
  have : cutoffWeight χ β lam h = fun p => (closedBall (0 : ℂ) h).indicator
      (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2) :=
    funext fun p => cutoffWeight_eq_indicator h p
  rw [this]
  exact measurable_cutoffDensity hχ hlam β h

/-- **Integrals against `μ_{β,λ,ε₀}^{⊗ ι}` as box integrals.**
`∫ F dμ_{β,λ,ε₀}^{⊗ ι} = (N C_{β,λ,ε₀})^{-|ι|} ∫_{(Λ²)^ι} F(c) ∏ᵢ e^{β g_λ(rᵢ)} 𝟙_{rᵢ ≤ ε₀ R̄}
dc`. -/
theorem integral_pi_cutoffDipoleMeasure (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) {ι : Type*} [Fintype ι] (F : (ι → ℂ × ℂ) → ℝ) :
    ∫ c, F c ∂Measure.pi (fun _ : ι => cutoffDipoleMeasure χ N p₀ β lam ε₀) =
      ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ Fintype.card ι *
        ∫ c in boxConfig ι N, F c *
          ∏ i, cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam) (c i) := by
  classical
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  set h := ε₀ * truncationScale p₀ β lam
  have hd : Measurable fun c : ι → ℂ × ℂ =>
      ∏ i, ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (closedBall (0 : ℂ) h).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      (((measurable_cutoffDensity hχ hlam β _).comp (measurable_pi_apply i)).const_mul _)
  rw [pi_cutoffDipoleMeasure_eq hχ hlam β hε₀ hN,
    integral_withDensity_eq_integral_toReal_smul hd
      (Eventually.of_forall fun c => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_prod]
  have hti : ∀ i, (ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
      (closedBall (0 : ℂ) h).indicator
        (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2))).toReal =
      (N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ * cutoffWeight χ β lam h (c i) := by
    intro i
    rw [cutoffWeight_eq_indicator]
    exact ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hC.le) (cutoffDensity_nonneg β _ _))
  simp_rw [hti]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

open scoped Classical in
/-- **The normalization identity for `𝖬^0_{ε₀}`**:
`𝖬^0_{ε₀}(S) = (N C_{β,λ,ε₀})^{-|S|} I^0_{mult,ε₀}(S)` with `I^0_{mult,ε₀}` the multipole integral
with cutoff `ε₀ R̄` (`multipoleIntegralCut`), for `λ > 0`, `ε₀ > 0`, `N ≥ 1`. -/
theorem zeroPartitionFunction_singleton_eq (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (S : Finset ℕ) :
    zeroPartitionFunction χ N p₀ β lam M ε₀ {S} =
      ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ S.card *
        multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S := by
  rw [zeroPartitionFunction, Finset.prod_singleton, modelPartitionFunction,
    integral_pi_cutoffDipoleMeasure hχ hlam β hε₀ hN, Fintype.card_coe, multipoleIntegralCut]
  congr 1
  refine setIntegral_congr_fun (measurableSet_boxConfig N) fun c _ => ?_
  simp only [Finset.prod_const_one, mul_one]
  rfl

/-- `𝖬({i}) = 1` for a model with `ψ = 1` and a probability measure `ρ`. -/
theorem modelPartitionFunction_singleton_one {ρ : Measure (ℂ × ℂ)} [IsProbabilityMeasure ρ]
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) (i : ℕ) :
    modelPartitionFunction ρ β w (fun _ => 1) M lam {i} = 1 := by
  have hsub : Subsingleton ({i} : Finset ℕ) :=
    Finset.card_le_one_iff_subsingleton_coe.1 (by simp)
  have hconn : ∀ c : ({i} : Finset ℕ) → ℂ × ℂ, (SimpleGraph.fromRel fun a b : ({i} : Finset ℕ) =>
      MultipoleLinked M lam (c a) (c b)).Connected := fun c =>
    (SimpleGraph.connected_iff _).2 ⟨fun u v => by rw [Subsingleton.elim u v], ⟨⟨i, by simp⟩⟩⟩
  unfold modelPartitionFunction
  calc _ = ∫ _c : ({i} : Finset ℕ) → ℂ × ℂ, (1 : ℝ) ∂Measure.pi fun _ => ρ := by
        refine integral_congr_ae (Eventually.of_forall fun c => ?_)
        simp only [hconn c, ite_true, one_mul, Finset.prod_const_one, mul_one]
        refine Finset.prod_eq_one fun a _ => Finset.prod_eq_one fun b _ => ?_
        simp [Subsingleton.elim a b]
    _ = 1 := by simp

end ExpansionErrors

end MultipoleBKT

end
