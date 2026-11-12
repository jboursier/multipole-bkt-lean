/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.TreeIntegral
public import MultipoleBKT.Potential.DipoleInteraction
public import MultipoleBKT.Potential.BondBound
public import MultipoleBKT.Appendix.RadialIntegral

/-!
# Radial estimates

The radial integrals at the end of the proof of
Lemma A.5 and in Lemma A.2.

With `ρ_λ(u) = max(|u|, λ)` (`rho`):

* `exists_exp_smearedKernel_le`: `e^{β g_λ(u)} ≤ C ρ_λ(u)^{-β}` (from `g_λ(u) ≤ -log ρ_λ(u) + c`);
* `lintegral_exp_mul_rpow_lt_top`: `∫_ℂ e^{β g_λ(u)} ρ_λ(u)^s du < ∞` for `s < β - 2`;
* `lintegral_antitone_dipoleDist_le`: for a nonincreasing weight `φ`,
  `∫ φ(d((t, t + u), e)) dt ≤ 4 ∫_ℂ φ(|z|) dz`, `d` the distance of two dipoles (the minimum of
  four distances);
* `prod_rpow_mul_rpow_neg_le`: if `ρᵢ ≤ R` for all `i ∈ ι`, then
  `R^{-a} ∏ᵢ ρᵢ² ≤ ∏ᵢ ρᵢ^{2 - a/|ι|}`.

The last inequality replaces the paper's ordering of the radii: the tree bounds produce
`∏_{i ≠ i*} ρᵢ² = R^{-2} ∏ ρᵢ²` (`R` the largest radius) and the radial integral then factorizes;
it is finite for `|ι| ≤ p*(β)` (`two_sub_two_div_lt_of_le_pStar`).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset Filter
open scoped ENNReal

variable {χ : ℂ → ℝ} {lam β : ℝ}

/-- `ρ_λ(u) = max(|u|, λ)`. -/
noncomputable def rho (lam : ℝ) (u : ℂ) : ℝ := max ‖u‖ lam

theorem rho_pos (hlam : 0 < lam) (u : ℂ) : 0 < rho lam u := lt_max_of_lt_right hlam

theorem lam_le_rho (lam : ℝ) (u : ℂ) : lam ≤ rho lam u := le_max_right _ _

theorem norm_le_rho (lam : ℝ) (u : ℂ) : ‖u‖ ≤ rho lam u := le_max_left _ _

theorem continuous_rho (lam : ℝ) : Continuous (rho lam) :=
  continuous_norm.max continuous_const

theorem measurable_rho (lam : ℝ) : Measurable (rho lam) := (continuous_rho lam).measurable

/-- `e^{β g_λ(u)} ≤ C ρ_λ(u)^{-β}` for `β ≥ 0`, with `C > 0` depending on `χ` and `β`. -/
theorem exists_exp_smearedKernel_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ C, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ u : ℂ,
      Real.exp (β * smearedKernel χ lam u) ≤ C * rho lam u ^ (-β) := by
  set c₀ := max (∫ y : ℂ, TwoComponentCoulomb.logKernel y ∂smearedCharge χ 0 1) 0
  refine ⟨Real.exp (β * c₀), Real.exp_pos _, fun lam hlam u => ?_⟩
  have h := smearedKernel_le_neg_log_max hχ hlam u
  have hρ := rho_pos hlam u
  rw [Real.rpow_def_of_pos hρ, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : β * smearedKernel χ lam u ≤ β * (-Real.log (rho lam u) + c₀) :=
    mul_le_mul_of_nonneg_left h hβ
  unfold rho at *
  linarith

/-- `∫_ℂ ρ_λ(u)^e du < ∞` for `e < -2`. -/
theorem integrable_rpow_rho (hlam : 0 < lam) {e : ℝ} (he : e < -2) :
    Integrable fun u : ℂ => rho lam u ^ e := by
  have h := (integrable_fun_norm_complex_iff fun r : ℝ => max r lam ^ e).2 ?_
  · exact h
  have hc : Continuous fun r : ℝ => max r lam ^ e * r :=
    (Appendix.continuous_max_rpow hlam e).mul continuous_id
  have h1 : IntegrableOn (fun r : ℝ => max r lam ^ e * r) (Ioc 0 lam) :=
    (hc.continuousOn.integrableOn_Icc (a := 0) (b := lam)).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun r : ℝ => max r lam ^ e * r) (Ioi lam) := by
    refine (integrableOn_Ioi_rpow_of_lt (by linarith : e + 1 < -1) hlam).congr_fun
      (fun r hr => ?_) measurableSet_Ioi
    have hr' : lam < r := hr
    show r ^ (e + 1) = max r lam ^ e * r
    rw [max_eq_left hr'.le, Real.rpow_add_one (hlam.trans hr').ne']
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi hlam.le] at this

/-- `∫_ℂ e^{β g_λ(u)} ρ_λ(u)^s du < ∞` for `β > 2` and `s < β - 2`. -/
theorem lintegral_exp_mul_rpow_lt_top (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    {s : ℝ} (hs : s < β - 2) :
    ∫⁻ u : ℂ, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam u) * rho lam u ^ s) < ∞ := by
  obtain ⟨C, hC0, hC⟩ := exists_exp_smearedKernel_le hχ (by linarith : (0 : ℝ) ≤ β)
  have hint := (integrable_rpow_rho hlam (by linarith : s - β < -2)).const_mul C
  refine lt_of_le_of_lt (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_)
    hint.lintegral_lt_top
  have hρ := rho_pos hlam u
  calc Real.exp (β * smearedKernel χ lam u) * rho lam u ^ s
      ≤ C * rho lam u ^ (-β) * rho lam u ^ s :=
        mul_le_mul_of_nonneg_right (hC lam hlam u) (Real.rpow_nonneg hρ.le _)
    _ = C * rho lam u ^ (s - β) := by
        rw [mul_assoc, ← Real.rpow_add hρ]
        ring_nf

/-- For `|ι| = k ≤ p*(β)`, `2 - 2/k < β - 2`. -/
theorem two_sub_two_div_lt_of_le_pStar {k : ℕ} (hk : 1 ≤ k) (hkp : (k : ℕ∞) ≤ pStar β) :
    2 - 2 / (k : ℝ) < β - 2 := by
  have := (Appendix.le_pStar_iff hk).1 hkp
  unfold transitionBeta at this
  linarith

/-- **Ordering of the radii, factorized.** If `0 < ρᵢ ≤ R` for all `i` and `a ≥ 0`, then
`R^{-a} ∏ᵢ ρᵢ^2 ≤ ∏ᵢ ρᵢ^{2 - a/|ι|}`. -/
theorem prod_rpow_mul_rpow_neg_le {ι : Type*} [Fintype ι] [Nonempty ι] (ρ : ι → ℝ) {R a : ℝ}
    (hρ : ∀ i, 0 < ρ i) (hR : ∀ i, ρ i ≤ R) (ha : 0 ≤ a) :
    R ^ (-a) * ∏ i, ρ i ^ (2 : ℝ) ≤ ∏ i, ρ i ^ (2 - a / Fintype.card ι) := by
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsplit : ∀ i, ρ i ^ (2 - a / Fintype.card ι) =
      ρ i ^ (2 : ℝ) * ρ i ^ (-(a / Fintype.card ι)) := fun i => by
    rw [← Real.rpow_add (hρ i)]
    ring_nf
  simp_rw [hsplit]
  rw [Finset.prod_mul_distrib, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun i _ => (Real.rpow_nonneg (hρ i).le _))
  have hR0 : 0 < R := (hρ (Classical.arbitrary ι)).trans_le (hR _)
  have hak : 0 ≤ a / Fintype.card ι := div_nonneg ha hk.le
  calc R ^ (-a) = ∏ _i : ι, R ^ (-(a / Fintype.card ι)) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
        congr 1
        field_simp
    _ ≤ ∏ i, ρ i ^ (-(a / Fintype.card ι)) :=
        Finset.prod_le_prod₀ (fun i _ => (Real.rpow_nonneg hR0.le _)) fun i _ =>
          Real.rpow_le_rpow_of_nonpos (hρ i) (hR i) (by linarith)

/-- The distance of the dipole `(t, t + u)` to the dipole `e` is the distance of `t` to one of
four points. -/
theorem dipoleDist_eq_min (t u : ℂ) (e : ℂ × ℂ) :
    dipoleDist (t, t + u) e =
      min (min ‖t - e.1‖ ‖t - e.2‖) (min ‖t - (e.1 - u)‖ ‖t - (e.2 - u)‖) := by
  unfold dipoleDist
  simp only
  congr 2 <;> congr 1 <;> ring

/-- **Integrals of nonincreasing functions of the dipole distance.** -/
theorem lintegral_antitone_dipoleDist_le {φ : ℝ → ℝ≥0∞} (hφ : Antitone φ) (hφm : Measurable φ)
    (u : ℂ) (e : ℂ × ℂ) :
    ∫⁻ t : ℂ, φ (dipoleDist (t, t + u) e) ≤ 4 * ∫⁻ z : ℂ, φ ‖z‖ := by
  have hpt : ∀ t : ℂ, φ (dipoleDist (t, t + u) e) ≤
      φ ‖t - e.1‖ + φ ‖t - e.2‖ + φ ‖t - (e.1 - u)‖ + φ ‖t - (e.2 - u)‖ := by
    intro t
    rw [dipoleDist_eq_min, hφ.map_min, hφ.map_min, hφ.map_min]
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · exact le_add_right (le_add_right (le_add_right le_rfl))
    · exact le_add_right (le_add_right (le_add_left le_rfl))
    · exact le_add_right (le_add_left le_rfl)
    · exact le_add_left le_rfl
  have htr : ∀ p : ℂ, ∫⁻ t : ℂ, φ ‖t - p‖ = ∫⁻ z : ℂ, φ ‖z‖ := fun p =>
    lintegral_sub_right_eq_self (fun z => φ ‖z‖) p
  have hm : ∀ p : ℂ, Measurable fun t : ℂ => φ ‖t - p‖ := fun p =>
    hφm.comp (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
  have hm2 : Measurable fun t : ℂ => φ ‖t - e.1‖ + φ ‖t - e.2‖ := (hm _).add (hm _)
  have hm3 : Measurable fun t : ℂ => φ ‖t - e.1‖ + φ ‖t - e.2‖ + φ ‖t - (e.1 - u)‖ :=
    hm2.add (hm _)
  calc ∫⁻ t : ℂ, φ (dipoleDist (t, t + u) e)
      ≤ ∫⁻ t : ℂ, (φ ‖t - e.1‖ + φ ‖t - e.2‖ + φ ‖t - (e.1 - u)‖ + φ ‖t - (e.2 - u)‖) :=
        lintegral_mono hpt
    _ = 4 * ∫⁻ z : ℂ, φ ‖z‖ := by
        rw [lintegral_add_left hm3, lintegral_add_left hm2, lintegral_add_left (hm _), htr, htr,
          htr, htr]
        ring

/-- `∫_ℂ 𝟙_{|z| ≤ A} dz = π A²`. -/
theorem lintegral_indicator_norm_le (A : ℝ) :
    ∫⁻ z : ℂ, (Iic A).indicator (1 : ℝ → ℝ≥0∞) ‖z‖ = ENNReal.ofReal A ^ 2 * NNReal.pi := by
  have : (fun z : ℂ => (Iic A).indicator (1 : ℝ → ℝ≥0∞) ‖z‖) =
      (Metric.closedBall (0 : ℂ) A).indicator 1 := by
    funext z
    simp only [indicator, Set.mem_Iic, Metric.mem_closedBall, dist_zero_right, Pi.one_apply]
  rw [this, lintegral_indicator_one Metric.isClosed_closedBall.measurableSet,
    Complex.volume_closedBall]

end Limits

end MultipoleBKT

end
