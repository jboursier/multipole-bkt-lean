/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.UpperBound
import TwoComponentCoulomb.Potential.ElectricEnergy
import TwoComponentCoulomb.Integrals.Radial
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-!
# Errors from the energy upper bound (Lemma 3.10)

Lemma 3.10 of the paper compares the
screened interaction `ṽ_ij` (equation (3.18)) with the true dipole interaction `v_ij`
(Definition 3.6). The proof writes, for `l ∈ {i, j}`,
`D_l = 1_{B(z_l,τ)} ∇u_l - ∇h_l` with `h_l = g * (δ_{x_l}^{(λ)} - δ_{y_l}^{(λ)})`, and uses

* `‖D_l‖²_{L²} ≤ C r_l² / τ²` (`integral_norm_sq_screenedDefect_le`, with `C = 8π`): inside the disc
  `D_l = ∇ũ_l` is bounded by (3.20); outside, `|∇h_l(w)| ≤ 2 r_l / |w - z_l|²` (dipole decay);
* `∫ D_l · ∇h_m = 0` for `l, m ∈ {i, j}` (`integral_inner_screenedDefect_dipoleField`): the weak
  Neumann identity and the Green identity on `ℝ²` with a cutoff
  (`integral_inner_electricField_eq`), "since `h_m = O(|x|⁻¹)` and `∇h_m = O(|x|⁻²)`";
* `∫ ∇h_i · ∇h_j = 2π v_ij` (`integral_inner_dipoleField`).

Hence `ṽ_ij - v_ij = (1/2π) ∫ D_i · D_j`, and `|ṽ_ij - v_ij| ≤ 4 r_i r_j / τ²`
(`abs_screenedInteraction_sub_le`; no separation assumption). With the support property
(`screenedInteraction_eq_zero_of_dipoleDist`) and equation (3.32) (`abs_dipoleInteraction_le`),
this gives equations (3.50) and (3.51) (`lemma_3_10`).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ}

/-! ### The Green identity between two neutral configurations -/

section Cross

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}
  {d' : ι' → ℝ} {z' : ι' → ℂ} {α' : ι' → ℝ}

/-- The field of a neutral configuration paired with that of another is integrable. -/
theorem integrable_inner_electricField (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i)
    (hα' : ∀ i, 0 < α' i) (hn : ∑ i, d i = 0) (hn' : ∑ i, d' i = 0) :
    Integrable fun x => inner ℝ (electricField χ d z α x) (electricField χ d' z' α' x) := by
  refine ((integrable_norm_sq_electricField (z := z) hχ hα hn).add
    (integrable_norm_sq_electricField (z := z') hχ hα' hn')).mono'
    ((continuous_electricField hχ hα).inner (continuous_electricField hχ hα')).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply]
  refine (abs_real_inner_le_norm _ _).trans ?_
  nlinarith [sq_nonneg (‖electricField χ d z α x‖ - ‖electricField χ d' z' α' x‖)]

/-- **The Green identity on `ℝ²` between two neutral configurations** (the proof of Lemma 3.10, "by
integration by parts with a cutoff"): `∫ ∇h · ∇h' = 2π Σ_b d'_b ∫ h dδ_{z'_b}^{(α'_b)}`. -/
theorem integral_inner_electricField_eq (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i)
    (hα' : ∀ i, 0 < α' i) (hn : ∑ i, d i = 0) (hn' : ∑ i, d' i = 0) :
    ∫ x, inner ℝ (electricField χ d z α x) (electricField χ d' z' α' x) =
      2 * Real.pi *
        ∑ b, d' b * ∫ y, electricPotential χ d z α y ∂smearedCharge χ (z' b) (α' b) := by
  set E := electricField χ d z α with hE
  set E' := electricField χ d' z' α' with hE'
  set h := electricPotential χ d z α with hh
  obtain ⟨R₀, C, hR₀, hC, hdec⟩ := exists_decay_electric (d := d) (z := z) hχ hα hn
  obtain ⟨R₀', C', hR₀', hC', hdec'⟩ := exists_decay_electric (d := d') (z := z') hχ hα' hn'
  obtain ⟨K, φ, hK, hφ⟩ := TwoComponentCoulomb.exists_cutoff_family
  have hhc : ContDiff ℝ 1 h := contDiff_electricPotential hχ hα
  have hEc : Continuous E := continuous_electricField hχ hα
  have hE'c : Continuous E' := continuous_electricField hχ hα'
  have hint :=
    integrable_inner_electricField (d := d) (z := z) (d' := d') (z' := z') hχ hα hα' hn hn'
  have hid : ∀ᶠ R : ℝ in atTop, (∫ x, φ R x * inner ℝ (E x) (E' x)) +
      ∫ x, h x * fderiv ℝ (φ R) x (E' x) =
        2 * Real.pi * ∑ b, d' b * ∫ y, h y ∂smearedCharge χ (z' b) (α' b) := by
    filter_upwards [eventually_ge_atTop (max 1 (∑ b, (‖z' b‖ + α' b)))] with R hR
    have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hR)
    obtain ⟨h1, h2, -, h4, -, -, -⟩ := hφ R hR0
    have hξ : ContDiff ℝ 1 (fun x => φ R x * h x) := h1.mul hhc
    have hcξ : HasCompactSupport (fun x => φ R x * h x) := h2.mul_right
    have G := integral_fderiv_apply_electricField (d := d') (z := z') hχ hξ hcξ hα'
    have hpt : ∀ x, fderiv ℝ (fun y => φ R y * h y) x (E' x) =
        φ R x * inner ℝ (E x) (E' x) + h x * fderiv ℝ (φ R) x (E' x) := fun x => by
      rw [fderiv_fun_mul (h1.differentiable one_ne_zero x) (hhc.differentiable one_ne_zero x)]
      simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hh,
        fderiv_electricPotential_apply hχ hα, hE]
    have hI1 : Integrable (fun x => φ R x * inner ℝ (E x) (E' x)) :=
      Continuous.integrable_of_hasCompactSupport (h1.continuous.mul (hEc.inner hE'c))
        h2.mul_right
    have hI : Integrable (fun x => fderiv ℝ (fun y => φ R y * h y) x (E' x)) := by
      refine Continuous.integrable_of_hasCompactSupport
        ((hξ.continuous_fderiv one_ne_zero).clm_apply hE'c) ?_
      refine (hcξ.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ ?_
      intro h0
      exact hx (by simp [h0])
    have hI2 : Integrable (fun x => h x * fderiv ℝ (φ R) x (E' x)) := by
      refine (hI.sub hI1).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply, hpt]
      ring
    rw [← hE'] at G
    simp_rw [hpt] at G
    rw [← integral_add hI1 hI2, G]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_closedBall_smearedCharge (z := z' b) hχ (hα' b)] with x hx
    have hx' : ‖x‖ ≤ R := by
      have e1 : ‖x - z' b‖ ≤ α' b := by simpa [dist_eq_norm] using hx
      have e2 : ‖x‖ ≤ ‖x - z' b‖ + ‖z' b‖ := by simpa using norm_add_le (x - z' b) (z' b)
      have e3 : ‖z' b‖ + α' b ≤ ∑ b, (‖z' b‖ + α' b) :=
        Finset.single_le_sum (f := fun j => ‖z' j‖ + α' j)
          (fun j _ => add_nonneg (norm_nonneg _) (hα' j).le) (Finset.mem_univ b)
      linarith [le_max_right 1 (∑ b, (‖z' b‖ + α' b))]
    rw [h4 x hx', one_mul]
  have hA : Tendsto (fun R : ℝ => ∫ x, φ R x * inner ℝ (E x) (E' x)) atTop
      (𝓝 (∫ x, inner ℝ (E x) (E' x))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖inner ℝ (E x) (E' x)‖) ?_ ?_ hint.norm ?_
    · filter_upwards [eventually_gt_atTop 0] with R hR
      exact ((hφ R hR).1.continuous.mul (hEc.inner hE'c)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with R hR
      refine Eventually.of_forall fun x => ?_
      obtain ⟨-, -, h3, -⟩ := hφ R hR
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (h3 x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (h3 x).2
    · refine Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (max ‖x‖ 1)] with R hR
      have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR)
      obtain ⟨-, -, -, h4, -⟩ := hφ R hR0
      rw [h4 x ((le_max_left _ _).trans hR), one_mul]
  have hdec2 : ∀ x : ℂ, max R₀ R₀' ≤ ‖x‖ →
      |h x| ≤ max C C' / ‖x‖ ∧ ‖E' x‖ ≤ max C C' / ‖x‖ ^ 2 := by
    intro x hx
    have hx0 : 0 < ‖x‖ := lt_of_lt_of_le hR₀ ((le_max_left _ _).trans hx)
    exact ⟨(hdec x ((le_max_left _ _).trans hx)).1.trans
        (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le),
      (hdec' x ((le_max_right _ _).trans hx)).2.trans
        (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))⟩
  have hB := tendsto_integral_mul_fderiv_cutoff (lt_of_lt_of_le hR₀ (le_max_left _ _))
    (hC.trans (le_max_left _ _)) hdec2 hK
    (fun R hR => ⟨(hφ R hR).2.2.2.2.1, (hφ R hR).2.2.2.2.2.1, (hφ R hR).2.2.2.2.2.2⟩)
  have hsum := hA.add hB
  rw [add_zero] at hsum
  exact tendsto_nhds_unique hsum (tendsto_const_nhds.congr' (hid.mono fun R hR => hR.symm))

end Cross

/-! ### Dipole fields -/

section Dipole

variable {lam τ : ℝ}

/-- `∫ h_e dδ_a^{(λ)} = g_λ(x_e - a) - g_λ(y_e - a)` for the dipole `e = (x_e, y_e)` (Fubini). -/
theorem integral_dipolePotential_smearedCharge (hχ : IsMollifier χ) (hlam : 0 < lam)
    (e : ℂ × ℂ) (a : ℂ) :
    ∫ y, dipolePotential χ lam e y ∂smearedCharge χ a lam =
      smearedKernel χ lam (e.1 - a) - smearedKernel χ lam (e.2 - a) := by
  have := isFiniteMeasure_smearedCharge hχ a lam
  have hb : ∀ b, ∫ y, (∫ v, logKernel (y - v) ∂smearedCharge χ b lam) ∂smearedCharge χ a lam =
      smearedKernel χ lam (b - a) := fun b => by
    have := isFiniteMeasure_smearedCharge hχ b lam
    rw [← integral_logKernel_prod_smearedCharge χ a b lam,
      integral_prod _ (integrable_logKernel_prod_smearedCharge hχ a b lam lam)]
  have hi : ∀ b, Integrable (fun y => ∫ v, logKernel (y - v) ∂smearedCharge χ b lam)
      (smearedCharge χ a lam) := fun b =>
    integrable_smearedCharge_of_continuous hχ
      (continuous_integral_logKernel_sub_smearedCharge hχ b hlam) _ _
  simp only [dipolePotential]
  rw [integral_sub (hi _) (hi _), hb, hb]

/-- `|∇h_e|²` is integrable. -/
theorem integrable_norm_sq_dipoleField (hχ : IsMollifier χ) (hlam : 0 < lam) (e : ℂ × ℂ) :
    Integrable fun w => ‖dipoleField χ lam e w‖ ^ 2 := by
  rw [dipoleField_eq_electricField]
  exact integrable_norm_sq_electricField hχ (fun _ => hlam) (sum_dipoleCharge 1)

/-- `∇h_d · ∇h_e` is integrable. -/
theorem integrable_inner_dipoleField (hχ : IsMollifier χ) (hlam : 0 < lam) (d e : ℂ × ℂ) :
    Integrable fun w => inner ℝ (dipoleField χ lam d w) (dipoleField χ lam e w) := by
  rw [dipoleField_eq_electricField, dipoleField_eq_electricField]
  exact integrable_inner_electricField hχ (fun _ => hlam) (fun _ => hlam) (sum_dipoleCharge 1)
    (sum_dipoleCharge 1)

/-- **`∫ ∇h_d · ∇h_e = 2π v_ij`** (Green identity on `ℝ²`; the proof of Lemma 3.10). -/
theorem integral_inner_dipoleField (hχ : IsMollifier χ) (hlam : 0 < lam) (d e : ℂ × ℂ) :
    ∫ w, inner ℝ (dipoleField χ lam d w) (dipoleField χ lam e w) =
      2 * Real.pi * dipoleInteraction χ lam d e := by
  rw [dipoleField_eq_electricField, dipoleField_eq_electricField,
    integral_inner_electricField_eq hχ (fun _ => hlam) (fun _ => hlam) (sum_dipoleCharge 1)
      (sum_dipoleCharge 1), ← dipolePotential_eq_electricPotential]
  simp only [Fintype.sum_sum_type, dipoleCharge, dipoleCentre, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_singleton, one_mul, neg_mul,
    integral_dipolePotential_smearedCharge hχ hlam, dipoleInteraction_eq_sub hχ]
  ring

/-- The weak Neumann identity tested against another dipole potential:
`∫_{B(z_d,τ)} ∇u_d · ∇h_e = 2π v_ij`. -/
theorem setIntegral_inner_screenedField_dipoleField (hχ : IsMollifier χ) (hlam : 0 < lam)
    {d : ℂ × ℂ} (hd : 8 * max ‖d.2 - d.1‖ lam ≤ τ) (e : ℂ × ℂ) :
    ∫ w in ball (dipoleMidpoint d) τ, inner ℝ (screenedField χ lam τ d w) (dipoleField χ lam e w) =
      2 * Real.pi * dipoleInteraction χ lam d e := by
  have hτ0 := pos_of_screening hlam hd
  have hW := integral_fderiv_apply_screenedField hχ hlam hd (show τ < 2 * τ by linarith)
    (contDiff_dipolePotential hχ hlam e).contDiffOn
  have hpt : ∀ w ∈ ball (dipoleMidpoint d) τ, inner ℝ (screenedField χ lam τ d w)
      (dipoleField χ lam e w) = fderiv ℝ (dipolePotential χ lam e) w (screenedField χ lam τ d w) :=
    fun w _ => by
      rw [(hasGradientAt_dipolePotential hχ hlam e w).hasFDerivAt.fderiv, toDual_apply_apply,
        real_inner_comm]
  rw [setIntegral_congr_fun measurableSet_ball hpt, hW,
    integral_dipolePotential_smearedCharge hχ hlam, integral_dipolePotential_smearedCharge hχ hlam,
    dipoleInteraction_comm hχ, dipoleInteraction_eq_sub hχ]

/-- Decay of the dipole field outside the screening disc:
`|∇h(w)| ≤ 2 r / |w - z|²` for `|w - z| ≥ τ`. -/
theorem norm_dipoleField_le_of_le (hχ : IsMollifier χ) (hlam : 0 < lam) {d : ℂ × ℂ}
    (hd : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ} (hw : τ ≤ ‖w - dipoleMidpoint d‖) :
    ‖dipoleField χ lam d w‖ ≤ 2 * ‖d.2 - d.1‖ / ‖w - dipoleMidpoint d‖ ^ 2 := by
  have hτ0 := pos_of_screening hlam hd
  have hr := norm_le_of_screening hd
  have hw2 : τ / 2 ≤ ‖w - dipoleMidpoint d‖ := by linarith
  have h1 := lam_lt_norm_sub_of_screening hlam hd (norm_fst_sub_dipoleMidpoint d) hw2
  have h2 := lam_lt_norm_sub_of_screening hlam hd (norm_snd_sub_dipoleMidpoint d) hw2
  set p := w - dipoleMidpoint d with hp
  set b := (d.1 - d.2) / 2 with hb
  have hp0 : 0 < ‖p‖ := by linarith
  have hnb : ‖b‖ = ‖d.2 - d.1‖ / 2 := by
    rw [hb, norm_div, norm_sub_rev]
    norm_num
  have hbp : 2 * ‖b‖ ≤ ‖p‖ := by rw [hnb]; linarith
  have hbp' : 2 * ‖-b‖ ≤ ‖p‖ := by rwa [norm_neg]
  have e1 : w - d.1 = p - b := by rw [hp, hb, dipoleMidpoint]; ring
  have e2 : w - d.2 = p - -b := by rw [hp, hb, dipoleMidpoint]; ring
  rw [dipoleField, smearedField_of_lt hχ hlam h1, smearedField_of_lt hχ hlam h2, e1, e2]
  have k1 := norm_gradLogKernel_sub_sub_le hbp hp0
  have k2 := norm_gradLogKernel_sub_sub_le hbp' hp0
  rw [norm_neg] at k2
  calc ‖-((‖p - b‖ ^ 2)⁻¹ : ℝ) • (p - b) - -((‖p - -b‖ ^ 2)⁻¹ : ℝ) • (p - -b)‖
      ≤ ‖-((‖p - b‖ ^ 2)⁻¹ : ℝ) • (p - b) - -((‖p‖ ^ 2)⁻¹ : ℝ) • p‖ +
          ‖-((‖p - -b‖ ^ 2)⁻¹ : ℝ) • (p - -b) - -((‖p‖ ^ 2)⁻¹ : ℝ) • p‖ := by
        rw [← norm_neg (-((‖p - -b‖ ^ 2)⁻¹ : ℝ) • (p - -b) - -((‖p‖ ^ 2)⁻¹ : ℝ) • p)]
        refine (norm_add_le _ _).trans_eq' ?_
        congr 1
        abel
    _ ≤ 2 * ‖b‖ / ‖p‖ ^ 2 + 2 * ‖b‖ / ‖p‖ ^ 2 := add_le_add k1 k2
    _ = 2 * ‖d.2 - d.1‖ / ‖p‖ ^ 2 := by rw [hnb]; ring

end Dipole

/-! ### The radial integral `∫_{|u| ≥ τ} |u|⁻⁴ = π / τ²` -/

section Radial

/-- The radial profile of `u ↦ 1_{|u| ≥ τ} |u|⁻⁴`. -/
theorem indicator_compl_ball_inv_pow_four (τ : ℝ) (u : ℂ) :
    (ball (0 : ℂ) τ)ᶜ.indicator (fun u => (‖u‖ ^ 4)⁻¹) u =
      (Ici τ).indicator (fun y : ℝ => (y ^ 4)⁻¹) ‖u‖ := by
  have hmem : u ∈ (ball (0 : ℂ) τ)ᶜ ↔ ‖u‖ ∈ Ici τ := by simp
  by_cases hu : u ∈ (ball (0 : ℂ) τ)ᶜ
  · rw [indicator_of_mem hu, indicator_of_mem (hmem.1 hu)]
  · rw [indicator_of_notMem hu, indicator_of_notMem (fun h => hu (hmem.2 h))]

/-- `y · 1_{y ≥ τ} y⁻⁴ = 1_{y ≥ τ} y^{-3}` on `y > 0`. -/
theorem mul_indicator_Ici_inv_pow_four {τ y : ℝ} (hy : y ∈ Ioi (0 : ℝ)) :
    y * (Ici τ).indicator (fun y : ℝ => (y ^ 4)⁻¹) y =
      (Ioi τ ∪ {τ}).indicator (fun y : ℝ => y ^ (-3 : ℝ)) y := by
  have hy0 : 0 < y := hy
  have hIci : Ici τ = Ioi τ ∪ {τ} := by
    ext t
    simp [le_iff_lt_or_eq, or_comm]
  rw [← hIci]
  by_cases h : y ∈ Ici τ
  · rw [indicator_of_mem h, indicator_of_mem h, Real.rpow_neg hy0.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]

/-- **`∫_{|u| ≥ τ} |u|⁻⁴ du = π / τ²`**, and the integrand is integrable (`τ > 0`). -/
theorem integral_indicator_compl_ball_inv_pow_four {τ : ℝ} (hτ : 0 < τ) :
    Integrable ((ball (0 : ℂ) τ)ᶜ.indicator fun u => (‖u‖ ^ 4)⁻¹) ∧
      ∫ u, (ball (0 : ℂ) τ)ᶜ.indicator (fun u => (‖u‖ ^ 4)⁻¹) u = Real.pi / τ ^ 2 := by
  have hf : ((ball (0 : ℂ) τ)ᶜ.indicator fun u => (‖u‖ ^ 4)⁻¹) =
      fun u => (Ici τ).indicator (fun y : ℝ => (y ^ 4)⁻¹) ‖u‖ :=
    funext (indicator_compl_ball_inv_pow_four τ)
  have hI : IntegrableOn (fun t : ℝ => t ^ (-3 : ℝ)) (Ioi τ) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hτ
  have hcongr : EqOn (fun y : ℝ => y * (Ici τ).indicator (fun y : ℝ => (y ^ 4)⁻¹) y)
      ((Ioi τ ∪ {τ}).indicator fun y : ℝ => y ^ (-3 : ℝ)) (Ioi 0) :=
    fun y hy => mul_indicator_Ici_inv_pow_four hy
  have hsing : IntegrableOn (fun t : ℝ => t ^ (-3 : ℝ)) {τ} := by
    simp [IntegrableOn, Measure.restrict_singleton]
  rw [hf]
  constructor
  · rw [TwoComponentCoulomb.integrable_comp_norm_complex_iff]
    refine IntegrableOn.congr_fun ?_ hcongr.symm measurableSet_Ioi
    exact ((hI.union hsing).integrable_indicator (measurableSet_Ioi.union
      (measurableSet_singleton τ))).integrableOn
  · rw [TwoComponentCoulomb.integral_comp_norm_complex, setIntegral_congr_fun measurableSet_Ioi
      hcongr, setIntegral_indicator (measurableSet_Ioi.union (measurableSet_singleton τ))]
    have hsub : Ioi (0 : ℝ) ∩ (Ioi τ ∪ {τ}) = Ioi τ ∪ {τ} := by
      refine inter_eq_right.2 fun t ht => ?_
      rcases ht with ht | ht
      · exact lt_trans hτ ht
      · rw [mem_singleton_iff.1 ht]
        exact hτ
    rw [hsub, setIntegral_union (by simp) (measurableSet_singleton τ) hI hsing,
      integral_Ioi_rpow_of_lt (by norm_num) hτ]
    simp only [Measure.restrict_singleton]
    rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hτ.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [Real.volume_singleton, zero_smul, integral_zero_measure, add_zero,
      Nat.cast_ofNat]
    field_simp

/-- The translated form: `∫_{|w - z| ≥ τ} |w - z|⁻⁴ dw = π / τ²`. -/
theorem integral_indicator_compl_ball_inv_norm_sub_pow_four {τ : ℝ} (hτ : 0 < τ) (z : ℂ) :
    Integrable ((ball z τ)ᶜ.indicator fun w => (‖w - z‖ ^ 4)⁻¹) ∧
      ∫ w, (ball z τ)ᶜ.indicator (fun w => (‖w - z‖ ^ 4)⁻¹) w = Real.pi / τ ^ 2 := by
  obtain ⟨h1, h2⟩ := integral_indicator_compl_ball_inv_pow_four hτ
  have hf : ((ball z τ)ᶜ.indicator fun w => (‖w - z‖ ^ 4)⁻¹) =
      fun w => (ball (0 : ℂ) τ)ᶜ.indicator (fun u => (‖u‖ ^ 4)⁻¹) (w - z) := by
    funext w
    have hmem : w ∈ (ball z τ)ᶜ ↔ w - z ∈ (ball (0 : ℂ) τ)ᶜ := by
      simp [dist_eq_norm]
    by_cases hw : w ∈ (ball z τ)ᶜ
    · rw [indicator_of_mem hw, indicator_of_mem (hmem.1 hw)]
    · rw [indicator_of_notMem hw, indicator_of_notMem (fun h => hw (hmem.2 h))]
  rw [hf]
  exact ⟨h1.comp_sub_right z, by rw [integral_sub_right_eq_self, h2]⟩

end Radial

/-! ### The defect `D = 1_{B(z,τ)} ∇u - ∇h` -/

/-- A real inner product of two square-integrable fields is integrable. -/
theorem integrable_inner_of_integrable_sq {f g : ℂ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (hf2 : Integrable fun w => ‖f w‖ ^ 2)
    (hg2 : Integrable fun w => ‖g w‖ ^ 2) : Integrable fun w => inner ℝ (f w) (g w) := by
  refine (hf2.add hg2).mono' (hf.inner hg) (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply]
  refine (abs_real_inner_le_norm _ _).trans ?_
  nlinarith [sq_nonneg (‖f w‖ - ‖g w‖)]

/-- The product of the norms of two square-integrable fields is integrable. -/
theorem integrable_norm_mul_norm_of_integrable_sq {f g : ℂ → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hf2 : Integrable fun w => ‖f w‖ ^ 2) (hg2 : Integrable fun w => ‖g w‖ ^ 2) :
    Integrable fun w => ‖f w‖ * ‖g w‖ := by
  refine (hf2.add hg2).mono' (hf.norm.mul hg.norm) (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖f w‖ - ‖g w‖)]

section Defect

variable {lam τ : ℝ} {d : ℂ × ℂ}

/-- The defect `D = 1_{B(z,τ)} ∇u - ∇h` of the screened field (Lemma 3.10). -/
noncomputable def screenedDefect (χ : ℂ → ℝ) (lam τ : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℂ :=
  (ball (dipoleMidpoint d) τ).indicator (screenedField χ lam τ d) w - dipoleField χ lam d w

theorem screenedDefect_of_mem {w : ℂ} (hw : w ∈ ball (dipoleMidpoint d) τ) :
    screenedDefect χ lam τ d w = screenedCorrectionField τ d w := by
  rw [screenedDefect, indicator_of_mem hw, screenedField, add_sub_cancel_left]

theorem screenedDefect_of_notMem {w : ℂ} (hw : w ∉ ball (dipoleMidpoint d) τ) :
    screenedDefect χ lam τ d w = -dipoleField χ lam d w := by
  rw [screenedDefect, indicator_of_notMem hw, zero_sub]

theorem aestronglyMeasurable_screenedDefect (hχ : IsMollifier χ) (hlam : 0 < lam) :
    AEStronglyMeasurable (screenedDefect χ lam τ d) volume :=
  (((measurable_screenedField hχ hlam τ d).indicator measurableSet_ball).sub
    (continuous_dipoleField hχ hlam d).measurable).aestronglyMeasurable

/-- `|∇u|²` is integrable on `B(z, τ)`. -/
theorem integrableOn_norm_sq_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hd : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    IntegrableOn (fun w => ‖screenedField χ lam τ d w‖ ^ 2) (ball (dipoleMidpoint d) τ) :=
  integrableOn_of_continuousOn_closedBall
    ((continuousOn_screenedField_closedBall hχ hlam hd).norm.pow 2)

/-- `|D|²` is integrable. -/
theorem integrable_norm_sq_screenedDefect (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hd : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    Integrable fun w => ‖screenedDefect χ lam τ d w‖ ^ 2 := by
  have h1 := ((integrableOn_norm_sq_screenedField hχ hlam hd).integrable_indicator
    measurableSet_ball).const_mul 2
  have h2 := (integrable_norm_sq_dipoleField hχ hlam d).const_mul 2
  refine (h1.add h2).mono' ((aestronglyMeasurable_screenedDefect hχ hlam).norm.pow 2)
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Pi.add_apply]
  have key : ‖screenedDefect χ lam τ d w‖ ≤
      (ball (dipoleMidpoint d) τ).indicator (fun w => ‖screenedField χ lam τ d w‖) w +
        ‖dipoleField χ lam d w‖ := by
    rw [screenedDefect, ← norm_indicator_eq_indicator_norm]
    exact norm_sub_le _ _
  have hsq : ((ball (dipoleMidpoint d) τ).indicator (fun w => ‖screenedField χ lam τ d w‖) w) ^ 2 =
      (ball (dipoleMidpoint d) τ).indicator (fun w => ‖screenedField χ lam τ d w‖ ^ 2) w := by
    by_cases hw : w ∈ ball (dipoleMidpoint d) τ
    · rw [indicator_of_mem hw, indicator_of_mem hw]
    · rw [indicator_of_notMem hw, indicator_of_notMem hw]
      ring
  have hnn : 0 ≤ (ball (dipoleMidpoint d) τ).indicator (fun w => ‖screenedField χ lam τ d w‖) w :=
    indicator_nonneg (fun _ _ => norm_nonneg _) w
  calc ‖screenedDefect χ lam τ d w‖ ^ 2
      ≤ ((ball (dipoleMidpoint d) τ).indicator (fun w => ‖screenedField χ lam τ d w‖) w +
          ‖dipoleField χ lam d w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) key 2
    _ ≤ 2 * ((ball (dipoleMidpoint d) τ).indicator (fun w => ‖screenedField χ lam τ d w‖) w) ^ 2 +
          2 * ‖dipoleField χ lam d w‖ ^ 2 := by
        nlinarith [sq_nonneg ((ball (dipoleMidpoint d) τ).indicator
          (fun w => ‖screenedField χ lam τ d w‖) w - ‖dipoleField χ lam d w‖)]
    _ = 2 * (ball (dipoleMidpoint d) τ).indicator (fun w => ‖screenedField χ lam τ d w‖ ^ 2) w +
          2 * ‖dipoleField χ lam d w‖ ^ 2 := by rw [hsq]

/-- **`‖D‖²_{L²} ≤ 8π r² / τ²`** (equation (3.20) inside the disc and dipole decay
outside). -/
theorem integral_norm_sq_screenedDefect_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hd : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ∫ w, ‖screenedDefect χ lam τ d w‖ ^ 2 ≤ 8 * Real.pi * ‖d.2 - d.1‖ ^ 2 / τ ^ 2 := by
  set z := dipoleMidpoint d with hz
  set r := ‖d.2 - d.1‖ with hr
  have hτ0 := pos_of_screening hlam hd
  obtain ⟨hI, hval⟩ := integral_indicator_compl_ball_inv_norm_sub_pow_four hτ0 z
  set F : ℂ → ℝ := fun w => (ball z τ).indicator (fun _ => (2 * r / τ ^ 2) ^ 2) w +
    (2 * r) ^ 2 * (ball z τ)ᶜ.indicator (fun w => (‖w - z‖ ^ 4)⁻¹) w with hF
  have hFi : Integrable F :=
    ((integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball).add
      (hI.const_mul _)
  have hle : ∀ w, ‖screenedDefect χ lam τ d w‖ ^ 2 ≤ F w := by
    intro w
    by_cases hw : w ∈ ball z τ
    · have hwc : w ∉ (ball z τ)ᶜ := fun h => h hw
      rw [hF]
      simp only
      rw [indicator_of_mem hw, indicator_of_notMem hwc, mul_zero, add_zero,
        screenedDefect_of_mem hw]
      have hw' : ‖w - z‖ ≤ τ := by
        rw [mem_ball, dist_eq_norm] at hw
        exact hw.le
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_screenedCorrectionField_le hlam hd hw') 2
    · have hwc : w ∈ (ball z τ)ᶜ := hw
      rw [hF]
      simp only
      rw [indicator_of_notMem hw, indicator_of_mem hwc, zero_add, screenedDefect_of_notMem hw,
        norm_neg]
      have hw' : τ ≤ ‖w - z‖ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hw
        exact hw
      have hpos : 0 < ‖w - z‖ := lt_of_lt_of_le hτ0 hw'
      calc ‖dipoleField χ lam d w‖ ^ 2 ≤ (2 * r / ‖w - z‖ ^ 2) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_dipoleField_le_of_le hχ hlam hd hw') 2
        _ = (2 * r) ^ 2 * (‖w - z‖ ^ 4)⁻¹ := by
            field_simp
  calc ∫ w, ‖screenedDefect χ lam τ d w‖ ^ 2 ≤ ∫ w, F w :=
        integral_mono (integrable_norm_sq_screenedDefect hχ hlam hd) hFi hle
    _ = 8 * Real.pi * r ^ 2 / τ ^ 2 := by
        rw [hF, integral_add ((integrableOn_const measure_ball_lt_top.ne).integrable_indicator
          measurableSet_ball) (hI.const_mul _), integral_indicator measurableSet_ball,
          setIntegral_const, volume_real_ball_complex z hτ0.le, integral_const_mul, hval,
          smul_eq_mul]
        field_simp
        ring

/-- **`∫ D_d · ∇h_e = 0`** (the proof of Lemma 3.10). -/
theorem integral_inner_screenedDefect_dipoleField (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hd : 8 * max ‖d.2 - d.1‖ lam ≤ τ) (e : ℂ × ℂ) :
    ∫ w, inner ℝ (screenedDefect χ lam τ d w) (dipoleField χ lam e w) = 0 := by
  have hpt : ∀ w, inner ℝ (screenedDefect χ lam τ d w) (dipoleField χ lam e w) =
      (ball (dipoleMidpoint d) τ).indicator
        (fun w => inner ℝ (screenedField χ lam τ d w) (dipoleField χ lam e w)) w -
      inner ℝ (dipoleField χ lam d w) (dipoleField χ lam e w) := by
    intro w
    rw [screenedDefect, inner_sub_left]
    by_cases hw : w ∈ ball (dipoleMidpoint d) τ
    · rw [indicator_of_mem hw, indicator_of_mem hw]
    · rw [indicator_of_notMem hw, indicator_of_notMem hw, inner_zero_left]
  have h1 : IntegrableOn (fun w => inner ℝ (screenedField χ lam τ d w) (dipoleField χ lam e w))
      (ball (dipoleMidpoint d) τ) :=
    integrableOn_of_continuousOn_closedBall
      ((continuousOn_screenedField_closedBall hχ hlam hd).inner
        (continuous_dipoleField hχ hlam e).continuousOn)
  simp_rw [hpt]
  rw [integral_sub (h1.integrable_indicator measurableSet_ball)
    (integrable_inner_dipoleField hχ hlam d e), integral_indicator measurableSet_ball,
    setIntegral_inner_screenedField_dipoleField hχ hlam hd e, integral_inner_dipoleField hχ hlam,
    sub_self]

/-- **`2π ṽ_ij = ∫ D_i · D_j + 2π v_ij`** (the proof of Lemma 3.10). -/
theorem screenedInteraction_eq_integral_inner_screenedDefect (hχ : IsMollifier χ)
    (hlam : 0 < lam) {d e : ℂ × ℂ} (hd : 8 * max ‖d.2 - d.1‖ lam ≤ τ)
    (he : 8 * max ‖e.2 - e.1‖ lam ≤ τ) :
    2 * Real.pi * screenedInteraction χ lam τ d e =
      (∫ w, inner ℝ (screenedDefect χ lam τ d w) (screenedDefect χ lam τ e w)) +
        2 * Real.pi * dipoleInteraction χ lam d e := by
  set Dd := screenedDefect χ lam τ d with hDd
  set De := screenedDefect χ lam τ e with hDe
  set Hd := dipoleField χ lam d with hHd
  set He := dipoleField χ lam e with hHe
  have hmd := aestronglyMeasurable_screenedDefect (τ := τ) (d := d) hχ hlam
  have hme := aestronglyMeasurable_screenedDefect (τ := τ) (d := e) hχ hlam
  have hmHd : AEStronglyMeasurable Hd volume :=
    (continuous_dipoleField hχ hlam d).aestronglyMeasurable
  have hmHe : AEStronglyMeasurable He volume :=
    (continuous_dipoleField hχ hlam e).aestronglyMeasurable
  have hDd2 := integrable_norm_sq_screenedDefect hχ hlam hd
  have hDe2 := integrable_norm_sq_screenedDefect hχ hlam he
  have hHd2 := integrable_norm_sq_dipoleField hχ hlam d
  have hHe2 := integrable_norm_sq_dipoleField hχ hlam e
  have i1 : Integrable fun w => inner ℝ (Dd w) (De w) :=
    integrable_inner_of_integrable_sq hmd hme hDd2 hDe2
  have i2 : Integrable fun w => inner ℝ (Dd w) (He w) :=
    integrable_inner_of_integrable_sq hmd hmHe hDd2 hHe2
  have i3 : Integrable fun w => inner ℝ (Hd w) (De w) :=
    integrable_inner_of_integrable_sq hmHd hme hHd2 hDe2
  have i4 : Integrable fun w => inner ℝ (Hd w) (He w) :=
    integrable_inner_dipoleField hχ hlam d e
  have hpt : ∀ w, (ball (dipoleMidpoint d) τ ∩ ball (dipoleMidpoint e) τ).indicator
      (fun w => inner ℝ (screenedField χ lam τ d w) (screenedField χ lam τ e w)) w =
      inner ℝ (Dd w) (De w) + inner ℝ (Dd w) (He w) + inner ℝ (Hd w) (De w) +
        inner ℝ (Hd w) (He w) := by
    intro w
    have e1 : (ball (dipoleMidpoint d) τ ∩ ball (dipoleMidpoint e) τ).indicator
        (fun w => inner ℝ (screenedField χ lam τ d w) (screenedField χ lam τ e w)) w =
        inner ℝ ((ball (dipoleMidpoint d) τ).indicator (screenedField χ lam τ d) w)
          ((ball (dipoleMidpoint e) τ).indicator (screenedField χ lam τ e) w) := by
      by_cases hi : w ∈ ball (dipoleMidpoint d) τ <;>
        by_cases hj : w ∈ ball (dipoleMidpoint e) τ <;>
        simp [indicator, hi, hj]
    have e2 : ∀ (f : ℂ × ℂ), (ball (dipoleMidpoint f) τ).indicator (screenedField χ lam τ f) w =
        screenedDefect χ lam τ f w + dipoleField χ lam f w := fun f => by
      rw [screenedDefect, sub_add_cancel]
    rw [e1, e2, e2, inner_add_left, inner_add_right, inner_add_right]
    ring
  have hint : 2 * Real.pi * screenedInteraction χ lam τ d e =
      ∫ w, (ball (dipoleMidpoint d) τ ∩ ball (dipoleMidpoint e) τ).indicator
        (fun w => inner ℝ (screenedField χ lam τ d w) (screenedField χ lam τ e w)) w := by
    rw [integral_indicator (measurableSet_ball.inter measurableSet_ball), screenedInteraction,
      ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [hint]
  simp_rw [hpt]
  have i12 : Integrable fun w => inner ℝ (Dd w) (De w) + inner ℝ (Dd w) (He w) := i1.add i2
  have i123 : Integrable fun w => inner ℝ (Dd w) (De w) + inner ℝ (Dd w) (He w) +
      inner ℝ (Hd w) (De w) := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_inner_screenedDefect_dipoleField hχ hlam hd e]
  have h3 : ∫ w, inner ℝ (Hd w) (De w) = 0 := by
    rw [← integral_inner_screenedDefect_dipoleField hχ hlam he d]
    congr 1
    funext w
    exact real_inner_comm _ _
  rw [h3, integral_inner_dipoleField hχ hlam d e]
  ring

/-- **`|ṽ_ij - v_ij| ≤ 4 r_i r_j / τ²`** (Lemma 3.10, the bound without separation assumption): Cauchy--Schwarz with `‖D_l‖²_{L²} ≤ 8π r_l² / τ²`. -/
theorem abs_screenedInteraction_sub_le (hχ : IsMollifier χ) (hlam : 0 < lam) {d e : ℂ × ℂ}
    (hd : 8 * max ‖d.2 - d.1‖ lam ≤ τ) (he : 8 * max ‖e.2 - e.1‖ lam ≤ τ) :
    |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
      4 * (‖d.2 - d.1‖ * ‖e.2 - e.1‖) / τ ^ 2 := by
  have hτ0 := pos_of_screening hlam hd
  have hpi := Real.pi_pos
  have key := screenedInteraction_eq_integral_inner_screenedDefect hχ hlam hd he
  set I := ∫ w, inner ℝ (screenedDefect χ lam τ d w) (screenedDefect χ lam τ e w) with hI
  have hdiff : screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e =
      I / (2 * Real.pi) := by
    field_simp
    linarith
  have hmd := aestronglyMeasurable_screenedDefect (τ := τ) (d := d) hχ hlam
  have hme := aestronglyMeasurable_screenedDefect (τ := τ) (d := e) hχ hlam
  have hDd2 := integrable_norm_sq_screenedDefect hχ hlam hd
  have hDe2 := integrable_norm_sq_screenedDefect hχ hlam he
  have hcs : |I| ≤ Real.sqrt (∫ w, ‖screenedDefect χ lam τ d w‖ ^ 2) *
      Real.sqrt (∫ w, ‖screenedDefect χ lam τ e w‖ ^ 2) := by
    calc |I| ≤ ∫ w, |inner ℝ (screenedDefect χ lam τ d w) (screenedDefect χ lam τ e w)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ w, ‖screenedDefect χ lam τ d w‖ * ‖screenedDefect χ lam τ e w‖ :=
          integral_mono (integrable_inner_of_integrable_sq hmd hme hDd2 hDe2).abs
            (integrable_norm_mul_norm_of_integrable_sq hmd hme hDd2 hDe2)
            fun w => abs_real_inner_le_norm _ _
      _ ≤ _ := TwoComponentCoulomb.integral_mul_le_sqrt_mul_sqrt (fun w => norm_nonneg _)
          (fun w => norm_nonneg _) hmd.norm hme.norm hDd2 hDe2
  have hb : ∀ f : ℂ × ℂ, 8 * max ‖f.2 - f.1‖ lam ≤ τ →
      Real.sqrt (∫ w, ‖screenedDefect χ lam τ f w‖ ^ 2) ≤
        Real.sqrt (8 * Real.pi) * (‖f.2 - f.1‖ / τ) := by
    intro f hf
    calc Real.sqrt (∫ w, ‖screenedDefect χ lam τ f w‖ ^ 2)
        ≤ Real.sqrt (8 * Real.pi * ‖f.2 - f.1‖ ^ 2 / τ ^ 2) :=
          Real.sqrt_le_sqrt (integral_norm_sq_screenedDefect_le hχ hlam hf)
      _ = Real.sqrt (8 * Real.pi) * (‖f.2 - f.1‖ / τ) := by
          rw [show 8 * Real.pi * ‖f.2 - f.1‖ ^ 2 / τ ^ 2 =
              (8 * Real.pi) * (‖f.2 - f.1‖ / τ) ^ 2 by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hI' : |I| ≤ 8 * Real.pi * (‖d.2 - d.1‖ * ‖e.2 - e.1‖) / τ ^ 2 := by
    refine hcs.trans ((mul_le_mul (hb d hd) (hb e he) (Real.sqrt_nonneg _)
      (by positivity)).trans_eq ?_)
    have hs : Real.sqrt (8 * Real.pi) * Real.sqrt (8 * Real.pi) = 8 * Real.pi :=
      Real.mul_self_sqrt (by positivity)
    rw [show Real.sqrt (8 * Real.pi) * (‖d.2 - d.1‖ / τ) * (Real.sqrt (8 * Real.pi) *
        (‖e.2 - e.1‖ / τ)) = (Real.sqrt (8 * Real.pi) * Real.sqrt (8 * Real.pi)) *
          (‖d.2 - d.1‖ * ‖e.2 - e.1‖) / τ ^ 2 by ring, hs]
  rw [hdiff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    div_le_iff₀ (by positivity)]
  calc |I| ≤ 8 * Real.pi * (‖d.2 - d.1‖ * ‖e.2 - e.1‖) / τ ^ 2 := hI'
    _ = 4 * (‖d.2 - d.1‖ * ‖e.2 - e.1‖) / τ ^ 2 * (2 * Real.pi) := by ring

end Defect

/-! ### Lemma 3.10 -/

/-- **Lemma 3.10**: there is `C > 0` depending only on
`χ` such that, for `λ > 0`, `τ ≥ 8 max(r_i, λ)` and `τ ≥ 8 max(r_j, λ)`:

* `|ṽ_ij - v_ij| ≤ C r_i r_j / τ²` (the bound without separation assumption);
* if `d_ij ≥ min(r_i, r_j)`, equation (3.50)
  `|ṽ_ij| ≤ C r_i r_j / (max(d_ij, λ) max(r_i, r_j, d_ij)) 1_{d_ij ≤ 17τ/8}` and equation (3.51)
  `|ṽ_ij - v_ij| ≤ C r_i r_j / (max(d_ij, λ) max(r_i, r_j, d_ij)) 1_{d_ij > 17τ/8}
    + C r_i r_j / τ² 1_{d_ij ≤ 17τ/8}`.

The paper's hypothesis `σ₂[(x_i, x_j), (y_i, y_j)] = Id` is not used and not assumed. -/
theorem lemma_3_10 (hχ : IsMollifier χ) : ∃ C > 0, ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
    8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
    |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
        C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / τ ^ 2 ∧
      (min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ dipoleDist d e →
        |screenedInteraction χ lam τ d e| ≤
            (if dipoleDist d e ≤ 17 / 8 * τ then C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
              (max (dipoleDist d e) lam * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖))
            else 0) ∧
        |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
            (if 17 / 8 * τ < dipoleDist d e then C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
              (max (dipoleDist d e) lam * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖))
            else 0) +
            (if dipoleDist d e ≤ 17 / 8 * τ then C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / τ ^ 2
            else 0)) := by
  obtain ⟨C₁, hC₁, hv⟩ := abs_dipoleInteraction_le hχ
  refine ⟨C₁ + 19, by positivity, fun lam τ hlam d e hd he => ?_⟩
  have hτ0 := pos_of_screening hlam hd
  have hrd : ‖d.1 - d.2‖ ≤ τ / 8 := by rw [norm_sub_rev]; exact norm_le_of_screening hd
  have hre : ‖e.1 - e.2‖ ≤ τ / 8 := by rw [norm_sub_rev]; exact norm_le_of_screening he
  have hl := lam_le_of_screening hd
  set rr := ‖d.1 - d.2‖ * ‖e.1 - e.2‖ with hrr
  have hrr' : ‖d.2 - d.1‖ * ‖e.2 - e.1‖ = rr := by rw [norm_sub_rev d.2, norm_sub_rev e.2]
  have hrr0 : 0 ≤ rr := by positivity
  have hdiff := abs_screenedInteraction_sub_le hχ hlam hd he
  rw [hrr'] at hdiff
  have hdiffC : |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
      (C₁ + 19) * rr / τ ^ 2 :=
    hdiff.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hrr0)
      (by positivity))
  refine ⟨hdiffC, fun hmin => ?_⟩
  set dd := dipoleDist d e with hdd
  set MM := max dd lam * max dd (max ‖d.1 - d.2‖ ‖e.1 - e.2‖) with hMM
  have hvb : |dipoleInteraction χ lam d e| ≤ C₁ * rr / MM := hv lam hlam d e hmin
  have hdd0 : 0 ≤ dd := by
    rw [hdd, dipoleDist]
    exact le_min (le_min (norm_nonneg _) (norm_nonneg _)) (le_min (norm_nonneg _) (norm_nonneg _))
  have hMM0 : 0 ≤ MM := by positivity
  by_cases hnear : dd ≤ 17 / 8 * τ
  · rw [ite_eq_left hnear, ite_eq_right (not_lt.2 hnear), ite_eq_left hnear, zero_add]
    refine ⟨?_, hdiffC⟩
    have hτMM : 4 * rr / τ ^ 2 ≤ 19 * rr / MM := by
      rcases eq_or_lt_of_le hrr0 with h0 | h0
      · rw [← h0]
        simp
      have hdpos : 0 < ‖d.1 - d.2‖ := by
        by_contra h
        have h' : ‖d.1 - d.2‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
        rw [hrr, h', zero_mul] at h0
        exact lt_irrefl _ h0
      have hMMpos : 0 < MM := by
        rw [hMM]
        exact mul_pos (lt_of_lt_of_le hlam (le_max_right _ _))
          (lt_of_lt_of_le hdpos ((le_max_left _ _).trans (le_max_right _ _)))
      have hMMle : MM ≤ (17 / 8 * τ) * (17 / 8 * τ) := by
        rw [hMM]
        refine mul_le_mul (max_le hnear (by linarith)) (max_le hnear (max_le (by linarith)
          (by linarith))) (le_max_of_le_left hdd0) (by positivity)
      rw [div_le_div_iff₀ (by positivity) hMMpos]
      nlinarith
    calc |screenedInteraction χ lam τ d e|
        = |dipoleInteraction χ lam d e +
            (screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e)| := by ring_nf
      _ ≤ |dipoleInteraction χ lam d e| +
            |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| := abs_add_le _ _
      _ ≤ C₁ * rr / MM + 4 * rr / τ ^ 2 := add_le_add hvb hdiff
      _ ≤ C₁ * rr / MM + 19 * rr / MM := by linarith
      _ = (C₁ + 19) * rr / MM := by ring
  · have hfar : 17 / 8 * τ < dd := not_le.1 hnear
    rw [ite_eq_right hnear, ite_eq_left hfar, ite_eq_right hnear, add_zero]
    have hz : screenedInteraction χ lam τ d e = 0 :=
      screenedInteraction_eq_zero_of_dipoleDist χ lam (norm_le_of_screening hd)
        (norm_le_of_screening he) hfar.le
    rw [hz, abs_zero, zero_sub, abs_neg]
    refine ⟨le_rfl, hvb.trans ?_⟩
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hrr0) hMM0

end MultipoleBKT

end
