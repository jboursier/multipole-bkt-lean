/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.Screened
public import MultipoleBKT.Energy.RouteNeumann.Superposition
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Boundary testing for the concrete screened field

The Neumann problem (3.16) is tested up
to the boundary in (3.25). This lower analytic module first
integrates the Green source equation against the two smeared charges
for interior tests. Radial cutoffs then reach the boundary. The annular
errors tend to zero because the normal component vanishes uniformly there.

`RouteNeumann.integral_greenField_classical` is used to place the Green
representation in the energy class. The public identity in
`Energy.ScreenedNeumann` tests that represented solution.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ}

/-! ### A smooth radial cutoff for an annulus -/

/-- The derivative of the smooth transition function is bounded. -/
theorem exists_abs_deriv_smoothTransition_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℝ, |deriv Real.smoothTransition s| ≤ D := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun s hs => ?_
    rcases lt_or_ge s 0 with h | h
    · have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h] with u hu
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hu)
      rw [this.deriv_eq, deriv_const]
    · have h1 : 1 < s := by
        by_contra h'
        exact hs ⟨h, not_lt.1 h'⟩
      have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds h1] with u hu
        exact Real.smoothTransition.one_of_one_le (le_of_lt hu)
      rw [this.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 0, le_max_right _ _, fun s => (hC s).trans (le_max_left _ _)⟩

/-- A smooth radial cutoff, `1` on `B̄(z, r₁)` and `0` outside `B(z, r₂)`:
`ψ(w) = T((r₂² - |w - z|²) / (r₂² - r₁²))` with `T` the smooth transition function. -/
noncomputable def annulusCutoff (z : ℂ) (r₁ r₂ : ℝ) (w : ℂ) : ℝ :=
  Real.smoothTransition ((r₂ ^ 2 - ‖w - z‖ ^ 2) / (r₂ ^ 2 - r₁ ^ 2))

section Cutoff

variable {z : ℂ} {r₁ r₂ : ℝ}

theorem contDiff_annulusCutoff (z : ℂ) (r₁ r₂ : ℝ) : ContDiff ℝ 1 (annulusCutoff z r₁ r₂) := by
  have h : ContDiff ℝ 1 fun w : ℂ => (r₂ ^ 2 - ‖w - z‖ ^ 2) / (r₂ ^ 2 - r₁ ^ 2) :=
    (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).div_const _
  exact Real.smoothTransition.contDiff.comp h

theorem annulusCutoff_nonneg (z : ℂ) (r₁ r₂ : ℝ) (w : ℂ) : 0 ≤ annulusCutoff z r₁ r₂ w :=
  Real.smoothTransition.nonneg _

theorem annulusCutoff_le_one (z : ℂ) (r₁ r₂ : ℝ) (w : ℂ) : annulusCutoff z r₁ r₂ w ≤ 1 :=
  Real.smoothTransition.le_one _

theorem annulusCutoff_eq_one (h₁ : 0 ≤ r₁) (h : r₁ < r₂) {w : ℂ} (hw : ‖w - z‖ ≤ r₁) :
    annulusCutoff z r₁ r₂ w = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have hpos : 0 < r₂ ^ 2 - r₁ ^ 2 := by nlinarith
  rw [le_div_iff₀ hpos, one_mul]
  nlinarith [norm_nonneg (w - z)]

theorem annulusCutoff_eq_zero (h₁ : 0 ≤ r₁) (h : r₁ < r₂) {w : ℂ} (hw : r₂ ≤ ‖w - z‖) :
    annulusCutoff z r₁ r₂ w = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hpos : 0 < r₂ ^ 2 - r₁ ^ 2 := by nlinarith
  refine div_nonpos_of_nonpos_of_nonneg ?_ hpos.le
  nlinarith

/-- The derivative of the cutoff is radial:
`∇ψ(w) · v = T'(·) · (-(2 (w - z) · v) / (r₂² - r₁²))`. -/
theorem fderiv_annulusCutoff_apply (z : ℂ) (r₁ r₂ : ℝ) (w v : ℂ) :
    fderiv ℝ (annulusCutoff z r₁ r₂) w v =
      deriv Real.smoothTransition ((r₂ ^ 2 - ‖w - z‖ ^ 2) / (r₂ ^ 2 - r₁ ^ 2)) *
        ((r₂ ^ 2 - r₁ ^ 2)⁻¹ * -(2 * inner ℝ (w - z) v)) := by
  have h1 : HasFDerivAt (fun x : ℂ => ‖x - z‖ ^ 2)
      (2 • (innerSL ℝ (w - z)).comp (ContinuousLinearMap.id ℝ ℂ)) w :=
    ((hasFDerivAt_id w).sub_const z).norm_sq
  have h2 := (h1.const_sub (r₂ ^ 2)).const_mul (r₂ ^ 2 - r₁ ^ 2)⁻¹
  have hT : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((r₂ ^ 2 - r₁ ^ 2)⁻¹ * (r₂ ^ 2 - ‖w - z‖ ^ 2)))
      ((r₂ ^ 2 - r₁ ^ 2)⁻¹ * (r₂ ^ 2 - ‖w - z‖ ^ 2)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have h3 := hT.comp_hasFDerivAt w h2
  have e : annulusCutoff z r₁ r₂ =
      Real.smoothTransition ∘ fun x => (r₂ ^ 2 - r₁ ^ 2)⁻¹ * (r₂ ^ 2 - ‖x - z‖ ^ 2) := by
    funext x
    simp [annulusCutoff, div_eq_inv_mul]
  rw [e, h3.fderiv, div_eq_inv_mul]
  simp only [smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]

/-- `|∇ψ(w) · v| ≤ 2 D |(w - z) · v| / (r₂² - r₁²)`. -/
theorem abs_fderiv_annulusCutoff_apply_le {D : ℝ}
    (hD : ∀ s : ℝ, |deriv Real.smoothTransition s| ≤ D) (h₁ : 0 ≤ r₁) (h : r₁ < r₂) (w v : ℂ) :
    |fderiv ℝ (annulusCutoff z r₁ r₂) w v| ≤
      2 * D * |inner ℝ (w - z) v| / (r₂ ^ 2 - r₁ ^ 2) := by
  have hpos : 0 < r₂ ^ 2 - r₁ ^ 2 := by nlinarith
  rw [fderiv_annulusCutoff_apply, abs_mul, abs_mul, abs_neg, abs_mul,
    abs_of_pos (inv_pos.2 hpos), abs_two]
  calc |deriv Real.smoothTransition ((r₂ ^ 2 - ‖w - z‖ ^ 2) / (r₂ ^ 2 - r₁ ^ 2))| *
        ((r₂ ^ 2 - r₁ ^ 2)⁻¹ * (2 * |inner ℝ (w - z) v|))
      ≤ D * ((r₂ ^ 2 - r₁ ^ 2)⁻¹ * (2 * |inner ℝ (w - z) v|)) :=
        mul_le_mul_of_nonneg_right (hD _) (by positivity)
    _ = 2 * D * |inner ℝ (w - z) v| / (r₂ ^ 2 - r₁ ^ 2) := by
        field_simp

/-- `∇ψ = 0` on `B(z, r₁)`. -/
theorem fderiv_annulusCutoff_of_lt (h₁ : 0 ≤ r₁) (h : r₁ < r₂) {w : ℂ} (hw : ‖w - z‖ < r₁) :
    fderiv ℝ (annulusCutoff z r₁ r₂) w = 0 := by
  have : annulusCutoff z r₁ r₂ =ᶠ[𝓝 w] fun _ => (1 : ℝ) := by
    have hopen : IsOpen {x : ℂ | ‖x - z‖ < r₁} :=
      isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
    filter_upwards [hopen.mem_nhds hw] with x hx
    exact annulusCutoff_eq_one h₁ h (le_of_lt hx)
  rw [this.fderiv_eq]
  simp

end Cutoff

/-! ### Integrals over the disc -/

/-- A product `ψ φ` is `C¹` when `ψ` is `C¹` and vanishes outside `B(z, r)`, and `φ` is `C¹` on a
larger disc `B(z, ρ)`. -/
theorem contDiff_mul_of_eq_zero {z : ℂ} {r ρ : ℝ} (hr : r < ρ) {ψ φ : ℂ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψ0 : ∀ w, r ≤ ‖w - z‖ → ψ w = 0)
    (hφ : ContDiffOn ℝ 1 φ (ball z ρ)) : ContDiff ℝ 1 fun w => ψ w * φ w := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : ‖w - z‖ < ρ
  · exact hψ.contDiffAt.mul
      (hφ.contDiffAt (isOpen_ball.mem_nhds (by rwa [mem_ball, dist_eq_norm])))
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have hopen : IsOpen {x : ℂ | r < ‖x - z‖} :=
      isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    filter_upwards [hopen.mem_nhds (show r < ‖w - z‖ by linarith [not_lt.1 hw])] with x hx
    rw [hψ0 x (le_of_lt hx), zero_mul]

/-- The area of the annulus `B(z, τ) \ B(z, r)` is `π (τ² - r²)`. -/
theorem volume_real_ball_sdiff_ball {z : ℂ} {r τ : ℝ} (hr : 0 ≤ r) (hrτ : r ≤ τ) :
    volume.real (ball z τ \ ball z r) = Real.pi * (τ ^ 2 - r ^ 2) := by
  rw [measureReal_sdiff (ball_subset_ball hrτ) measurableSet_ball measure_ball_lt_top.ne,
    volume_real_ball_complex z (hr.trans hrτ), volume_real_ball_complex z hr]
  ring

/-- An integral over `B(z, τ)` of a function vanishing on `B(z, r)` and bounded by `C` on the
annulus is at most `C π (τ² - r²)`. -/
theorem abs_setIntegral_ball_le_of_annulus {z : ℂ} {r τ C : ℝ} (hr : 0 ≤ r) (hrτ : r ≤ τ)
    {f : ℂ → ℝ} (h0 : ∀ w ∈ ball z τ, ‖w - z‖ < r → f w = 0)
    (hC : ∀ w, r ≤ ‖w - z‖ → ‖w - z‖ < τ → |f w| ≤ C) :
    |∫ w in ball z τ, f w| ≤ C * (Real.pi * (τ ^ 2 - r ^ 2)) := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := ball z τ \ ball z r)
    measurableSet_ball sdiff_subset fun w hw => ?_]
  · rw [← volume_real_ball_sdiff_ball (z := z) hr hrτ, ← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const
      ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top) fun w hw => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨h1, h2⟩ := hw
    rw [mem_ball, dist_eq_norm] at h1 h2
    exact hC w (not_lt.1 h2) h1
  · obtain ⟨h1, h2⟩ := hw
    have h3 : w ∈ ball z r := by
      by_contra h
      exact h2 ⟨h1, h⟩
    rw [mem_ball, dist_eq_norm] at h3
    exact h0 w h1 h3

/-! ### The weak Neumann identity -/

section Neumann

variable {lam τ : ℝ} {d : ℂ × ℂ}

/-- **The cutoff estimate**: with the cutoff `ψ_t` of the annulus `τ(1 - t) ≤ |w - z| ≤ τ(1 - t/2)`,
the defect of the weak Neumann identity is at most `M_F · 2πτ² t + 8π M_φ D η`, where `M_F` bounds
`∇φ · ∇u` and `M_φ` bounds `φ` on `B̄(z, τ)`, `D` bounds the derivative of the transition
function, and `η` bounds the normal component `(w - z) · ∇u(w)` on the annulus. -/
theorem abs_setIntegral_fderiv_apply_screenedField_sub_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {ρ : ℝ} (hρ : τ < ρ) {φ : ℂ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (ball (dipoleMidpoint d) ρ)) {MF Mφ D : ℝ}
    (hMF : ∀ w ∈ closedBall (dipoleMidpoint d) τ,
      |fderiv ℝ φ w (screenedField χ lam τ d w)| ≤ MF)
    (hMφ : ∀ w ∈ closedBall (dipoleMidpoint d) τ, |φ w| ≤ Mφ)
    (hD : ∀ s : ℝ, |deriv Real.smoothTransition s| ≤ D) {t η : ℝ} (ht : 0 < t)
    (ht2 : t ≤ 1 / 2)
    (hη : ∀ w, τ * (1 - t) ≤ ‖w - dipoleMidpoint d‖ → ‖w - dipoleMidpoint d‖ < τ →
      |inner ℝ (w - dipoleMidpoint d) (screenedField χ lam τ d w)| ≤ η) :
    |(∫ w in ball (dipoleMidpoint d) τ, fderiv ℝ φ w (screenedField χ lam τ d w)) -
        2 * Real.pi *
          ((∫ v, φ v ∂smearedCharge χ d.1 lam) - ∫ v, φ v ∂smearedCharge χ d.2 lam)| ≤
      MF * (2 * Real.pi * τ ^ 2 * t) + 8 * Real.pi * Mφ * D * η := by
  set z := dipoleMidpoint d with hz
  set U := screenedField χ lam τ d with hU
  have hτ0 := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have hl := lam_le_of_screening hτ
  have hz0 : z ∈ closedBall z τ := mem_closedBall_self hτ0.le
  have hMF0 : 0 ≤ MF := (abs_nonneg _).trans (hMF z hz0)
  have hMφ0 : 0 ≤ Mφ := (abs_nonneg _).trans (hMφ z hz0)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hη0 : 0 ≤ η := by
    refine (abs_nonneg _).trans (hη (z + ((τ * (1 - t / 2) : ℝ) : ℂ)) ?_ ?_)
    · rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by nlinarith)]
      nlinarith
    · rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by nlinarith)]
      nlinarith
  set r₁ := τ * (1 - t) with hr₁
  set r₂ := τ * (1 - t / 2) with hr₂
  have h₁ : 0 ≤ r₁ := mul_nonneg hτ0.le (by linarith)
  have h₁₂ : r₁ < r₂ := by rw [hr₁, hr₂]; nlinarith
  have h₂ : r₂ < τ := by rw [hr₂]; nlinarith
  have hτr₁ : τ / 2 ≤ r₁ := by rw [hr₁]; nlinarith
  set ψ := annulusCutoff z r₁ r₂ with hψ
  have hψc : ContDiff ℝ 1 ψ := contDiff_annulusCutoff z r₁ r₂
  have hψ0 : ∀ w, r₂ ≤ ‖w - z‖ → ψ w = 0 := fun w hw => annulusCutoff_eq_zero h₁ h₁₂ hw
  have hψ1 : ∀ w, ‖w - z‖ ≤ r₁ → ψ w = 1 := fun w hw => annulusCutoff_eq_one h₁ h₁₂ hw
  set ξ : ℂ → ℝ := fun w => ψ w * φ w with hξ
  have hξc : ContDiff ℝ 1 ξ := contDiff_mul_of_eq_zero (h₂.trans hρ) hψc hψ0 hφ
  have hs : tsupport ξ ⊆ ball z τ := by
    apply subset_trans (show tsupport ξ ⊆ closedBall z r₂ from ?_)
      (closedBall_subset_ball h₂)
    apply closure_minimal _ isClosed_closedBall
    intro w hw
    by_contra hn
    apply hw
    change ψ w * φ w = 0
    rw [hψ0 w ?_, zero_mul]
    exact (not_le.mp (by simpa only [mem_closedBall, dist_eq_norm] using hn)).le
  have hc : HasCompactSupport ξ :=
    HasCompactSupport.intro (isCompact_closedBall z r₂) fun w hw => by
      change ψ w * φ w = 0
      rw [hψ0 w ?_, zero_mul]
      exact (not_le.mp (by simpa only [mem_closedBall, dist_eq_norm] using hw)).le
  have hG := RouteNeumann.integral_greenField_source hχ hlam hτ hξc hc hs
  have he : (∫ w in ball z τ, fderiv ℝ ξ w (RouteNeumann.greenField χ lam τ d w)) =
      ∫ w in ball z τ, fderiv ℝ ξ w (U w) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro w hw
    dsimp only
    rw [RouteNeumann.greenField_eq_screenedField hχ hlam hτ
      (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le)]
  rw [he] at hG
  have hδ : ∀ a, ‖a - z‖ = ‖d.2 - d.1‖ / 2 →
      ∫ v, ξ v ∂smearedCharge χ a lam = ∫ v, φ v ∂smearedCharge χ a lam := by
    intro a ha
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_closedBall_smearedCharge (z := a) hχ hlam] with v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    have hvz : ‖v - z‖ ≤ r₁ := by
      have := norm_sub_le_norm_sub_add_norm_sub v a z
      linarith
    simp only [hξ, hψ1 v hvz, one_mul]
  rw [hδ _ (norm_fst_sub_dipoleMidpoint d), hδ _ (norm_snd_sub_dipoleMidpoint d)] at hG
  set F : ℂ → ℝ := fun w => fderiv ℝ φ w (U w) with hF
  set P : ℂ → ℝ := fun w => φ w * fderiv ℝ ψ w (U w) with hP
  have hprod : ∀ w ∈ ball z τ, fderiv ℝ ξ w (U w) = ψ w * F w + P w := by
    intro w hw
    have hwρ : w ∈ ball z ρ := ball_subset_ball hρ.le hw
    have hdφ : DifferentiableAt ℝ φ w :=
      (hφ.contDiffAt (isOpen_ball.mem_nhds hwρ)).differentiableAt one_ne_zero
    have hdψ : DifferentiableAt ℝ ψ w := hψc.differentiable one_ne_zero w
    rw [hξ, fderiv_fun_mul hdψ hdφ]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, hF, hP]
  rw [setIntegral_congr_fun measurableSet_ball hprod] at hG
  have hKρ : closedBall z τ ⊆ ball z ρ := closedBall_subset_ball hρ
  have hK2 : closedBall z τ ⊆ ball z (2 * τ) := closedBall_subset_ball (by linarith)
  have hUc : ContinuousOn U (closedBall z τ) := (continuousOn_screenedField hχ hlam hτ).mono hK2
  have hφc : ContinuousOn φ (closedBall z τ) := hφ.continuousOn.mono hKρ
  have hFc : ContinuousOn F (closedBall z τ) :=
    ((hφ.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hKρ).clm_apply hUc
  have hPc : ContinuousOn P (closedBall z τ) :=
    hφc.mul ((hψc.continuous_fderiv one_ne_zero).continuousOn.clm_apply hUc)
  have hψFc : ContinuousOn (fun w => ψ w * F w) (closedBall z τ) :=
    hψc.continuous.continuousOn.mul hFc
  have hint : ∀ f : ℂ → ℝ, ContinuousOn f (closedBall z τ) → IntegrableOn f (ball z τ) :=
    fun f hf => (hf.integrableOn_compact (isCompact_closedBall z τ)).mono_set ball_subset_closedBall
  rw [integral_add (hint _ hψFc) (hint _ hPc)] at hG
  have hsplit : (∫ w in ball z τ, F w) - 2 * Real.pi *
      ((∫ v, φ v ∂smearedCharge χ d.1 lam) - ∫ v, φ v ∂smearedCharge χ d.2 lam) =
        (∫ w in ball z τ, (1 - ψ w) * F w) - ∫ w in ball z τ, P w := by
    rw [← hG]
    have e : (∫ w in ball z τ, (1 - ψ w) * F w) =
        (∫ w in ball z τ, F w) - ∫ w in ball z τ, ψ w * F w := by
      rw [← integral_sub (hint _ hFc) (hint _ hψFc)]
      congr 1
      funext w
      ring
    rw [e]
    ring
  rw [hsplit]
  have hb1 : |∫ w in ball z τ, (1 - ψ w) * F w| ≤ MF * (Real.pi * (τ ^ 2 - r₁ ^ 2)) := by
    refine abs_setIntegral_ball_le_of_annulus h₁ (by linarith) (fun w _ hw => ?_)
      (fun w _ hw2 => ?_)
    · rw [hψ1 w hw.le, sub_self, zero_mul]
    · have hwK : w ∈ closedBall z τ := by
        rw [mem_closedBall, dist_eq_norm]
        exact hw2.le
      rw [abs_mul]
      have h01 : |1 - ψ w| ≤ 1 := by
        rw [abs_le]
        constructor <;>
          linarith [annulusCutoff_nonneg z r₁ r₂ w, annulusCutoff_le_one z r₁ r₂ w]
      calc |1 - ψ w| * |F w| ≤ 1 * MF := mul_le_mul h01 (hMF w hwK) (abs_nonneg _) zero_le_one
        _ = MF := one_mul _
  have hpos : 0 < r₂ ^ 2 - r₁ ^ 2 := by nlinarith
  have hb2 : |∫ w in ball z τ, P w| ≤
      Mφ * (2 * D * η / (r₂ ^ 2 - r₁ ^ 2)) * (Real.pi * (τ ^ 2 - r₁ ^ 2)) := by
    refine abs_setIntegral_ball_le_of_annulus h₁ (by linarith) (fun w _ hw => ?_)
      (fun w hw1 hw2 => ?_)
    · simp only [hP, hψ, fderiv_annulusCutoff_of_lt h₁ h₁₂ hw, zero_apply,
        mul_zero]
    · have hwK : w ∈ closedBall z τ := by
        rw [mem_closedBall, dist_eq_norm]
        exact hw2.le
      rw [hP, abs_mul]
      refine mul_le_mul (hMφ w hwK) ?_ (abs_nonneg _) hMφ0
      refine (abs_fderiv_annulusCutoff_apply_le hD h₁ h₁₂ w (U w)).trans ?_
      have := hη w hw1 hw2
      gcongr
  have hA : Real.pi * (τ ^ 2 - r₁ ^ 2) ≤ 2 * Real.pi * τ ^ 2 * t := by
    have h' : τ ^ 2 - r₁ ^ 2 ≤ 2 * τ ^ 2 * t := by
      rw [hr₁]
      nlinarith [mul_nonneg (sq_nonneg τ) (sq_nonneg t)]
    calc Real.pi * (τ ^ 2 - r₁ ^ 2) ≤ Real.pi * (2 * τ ^ 2 * t) :=
          mul_le_mul_of_nonneg_left h' Real.pi_pos.le
      _ = 2 * Real.pi * τ ^ 2 * t := by ring
  have hB : τ ^ 2 - r₁ ^ 2 ≤ 4 * (r₂ ^ 2 - r₁ ^ 2) := by
    rw [hr₁, hr₂]
    nlinarith
  have hb2' : Mφ * (2 * D * η / (r₂ ^ 2 - r₁ ^ 2)) * (Real.pi * (τ ^ 2 - r₁ ^ 2)) ≤
      8 * Real.pi * Mφ * D * η := by
    have e : Mφ * (2 * D * η / (r₂ ^ 2 - r₁ ^ 2)) * (Real.pi * (τ ^ 2 - r₁ ^ 2)) =
        (2 * Real.pi * Mφ * D * η) * ((τ ^ 2 - r₁ ^ 2) / (r₂ ^ 2 - r₁ ^ 2)) := by
      field_simp
    have h4 : (τ ^ 2 - r₁ ^ 2) / (r₂ ^ 2 - r₁ ^ 2) ≤ 4 := by
      rw [div_le_iff₀ hpos]
      exact hB
    rw [e]
    calc (2 * Real.pi * Mφ * D * η) * ((τ ^ 2 - r₁ ^ 2) / (r₂ ^ 2 - r₁ ^ 2))
        ≤ (2 * Real.pi * Mφ * D * η) * 4 :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 8 * Real.pi * Mφ * D * η := by ring
  calc |(∫ w in ball z τ, (1 - ψ w) * F w) - ∫ w in ball z τ, P w|
      ≤ |∫ w in ball z τ, (1 - ψ w) * F w| + |∫ w in ball z τ, P w| := abs_sub _ _
    _ ≤ MF * (Real.pi * (τ ^ 2 - r₁ ^ 2)) +
          Mφ * (2 * D * η / (r₂ ^ 2 - r₁ ^ 2)) * (Real.pi * (τ ^ 2 - r₁ ^ 2)) :=
        add_le_add hb1 hb2
    _ ≤ MF * (2 * Real.pi * τ ^ 2 * t) + 8 * Real.pi * Mφ * D * η :=
        add_le_add (mul_le_mul_of_nonneg_left hA hMF0) hb2'

/-- **The classical weak Neumann identity** (equation (3.16)): for `φ` of class `C¹` on a disc `B(z, ρ)`, `ρ > τ`,
`∫_{B(z,τ)} ∇φ · ∇u = 2π (∫ φ dδ_x^{(λ)} - ∫ φ dδ_y^{(λ)})`, where `∇u` is the Green superposition.
It is `-Δu = 2π (δ_x^{(λ)} - δ_y^{(λ)})` in `B(z, τ)` with `∂u/∂ν = 0` on `∂B(z, τ)`, in weak
form. -/
theorem RouteNeumann.integral_greenField_classical (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {ρ : ℝ} (hρ : τ < ρ) {φ : ℂ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (ball (dipoleMidpoint d) ρ)) :
    ∫ w in ball (dipoleMidpoint d) τ, fderiv ℝ φ w (RouteNeumann.greenField χ lam τ d w) =
      2 * Real.pi *
        ((∫ v, φ v ∂smearedCharge χ d.1 lam) - ∫ v, φ v ∂smearedCharge χ d.2 lam) := by
  have he : (∫ w in ball (dipoleMidpoint d) τ,
      fderiv ℝ φ w (RouteNeumann.greenField χ lam τ d w)) =
      ∫ w in ball (dipoleMidpoint d) τ, fderiv ℝ φ w (screenedField χ lam τ d w) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro w hw
    dsimp only
    rw [RouteNeumann.greenField_eq_screenedField hχ hlam hτ
      (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le)]
  rw [he]
  set z := dipoleMidpoint d with hz
  set U := screenedField χ lam τ d with hU
  have hτ0 := pos_of_screening hlam hτ
  have hKρ : closedBall z τ ⊆ ball z ρ := closedBall_subset_ball hρ
  have hK2 : closedBall z τ ⊆ ball z (2 * τ) := closedBall_subset_ball (by linarith)
  have hUc : ContinuousOn U (closedBall z τ) := (continuousOn_screenedField hχ hlam hτ).mono hK2
  have hφc : ContinuousOn φ (closedBall z τ) := hφ.continuousOn.mono hKρ
  have hFc : ContinuousOn (fun w => fderiv ℝ φ w (U w)) (closedBall z τ) :=
    ((hφ.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hKρ).clm_apply hUc
  obtain ⟨MF, hMF⟩ := (isCompact_closedBall z τ).exists_bound_of_continuousOn hFc
  obtain ⟨Mφ, hMφ⟩ := (isCompact_closedBall z τ).exists_bound_of_continuousOn hφc
  obtain ⟨D, hD0, hD⟩ := exists_abs_deriv_smoothTransition_le
  have hz0 : z ∈ closedBall z τ := mem_closedBall_self hτ0.le
  have hMF0 : 0 ≤ MF := (norm_nonneg _).trans (hMF z hz0)
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ z hz0)
  have hGc : ContinuousOn (fun w => inner ℝ (w - z) (U w)) (closedBall z τ) :=
    (continuous_id.sub continuous_const).continuousOn.inner hUc
  have hGu := (isCompact_closedBall z τ).uniformContinuousOn_of_continuous hGc
  rw [Metric.uniformContinuousOn_iff] at hGu
  refine eq_of_forall_dist_le fun ε hε => ?_
  rw [Real.dist_eq]
  set η := ε / (2 * (8 * Real.pi * Mφ * D + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδG⟩ := hGu η hη
  set t := min (1 / 2) (min (δ / (2 * τ)) (ε / (2 * (2 * Real.pi * τ ^ 2 * MF + 1)))) with htdef
  have ht : 0 < t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ht2 : t ≤ 1 / 2 := min_le_left _ _
  have htδ : τ * t < δ := by
    have h1 : t ≤ δ / (2 * τ) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : τ * t ≤ δ / 2 := by
      calc τ * t ≤ τ * (δ / (2 * τ)) := mul_le_mul_of_nonneg_left h1 hτ0.le
        _ = δ / 2 := by field_simp
    linarith
  have htε : MF * (2 * Real.pi * τ ^ 2 * t) ≤ ε / 2 := by
    have h1 : t ≤ ε / (2 * (2 * Real.pi * τ ^ 2 * MF + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hA : 0 ≤ 2 * Real.pi * τ ^ 2 * MF := by positivity
    calc MF * (2 * Real.pi * τ ^ 2 * t) = (2 * Real.pi * τ ^ 2 * MF) * t := by ring
      _ ≤ (2 * Real.pi * τ ^ 2 * MF) * (ε / (2 * (2 * Real.pi * τ ^ 2 * MF + 1))) :=
          mul_le_mul_of_nonneg_left h1 hA
      _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hηε : 8 * Real.pi * Mφ * D * η ≤ ε / 2 := by
    have hB : 0 ≤ 8 * Real.pi * Mφ * D := by positivity
    rw [hηdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hηcond : ∀ w, τ * (1 - t) ≤ ‖w - z‖ → ‖w - z‖ < τ →
      |inner ℝ (w - z) (U w)| ≤ η := by
    intro w hw1 hw2
    have hwpos : 0 < ‖w - z‖ := lt_of_lt_of_le (by nlinarith) hw1
    set w' : ℂ := z + (τ / ‖w - z‖) • (w - z) with hw'
    have hw'n : ‖w' - z‖ = τ := by
      rw [hw', add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hτ0 hwpos), div_mul_cancel₀ _ hwpos.ne']
    have hG' : inner ℝ (w' - z) (U w') = 0 := by
      change inner ℝ (w' - z) (screenedField χ lam τ d w') = 0
      rw [← RouteNeumann.greenField_eq_screenedField hχ hlam hτ hw'n.le]
      exact RouteNeumann.inner_greenField_eq_zero hχ hlam hτ hw'n
    have hwK : w ∈ closedBall z τ := by
      rw [mem_closedBall, dist_eq_norm]
      exact hw2.le
    have hw'K : w' ∈ closedBall z τ := by
      rw [mem_closedBall, dist_eq_norm, hw'n]
    have hdist : dist w w' < δ := by
      rw [dist_eq_norm]
      have e : w - w' = (1 - τ / ‖w - z‖) • (w - z) := by
        rw [hw', sub_smul, one_smul]
        abel
      have hneg : 1 - τ / ‖w - z‖ ≤ 0 := by
        rw [sub_nonpos, le_div_iff₀ hwpos, one_mul]
        exact hw2.le
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonpos hneg]
      have e2 : -(1 - τ / ‖w - z‖) * ‖w - z‖ = τ - ‖w - z‖ := by
        field_simp
        ring
      rw [e2]
      nlinarith
    have h := hδG w hwK w' hw'K hdist
    rw [Real.dist_eq, hG', sub_zero] at h
    exact h.le
  have hbd := abs_setIntegral_fderiv_apply_screenedField_sub_le hχ hlam hτ hρ hφ
    (MF := MF) (Mφ := Mφ) (fun w hw => by simpa [Real.norm_eq_abs] using hMF w hw)
    (fun w hw => by simpa [Real.norm_eq_abs] using hMφ w hw) hD ht ht2 hηcond
  linarith

end Neumann

end MultipoleBKT

end
