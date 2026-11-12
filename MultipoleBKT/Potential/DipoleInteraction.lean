/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteMixed.Calculus
public import MultipoleBKT.Frozen.DipoleInteraction
public import MultipoleBKT.Frozen.IsStableDipolePair

/-!
# The dipole interaction and its classical Hessian integral

See Lemma 3.7 of the paper. The kernel has a continuous classical Hessian by
`contDiff_smearedKernel_two`.

`dipoleInteraction_eq_integral_hessian` is (3.38): apply the
fundamental theorem of calculus along each of the two dipoles, with centered
parameters in `[-1/2, 1/2]`. The far case of item (2) integrates the Hessian
bound on this rectangle, whose points have modulus at least `d_ij / 2`.
The near case uses the two one-segment gradient estimates, as in the paper.

Under the additional global Lipschitz regularity of `D²g₁` in item (1),
scaling and the logarithmic exterior give the cubic decay bound for Hessian
increments. Subtracting the central Hessian inside the double integral gives
the first-order remainder and `lemma_3_7_vijexp2`.

The near case uses `dipoleInteraction_eq_mixed` to group the two gradient
segment estimates. The Appendix lower event uses the Hessian integral and
the global classical Hessian bound. The symmetric third-order expansion
(3.29) is not proved in this module.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace NNReal
open ComplexConjugate
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- `d_ij = dist({x_i, y_i}, {x_j, y_j})` for `d = (x_i, y_i)` and `e = (x_j, y_j)`: the minimum
of the four distances, as in `MultipoleLinked`. See Lemma 3.7 of the paper. -/
noncomputable def dipoleDist (d e : ℂ × ℂ) : ℝ :=
  min (min ‖d.1 - e.1‖ ‖d.1 - e.2‖) (min ‖d.2 - e.1‖ ‖d.2 - e.2‖)

/-! ### Derivatives of `g_λ` -/

/-- `g_λ` is differentiable, for `λ > 0`. -/
theorem differentiable_smearedKernel (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Differentiable ℝ (smearedKernel χ lam) := by
  rw [← twoRadiusKernel_self]
  exact differentiable_twoRadiusKernel hχ hlam hlam

/-- `g_λ = g` near `z` when `|z| > 2λ`. -/
theorem smearedKernel_eventuallyEq_logKernel (hχ : IsMollifier χ) (hlam : 0 < lam) {z : ℂ}
    (hz : 2 * lam < ‖z‖) : smearedKernel χ lam =ᶠ[𝓝 z] fun w => -Real.log ‖w‖ := by
  filter_upwards [(continuous_norm.tendsto z).eventually (lt_mem_nhds hz)] with w hw
  exact smearedKernel_eq_logKernel hχ hlam hw.le

/-- `∇g_λ(z) = ∇g(z) = -z / |z|²` for `|z| > 2λ`. -/
theorem hasFDerivAt_smearedKernel_of_lt (hχ : IsMollifier χ) (hlam : 0 < lam) {z : ℂ}
    (hz : 2 * lam < ‖z‖) :
    HasFDerivAt (smearedKernel χ lam) (toDual ℝ ℂ (-(‖z‖ ^ 2)⁻¹ • z)) z := by
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  exact (hasFDerivAt_neg_log_norm hz0).congr_of_eventuallyEq
    (smearedKernel_eventuallyEq_logKernel hχ hlam hz)

/-- `|∇g_λ| ≤ √(π M) / λ` (Lemma 3.1 at scale `λ`). -/
theorem norm_fderiv_smearedKernel_le_inv (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (z : ℂ) :
    ‖fderiv ℝ (smearedKernel χ lam) z‖ ≤ Real.sqrt (Real.pi * M) / lam := by
  rw [← twoRadiusKernel_self]
  exact norm_fderiv_twoRadiusKernel_le hχ hM hlam hlam z

/-- **Equation (3.36), `q = 1`**: `|∇g_λ(z)| ≤ (1 + 2 √(π M)) / max(|z|, λ)`. -/
theorem norm_fderiv_smearedKernel_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (z : ℂ) :
    ‖fderiv ℝ (smearedKernel χ lam) z‖ ≤ (1 + 2 * Real.sqrt (Real.pi * M)) / max ‖z‖ lam := by
  have hS : 0 ≤ Real.sqrt (Real.pi * M) := Real.sqrt_nonneg _
  have hmax : 0 < max ‖z‖ lam := lt_max_of_lt_right hlam
  rcases lt_or_ge (2 * lam) ‖z‖ with hz | hz
  · have hz0 : 0 < ‖z‖ := by linarith
    rw [(hasFDerivAt_smearedKernel_of_lt hχ hlam hz).fderiv, LinearIsometryEquiv.norm_map,
      norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity),
      max_eq_left (by linarith : lam ≤ ‖z‖)]
    rw [le_div_iff₀ hz0]
    have : (‖z‖ ^ 2)⁻¹ * ‖z‖ * ‖z‖ = 1 := by field_simp
    rw [this]
    linarith
  · have h1 := norm_fderiv_smearedKernel_le_inv hχ hM hlam z
    have h2 : max ‖z‖ lam ≤ 2 * lam := max_le hz (by linarith)
    refine h1.trans ?_
    rw [div_le_div_iff₀ hlam hmax]
    nlinarith

/-- Differentiate the scaling identity (3.35) twice.
-/
theorem hessian_smearedKernel_scale (hχ : IsMollifier χ) (hlam : 0 < lam) (z : ℂ) :
    fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) z =
      (lam⁻¹ ^ 2) • fderiv ℝ (fderiv ℝ (smearedKernel χ 1)) (lam⁻¹ • z) := by
  have he : smearedKernel χ lam = fun x => TwoComponentCoulomb.logKernel (lam : ℂ) +
      smearedKernel χ 1 (lam⁻¹ • x) := by
    funext x
    rw [smearedKernel_eq_logKernel_add hχ hlam]
    congr 1
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  rw [he]
  have hd : fderiv ℝ (fun x => TwoComponentCoulomb.logKernel (lam : ℂ) +
      smearedKernel χ 1 (lam⁻¹ • x)) = fun x => lam⁻¹ • fderiv ℝ (smearedKernel χ 1) (lam⁻¹ • x) := by
    funext x
    rw [fderiv_const_add, fderiv_comp_smul]
  have hf' : ContDiff ℝ 1 (fderiv ℝ (smearedKernel χ 1)) :=
    (contDiff_smearedKernel_two hχ one_pos).fderiv_right (by norm_num)
  have hdd := hf'.differentiable (by norm_num)
  have hds : DifferentiableAt ℝ (fun x : ℂ => fderiv ℝ (smearedKernel χ 1) (lam⁻¹ • x)) z := by
    apply (hdd _).comp z
    exact (differentiableAt_id.const_smul lam⁻¹)
  rw [hd, fderiv_fun_const_smul hds (lam⁻¹), fderiv_comp_smul, smul_smul, sq]

/-- Outside the cutoff, the classical Hessian is that of the logarithm.
See (3.36). -/
theorem hessian_smearedKernel_of_lt (hχ : IsMollifier χ) (hlam : 0 < lam) {z : ℂ} (hz : 2 * lam < ‖z‖) :
    fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) z =
      (toDual ℝ ℂ).toContinuousLinearMap.comp
        (((conj z ^ 2)⁻¹) • Complex.conjCLE.toContinuousLinearMap) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hz' : conj z ≠ 0 := (map_ne_zero _).mpr hz0
  have hd := (((hasDerivAt_inv hz').hasFDerivAt.restrictScalars ℝ).comp z
    Complex.conjCLE.hasFDerivAt).neg
  have hd' := (toDual ℝ ℂ).toContinuousLinearMap.hasFDerivAt.comp z hd
  have hg : fderiv ℝ (smearedKernel χ lam) =ᶠ[𝓝 z] fun w => toDual ℝ ℂ (-(conj w)⁻¹) := by
    filter_upwards [(continuous_norm.tendsto z).eventually (lt_mem_nhds hz)] with w hw
    rw [(hasFDerivAt_smearedKernel_of_lt hχ hlam hw).fderiv]
    congr 1
    rw [Complex.inv_def, Complex.normSq_conj, Complex.conj_conj, Complex.normSq_eq_norm_sq,
      Complex.real_smul]
    push_cast
    ring
  have hh := hd'.congr_of_eventuallyEq hg
  rw [hh.fderiv]
  congr 1
  ext v
  simp [ContinuousLinearMap.comp_apply]
  ring

private theorem norm_inv_square_sub_le {s : ℝ} {z w : ℂ} (hs : 0 < s) (hz : s ≤ ‖z‖) (hw : s ≤ ‖w‖) :
    ‖(conj z ^ 2)⁻¹ - (conj w ^ 2)⁻¹‖ ≤ 2 * ‖z - w‖ / s ^ 3 := by
  have hz0 : conj z ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp (hs.trans_le hz))
  have hw0 : conj w ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp (hs.trans_le hw))
  have he : (conj z ^ 2)⁻¹ - (conj w ^ 2)⁻¹ =
      ((conj z)⁻¹ - (conj w)⁻¹) * ((conj z)⁻¹ + (conj w)⁻¹) := by
    rw [← inv_pow, ← inv_pow]; ring
  rw [he, norm_mul]
  have hi : ‖(conj z)⁻¹ - (conj w)⁻¹‖ = ‖z - w‖ / (‖z‖ * ‖w‖) := by
    simpa only [dist_eq_norm, ← map_sub, Complex.norm_conj] using dist_inv_inv₀ hz0 hw0
  rw [hi]
  have hb : ‖(conj z)⁻¹ + (conj w)⁻¹‖ ≤ 2 / s := by
    calc _ ≤ ‖(conj z)⁻¹‖ + ‖(conj w)⁻¹‖ := norm_add_le _ _
      _ = ‖z‖⁻¹ + ‖w‖⁻¹ := by simp only [norm_inv, Complex.norm_conj]
      _ ≤ s⁻¹ + s⁻¹ := add_le_add (inv_anti₀ hs hz) (inv_anti₀ hs hw)
      _ = 2 / s := by ring
  have hn : ‖z - w‖ / (‖z‖ * ‖w‖) ≤ ‖z - w‖ / s ^ 2 :=
    div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hs)
      (by nlinarith [mul_le_mul hz hw hs.le (hs.le.trans hz)])
  have hh := mul_le_mul hn hb (norm_nonneg ((conj z)⁻¹ + (conj w)⁻¹))
    (by positivity : 0 ≤ ‖z - w‖ / s ^ 2)
  convert hh using 1
  ring

private theorem norm_log_hessian_sub_le (z w : ℂ) :
    ‖(toDual ℝ ℂ).toContinuousLinearMap.comp (((conj z ^ 2)⁻¹) • Complex.conjCLE.toContinuousLinearMap) -
      (toDual ℝ ℂ).toContinuousLinearMap.comp (((conj w ^ 2)⁻¹) • Complex.conjCLE.toContinuousLinearMap)‖ ≤
      ‖(conj z ^ 2)⁻¹ - (conj w ^ 2)⁻¹‖ := by
  have he : ((conj z ^ 2)⁻¹) • Complex.conjCLE.toContinuousLinearMap -
      ((conj w ^ 2)⁻¹) • Complex.conjCLE.toContinuousLinearMap =
      ((conj z ^ 2)⁻¹ - (conj w ^ 2)⁻¹) • Complex.conjCLE.toContinuousLinearMap := by
    ext v
    simp only [sub_apply, smul_apply]
    exact (sub_mul _ _ _).symm
  rw [← ContinuousLinearMap.comp_sub, he]
  calc _ ≤ ‖(toDual ℝ ℂ).toContinuousLinearMap‖ *
      ‖((conj z ^ 2)⁻¹ - (conj w ^ 2)⁻¹) • Complex.conjCLE.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by
      have ht : ‖(toDual ℝ ℂ).toContinuousLinearMap‖ = 1 :=
        (toDual ℝ ℂ).norm_toContinuousLinearMap
      have hc : ‖Complex.conjCLE.toContinuousLinearMap‖ = 1 :=
        Complex.conjLIE.norm_toContinuousLinearMap
      rw [norm_smul, ht, hc, mul_one, one_mul]

/-- The classical form of (3.36), `q = 2`.
Use the
bounded classical Hessian near the cutoff and the logarithmic Hessian outside. -/
theorem norm_hessian_smearedKernel_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (z : ℂ) :
    ‖fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) z‖ ≤
      (1 + 12 * Real.pi * M) / max ‖z‖ lam ^ 2 := by
  have hM0 := hχ.nonneg_of_le hM
  have hm : 0 < max ‖z‖ lam := lt_max_of_lt_right hlam
  rcases lt_or_ge (2 * lam) ‖z‖ with hz | hz
  · have hz0 : 0 < ‖z‖ := by linarith
    rw [hessian_smearedKernel_of_lt hχ hlam hz, max_eq_left (by linarith : lam ≤ ‖z‖)]
    have hh : ‖(toDual ℝ ℂ).toContinuousLinearMap.comp
        (((conj z ^ 2)⁻¹) • Complex.conjCLE.toContinuousLinearMap)‖ ≤ ‖z‖⁻¹ ^ 2 := by
      calc _ ≤ ‖(toDual ℝ ℂ).toContinuousLinearMap‖ *
          ‖((conj z ^ 2)⁻¹) • Complex.conjCLE.toContinuousLinearMap‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ = _ := by
          have ht : ‖(toDual ℝ ℂ).toContinuousLinearMap‖ = 1 :=
            (toDual ℝ ℂ).norm_toContinuousLinearMap
          have hc : ‖Complex.conjCLE.toContinuousLinearMap‖ = 1 :=
            Complex.conjLIE.norm_toContinuousLinearMap
          rw [norm_smul, ht, hc]
          simp only [norm_inv, norm_pow, Complex.norm_conj, one_mul, mul_one, inv_pow]
    refine hh.trans ?_
    have he : ‖z‖⁻¹ ^ 2 = 1 / ‖z‖ ^ 2 := by ring
    rw [he, div_le_div_iff₀ (sq_pos_of_pos hz0) (sq_pos_of_pos hz0)]
    nlinarith [mul_nonneg (show 0 ≤ 12 * Real.pi * M by positivity) (sq_nonneg ‖z‖)]
  · have hb : ‖fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) z‖ ≤
        3 * (Real.pi * M / lam ^ 2) := by
      rw [← twoRadiusKernel_self]
      exact norm_fderiv_fderiv_twoRadiusKernel_le hχ hM hlam hlam z
    refine hb.trans ?_
    rw [le_div_iff₀ (sq_pos_of_pos hm)]
    have hp : max ‖z‖ lam ^ 2 ≤ 4 * lam ^ 2 := by
      have hh : max ‖z‖ lam ≤ 2 * lam := max_le hz (by linarith)
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * (Real.pi * M / lam ^ 2) by positivity)
    have he : 3 * (Real.pi * M / lam ^ 2) * (4 * lam ^ 2) = 12 * Real.pi * M := by
      field_simp
      ring
    rw [he] at hh
    linarith

/-- `A / x ≤ c A / y` when `0 ≤ A`, `0 < x`, `0 < y` and `y ≤ c x`. -/
theorem div_le_mul_div_of_le_mul {A x y c : ℝ} (hA : 0 ≤ A) (hx : 0 < x) (hy : 0 < y)
    (h : y ≤ c * x) : A / x ≤ c * A / y := by
  rw [div_le_div_iff₀ hx hy]
  calc A * y ≤ A * (c * x) := mul_le_mul_of_nonneg_left h hA
    _ = c * A * x := by ring

/-- Scaling and the logarithmic exterior give the `q = 3` estimate in
(3.36), in its Lipschitz-Hessian form. -/
theorem norm_hessian_smearedKernel_sub_le (hχ : IsMollifier χ) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ (smearedKernel χ 1))))
    (hlam : 0 < lam) {s : ℝ} {z w : ℂ} (hz : s ≤ ‖z‖) (hw : s ≤ ‖w‖) :
    ‖fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) z -
      fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) w‖ ≤
      (2 + 8 * (L : ℝ)) * ‖z - w‖ / max s lam ^ 3 := by
  have hm : 0 < max s lam := lt_max_of_lt_right hlam
  rcases lt_or_ge (2 * lam) s with hs | hs
  · rw [hessian_smearedKernel_of_lt hχ hlam (hs.trans_le hz),
      hessian_smearedKernel_of_lt hχ hlam (hs.trans_le hw)]
    have hs0 : 0 < s := by linarith
    have hb := (norm_log_hessian_sub_le z w).trans (norm_inv_square_sub_le hs0 hz hw)
    rw [max_eq_left (by linarith : lam ≤ s)]
    refine hb.trans ?_
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith [norm_nonneg (z - w), L.coe_nonneg]
  · have hb := hL.norm_sub_le (lam⁻¹ • z) (lam⁻¹ • w)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam.le)] at hb
    have hg : ‖fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) z -
        fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) w‖ ≤ (L : ℝ) * ‖z - w‖ / lam ^ 3 := by
      rw [hessian_smearedKernel_scale hχ hlam z, hessian_smearedKernel_scale hχ hlam w]
      rw [← smul_sub (lam⁻¹ ^ 2)
        (fderiv ℝ (fderiv ℝ (smearedKernel χ 1)) (lam⁻¹ • z))
        (fderiv ℝ (fderiv ℝ (smearedKernel χ 1)) (lam⁻¹ • w))]
      calc _ ≤ ‖lam⁻¹ ^ 2‖ * ‖fderiv ℝ (fderiv ℝ (smearedKernel χ 1)) (lam⁻¹ • z) -
            fderiv ℝ (fderiv ℝ (smearedKernel χ 1)) (lam⁻¹ • w)‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ ‖lam⁻¹ ^ 2‖ * ((L : ℝ) * (lam⁻¹ * ‖z - w‖)) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = _ := by rw [Real.norm_of_nonneg (sq_nonneg _)]; ring
    have hp : max s lam ^ 3 ≤ 8 * lam ^ 3 := by
      calc _ ≤ (2 * lam) ^ 3 := by gcongr; exact max_le hs (by linarith)
        _ = _ := by ring
    have hd := div_le_mul_div_of_le_mul (A := (L : ℝ) * ‖z - w‖)
      (by positivity) (pow_pos hlam _) (pow_pos hm _) hp
    refine hg.trans (hd.trans ?_)
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith [norm_nonneg (z - w), L.coe_nonneg]

/-! ### Increments of `g_λ` -/

section Increments

/-- `max(D, λ) ≤ 2 max(D / 2, λ)` for `λ ≥ 0`. -/
theorem max_le_two_mul_max_half {D lam : ℝ} (hlam : 0 ≤ lam) :
    max D lam ≤ 2 * max (D / 2) lam :=
  max_le (by linarith [le_max_left (D / 2) lam]) (by linarith [le_max_right (D / 2) lam])

/-- A point of the segment `[q, p]` whose endpoints have norms `≥ D ≥ |p - q|` has norm
`≥ D / 2`. -/
theorem half_le_norm_of_mem_segment {D : ℝ} {p q z : ℂ} (hp : D ≤ ‖p‖) (hq : D ≤ ‖q‖)
    (hpq : ‖p - q‖ ≤ D) (hz : z ∈ segment ℝ q p) : D / 2 ≤ ‖z‖ := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hz
  show D / 2 ≤ ‖q + θ • (p - q)‖
  have hn := norm_nonneg (p - q)
  rcases le_total θ (1 / 2) with hθ | hθ
  · have h2 : ‖θ • (p - q)‖ ≤ D / 2 := by
      rw [norm_smul, Real.norm_of_nonneg h0]
      nlinarith
    have h3 : ‖q‖ ≤ ‖q + θ • (p - q)‖ + ‖θ • (p - q)‖ := by
      simpa using norm_sub_le (q + θ • (p - q)) (θ • (p - q))
    linarith
  · have e : q + θ • (p - q) = p - (1 - θ) • (p - q) := by
      rw [sub_smul, one_smul]
      abel
    have h2 : ‖(1 - θ) • (p - q)‖ ≤ D / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      nlinarith
    have h3 : ‖p‖ ≤ ‖p - (1 - θ) • (p - q)‖ + ‖(1 - θ) • (p - q)‖ := by
      simpa using norm_sub_le (p - (1 - θ) • (p - q)) (-((1 - θ) • (p - q)))
    rw [e]
    linarith

/-- **One-segment estimate** (Lemma 3.7): if `|p|, |q| ≥ D` and `|p - q| ≤ D`, then `|g_λ(p) - g_λ(q)| ≤ 2 (1 + 2 √(π M)) |p - q| / max(D, λ)`. -/
theorem abs_smearedKernel_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {D : ℝ} {p q : ℂ} (hp : D ≤ ‖p‖) (hq : D ≤ ‖q‖) (hpq : ‖p - q‖ ≤ D) :
    |smearedKernel χ lam p - smearedKernel χ lam q| ≤
      2 * (1 + 2 * Real.sqrt (Real.pi * M)) * ‖p - q‖ / max D lam := by
  set K := 1 + 2 * Real.sqrt (Real.pi * M) with hK
  have hK0 : 0 ≤ K := by positivity
  have hbound : ∀ z ∈ segment ℝ q p, ‖fderiv ℝ (smearedKernel χ lam) z‖ ≤ 2 * K / max D lam := by
    intro z hz
    have hz' := half_le_norm_of_mem_segment hp hq hpq hz
    refine (norm_fderiv_smearedKernel_le hχ hM hlam z).trans ?_
    refine div_le_mul_div_of_le_mul hK0 (lt_max_of_lt_right hlam) (lt_max_of_lt_right hlam) ?_
    exact max_le (by linarith [le_max_left ‖z‖ lam]) (by linarith [le_max_right ‖z‖ lam])
  have h := (convex_segment q p).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (differentiable_smearedKernel hχ hlam z).hasFDerivAt.hasFDerivWithinAt) hbound
    (left_mem_segment ℝ q p) (right_mem_segment ℝ q p)
  rw [Real.norm_eq_abs] at h
  calc |smearedKernel χ lam p - smearedKernel χ lam q| ≤ 2 * K / max D lam * ‖p - q‖ := h
    _ = 2 * K * ‖p - q‖ / max D lam := by ring

end Increments

/-! ### The dipole–dipole interaction -/

section Interaction

/-- `d_ij` is symmetric in the two dipoles. -/
theorem dipoleDist_comm (d e : ℂ × ℂ) : dipoleDist d e = dipoleDist e d := by
  simp only [dipoleDist, norm_sub_rev e.1, norm_sub_rev e.2]
  exact min_min_min_comm _ _ _ _

theorem dipoleDist_le_fst_fst (d e : ℂ × ℂ) : dipoleDist d e ≤ ‖d.1 - e.1‖ :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem dipoleDist_le_fst_snd (d e : ℂ × ℂ) : dipoleDist d e ≤ ‖d.1 - e.2‖ :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem dipoleDist_le_snd_fst (d e : ℂ × ℂ) : dipoleDist d e ≤ ‖d.2 - e.1‖ :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem dipoleDist_le_snd_snd (d e : ℂ × ℂ) : dipoleDist d e ≤ ‖d.2 - e.2‖ :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- `v_ij = v_{i,j,+} - v_{i,j,-}` (Definition 3.6), with
`v_{i,j,+} = g_λ(x_i - x_j) - g_λ(y_i - x_j)` and `v_{i,j,-} = g_λ(x_i - y_j) - g_λ(y_i - y_j)`. -/
theorem dipoleInteraction_eq_sub (hχ : IsMollifier χ) (lam : ℝ) (d e : ℂ × ℂ) :
    dipoleInteraction χ lam d e =
      (smearedKernel χ lam (d.1 - e.1) - smearedKernel χ lam (d.2 - e.1)) -
        (smearedKernel χ lam (d.1 - e.2) - smearedKernel χ lam (d.2 - e.2)) := by
  rw [dipoleInteraction, show e.1 - d.2 = -(d.2 - e.1) by ring, smearedKernel_neg hχ]
  ring

/-- `v_ij` as a mixed second difference of `g_λ`, with `a = x_i - x_j`, `h = y_i - x_i`,
`k = x_j - y_j`. -/
theorem dipoleInteraction_eq_mixed (hχ : IsMollifier χ) (lam : ℝ) (d e : ℂ × ℂ) :
    dipoleInteraction χ lam d e =
      smearedKernel χ lam ((d.1 - e.1) + (d.2 - d.1) + (e.1 - e.2)) -
        smearedKernel χ lam ((d.1 - e.1) + (d.2 - d.1)) -
        smearedKernel χ lam ((d.1 - e.1) + (e.1 - e.2)) + smearedKernel χ lam (d.1 - e.1) := by
  rw [dipoleInteraction_eq_sub hχ, show d.1 - e.1 + (d.2 - d.1) + (e.1 - e.2) = d.2 - e.2 by ring,
    show d.1 - e.1 + (d.2 - d.1) = d.2 - e.1 by ring,
    show d.1 - e.1 + (e.1 - e.2) = d.1 - e.2 by ring]
  ring

/-- **Equation (3.38)** with `ρ = z_j - z_i`, `r_i = y_i - x_i`,
`r_j = y_j - x_j`. Integrate the continuous Hessian first along `r_i`, then
along `r_j`. -/
theorem dipoleInteraction_eq_integral_hessian (hχ : IsMollifier χ) (hlam : 0 < lam)
    (d e : ℂ × ℂ) :
    dipoleInteraction χ lam d e =
      -(∫ t in -(1 / 2 : ℝ)..1 / 2, ∫ s in -(1 / 2 : ℝ)..1 / 2,
        fderiv ℝ (fderiv ℝ (smearedKernel χ lam))
          ((1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2) + s • (d.2 - d.1) + t • (e.2 - e.1))
          (d.2 - d.1) (e.2 - e.1)) := by
  rw [RouteMixed.integral_hessian_rectangle (contDiff_smearedKernel_two hχ hlam)]
  have ep : (1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2) + (1 / 2 : ℝ) • (d.2 - d.1) +
      (1 / 2 : ℝ) • (e.2 - e.1) = -(d.1 - e.2) := by
    simp only [Complex.real_smul]
    push_cast
    ring
  have em : (1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2) + (1 / 2 : ℝ) • (d.2 - d.1) +
      (-(1 / 2 : ℝ)) • (e.2 - e.1) = -(d.1 - e.1) := by
    simp only [Complex.real_smul]
    push_cast
    ring
  have mp : (1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2) + (-(1 / 2 : ℝ)) • (d.2 - d.1) +
      (1 / 2 : ℝ) • (e.2 - e.1) = -(d.2 - e.2) := by
    simp only [Complex.real_smul]
    push_cast
    ring
  have mm : (1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2) + (-(1 / 2 : ℝ)) • (d.2 - d.1) +
      (-(1 / 2 : ℝ)) • (e.2 - e.1) = -(d.2 - e.1) := by
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [ep, em, mp, mm, smearedKernel_neg hχ, smearedKernel_neg hχ,
    smearedKernel_neg hχ, smearedKernel_neg hχ, dipoleInteraction_eq_sub hχ]
  ring

/-- The centered rectangle in (3.38) stays at distance at least
`d_ij / 2` from zero in the far case. -/
theorem half_dipoleDist_le_norm_rectangle {d e : ℂ × ℂ}
    (hfar : 2 * (‖d.2 - d.1‖ + ‖e.2 - e.1‖) ≤ dipoleDist d e)
    {s t : ℝ} (hs : s ∈ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    dipoleDist d e / 2 ≤ ‖(1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2) +
      s • (d.2 - d.1) + t • (e.2 - e.1)‖ := by
  have he : (1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2) +
      s • (d.2 - d.1) + t • (e.2 - e.1) =
      (e.1 - d.1) + (s - 1 / 2) • (d.2 - d.1) + (t + 1 / 2) • (e.2 - e.1) := by
    simp only [Complex.real_smul]
    push_cast
    ring
  have hb : ‖(s - 1 / 2) • (d.2 - d.1) + (t + 1 / 2) • (e.2 - e.1)‖ ≤
      ‖d.2 - d.1‖ + ‖e.2 - e.1‖ := by
    calc _ ≤ ‖(s - 1 / 2) • (d.2 - d.1)‖ + ‖(t + 1 / 2) • (e.2 - e.1)‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonpos (by linarith [hs.2]), abs_of_nonneg (by linarith [ht.1])]
        nlinarith [norm_nonneg (d.2 - d.1), norm_nonneg (e.2 - e.1), hs.1, ht.2]
  have hn := norm_sub_le
    ((e.1 - d.1) + ((s - 1 / 2) • (d.2 - d.1) + (t + 1 / 2) • (e.2 - e.1)))
    ((s - 1 / 2) • (d.2 - d.1) + (t + 1 / 2) • (e.2 - e.1))
  rw [add_sub_cancel_right, norm_sub_rev e.1] at hn
  rw [he, add_assoc]
  linarith [dipoleDist_le_fst_fst d e]

/-- The far case of item (2), obtained by bounding the Hessian in
(3.38). -/
theorem abs_dipoleInteraction_le_far (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {d e : ℂ × ℂ}
    (hfar : 2 * (‖d.2 - d.1‖ + ‖e.2 - e.1‖) ≤ dipoleDist d e) :
    |dipoleInteraction χ lam d e| ≤
      4 * (1 + 12 * Real.pi * M) * ‖d.1 - d.2‖ * ‖e.1 - e.2‖ / max (dipoleDist d e) lam ^ 2 := by
  rw [dipoleInteraction_eq_integral_hessian hχ hlam, abs_neg, ← Real.norm_eq_abs]
  apply RouteMixed.norm_integral_integral_le
  intro s hs t ht
  let x := (1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2) + s • (d.2 - d.1) + t • (e.2 - e.1)
  have hx := half_dipoleDist_le_norm_rectangle hfar hs ht
  have hM0 := hχ.nonneg_of_le hM
  have hm : max (dipoleDist d e) lam ≤ 2 * max ‖x‖ lam :=
    max_le (by linarith [le_max_left ‖x‖ lam]) (by linarith [le_max_right ‖x‖ lam])
  have hb : (1 + 12 * Real.pi * M) / max ‖x‖ lam ^ 2 ≤
      4 * (1 + 12 * Real.pi * M) / max (dipoleDist d e) lam ^ 2 := by
    apply div_le_mul_div_of_le_mul (by positivity) (by positivity) (by positivity)
    nlinarith [show 0 < max ‖x‖ lam from lt_max_of_lt_right hlam,
      show 0 < max (dipoleDist d e) lam from lt_max_of_lt_right hlam]
  calc _ ≤ ‖fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) x‖ * ‖d.2 - d.1‖ * ‖e.2 - e.1‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ (4 * (1 + 12 * Real.pi * M) / max (dipoleDist d e) lam ^ 2) *
        ‖d.2 - d.1‖ * ‖e.2 - e.1‖ := by
      gcongr
      exact (norm_hessian_smearedKernel_le hχ hM hlam x).trans hb
    _ = _ := by rw [norm_sub_rev d.2, norm_sub_rev e.2]; ring

/-- First-order expansion of the Hessian in (3.38).
The explicit
constant depends on the global Lipschitz constant of `D²g₁`. -/
theorem dipoleInteraction_hessian_remainder_le (hχ : IsMollifier χ) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ (smearedKernel χ 1))))
    (hlam : 0 < lam) {d e : ℂ × ℂ}
    (hfar : 4 * max ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ dipoleDist d e) :
    |dipoleInteraction χ lam d e +
      fderiv ℝ (fderiv ℝ (smearedKernel χ lam))
        ((1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2)) (d.2 - d.1) (e.2 - e.1)| ≤
      8 * (2 + 8 * (L : ℝ)) * ‖d.1 - d.2‖ * ‖e.1 - e.2‖ *
        (‖d.1 - d.2‖ + ‖e.1 - e.2‖) /
        max ‖(1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2)‖ lam ^ 3 := by
  let ρ := (1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2)
  let h := d.2 - d.1
  let k := e.2 - e.1
  let H := fderiv ℝ (fderiv ℝ (smearedKernel χ lam))
  have hn : ‖h‖ + ‖k‖ ≤ ‖ρ‖ := by
    have he : e.1 - d.1 = ρ + (1 / 2 : ℝ) • h + (-(1 / 2 : ℝ)) • k := by
      dsimp only [ρ, h, k]
      simp only [Complex.real_smul]
      push_cast
      ring
    have hb := RouteMixed.norm_rectangle_shift_le h k
      (show (1 / 2 : ℝ) ∈ Icc (-(1 / 2)) (1 / 2) by constructor <;> norm_num)
      (show (-(1 / 2 : ℝ)) ∈ Icc (-(1 / 2)) (1 / 2) by constructor <;> norm_num)
    have hd := dipoleDist_le_fst_fst d e
    rw [← norm_sub_rev e.1, he, add_assoc] at hd
    have ht := norm_add_le ρ ((1 / 2 : ℝ) • h + (-(1 / 2 : ℝ)) • k)
    have hmax : ‖h‖ + ‖k‖ ≤ 2 * max ‖d.1 - d.2‖ ‖e.1 - e.2‖ := by
      dsimp only [h, k]
      rw [norm_sub_rev d.2, norm_sub_rev e.2]
      linarith [le_max_left ‖d.1 - d.2‖ ‖e.1 - e.2‖,
        le_max_right ‖d.1 - d.2‖ ‖e.1 - e.2‖]
    linarith [norm_nonneg h, norm_nonneg k]
  have hc : Continuous H := by
    dsimp only [H]
    rw [← twoRadiusKernel_self]
    exact continuous_fderiv_fderiv_twoRadiusKernel hχ hlam hlam
  rw [dipoleInteraction_eq_integral_hessian hχ hlam]
  change |-(∫ t in -(1 / 2 : ℝ)..1 / 2, ∫ s in -(1 / 2 : ℝ)..1 / 2,
    H (ρ + s • h + t • k) h k) + H ρ h k| ≤ _
  rw [show -(∫ t in -(1 / 2 : ℝ)..1 / 2, ∫ s in -(1 / 2 : ℝ)..1 / 2,
    H (ρ + s • h + t • k) h k) + H ρ h k =
    -((∫ t in -(1 / 2 : ℝ)..1 / 2, ∫ s in -(1 / 2 : ℝ)..1 / 2,
      H (ρ + s • h + t • k) h k) - H ρ h k) by ring, abs_neg, ← Real.norm_eq_abs]
  apply RouteMixed.norm_integral_integral_sub_const_le
  · exact ((hc.comp ((continuous_const.add (continuous_fst.smul continuous_const)).add
      (continuous_snd.smul continuous_const))).clm_apply continuous_const).clm_apply continuous_const
  · intro s hs t ht
    have hshift := RouteMixed.norm_rectangle_shift_le h k hs ht
    have hx : ‖ρ‖ / 2 ≤ ‖ρ + s • h + t • k‖ := by
      have hh := norm_sub_le (ρ + (s • h + t • k)) (s • h + t • k)
      rw [add_sub_cancel_right] at hh
      rw [add_assoc]
      linarith
    have hρ : ‖ρ‖ / 2 ≤ ‖ρ‖ := by linarith [norm_nonneg ρ]
    have hb := norm_hessian_smearedKernel_sub_le hχ hL hlam hx hρ
    have hm : max ‖ρ‖ lam ≤ 2 * max (‖ρ‖ / 2) lam := max_le_two_mul_max_half hlam.le
    have hm0 : 0 < max (‖ρ‖ / 2) lam := lt_max_of_lt_right hlam
    have hp : max ‖ρ‖ lam ^ 3 ≤ 8 * max (‖ρ‖ / 2) lam ^ 3 := by
      calc _ ≤ (2 * max (‖ρ‖ / 2) lam) ^ 3 := by gcongr
        _ = _ := by ring
    have hd := div_le_mul_div_of_le_mul
      (A := (2 + 8 * (L : ℝ)) * ‖(ρ + s • h + t • k) - ρ‖)
      (by positivity) (pow_pos hm0 _) (by positivity) hp
    have hshift' : ‖(ρ + s • h + t • k) - ρ‖ ≤ ‖h‖ + ‖k‖ := by
      rw [show (ρ + s • h + t • k) - ρ = s • h + t • k by abel]
      linarith [norm_nonneg h, norm_nonneg k]
    have hhb : ‖H (ρ + s • h + t • k) - H ρ‖ ≤
        8 * (2 + 8 * (L : ℝ)) * (‖h‖ + ‖k‖) / max ‖ρ‖ lam ^ 3 := by
      refine hb.trans (hd.trans ?_)
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc 8 * ((2 + 8 * (L : ℝ)) * ‖(ρ + s • h + t • k) - ρ‖) =
          (8 * (2 + 8 * (L : ℝ))) * ‖(ρ + s • h + t • k) - ρ‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hshift' (by positivity)
    have he : H (ρ + s • h + t • k) h k - H ρ h k =
        (H (ρ + s • h + t • k) - H ρ) h k := rfl
    rw [he]
    calc _ ≤ ‖H (ρ + s • h + t • k) - H ρ‖ * ‖h‖ * ‖k‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ (8 * (2 + 8 * (L : ℝ)) * (‖h‖ + ‖k‖) / max ‖ρ‖ lam ^ 3) * ‖h‖ * ‖k‖ := by gcongr
      _ = _ := by
        dsimp only [h, k, ρ]
        rw [norm_sub_rev d.2, norm_sub_rev e.2]
        ring

/-- **Equation (3.30)** with an explicit remainder. The hypothesis is exactly
the additional Lipschitz regularity of `D²g₁` in item (1). -/
theorem lemma_3_7_vijexp2 (hχ : IsMollifier χ) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ (smearedKernel χ 1))))
    (hlam : 0 < lam) {d e : ℂ × ℂ}
    (hfar : 4 * max ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ dipoleDist d e) :
    |dipoleInteraction χ lam d e +
      fderiv ℝ (fderiv ℝ (smearedKernel χ lam))
        ((1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2)) (d.2 - d.1) (e.2 - e.1)| ≤
      16 * (2 + 8 * (L : ℝ)) *
        (min ‖d.1 - d.2‖ ‖e.1 - e.2‖ * (‖d.1 - d.2‖ ^ 2 + ‖e.1 - e.2‖ ^ 2)) /
        max ‖(1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2)‖ lam ^ 3 := by
  have hb := dipoleInteraction_hessian_remainder_le hχ hL hlam hfar
  have halg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      a * b * (a + b) ≤ 2 * (min a b * (a ^ 2 + b ^ 2)) := by
    have h₁ : a * (a + b) ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
    have h₂ : b * (a + b) ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab]
      nlinarith [mul_le_mul_of_nonneg_left h₂ ha]
    · rw [min_eq_right hab]
      nlinarith [mul_le_mul_of_nonneg_left h₁ hb]
  refine hb.trans ?_
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  have hh := mul_le_mul_of_nonneg_left
    (halg ‖d.1 - d.2‖ ‖e.1 - e.2‖ (norm_nonneg _) (norm_nonneg _)) (show 0 ≤ 8 * (2 + 8 * (L : ℝ)) by positivity)
  nlinarith

/-- `v_ij = v_ji`. -/
theorem dipoleInteraction_comm (hχ : IsMollifier χ) (lam : ℝ) (d e : ℂ × ℂ) :
    dipoleInteraction χ lam d e = dipoleInteraction χ lam e d := by
  rw [dipoleInteraction, dipoleInteraction, show e.1 - d.1 = -(d.1 - e.1) by ring,
    show e.2 - d.2 = -(d.2 - e.2) by ring, smearedKernel_neg hχ, smearedKernel_neg hχ]
  ring

/-- `v_ij = 0` when `r_j = 0`. -/
theorem dipoleInteraction_eq_zero_of_right (hχ : IsMollifier χ) (lam : ℝ) (d : ℂ × ℂ) {e : ℂ × ℂ}
    (he : e.1 = e.2) : dipoleInteraction χ lam d e = 0 := by
  rw [dipoleInteraction_eq_sub hχ, he]
  ring

/-- `v_ij = 0` when `r_i = 0`. -/
theorem dipoleInteraction_eq_zero_of_left (hχ : IsMollifier χ) (lam : ℝ) {d : ℂ × ℂ}
    (hd : d.1 = d.2) (e : ℂ × ℂ) : dipoleInteraction χ lam d e = 0 := by
  rw [dipoleInteraction_eq_sub hχ, hd]
  ring

/-- The core of equation (3.32), when `r_j ≤ r_i` and `r_j ≤ d_ij`, in product form:
`|v_ij| max(d_ij, λ) max(d_ij, r_i) ≤ (16 (1 + 2 √(π M)) + 4 (1 + 12 π M)) r_i r_j`. -/
theorem abs_dipoleInteraction_mul_le_of_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {d e : ℂ × ℂ} (hr : ‖e.1 - e.2‖ ≤ ‖d.1 - d.2‖)
    (hD : ‖e.1 - e.2‖ ≤ dipoleDist d e) :
    |dipoleInteraction χ lam d e| * (max (dipoleDist d e) lam * max (dipoleDist d e) ‖d.1 - d.2‖) ≤
      (16 * (1 + 2 * Real.sqrt (Real.pi * M)) + 4 * (1 + 12 * Real.pi * M)) *
        (‖d.1 - d.2‖ * ‖e.1 - e.2‖) := by
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  set K₁ := 1 + 2 * Real.sqrt (Real.pi * M) with hK₁
  set K₂ := 1 + 12 * Real.pi * M with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  set D := dipoleDist d e with hDdef
  set ri := ‖d.1 - d.2‖ with hri
  set rj := ‖e.1 - e.2‖ with hrj
  have hrj0 : 0 ≤ rj := norm_nonneg _
  have hri0 : 0 ≤ ri := hrj0.trans hr
  have hX : 0 < max D lam := lt_max_of_lt_right hlam
  have hY : 0 ≤ max D ri := hri0.trans (le_max_right _ _)
  have hrr : 0 ≤ ri * rj := mul_nonneg hri0 hrj0
  rcases le_or_gt D (4 * ri) with h4 | h4
  · -- `r_j ≤ d_ij ≤ 4 r_i`: two one-segment estimates
    rw [dipoleInteraction_eq_mixed hχ]
    have e1 : (d.1 - e.1 + (d.2 - d.1) + (e.1 - e.2)) - (d.1 - e.1 + (d.2 - d.1)) = e.1 - e.2 := by
      ring
    have e2 : (d.1 - e.1 + (e.1 - e.2)) - (d.1 - e.1) = e.1 - e.2 := by ring
    have hA := abs_smearedKernel_sub_le hχ hM hlam
      (p := d.1 - e.1 + (d.2 - d.1) + (e.1 - e.2)) (q := d.1 - e.1 + (d.2 - d.1)) (D := D)
      (by rw [show d.1 - e.1 + (d.2 - d.1) + (e.1 - e.2) = d.2 - e.2 by ring]
          exact dipoleDist_le_snd_snd d e)
      (by rw [show d.1 - e.1 + (d.2 - d.1) = d.2 - e.1 by ring]; exact dipoleDist_le_snd_fst d e)
      (by rw [e1]; exact hD)
    have hB := abs_smearedKernel_sub_le hχ hM hlam
      (p := d.1 - e.1 + (e.1 - e.2)) (q := d.1 - e.1) (D := D)
      (by rw [show d.1 - e.1 + (e.1 - e.2) = d.1 - e.2 by ring]; exact dipoleDist_le_fst_snd d e)
      (dipoleDist_le_fst_fst d e) (by rw [e2]; exact hD)
    rw [e1] at hA
    rw [e2] at hB
    have hA' : |smearedKernel χ lam (d.1 - e.1 + (d.2 - d.1) + (e.1 - e.2)) -
        smearedKernel χ lam (d.1 - e.1 + (d.2 - d.1))| ≤ 2 * K₁ * rj / max D lam := hA
    have hB' : |smearedKernel χ lam (d.1 - e.1 + (e.1 - e.2)) - smearedKernel χ lam (d.1 - e.1)| ≤
        2 * K₁ * rj / max D lam := hB
    have hv : |smearedKernel χ lam (d.1 - e.1 + (d.2 - d.1) + (e.1 - e.2)) -
          smearedKernel χ lam (d.1 - e.1 + (d.2 - d.1)) -
          smearedKernel χ lam (d.1 - e.1 + (e.1 - e.2)) + smearedKernel χ lam (d.1 - e.1)| ≤
        4 * K₁ * rj / max D lam := by
      calc _ = |(smearedKernel χ lam (d.1 - e.1 + (d.2 - d.1) + (e.1 - e.2)) -
              smearedKernel χ lam (d.1 - e.1 + (d.2 - d.1))) -
            (smearedKernel χ lam (d.1 - e.1 + (e.1 - e.2)) - smearedKernel χ lam (d.1 - e.1))| := by
            congr 1
            ring
        _ ≤ _ := abs_sub _ _
        _ ≤ 2 * K₁ * rj / max D lam + 2 * K₁ * rj / max D lam := add_le_add hA' hB'
        _ = 4 * K₁ * rj / max D lam := by ring
    have hY4 : max D ri ≤ 4 * ri := max_le h4 (by linarith)
    calc _ ≤ 4 * K₁ * rj / max D lam * (max D lam * max D ri) :=
          mul_le_mul_of_nonneg_right hv (mul_nonneg hX.le hY)
      _ = 4 * K₁ * rj * max D ri := by field_simp
      _ ≤ 4 * K₁ * rj * (4 * ri) := mul_le_mul_of_nonneg_left hY4 (by positivity)
      _ = 16 * K₁ * (ri * rj) := by ring
      _ ≤ (16 * K₁ + 4 * K₂) * (ri * rj) := by
          refine mul_le_mul_of_nonneg_right ?_ hrr
          linarith
  · -- `d_ij > 4 r_i`: integrate the Hessian along both dipoles
    have hhk : 2 * (‖d.2 - d.1‖ + ‖e.1 - e.2‖) ≤ D := by
      rw [norm_sub_rev]
      linarith
    have hv := abs_dipoleInteraction_le_far hχ hM hlam
      (show 2 * (‖d.2 - d.1‖ + ‖e.2 - e.1‖) ≤ dipoleDist d e by
        rw [norm_sub_rev e.2]; exact hhk)
    have hYD : max D ri ≤ max D lam := by
      rw [max_eq_left (by linarith : ri ≤ D)]
      exact le_max_left _ _
    calc _ ≤ 4 * K₂ * ri * rj / max D lam ^ 2 * (max D lam * max D ri) :=
          mul_le_mul_of_nonneg_right hv (mul_nonneg hX.le hY)
      _ ≤ 4 * K₂ * ri * rj / max D lam ^ 2 * (max D lam * max D lam) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYD hX.le) ?_
          positivity
      _ = 4 * K₂ * (ri * rj) := by field_simp
      _ ≤ (16 * K₁ + 4 * K₂) * (ri * rj) := by
          refine mul_le_mul_of_nonneg_right ?_ hrr
          linarith

/-- **Equation (3.32)** with an explicit constant, for all positions (the event `𝒜_ij` is not
needed): if `d_ij ≥ min(r_i, r_j)`, then
`|v_ij| ≤ C r_i r_j / (max(d_ij, λ) max(d_ij, max(r_i, r_j)))` with
`C = 16 (1 + 2 √(π M)) + 4 (1 + 12 π M)`, `M` a bound for `χ`. -/
theorem abs_dipoleInteraction_le_of_bound (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {d e : ℂ × ℂ} (hD : min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ dipoleDist d e) :
    |dipoleInteraction χ lam d e| ≤
      (16 * (1 + 2 * Real.sqrt (Real.pi * M)) + 4 * (1 + 12 * Real.pi * M)) *
        (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
        (max (dipoleDist d e) lam * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖)) := by
  have hX : 0 < max (dipoleDist d e) lam := lt_max_of_lt_right hlam
  rcases eq_or_ne e.1 e.2 with he | he
  · rw [dipoleInteraction_eq_zero_of_right hχ lam d he, he, sub_self, norm_zero, mul_zero,
      mul_zero, zero_div, abs_zero]
  rcases eq_or_ne d.1 d.2 with hd | hd
  · rw [dipoleInteraction_eq_zero_of_left hχ lam hd e, hd, sub_self, norm_zero, zero_mul,
      mul_zero, zero_div, abs_zero]
  have hri : 0 < ‖d.1 - d.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hd)
  have hY : 0 < max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖) :=
    lt_max_of_lt_right (lt_max_of_lt_left hri)
  rw [le_div_iff₀ (mul_pos hX hY)]
  rcases le_total ‖e.1 - e.2‖ ‖d.1 - d.2‖ with hr | hr
  · rw [min_eq_right hr] at hD
    rw [max_eq_left hr]
    exact abs_dipoleInteraction_mul_le_of_le hχ hM hlam hr hD
  · rw [min_eq_left hr] at hD
    rw [dipoleDist_comm] at hD ⊢
    rw [max_eq_right hr, dipoleInteraction_comm hχ, mul_comm ‖d.1 - d.2‖]
    exact abs_dipoleInteraction_mul_le_of_le hχ hM hlam hr hD

/-- **Equation (3.32)** for all positions: there is `C > 0` depending only on `χ` such that, for
every `λ > 0` and all dipoles with `d_ij ≥ min(r_i, r_j)`,
`|v_ij| ≤ C r_i r_j / (max(d_ij, λ) max(d_ij, max(r_i, r_j)))`. -/
theorem abs_dipoleInteraction_le (hχ : IsMollifier χ) : ∃ C > 0, ∀ lam : ℝ, 0 < lam →
    ∀ d e : ℂ × ℂ, min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ dipoleDist d e →
      |dipoleInteraction χ lam d e| ≤ C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
        (max (dipoleDist d e) lam * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖)) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  exact ⟨_, by positivity, fun lam hlam d e hD => abs_dipoleInteraction_le_of_bound hχ hM hlam hD⟩

/-- The one-segment estimate behind equation (3.34): if `r_i ≤ min(|x_i - x|, |y_i - x|)`, then
`|g_λ(x_i - x) - g_λ(y_i - x)| ≤ 2 (1 + 2 √(π M)) r_i / max(min(|x_i - x|, |y_i - x|), λ)`. -/
theorem abs_smearedKernel_sub_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {d : ℂ × ℂ} {x : ℂ} (h : ‖d.1 - d.2‖ ≤ min ‖d.1 - x‖ ‖d.2 - x‖) :
    |smearedKernel χ lam (d.1 - x) - smearedKernel χ lam (d.2 - x)| ≤
      2 * (1 + 2 * Real.sqrt (Real.pi * M)) * ‖d.1 - d.2‖ / max (min ‖d.1 - x‖ ‖d.2 - x‖) lam := by
  have e : d.1 - x - (d.2 - x) = d.1 - d.2 := by ring
  have := abs_smearedKernel_sub_le hχ hM hlam (p := d.1 - x) (q := d.2 - x)
    (D := min ‖d.1 - x‖ ‖d.2 - x‖) (min_le_left _ _) (min_le_right _ _) (by rw [e]; exact h)
  rwa [e] at this

/-- **Lemma 3.7 (3)** (equations (3.33), (3.34)): there is
`C > 0` depending only on `χ` such that, for `λ > 0` and dipoles `d = (x_i, y_i)`, `e = (x_j, y_j)`,
with `d_{i,j}^+ = dist({x_i, y_i}, x_j)` and `d_{i,j}^- = dist({x_i, y_i}, y_j)`:
if `d_{i,j}^+ ≥ r_i`, then `|v_{i,j,+}| ≤ C r_i / max(d_{i,j}^+, λ)`, and
if `d_{i,j}^- ≥ r_i`, then `|v_{i,j,-}| ≤ C r_i / max(d_{i,j}^-, λ)`, where
`v_{i,j,+} = g_λ(x_i - x_j) - g_λ(y_i - x_j)` and `v_{i,j,-} = g_λ(x_i - y_j) - g_λ(y_i - y_j)`. -/
theorem lemma_3_7_3 (hχ : IsMollifier χ) : ∃ C > 0, ∀ lam : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
    (‖d.1 - d.2‖ ≤ min ‖d.1 - e.1‖ ‖d.2 - e.1‖ →
      |smearedKernel χ lam (d.1 - e.1) - smearedKernel χ lam (d.2 - e.1)| ≤
        C * ‖d.1 - d.2‖ / max (min ‖d.1 - e.1‖ ‖d.2 - e.1‖) lam) ∧
    (‖d.1 - d.2‖ ≤ min ‖d.1 - e.2‖ ‖d.2 - e.2‖ →
      |smearedKernel χ lam (d.1 - e.2) - smearedKernel χ lam (d.2 - e.2)| ≤
        C * ‖d.1 - d.2‖ / max (min ‖d.1 - e.2‖ ‖d.2 - e.2‖) lam) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  exact ⟨_, by positivity, fun lam hlam d e => ⟨abs_smearedKernel_sub_sub_le hχ hM hlam,
    abs_smearedKernel_sub_sub_le hχ hM hlam⟩⟩

end Interaction

end MultipoleBKT

end
