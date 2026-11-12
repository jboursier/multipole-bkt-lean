/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.ScreenedNeumann
public import MultipoleBKT.Potential.DipoleInteraction

/-!
# The energy upper bound with screened dipole fields (Section 3.3: Lemma 3.4, equation (3.53))

This file proves Lemma 3.4 of the paper:
for a configuration `c : Fin N → ℂ × ℂ`, `c i = (x_i, y_i)`, `λ > 0` and `τ ≥ 8 max(r_i, λ)` for
all `i` (`r_i = |y_i - x_i|`),

`F_λ(X_N, Y_N) ≤ -Σᵢ g_λ(x_i - y_i) + ½ Σ_{i ≠ j} ṽ_ij + Σᵢ r_i² / τ²`

(`lemma_3_4`; the paper's `O(Σᵢ r_i²/τ²)` with the explicit constant `1`), and equation (3.53),
its specialization to `τ₀ = 8 ε₀ R` (`eq_b2`, `exists_eq_b2`).

The proof is the paper's. The pasted field `E = Σᵢ 1_{B(z_i,τ)} ∇u_i` satisfies
`∫ E · ∇h_λ = ∫ |∇h_λ|²` by the weak Neumann identity
(`MultipoleBKT.integral_fderiv_apply_screenedField`, with `φ = h_λ`) and the energy identity, so
`∫ |∇h_λ|² ≤ ∫ |E|²` (the `L²`-projection property, `integral_norm_sq_electricField_le`). The
square `|E|²` expands into `Σᵢ ∫_{B_i} |∇u_i|² + 2π Σ_{i≠j} ṽ_ij`. By the weak Neumann identity
with `φ = h_i` and `φ = ũ_i`,
`∫_{B_i} |∇u_i|² = 4π(g(λ) + κ) - 4π g_λ(x_i - y_i) + 2π ∫ ũ_i d(δ_{x_i}^{(λ)} - δ_{y_i}^{(λ)})`
(`setIntegral_norm_sq_screenedField_eq`), and the last term is at most `4π r_i² / τ²` by (3.20)
(`abs_integral_screenedCorrection_sub_le`). Then equation (2.57) concludes. The hypothesis
`σ_N = Id` of the paper is not used by the proof and is not assumed.

The file also records the support property of `ṽ_ij` from Lemma 3.10:
`ṽ_ij = 0` when `d_ij ≥ 17τ/8` (`screenedInteraction_eq_zero_of_dipoleDist`).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ}

/-! ### Integrals against one smeared charge -/

/-- A function continuous on `B̄(a, λ)` is integrable for `δ_a^{(λ)}`, `λ > 0`. -/
theorem integrable_smearedCharge_of_continuousOn (hχ : IsMollifier χ) {a : ℂ} {lam : ℝ}
    (hlam : 0 < lam) {f : ℂ → ℝ} (hf : ContinuousOn f (closedBall a lam)) :
    Integrable f (smearedCharge χ a lam) := by
  have := isFiniteMeasure_smearedCharge hχ a lam
  have hr : (smearedCharge χ a lam).restrict (closedBall a lam) = smearedCharge χ a lam :=
    Measure.restrict_eq_self_of_ae_mem (ae_mem_closedBall_smearedCharge hχ hlam)
  rw [← hr]
  exact hf.integrableOn_compact (isCompact_closedBall a lam)

section Dipole

variable {lam τ : ℝ} {d : ℂ × ℂ}

/-- The self-energy of the dipole potential:
`∫ h dδ_x^{(λ)} - ∫ h dδ_y^{(λ)} = 2 (g(λ) + κ) - 2 g_λ(x - y)` (equation (2.4)). -/
theorem integral_dipolePotential_sub (hχ : IsMollifier χ) (hlam : 0 < lam) (d : ℂ × ℂ) :
    (∫ v, dipolePotential χ lam d v ∂smearedCharge χ d.1 lam) -
        ∫ v, dipolePotential χ lam d v ∂smearedCharge χ d.2 lam =
      2 * (logKernel (lam : ℂ) + kappa χ) - 2 * smearedKernel χ lam (d.1 - d.2) := by
  have h := fun a => integral_electricPotential_smearedCharge (d := dipoleCharge 1)
    (z := dipoleCentre fun _ : Fin 1 => d) (α := fun _ => lam) hχ (fun _ => hlam) a
  have h1 : ∫ v, dipolePotential χ lam d v ∂smearedCharge χ d.1 lam =
      smearedKernel χ lam 0 - smearedKernel χ lam (d.2 - d.1) := by
    rw [dipolePotential_eq_electricPotential,
      show smearedCharge χ d.1 lam =
        smearedCharge χ (dipoleCentre (fun _ : Fin 1 => d) (Sum.inl 0)) lam from rfl, h]
    simp only [dipoleCentre, Fintype.sum_sum_type, dipoleCharge, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, one_mul, neg_mul,
      integral_logKernel_prod_smearedCharge, sub_self]
    ring
  have h2 : ∫ v, dipolePotential χ lam d v ∂smearedCharge χ d.2 lam =
      smearedKernel χ lam (d.1 - d.2) - smearedKernel χ lam 0 := by
    rw [dipolePotential_eq_electricPotential,
      show smearedCharge χ d.2 lam =
        smearedCharge χ (dipoleCentre (fun _ : Fin 1 => d) (Sum.inr 0)) lam from rfl, h]
    simp only [dipoleCentre, Fintype.sum_sum_type, dipoleCharge, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, one_mul, neg_mul,
      integral_logKernel_prod_smearedCharge, sub_self]
    ring
  rw [h1, h2, smearedKernel_zero hχ hlam, show d.2 - d.1 = -(d.1 - d.2) by ring,
    smearedKernel_neg hχ]
  ring

/-- `|∫ ũ dδ_x^{(λ)} - ∫ ũ dδ_y^{(λ)}| ≤ 2 r² / τ²`, from (3.20). -/
theorem abs_integral_screenedCorrection_sub_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    |(∫ v, screenedCorrection τ d v ∂smearedCharge χ d.1 lam) -
        ∫ v, screenedCorrection τ d v ∂smearedCharge χ d.2 lam| ≤
      2 * ‖d.2 - d.1‖ ^ 2 / τ ^ 2 := by
  set z := dipoleMidpoint d with hz
  set u := screenedCorrection τ d with hu
  have hτ0 := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have hl := lam_le_of_screening hτ
  have := isProbabilityMeasure_smearedCharge hχ d.2 hlam
  set s : Set ℂ := closedBall z (‖d.2 - d.1‖ / 2 + lam) with hs
  have hsτ : ∀ w ∈ s, ‖w - z‖ ≤ τ := fun w hw => by
    rw [hs, mem_closedBall, dist_eq_norm] at hw
    linarith
  have hu' : ∀ w ∈ s, HasFDerivAt u (toDual ℝ ℂ (screenedCorrectionField τ d w)) w :=
    fun w hw => hasFDerivAt_screenedCorrection hlam hτ (by linarith [hsτ w hw])
  have huc : ContinuousOn u s := fun w hw => (hu' w hw).continuousAt.continuousWithinAt
  have hmem : ∀ v ∈ closedBall d.2 lam, v ∈ s ∧ v + (d.1 - d.2) ∈ s := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    constructor
    · rw [hs, mem_closedBall, dist_eq_norm]
      have := norm_sub_le_norm_sub_add_norm_sub v d.2 z
      rw [hz, norm_snd_sub_dipoleMidpoint] at this
      linarith
    · rw [hs, mem_closedBall, dist_eq_norm]
      have e : v + (d.1 - d.2) - z = (v - d.2) + (d.1 - z) := by ring
      rw [e]
      have := norm_add_le (v - d.2) (d.1 - z)
      rw [hz, norm_fst_sub_dipoleMidpoint] at this
      linarith
  have hshift : ∫ v, u v ∂smearedCharge χ d.1 lam =
      ∫ v, u (v + (d.1 - d.2)) ∂smearedCharge χ d.2 lam := by
    have hmap := map_add_right_smearedCharge χ d.2 (d.1 - d.2) lam
    rw [show d.2 + (d.1 - d.2) = d.1 by ring] at hmap
    rw [← hmap, (measurableEmbedding_addRight (d.1 - d.2)).integral_map]
  have hi1 : Integrable (fun v => u (v + (d.1 - d.2))) (smearedCharge χ d.2 lam) := by
    refine integrable_smearedCharge_of_continuousOn hχ hlam ?_
    refine huc.comp (continuous_id.add continuous_const).continuousOn fun v hv => (hmem v hv).2
  have hi2 : Integrable u (smearedCharge χ d.2 lam) :=
    integrable_smearedCharge_of_continuousOn hχ hlam
      (huc.mono fun v hv => (hmem v hv).1)
  rw [hshift, ← integral_sub hi1 hi2, ← Real.norm_eq_abs]
  have hbd : ∀ᵐ v ∂smearedCharge χ d.2 lam,
      ‖u (v + (d.1 - d.2)) - u v‖ ≤ 2 * ‖d.2 - d.1‖ ^ 2 / τ ^ 2 := by
    filter_upwards [ae_mem_closedBall_smearedCharge (z := d.2) hχ hlam] with v hv
    obtain ⟨h1, h2⟩ := hmem v hv
    have key :=
      (convex_closedBall z (‖d.2 - d.1‖ / 2 + lam)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := u) (C := 2 * ‖d.2 - d.1‖ / τ ^ 2)
      (fun w hw => (hu' w hw).hasFDerivWithinAt)
      (fun w hw => by
        rw [LinearIsometryEquiv.norm_map]
        exact norm_screenedCorrectionField_le hlam hτ (hsτ w hw)) h1 h2
    rw [add_sub_cancel_left, norm_sub_rev d.1 d.2] at key
    calc ‖u (v + (d.1 - d.2)) - u v‖ ≤ 2 * ‖d.2 - d.1‖ / τ ^ 2 * ‖d.2 - d.1‖ := key
      _ = 2 * ‖d.2 - d.1‖ ^ 2 / τ ^ 2 := by ring
  have := norm_integral_le_of_norm_le_const hbd
  rwa [probReal_univ, mul_one] at this

/-- The screened field is integrable on `B(z, τ)` against any field continuous on `B̄(z, τ)`. -/
theorem integrableOn_of_continuousOn_closedBall {z : ℂ} {f : ℂ → ℝ}
    (hf : ContinuousOn f (closedBall z τ)) : IntegrableOn f (ball z τ) :=
  (hf.integrableOn_compact (isCompact_closedBall z τ)).mono_set ball_subset_closedBall

/-- The screened field is continuous on `B̄(z, τ)`. -/
theorem continuousOn_screenedField_closedBall (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ContinuousOn (screenedField χ lam τ d) (closedBall (dipoleMidpoint d) τ) :=
  (continuousOn_screenedField hχ hlam hτ).mono
    (closedBall_subset_ball (by linarith [pos_of_screening hlam hτ]))

/-- **The Dirichlet energy of the screened potential** (3.26): with
`ũ = screenedCorrection τ d`,
`∫_{B(z,τ)} |∇u|² = 4π (g(λ) + κ) - 4π g_λ(x - y) + 2π (∫ ũ dδ_x^{(λ)} - ∫ ũ dδ_y^{(λ)})`. -/
theorem setIntegral_norm_sq_screenedField_eq (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ∫ w in ball (dipoleMidpoint d) τ, ‖screenedField χ lam τ d w‖ ^ 2 =
      4 * Real.pi * (logKernel (lam : ℂ) + kappa χ) -
          4 * Real.pi * smearedKernel χ lam (d.1 - d.2) +
        2 * Real.pi * ((∫ v, screenedCorrection τ d v ∂smearedCharge χ d.1 lam) -
          ∫ v, screenedCorrection τ d v ∂smearedCharge χ d.2 lam) := by
  set z := dipoleMidpoint d with hz
  set U := screenedField χ lam τ d with hU
  have hτ0 := pos_of_screening hlam hτ
  have hρ : τ < 2 * τ := by linarith
  have hW1 := integral_fderiv_apply_screenedField hχ hlam hτ hρ
    (contDiff_dipolePotential hχ hlam d).contDiffOn
  have hW2 := integral_fderiv_apply_screenedField hχ hlam hτ hρ
    (contDiffOn_screenedCorrection hlam hτ)
  have hpt : ∀ w ∈ ball z τ, ‖U w‖ ^ 2 = fderiv ℝ (dipolePotential χ lam d) w (U w) +
      fderiv ℝ (screenedCorrection τ d) w (U w) := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    rw [(hasGradientAt_dipolePotential hχ hlam d w).hasFDerivAt.fderiv,
      (hasFDerivAt_screenedCorrection hlam hτ (by linarith)).fderiv, toDual_apply_apply,
      toDual_apply_apply, ← inner_add_left, ← real_inner_self_eq_norm_sq]
    rfl
  have hUc := continuousOn_screenedField_closedBall hχ hlam hτ
  have hK2 : closedBall z τ ⊆ ball z (2 * τ) := closedBall_subset_ball hρ
  have hi1 : IntegrableOn (fun w => fderiv ℝ (dipolePotential χ lam d) w (U w)) (ball z τ) :=
    integrableOn_of_continuousOn_closedBall
      (((contDiff_dipolePotential hχ hlam d).continuous_fderiv one_ne_zero).continuousOn.clm_apply
        hUc)
  have hi2 : IntegrableOn (fun w => fderiv ℝ (screenedCorrection τ d) w (U w)) (ball z τ) :=
    integrableOn_of_continuousOn_closedBall
      ((((contDiffOn_screenedCorrection hlam hτ).continuousOn_fderiv_of_isOpen isOpen_ball
        le_rfl).mono hK2).clm_apply hUc)
  rw [setIntegral_congr_fun measurableSet_ball hpt, integral_add hi1 hi2, hW1, hW2,
    integral_dipolePotential_sub hχ hlam d]
  ring

/-- **The Dirichlet energy bound** (the proof of Lemma 3.4):
`∫_{B(z,τ)} |∇u|² ≤ 4π (g(λ) + κ) - 4π g_λ(x - y) + 4π r² / τ²`. -/
theorem setIntegral_norm_sq_screenedField_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) :
    ∫ w in ball (dipoleMidpoint d) τ, ‖screenedField χ lam τ d w‖ ^ 2 ≤
      4 * Real.pi * (logKernel (lam : ℂ) + kappa χ) -
          4 * Real.pi * smearedKernel χ lam (d.1 - d.2) +
        4 * Real.pi * (‖d.2 - d.1‖ ^ 2 / τ ^ 2) := by
  rw [setIntegral_norm_sq_screenedField_eq hχ hlam hτ]
  have h := abs_integral_screenedCorrection_sub_le hχ hlam hτ
  have h' := mul_le_mul_of_nonneg_left ((le_abs_self _).trans h)
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  have e : 2 * Real.pi * (2 * ‖d.2 - d.1‖ ^ 2 / τ ^ 2) =
      4 * Real.pi * (‖d.2 - d.1‖ ^ 2 / τ ^ 2) := by ring
  linarith

end Dipole

/-! ### The pasted field and the `L²`-projection property -/

section Configuration

variable {lam τ : ℝ} {N : ℕ}

/-- The pasted field `E = Σᵢ 1_{B(z_i,τ)} ∇u_i` (Section 3.3). -/
noncomputable def screenedTotalField (χ : ℂ → ℝ) (lam τ : ℝ) {N : ℕ} (c : Fin N → ℂ × ℂ)
    (w : ℂ) : ℂ :=
  ∑ i, (ball (dipoleMidpoint (c i)) τ).indicator (screenedField χ lam τ (c i)) w

/-- `∇u_i · ∇u_j` is integrable on `B(z_i, τ) ∩ B(z_j, τ)`. -/
theorem integrableOn_inner_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam) {d e : ℂ × ℂ}
    (hd : 8 * max ‖d.2 - d.1‖ lam ≤ τ) (he : 8 * max ‖e.2 - e.1‖ lam ≤ τ) :
    IntegrableOn (fun w => inner ℝ (screenedField χ lam τ d w) (screenedField χ lam τ e w))
      (ball (dipoleMidpoint d) τ ∩ ball (dipoleMidpoint e) τ) := by
  have hK : IsCompact (closedBall (dipoleMidpoint d) τ ∩ closedBall (dipoleMidpoint e) τ) :=
    (isCompact_closedBall _ _).inter_right isClosed_closedBall
  have hc : ContinuousOn (fun w => inner ℝ (screenedField χ lam τ d w) (screenedField χ lam τ e w))
      (closedBall (dipoleMidpoint d) τ ∩ closedBall (dipoleMidpoint e) τ) :=
    ((continuousOn_screenedField_closedBall hχ hlam hd).mono inter_subset_left).inner
      ((continuousOn_screenedField_closedBall hχ hlam he).mono inter_subset_right)
  exact (hc.integrableOn_compact hK).mono_set
    (inter_subset_inter ball_subset_closedBall ball_subset_closedBall)

/-- `|E|² = Σᵢ Σⱼ 1_{B_i ∩ B_j} ∇u_i · ∇u_j`. -/
theorem norm_sq_screenedTotalField (χ : ℂ → ℝ) (lam τ : ℝ) (c : Fin N → ℂ × ℂ) (w : ℂ) :
    ‖screenedTotalField χ lam τ c w‖ ^ 2 =
      ∑ i, ∑ j, (ball (dipoleMidpoint (c i)) τ ∩ ball (dipoleMidpoint (c j)) τ).indicator
        (fun w => inner ℝ (screenedField χ lam τ (c i) w) (screenedField χ lam τ (c j) w)) w := by
  rw [← real_inner_self_eq_norm_sq, screenedTotalField, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : w ∈ ball (dipoleMidpoint (c i)) τ <;>
    by_cases hj : w ∈ ball (dipoleMidpoint (c j)) τ <;>
    simp [indicator, hi, hj]

/-- `E · F = Σᵢ 1_{B_i} F · ∇u_i` for any field `F`. -/
theorem inner_screenedTotalField (χ : ℂ → ℝ) (lam τ : ℝ) (c : Fin N → ℂ × ℂ) (F : ℂ → ℂ)
    (w : ℂ) :
    inner ℝ (F w) (screenedTotalField χ lam τ c w) =
      ∑ i, (ball (dipoleMidpoint (c i)) τ).indicator
        (fun w => inner ℝ (F w) (screenedField χ lam τ (c i) w)) w := by
  rw [screenedTotalField, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : w ∈ ball (dipoleMidpoint (c i)) τ <;> simp [indicator, hi]

/-- `∫ |E|² = Σᵢ Σⱼ ∫_{B_i ∩ B_j} ∇u_i · ∇u_j`, and `|E|²` is integrable. -/
theorem integral_norm_sq_screenedTotalField (hχ : IsMollifier χ) (hlam : 0 < lam)
    (c : Fin N → ℂ × ℂ) (hτ : ∀ i, 8 * max ‖(c i).2 - (c i).1‖ lam ≤ τ) :
    Integrable (fun w => ‖screenedTotalField χ lam τ c w‖ ^ 2) ∧
      ∫ w, ‖screenedTotalField χ lam τ c w‖ ^ 2 =
        ∑ i, ∑ j, ∫ w in ball (dipoleMidpoint (c i)) τ ∩ ball (dipoleMidpoint (c j)) τ,
          inner ℝ (screenedField χ lam τ (c i) w) (screenedField χ lam τ (c j) w) := by
  have hint : ∀ i j, Integrable ((ball (dipoleMidpoint (c i)) τ ∩
      ball (dipoleMidpoint (c j)) τ).indicator
        (fun w => inner ℝ (screenedField χ lam τ (c i) w) (screenedField χ lam τ (c j) w))) :=
    fun i j => (integrableOn_inner_screenedField hχ hlam (hτ i) (hτ j)).integrable_indicator
      (measurableSet_ball.inter measurableSet_ball)
  simp_rw [norm_sq_screenedTotalField]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact integral_indicator (measurableSet_ball.inter measurableSet_ball)

/-- The energy identity in the form
`∫ |∇h_λ|² = 2π Σᵢ (∫ h_λ dδ_{x_i}^{(λ)} - ∫ h_λ dδ_{y_i}^{(λ)})`. -/
theorem integral_norm_sq_electricField_eq_sum (hχ : IsMollifier χ) (hlam : 0 < lam)
    (c : Fin N → ℂ × ℂ) :
    ∫ w, ‖electricField χ (dipoleCharge N) (dipoleCentre c) (fun _ => lam) w‖ ^ 2 =
      2 * Real.pi * ∑ i,
        ((∫ v, electricPotential χ (dipoleCharge N) (dipoleCentre c) (fun _ => lam) v
            ∂smearedCharge χ (c i).1 lam) -
          ∫ v, electricPotential χ (dipoleCharge N) (dipoleCentre c) (fun _ => lam) v
            ∂smearedCharge χ (c i).2 lam) := by
  rw [integral_norm_sq_electricField hχ (fun _ => hlam) (sum_dipoleCharge N)]
  have h := integral_electricPotential_smearedCharge (d := dipoleCharge N) (z := dipoleCentre c)
    (α := fun _ => lam) hχ (fun _ => hlam)
  congr 1
  have e : ∀ a, ∑ b, dipoleCharge N a * dipoleCharge N b *
      ∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
        ∂(smearedCharge χ (dipoleCentre c a) lam).prod (smearedCharge χ (dipoleCentre c b) lam) =
      dipoleCharge N a * ∫ v, electricPotential χ (dipoleCharge N) (dipoleCentre c)
        (fun _ => lam) v ∂smearedCharge χ (dipoleCentre c a) lam := by
    intro a
    rw [h a, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun a _ => e a, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [dipoleCharge, dipoleCentre, sub_eq_add_neg]

/-- **The `L²`-projection property** (the proof of Lemma 3.4):
`∫ |∇h_λ|² ≤ ∫ |E|²` for the pasted field `E = Σᵢ 1_{B(z_i,τ)} ∇u_i`. -/
theorem integral_norm_sq_electricField_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    (c : Fin N → ℂ × ℂ) (hτ : ∀ i, 8 * max ‖(c i).2 - (c i).1‖ lam ≤ τ) :
    ∫ w, ‖electricField χ (dipoleCharge N) (dipoleCentre c) (fun _ => lam) w‖ ^ 2 ≤
      ∫ w, ‖screenedTotalField χ lam τ c w‖ ^ 2 := by
  set E := electricField χ (dipoleCharge N) (dipoleCentre c) (fun _ => lam) with hE
  set h := electricPotential χ (dipoleCharge N) (dipoleCentre c) (fun _ => lam) with hh
  set Es := screenedTotalField χ lam τ c with hEs
  have hEc : Continuous E := continuous_electricField hχ fun _ => hlam
  have hhc : ContDiff ℝ 1 h := contDiff_electricPotential hχ fun _ => hlam
  -- `∫_{B_i} ∇h · ∇u_i = 2π (∫ h dδ_{x_i} - ∫ h dδ_{y_i})`
  have hW : ∀ i,
      ∫ w in ball (dipoleMidpoint (c i)) τ, inner ℝ (E w) (screenedField χ lam τ (c i) w) =
      2 * Real.pi * ((∫ v, h v ∂smearedCharge χ (c i).1 lam) -
        ∫ v, h v ∂smearedCharge χ (c i).2 lam) := by
    intro i
    have hτ0 := pos_of_screening hlam (hτ i)
    rw [← integral_fderiv_apply_screenedField hχ hlam (hτ i) (show τ < 2 * τ by linarith)
      hhc.contDiffOn]
    refine setIntegral_congr_fun measurableSet_ball fun w _ => ?_
    rw [hh, fderiv_electricPotential_apply hχ (fun _ => hlam)]
  have hiE : ∀ i, Integrable ((ball (dipoleMidpoint (c i)) τ).indicator
      (fun w => inner ℝ (E w) (screenedField χ lam τ (c i) w))) := by
    intro i
    refine (integrableOn_of_continuousOn_closedBall ?_).integrable_indicator measurableSet_ball
    exact hEc.continuousOn.inner (continuousOn_screenedField_closedBall hχ hlam (hτ i))
  have hcross : ∫ w, inner ℝ (E w) (Es w) = ∫ w, ‖E w‖ ^ 2 := by
    simp_rw [hEs, inner_screenedTotalField]
    rw [integral_finsetSum _ fun i _ => hiE i, integral_norm_sq_electricField_eq_sum hχ hlam c,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator measurableSet_ball, hW i]
  have hEsi : Integrable fun w => ‖Es w‖ ^ 2 :=
    (integral_norm_sq_screenedTotalField hχ hlam c hτ).1
  have hEi : Integrable fun w => ‖E w‖ ^ 2 :=
    integrable_norm_sq_electricField hχ (fun _ => hlam) (sum_dipoleCharge N)
  have hcrossi : Integrable fun w => inner ℝ (E w) (Es w) := by
    simp_rw [hEs, inner_screenedTotalField]
    exact integrable_finsetSum _ fun i _ => hiE i
  have hpos : 0 ≤ ∫ w, ‖Es w - E w‖ ^ 2 := integral_nonneg fun w => sq_nonneg _
  have hexp : ∫ w, ‖Es w - E w‖ ^ 2 =
      (∫ w, ‖Es w‖ ^ 2) - 2 * (∫ w, inner ℝ (E w) (Es w)) + ∫ w, ‖E w‖ ^ 2 := by
    have hpt : ∀ w, ‖Es w - E w‖ ^ 2 =
        ‖Es w‖ ^ 2 - 2 * inner ℝ (E w) (Es w) + ‖E w‖ ^ 2 := fun w => by
      rw [norm_sub_sq_real, real_inner_comm]
    have hI1 : Integrable fun w => ‖Es w‖ ^ 2 - 2 * inner ℝ (E w) (Es w) :=
      hEsi.sub (hcrossi.const_mul 2)
    have hI2 : Integrable fun w => 2 * inner ℝ (E w) (Es w) := hcrossi.const_mul 2
    simp_rw [hpt]
    rw [integral_add hI1 hEi, integral_sub hEsi hI2, integral_const_mul]
  rw [hexp, hcross] at hpos
  linarith

/-- `∫ |E|² = Σᵢ ∫_{B_i} |∇u_i|² + 2π Σᵢ Σ_{j ≠ i} ṽ_ij` (equation (3.26)). -/
theorem integral_norm_sq_screenedTotalField_eq (hχ : IsMollifier χ) (hlam : 0 < lam)
    (c : Fin N → ℂ × ℂ) (hτ : ∀ i, 8 * max ‖(c i).2 - (c i).1‖ lam ≤ τ) :
    ∫ w, ‖screenedTotalField χ lam τ c w‖ ^ 2 =
      (∑ i, ∫ w in ball (dipoleMidpoint (c i)) τ, ‖screenedField χ lam τ (c i) w‖ ^ 2) +
        2 * Real.pi * ∑ i, ∑ j ∈ Finset.univ.erase i, screenedInteraction χ lam τ (c i) (c j) := by
  rw [(integral_norm_sq_screenedTotalField hχ hlam c hτ).2, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), inter_self, Finset.mul_sum]
  congr 1
  · simp_rw [real_inner_self_eq_norm_sq]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [screenedInteraction, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- **Lemma 3.4** (equation (3.17)): for `λ > 0` and
`τ ≥ 8 max(r_i, λ)` for every `i`, with `r_i = |y_i - x_i|`,
`F_λ(X_N, Y_N) ≤ -Σᵢ g_λ(x_i - y_i) + ½ Σ_{i ≠ j} ṽ_ij + Σᵢ r_i² / τ²`,
`ṽ_ij` as in equation (3.18). The paper's error `O(Σᵢ r_i²/τ²)` holds with the constant `1`, and
its hypothesis `σ_N = Id` is not needed. -/
theorem lemma_3_4 (hχ : IsMollifier χ) (c : Fin N → ℂ × ℂ) (hlam : 0 < lam)
    (hτ : ∀ i, 8 * max ‖(c i).2 - (c i).1‖ lam ≤ τ) :
    energy χ lam c ≤ -∑ i, smearedKernel χ lam ((c i).1 - (c i).2) +
      1 / 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, screenedInteraction χ lam τ (c i) (c j) +
      ∑ i, ‖(c i).2 - (c i).1‖ ^ 2 / τ ^ 2 := by
  rw [energy_eq_integral_norm_sq_electricField hχ c hlam]
  have h1 := integral_norm_sq_electricField_le hχ hlam c hτ
  rw [integral_norm_sq_screenedTotalField_eq hχ hlam c hτ] at h1
  have h2 : ∑ i, ∫ w in ball (dipoleMidpoint (c i)) τ, ‖screenedField χ lam τ (c i) w‖ ^ 2 ≤
      ∑ i, (4 * Real.pi * (logKernel (lam : ℂ) + kappa χ) -
        4 * Real.pi * smearedKernel χ lam ((c i).1 - (c i).2) +
          4 * Real.pi * (‖(c i).2 - (c i).1‖ ^ 2 / τ ^ 2)) :=
    Finset.sum_le_sum fun i _ => setIntegral_norm_sq_screenedField_le hχ hlam (hτ i)
  have e : ∑ i : Fin N, (4 * Real.pi * (logKernel (lam : ℂ) + kappa χ) -
        4 * Real.pi * smearedKernel χ lam ((c i).1 - (c i).2) +
          4 * Real.pi * (‖(c i).2 - (c i).1‖ ^ 2 / τ ^ 2)) =
      4 * Real.pi * (N * (logKernel (lam : ℂ) + kappa χ) -
        ∑ i, smearedKernel χ lam ((c i).1 - (c i).2) +
          ∑ i, ‖(c i).2 - (c i).1‖ ^ 2 / τ ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [e] at h2
  have hpi := Real.pi_pos
  have h3 : 1 / (4 * Real.pi) * ∫ w,
      ‖electricField χ (dipoleCharge N) (dipoleCentre c) (fun _ => lam) w‖ ^ 2 ≤
      1 / (4 * Real.pi) * (4 * Real.pi * (N * (logKernel (lam : ℂ) + kappa χ) -
        ∑ i, smearedKernel χ lam ((c i).1 - (c i).2) +
          ∑ i, ‖(c i).2 - (c i).1‖ ^ 2 / τ ^ 2) +
        2 * Real.pi * ∑ i, ∑ j ∈ Finset.univ.erase i, screenedInteraction χ lam τ (c i) (c j)) :=
    mul_le_mul_of_nonneg_left (h1.trans (by linarith)) (by positivity)
  have e2 : 1 / (4 * Real.pi) * (4 * Real.pi * (N * (logKernel (lam : ℂ) + kappa χ) -
        ∑ i, smearedKernel χ lam ((c i).1 - (c i).2) +
          ∑ i, ‖(c i).2 - (c i).1‖ ^ 2 / τ ^ 2) +
        2 * Real.pi * ∑ i, ∑ j ∈ Finset.univ.erase i, screenedInteraction χ lam τ (c i) (c j)) =
      N * (logKernel (lam : ℂ) + kappa χ) - ∑ i, smearedKernel χ lam ((c i).1 - (c i).2) +
        ∑ i, ‖(c i).2 - (c i).1‖ ^ 2 / τ ^ 2 +
        1 / 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, screenedInteraction χ lam τ (c i) (c j) := by
    field_simp
    ring
  rw [e2] at h3
  linarith

/-- Lemma 3.4 with the error written as in the paper, `O(Σᵢ r_i²/τ²)`: a universal constant. -/
theorem lemma_3_4_exists (hχ : IsMollifier χ) : ∃ C > 0, ∀ (N : ℕ) (c : Fin N → ℂ × ℂ)
    (lam τ : ℝ), 0 < lam → (∀ i, 8 * max ‖(c i).2 - (c i).1‖ lam ≤ τ) →
    energy χ lam c ≤ -∑ i, smearedKernel χ lam ((c i).1 - (c i).2) +
      1 / 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, screenedInteraction χ lam τ (c i) (c j) +
      C * ∑ i, ‖(c i).2 - (c i).1‖ ^ 2 / τ ^ 2 :=
  ⟨1, one_pos, fun _ c _ _ hlam hτ => by simpa using lemma_3_4 hχ c hlam hτ⟩

/-- **Equation (3.53)**, with `τ₀ = 8 ε₀ R` (Definition 3.11): if `λ > 0`,
`λ ≤ ε₀ R` and `|x_i - y_i| ≤ ε₀ R` for every `i`, then
`F_λ(X_N, Y_N) ≤ -Σᵢ g_λ(x_i - y_i) + ½ Σ_{i≠j} ṽ_ij + (1/64) Σᵢ |x_i - y_i|² / (ε₀ R)²`.
Here `R` is any positive scale; the paper takes the truncation scale `R̄_{β,λ}`. -/
theorem eq_b2 (hχ : IsMollifier χ) (c : Fin N → ℂ × ℂ) {ε₀ R : ℝ} (hlam : 0 < lam)
    (hlamR : lam ≤ ε₀ * R) (hc : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) :
    energy χ lam c ≤ -∑ i, smearedKernel χ lam ((c i).1 - (c i).2) +
      1 / 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, upperBoundInteraction χ lam ε₀ R (c i) (c j) +
      1 / 64 * ∑ i, ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2 := by
  have hτ : ∀ i, 8 * max ‖(c i).2 - (c i).1‖ lam ≤ 8 * ε₀ * R := by
    intro i
    have h1 : ‖(c i).2 - (c i).1‖ ≤ ε₀ * R := by
      rw [norm_sub_rev]
      exact hc i
    have := max_le h1 hlamR
    linarith
  have h := lemma_3_4 hχ c hlam hτ
  have e : ∑ i, ‖(c i).2 - (c i).1‖ ^ 2 / (8 * ε₀ * R) ^ 2 =
      1 / 64 * ∑ i, ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_sub_rev]
    ring
  rw [e] at h
  exact h

/-- **Equation (3.53)** in the paper's form: for every `β > 0` there is `L > 0` depending only on `β`
(here `L = β / 64`) such that, for `λ > 0`, `λ ≤ ε₀ R` and `|x_i - y_i| ≤ ε₀ R` for every `i`,
`F_λ ≤ -Σᵢ g_λ(x_i - y_i) + ½ Σ_{i≠j} ṽ_ij + (L/β) Σᵢ |x_i - y_i|² / (ε₀ R)²`. -/
theorem exists_eq_b2 (hχ : IsMollifier χ) {β : ℝ} (hβ : 0 < β) : ∃ L > 0, ∀ (N : ℕ)
    (c : Fin N → ℂ × ℂ) (lam ε₀ R : ℝ), 0 < lam → lam ≤ ε₀ * R →
    (∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
    energy χ lam c ≤ -∑ i, smearedKernel χ lam ((c i).1 - (c i).2) +
      1 / 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, upperBoundInteraction χ lam ε₀ R (c i) (c j) +
      L / β * ∑ i, ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2 := by
  refine ⟨β / 64, by positivity, fun N c lam ε₀ R hlam hlamR hc => ?_⟩
  have e : β / 64 / β = 1 / 64 := by field_simp
  rw [e]
  exact eq_b2 hχ c hlam hlamR hc

end Configuration

/-! ### The range of `ṽ` (Lemma 3.10) -/

/-- **Lemma 3.10, support of `ṽ_ij`**: if `r_i, r_j ≤ τ/8` and
`d_ij ≥ 17τ/8`, the screening discs are disjoint and `ṽ_ij = 0`. -/
theorem screenedInteraction_eq_zero_of_dipoleDist (χ : ℂ → ℝ) (lam : ℝ) {τ : ℝ}
    {d e : ℂ × ℂ} (hd : ‖d.2 - d.1‖ ≤ τ / 8) (he : ‖e.2 - e.1‖ ≤ τ / 8)
    (h : 17 / 8 * τ ≤ dipoleDist d e) : screenedInteraction χ lam τ d e = 0 := by
  refine screenedInteraction_eq_zero_of_le χ lam τ ?_
  have h1 := dipoleDist_le_fst_fst d e
  have h2 : ‖d.1 - e.1‖ ≤ ‖dipoleMidpoint d - dipoleMidpoint e‖ + ‖d.1 - dipoleMidpoint d‖ +
      ‖e.1 - dipoleMidpoint e‖ := by
    have e1 : d.1 - e.1 = (dipoleMidpoint d - dipoleMidpoint e) + (d.1 - dipoleMidpoint d) -
        (e.1 - dipoleMidpoint e) := by ring
    have h3 := norm_add_le (dipoleMidpoint d - dipoleMidpoint e) (d.1 - dipoleMidpoint d)
    have h4 := norm_sub_le ((dipoleMidpoint d - dipoleMidpoint e) + (d.1 - dipoleMidpoint d))
      (e.1 - dipoleMidpoint e)
    rw [e1]
    linarith
  rw [norm_fst_sub_dipoleMidpoint, norm_fst_sub_dipoleMidpoint] at h2
  linarith

end MultipoleBKT

end
