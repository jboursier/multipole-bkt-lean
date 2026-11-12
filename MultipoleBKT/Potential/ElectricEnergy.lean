/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.Electric
public import MultipoleBKT.Frozen.Energy
import TwoComponentCoulomb.Potential.ElectricEnergy

/-!
# The electric energy of radial smeared charges and equation (2.57)

For an admissible mollifier `χ`, a neutral configuration (`Σᵢ dᵢ = 0`) of smeared charges
`dᵢ δ_{zᵢ}^{(αᵢ)}` with radii `αᵢ > 0`, and `h_α = electricPotential χ d z α`
(equation (3.2)), the Dirichlet energy of
`h_α` is finite and

`(1 / 2π) ∫ |∇h_α|² = Σᵢⱼ dᵢ dⱼ ∬ g(x - y) dδ_{zᵢ}^{(αᵢ)}(x) dδ_{zⱼ}^{(αⱼ)}(y)`.

The paper obtains it, and equation (2.57), by "a direct insertion into (2.5) and
integration by parts using (2.56)", without further proof. Here the integration by parts
is the Green identity `integral_fderiv_apply_electricField` applied to `ξ = φ_R h_α` with a smooth
cutoff `φ_R` (equal to `1` on `B(0, R)`, supported in `B(0, 2R)`, `|∇φ_R| ≤ K / R`), and `R → ∞`
using the decay `exists_decay_electric` (the cross term `∫ h_α ∇φ_R · ∇h_α` is `O(R⁻²)`).

* `integral_electricPotential_smearedCharge` : `∫ h_α dδ_{zᵢ}^{(αᵢ)} = Σⱼ dⱼ P_{ij}` (Fubini), with
  `P_{ij} = ∬ g(x - y) dδ_{zᵢ}^{(αᵢ)}(x) dδ_{zⱼ}^{(αⱼ)}(y)`.
* `integral_norm_sq_electricField` : **the energy identity** `∫ |∇h_α|² = 2π Σᵢⱼ dᵢ dⱼ P_{ij}`;
  `integral_norm_sq_gradient_electricPotential` states it with `gradient h_α`.
* `sum_mul_integral_logKernel_prod_nonneg` : `Σᵢⱼ dᵢ dⱼ P_{ij} ≥ 0` for a neutral configuration.
* `dipoleCharge`, `dipoleCentre` : the configuration `(x₁, …, x_N, y₁, …, y_N)` of
  `c : Fin N → ℂ × ℂ` with charges `+1` at the `xᵢ` and `-1` at the `yᵢ`.
* `energy_eq_integral_norm_sq_electricField` and `energy_eq_integral_norm_sq_gradient` :
  **Equation (2.57)**, `F_λ(X_N, Y_N) = (1 / 4π) ∫ |∇h_λ|² - N (g(λ) + κ)` for `λ > 0`, for the
  frozen energy `MultipoleBKT.energy` (equation (2.5)).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ}

/-! ### The cross term -/

/-- If `|h(x)| ≤ C / |x|` and `|E(x)| ≤ C / |x|²` for `|x| ≥ R₀`, and `φ_R` is a family of cutoffs
with `∇φ_R = 0` off the annulus `R ≤ |x| ≤ 2R` and `|∇φ_R| ≤ K / R`, then
`∫ h ∇φ_R · E → 0` as `R → ∞` (it is `O(R⁻²)`). -/
theorem tendsto_integral_mul_fderiv_cutoff {h : ℂ → ℝ} {E : ℂ → ℂ} {R₀ C : ℝ} (hR₀ : 0 < R₀)
    (hC : 0 ≤ C) (hdec : ∀ x : ℂ, R₀ ≤ ‖x‖ → |h x| ≤ C / ‖x‖ ∧ ‖E x‖ ≤ C / ‖x‖ ^ 2) {K : ℝ}
    (hK : 0 ≤ K) {φ : ℝ → ℂ → ℝ} (hφ : ∀ R : ℝ, 0 < R →
      (∀ x, ‖x‖ < R → fderiv ℝ (φ R) x = 0) ∧ (∀ x, 2 * R < ‖x‖ → fderiv ℝ (φ R) x = 0) ∧
      (∀ x v, |fderiv ℝ (φ R) x v| ≤ K / R * ‖v‖)) :
    Tendsto (fun R : ℝ => ∫ x, h x * fderiv ℝ (φ R) x (E x)) atTop (𝓝 0) := by
  have hbound : ∀ᶠ R : ℝ in atTop,
      ‖∫ x, h x * fderiv ℝ (φ R) x (E x)‖ ≤ 9 * Real.pi * (K * C ^ 2) / R ^ 2 := by
    filter_upwards [eventually_ge_atTop R₀] with R hR
    have hR0 : 0 < R := lt_of_lt_of_le hR₀ hR
    obtain ⟨h5, h6, h7⟩ := hφ R hR0
    set M : ℝ := K * C ^ 2 / R ^ 4 with hM
    have hM0 : 0 ≤ M := by positivity
    have hpt : ∀ x, ‖h x * fderiv ℝ (φ R) x (E x)‖ ≤
        (ball (0 : ℂ) (3 * R)).indicator (fun _ => M) x := by
      intro x
      have hind : 0 ≤ (ball (0 : ℂ) (3 * R)).indicator (fun _ => M) x :=
        Set.indicator_nonneg (fun _ _ => hM0) x
      by_cases hx1 : ‖x‖ < R
      · rw [h5 x hx1]
        simpa using hind
      by_cases hx2 : 2 * R < ‖x‖
      · rw [h6 x hx2]
        simpa using hind
      rw [not_lt] at hx1 hx2
      have hxball : x ∈ ball (0 : ℂ) (3 * R) := by
        rw [mem_ball_zero_iff]
        linarith
      rw [Set.indicator_of_mem hxball]
      obtain ⟨hp, hf⟩ := hdec x (hR.trans hx1)
      have hp' : |h x| ≤ C / R := hp.trans (div_le_div_of_nonneg_left hC hR0 hx1)
      have hf' : ‖E x‖ ≤ C / R ^ 2 :=
        hf.trans (div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ hR0.le hx1 2))
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |h x| * |fderiv ℝ (φ R) x (E x)| ≤ (C / R) * (K / R * (C / R ^ 2)) := by
            refine mul_le_mul hp' ((h7 x _).trans ?_) (abs_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left hf' (by positivity)
        _ = M := by
            rw [hM]
            field_simp
    have hint : Integrable ((ball (0 : ℂ) (3 * R)).indicator (fun _ => M)) :=
      (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
    calc ‖∫ x, h x * fderiv ℝ (φ R) x (E x)‖
        ≤ ∫ x, (ball (0 : ℂ) (3 * R)).indicator (fun _ => M) x :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
      _ = Real.pi * (3 * R) ^ 2 * M := by
          rw [integral_indicator_const M measurableSet_ball,
            volume_real_ball_complex 0 (by positivity), smul_eq_mul]
      _ = 9 * Real.pi * (K * C ^ 2) / R ^ 2 := by
          rw [hM]
          field_simp
          ring
  have hlim : Tendsto (fun R : ℝ => 9 * Real.pi * (K * C ^ 2) / R ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  exact squeeze_zero_norm' hbound hlim

section Energy

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-! ### The Green identity with a cutoff -/

/-- The mean of the electric potential over the `i`-th charge (Fubini):
`∫ h_α dδ_{zᵢ}^{(αᵢ)} = Σⱼ dⱼ ∬ g(x - y) dδ_{zᵢ}^{(αᵢ)}(x) dδ_{zⱼ}^{(αⱼ)}(y)`. -/
theorem integral_electricPotential_smearedCharge (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i)
    (i : ι) :
    ∫ y, electricPotential χ d z α y ∂smearedCharge χ (z i) (α i) =
      ∑ j, d j * ∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
        ∂(smearedCharge χ (z i) (α i)).prod (smearedCharge χ (z j) (α j)) := by
  unfold electricPotential
  have hint : ∀ j, Integrable
      (fun y : ℂ => d j * ∫ w, logKernel (y - w) ∂smearedCharge χ (z j) (α j))
      (smearedCharge χ (z i) (α i)) := fun j =>
    (integrable_smearedCharge_of_continuous hχ
      (continuous_integral_logKernel_sub_smearedCharge hχ (z j) (hα j)) _ _).const_mul (d j)
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := isFiniteMeasure_smearedCharge hχ (z j) (α j)
  rw [integral_const_mul, integral_prod _
    (integrable_logKernel_prod_smearedCharge hχ (z i) (z j) (α i) (α j))]

/-- **The Green identity for `ξ = φ h_α`**: if `φ` is a `C¹` compactly supported function equal to
`1` on a ball `B̄(0, R)` containing all the discs, then
`∫ φ |∇h_α|² + ∫ h_α ∇φ · ∇h_α = 2π Σᵢⱼ dᵢ dⱼ P_{ij}`. -/
theorem integral_cutoff_identity (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) {R : ℝ} (hφ1 : ∀ x, ‖x‖ ≤ R → φ x = 1)
    (hR : ∀ i, ‖z i‖ + α i ≤ R) :
    (∫ x, φ x * ‖electricField χ d z α x‖ ^ 2) +
        ∫ x, electricPotential χ d z α x * fderiv ℝ φ x (electricField χ d z α x) =
      2 * Real.pi * ∑ i, ∑ j, d i * d j * ∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
        ∂(smearedCharge χ (z i) (α i)).prod (smearedCharge χ (z j) (α j)) := by
  set h := electricPotential χ d z α with hh
  set E := electricField χ d z α with hE
  have hhc : ContDiff ℝ 1 h := contDiff_electricPotential hχ hα
  have hξ : ContDiff ℝ 1 (fun x => φ x * h x) := hφ.mul hhc
  have hcξ : HasCompactSupport (fun x => φ x * h x) := hφc.mul_right
  have G := integral_fderiv_apply_electricField (d := d) (z := z) hχ hξ hcξ hα
  have hpt : ∀ x, fderiv ℝ (fun y => φ y * h y) x (E x) =
      φ x * ‖E x‖ ^ 2 + h x * fderiv ℝ φ x (E x) := fun x => by
    rw [fderiv_fun_mul (hφ.differentiable one_ne_zero x) (hhc.differentiable one_ne_zero x)]
    simp [hh, hE, fderiv_electricPotential_apply hχ hα]
  have hI1 : Integrable (fun x => φ x * ‖E x‖ ^ 2) :=
    Continuous.integrable_of_hasCompactSupport
      (hφ.continuous.mul ((continuous_electricField hχ hα).norm.pow 2)) hφc.mul_right
  have hI : Integrable (fun x => fderiv ℝ (fun y => φ y * h y) x (E x)) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((hξ.continuous_fderiv one_ne_zero).clm_apply (continuous_electricField hχ hα)) ?_
    refine (hcξ.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ ?_
    intro h0
    exact hx (by simp [h0])
  have hI2 : Integrable (fun x => h x * fderiv ℝ φ x (E x)) := by
    refine (hI.sub hI1).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, hpt]
    ring
  rw [← hE] at G
  simp_rw [hpt] at G
  rw [← integral_add hI1 hI2, G]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hae : ∀ᵐ x ∂smearedCharge χ (z i) (α i), φ x * h x = h x := by
    filter_upwards [ae_mem_closedBall_smearedCharge (z := z i) hχ (hα i)] with x hx
    have hx' : ‖x‖ ≤ R := by
      have h1 : ‖x - z i‖ ≤ α i := by simpa [dist_eq_norm] using hx
      have h2 : ‖x‖ ≤ ‖x - z i‖ + ‖z i‖ := by
        simpa using norm_add_le (x - z i) (z i)
      linarith [hR i]
    rw [hφ1 x hx', one_mul]
  rw [integral_congr_ae hae, integral_electricPotential_smearedCharge hχ hα i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The energy identity -/

/-- **The energy identity** (equation (2.57) and Section 3.1): for a neutral
configuration (`Σᵢ dᵢ = 0`) of smeared charges with radii `αᵢ > 0`,
`∫ |∇h_α|² = 2π Σᵢⱼ dᵢ dⱼ ∬ g(x - y) dδ_{zᵢ}^{(αᵢ)}(x) dδ_{zⱼ}^{(αⱼ)}(y)`. -/
theorem integral_norm_sq_electricField (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i)
    (hn : ∑ i, d i = 0) :
    ∫ x, ‖electricField χ d z α x‖ ^ 2 =
      2 * Real.pi * ∑ i, ∑ j, d i * d j * ∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
        ∂(smearedCharge χ (z i) (α i)).prod (smearedCharge χ (z j) (α j)) := by
  obtain ⟨R₀, C, hR₀, hC, hdec⟩ := exists_decay_electric (d := d) (z := z) hχ hα hn
  obtain ⟨K, φ, hK, hφ⟩ := TwoComponentCoulomb.exists_cutoff_family
  have hid : ∀ᶠ R : ℝ in atTop, (∫ x, φ R x * ‖electricField χ d z α x‖ ^ 2) +
      ∫ x, electricPotential χ d z α x * fderiv ℝ (φ R) x (electricField χ d z α x) =
        2 * Real.pi * ∑ i, ∑ j, d i * d j * ∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
          ∂(smearedCharge χ (z i) (α i)).prod (smearedCharge χ (z j) (α j)) := by
    filter_upwards [eventually_ge_atTop (max R₀ (∑ i, (‖z i‖ + α i)))] with R hR
    have hR0 : 0 < R := lt_of_lt_of_le hR₀ ((le_max_left _ _).trans hR)
    obtain ⟨h1, h2, -, h4, -, -, -⟩ := hφ R hR0
    refine integral_cutoff_identity hχ hα h1 h2 h4 fun i => ?_
    exact (Finset.single_le_sum (f := fun j => ‖z j‖ + α j)
      (fun j _ => add_nonneg (norm_nonneg _) (hα j).le) (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans hR)
  have hA : Tendsto (fun R : ℝ => ∫ x, φ R x * ‖electricField χ d z α x‖ ^ 2) atTop
      (𝓝 (∫ x, ‖electricField χ d z α x‖ ^ 2)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖electricField χ d z α x‖ ^ 2) ?_ ?_
      (integrable_norm_sq_electricField hχ hα hn) ?_
    · filter_upwards [eventually_gt_atTop 0] with R hR
      exact ((hφ R hR).1.continuous.mul
        ((continuous_electricField hχ hα).norm.pow 2)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with R hR
      refine Eventually.of_forall fun x => ?_
      obtain ⟨-, -, h3, -⟩ := hφ R hR
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h3 x).1 (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (h3 x).2
    · refine Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (max ‖x‖ 1)] with R hR
      have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR)
      obtain ⟨-, -, -, h4, -⟩ := hφ R hR0
      rw [h4 x ((le_max_left _ _).trans hR), one_mul]
  have hB := tendsto_integral_mul_fderiv_cutoff hR₀ hC hdec hK
    (fun R hR => ⟨(hφ R hR).2.2.2.2.1, (hφ R hR).2.2.2.2.2.1, (hφ R hR).2.2.2.2.2.2⟩)
  have hsum := hA.add hB
  rw [add_zero] at hsum
  exact tendsto_nhds_unique hsum (tendsto_const_nhds.congr' (hid.mono fun R hR => hR.symm))

/-- The energy identity with `∇h_α` written as `gradient h_α`. -/
theorem integral_norm_sq_gradient_electricPotential (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i)
    (hn : ∑ i, d i = 0) :
    ∫ x, ‖gradient (electricPotential χ d z α) x‖ ^ 2 =
      2 * Real.pi * ∑ i, ∑ j, d i * d j * ∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
        ∂(smearedCharge χ (z i) (α i)).prod (smearedCharge χ (z j) (α j)) := by
  simp_rw [gradient_electricPotential hχ hα]
  exact integral_norm_sq_electricField hχ hα hn

/-- **Positivity of the energy of a neutral configuration**:
`Σᵢⱼ dᵢ dⱼ ∬ g(x - y) dδ_{zᵢ}^{(αᵢ)}(x) dδ_{zⱼ}^{(αⱼ)}(y) ≥ 0` when `Σᵢ dᵢ = 0`. -/
theorem sum_mul_integral_logKernel_prod_nonneg (hχ : IsMollifier χ) (hα : ∀ i, 0 < α i)
    (hn : ∑ i, d i = 0) :
    0 ≤ ∑ i, ∑ j, d i * d j * ∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
        ∂(smearedCharge χ (z i) (α i)).prod (smearedCharge χ (z j) (α j)) := by
  have h := integral_norm_sq_electricField (d := d) (z := z) hχ hα hn
  have h0 : 0 ≤ ∫ x, ‖electricField χ d z α x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [h] at h0
  exact nonneg_of_mul_nonneg_right h0 (by positivity)

end Energy

/-! ### The electric formulation of the energy -/

/-- The charges of a dipole configuration (Section 3.1): `+1` at the `xᵢ` (left summand)
and `-1` at the `yᵢ` (right summand). -/
def dipoleCharge (N : ℕ) : Fin N ⊕ Fin N → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => -1)

/-- The centres of the dipole configuration `c : Fin N → ℂ × ℂ`, `c i = (xᵢ, yᵢ)`: `xᵢ` (left
summand) and `yᵢ` (right summand), i.e. `z₁, …, z_{2N} = x₁, …, x_N, y₁, …, y_N`
(Section 3.1). -/
def dipoleCentre {N : ℕ} (c : Fin N → ℂ × ℂ) : Fin N ⊕ Fin N → ℂ :=
  Sum.elim (fun i => (c i).1) (fun i => (c i).2)

/-- A dipole configuration is neutral. -/
theorem sum_dipoleCharge (N : ℕ) : ∑ a, dipoleCharge N a = 0 := by
  simp [dipoleCharge, Fintype.sum_sum_type]

/-- **The energy as an electric energy** (equation (2.57)): for `λ > 0`,
`F_λ(X_N, Y_N) = (1 / 4π) ∫ |∇h_λ|² - N (g(λ) + κ)`, where
`h_λ = g * (Σᵢ δ_{xᵢ}^{(λ)} - δ_{yᵢ}^{(λ)})` (equation (2.55)) and `∇h_λ` is its field. -/
theorem energy_eq_integral_norm_sq_electricField (hχ : IsMollifier χ) {N : ℕ}
    (c : Fin N → ℂ × ℂ) {lam : ℝ} (hlam : 0 < lam) :
    energy χ lam c = 1 / (4 * Real.pi) *
        (∫ x, ‖electricField χ (dipoleCharge N) (dipoleCentre c) (fun _ => lam) x‖ ^ 2) -
      N * (logKernel lam + kappa χ) := by
  have h := integral_norm_sq_electricField (d := dipoleCharge N) (z := dipoleCentre c)
    (α := fun _ => lam) hχ (fun _ => hlam) (sum_dipoleCharge N)
  rw [h]
  simp only [energy, Fintype.sum_sum_type, dipoleCharge, dipoleCentre, Sum.elim_inl,
    Sum.elim_inr, one_mul, mul_one, neg_mul, neg_neg, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- Equation (2.57) with `∇h_λ` written as `gradient h_λ`. -/
theorem energy_eq_integral_norm_sq_gradient (hχ : IsMollifier χ) {N : ℕ} (c : Fin N → ℂ × ℂ)
    {lam : ℝ} (hlam : 0 < lam) :
    energy χ lam c = 1 / (4 * Real.pi) *
        (∫ x, ‖gradient (electricPotential χ (dipoleCharge N) (dipoleCentre c) (fun _ => lam)) x‖
          ^ 2) -
      N * (logKernel lam + kappa χ) := by
  simp_rw [gradient_electricPotential hχ (fun _ => hlam)]
  exact energy_eq_integral_norm_sq_electricField hχ c hlam

end MultipoleBKT

end
