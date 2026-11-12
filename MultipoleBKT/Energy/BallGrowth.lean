/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.ElectricEnergy
public import MultipoleBKT.Potential.RouteLocal.UnitScale
public import MultipoleBKT.Frozen.StableMatching

/-!
# Proposition 3.3: the ball-growth lower bound on the energy

Proposition 3.3 of the paper (equations (3.6)–(3.9)) and its proof. Here `χ` is an
admissible mollifier, `g = logKernel`, `g_λ = smearedKernel χ λ`, `κ = kappa χ`,
`δ_z^{(λ)} = smearedCharge χ z λ`, the configuration is `c : Fin N → ℂ × ℂ` with
`c i = (x_i, y_i)`, and `g * δ₀^{(α)} * δ₀^{(η)} = twoRadiusKernel χ α η`.

**Statement.** Let `λ > 0`, radii `τ_i^±` with `τ_i^± ≥ λ`, and a split `[N] = I₁ ⊔ I₂` with
`|x_i - y_i| ≤ 2(τ_i^+ + τ_i^-)` and `τ_i^+ = τ_i^-` for `i ∈ I₁` (3.7), and
`|x_i - y_i| ≥ 2(τ_i^+ + τ_i^-)` for `i ∈ I₂` (3.8). Then, with `v'_ij` as in (3.6),

`F_λ ≥ -Σ_{I₁} g_λ(x_i - y_i) - ½ Σ_{I₂} (g(τ_i^+) + g(τ_i^-) + 2κ) + ½ Σ_{i ≠ j} v'_ij
  - C Σ_{I₁} (|x_i - y_i| / τ_i^+)²`

with `C = 3π M`, `M ≥ max(sup χ, 1)` (so `C` depends only on `χ`).

**Proof** (the paper's). Write `T^ρ_ij` for the `(i, j)` term of the bilinear expansion of the
energy of the charges `δ_{x_i}^{(ρ_i^+)} - δ_{y_i}^{(ρ_i^-)}`.

1. `F_λ = ½ Σ_ij T^λ_ij - N (g(λ) + κ)` (definition (2.5), translation invariance:
   `energy_eq_sum_smearedKernel`, public in `MultipoleBKT.Gibbs.Basic`).
2. `Σ_ij T^τ_ij ≥ 0`: the Dirichlet energy of `h_τ` is nonnegative (energy identity of
   `MultipoleBKT.Potential.ElectricEnergy`, `sum_twoRadiusKernel_nonneg`).
3. `T^λ_ij - T^τ_ij = v'_ij` for all `i, j` (the kernels are even,
   `sub_eq_ballGrowthInteraction`). Hence
   `F_λ ≥ ½ Σ_{i ≠ j} v'_ij + Σ_i (½ v'_ii - g(λ) - κ)`.
4. Diagonal terms. For `i ∈ I₂`, Newton's theorem for the disjoint enlarged balls and for `g_λ`
   gives `½ v'_ii - g(λ) - κ = -½ (g(τ_i^+) + g(τ_i^-) + 2κ)` (equation (3.15),
   `ballGrowthInteraction_self_of_le`). For `i ∈ I₁` (`τ_i^+ = τ_i^- = τ`),
   `½ v'_ii - g(λ) - κ = -g_λ(x_i - y_i) - ½ (2 K(0) - K(w) - K(-w))`.
   Scale this neutral self-interaction to radius one (3.13), then split it into
   two translated averages (3.14). Apply the singly smoothed Taylor bound
   inside each average. The averaged gradient vanishes by oddness of the field
   and evenness of the charge. This gives `2 K(0) - K(w) - K(-w) ≤ 6πM |w|² / τ²`
   (`RouteLocal.neutral_self_le_sq`, used by `ballGrowthInteraction_self_of_eq`).

Main results:

* `ballGrowthInteraction`: `v'_ij` of equation (3.6).
* `smearedKernel_sub_twoRadiusKernel_eq_zero` : each term of `v'_ij` vanishes when the
  corresponding enlarged balls are disjoint.
* `prop_3_3`: **Proposition 3.3**, equation (3.9), with the paper's hypotheses (including
  `σ_N = Id`, which the proof does not use). `energy_ge_ballGrowth` is the same bound without the
  matching hypothesis and with only the hypotheses the proof uses.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- The interaction `v'_ij` of equation (3.6): with `c i = (x_i, y_i)` and
`K_{α,η} = g * δ₀^{(α)} * δ₀^{(η)} = twoRadiusKernel χ α η`,
`v'_ij = (g_λ - K_{τ_i^+, τ_j^+})(x_i - x_j) + (g_λ - K_{τ_i^-, τ_j^-})(y_i - y_j)
  - (g_λ - K_{τ_i^-, τ_j^+})(y_i - x_j) - (g_λ - K_{τ_i^+, τ_j^-})(x_i - y_j)`.
The paper uses it for `i ≠ j`; the formula is the same for `i = j`. -/
noncomputable def ballGrowthInteraction (χ : ℂ → ℝ) {N : ℕ} (lam : ℝ) (τp τm : Fin N → ℝ)
    (c : Fin N → ℂ × ℂ) (i j : Fin N) : ℝ :=
  (smearedKernel χ lam ((c i).1 - (c j).1) -
      twoRadiusKernel χ (τp i) (τp j) ((c i).1 - (c j).1)) +
    (smearedKernel χ lam ((c i).2 - (c j).2) -
      twoRadiusKernel χ (τm i) (τm j) ((c i).2 - (c j).2)) -
    (smearedKernel χ lam ((c i).2 - (c j).1) -
      twoRadiusKernel χ (τm i) (τp j) ((c i).2 - (c j).1)) -
    (smearedKernel χ lam ((c i).1 - (c j).2) -
      twoRadiusKernel χ (τp i) (τm j) ((c i).1 - (c j).2))

/-- The "crucial point" after Proposition 3.3: if `λ ≤ α`, `λ ≤ η` and the
enlarged balls `B(a, α)`, `B(b, η)` are disjoint (`|a - b| ≥ α + η`), then
`(g_λ - g * δ₀^{(α)} * δ₀^{(η)})(a - b) = 0` (Newton's theorem). -/
theorem smearedKernel_sub_twoRadiusKernel_eq_zero (hχ : IsMollifier χ) (hlam : 0 < lam)
    {α η : ℝ} (hα : lam ≤ α) (hη : lam ≤ η) {z : ℂ} (hz : α + η ≤ ‖z‖) :
    smearedKernel χ lam z - twoRadiusKernel χ α η z = 0 := by
  rw [smearedKernel_eq_logKernel hχ hlam (by linarith),
    twoRadiusKernel_eq_logKernel hχ (by linarith) (by linarith) hz, sub_self]

/-! ### Step 1: the energy in terms of `g_λ` -/

/-- The energy (equation (2.5)) written with `g_λ`: the pair interaction of `δ_a^{(λ)}` and
`δ_b^{(λ)}` is `g_λ(b - a)`. Private: the same statement is public as
`MultipoleBKT.energy_eq_sum_smearedKernel` in `MultipoleBKT.Gibbs.Basic`, which this module does
not import. -/
private theorem energy_eq_sum_smearedKernel_aux (χ : ℂ → ℝ) {N : ℕ} (lam : ℝ) (c : Fin N → ℂ × ℂ) :
    energy χ lam c = (1 / 2) * ∑ i, ∑ j,
        (smearedKernel χ lam ((c j).1 - (c i).1) - smearedKernel χ lam ((c j).2 - (c i).1) -
          smearedKernel χ lam ((c j).1 - (c i).2) + smearedKernel χ lam ((c j).2 - (c i).2)) -
      N * (logKernel lam + kappa χ) := by
  simp only [energy, integral_logKernel_prod_smearedCharge_eq_twoRadiusKernel,
    twoRadiusKernel_self]

/-! ### Step 2: positivity of the energy with enlarged radii -/

/-- The energy of the configuration with enlarged radii is nonnegative (the proof of Proposition 3.3:
`∫ |∇h_τ|² ≥ 0`): `Σ_ij T^τ_ij ≥ 0`. -/
theorem sum_twoRadiusKernel_nonneg (hχ : IsMollifier χ) {N : ℕ} (c : Fin N → ℂ × ℂ)
    {τp τm : Fin N → ℝ} (hp : ∀ i, 0 < τp i) (hm : ∀ i, 0 < τm i) :
    0 ≤ ∑ i, ∑ j,
      (twoRadiusKernel χ (τp i) (τp j) ((c j).1 - (c i).1) -
        twoRadiusKernel χ (τp i) (τm j) ((c j).2 - (c i).1) -
        twoRadiusKernel χ (τm i) (τp j) ((c j).1 - (c i).2) +
        twoRadiusKernel χ (τm i) (τm j) ((c j).2 - (c i).2)) := by
  have hα : ∀ a, 0 < Sum.elim τp τm a := fun a => by
    rcases a with i | i
    · exact hp i
    · exact hm i
  have h := sum_mul_integral_logKernel_prod_nonneg (d := dipoleCharge N) (z := dipoleCentre c)
    hχ hα (sum_dipoleCharge N)
  simp only [Fintype.sum_sum_type, dipoleCharge, dipoleCentre, Sum.elim_inl, Sum.elim_inr,
    integral_logKernel_prod_smearedCharge_eq_twoRadiusKernel, one_mul, neg_mul, neg_neg,
    Finset.sum_neg_distrib, Finset.sum_add_distrib] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith

/-! ### Step 3: the resummation over dipole indices -/

/-- `T^λ_ij - T^τ_ij = v'_ij` (the proof of Proposition 3.3), using that `g_λ` and the two-radius
kernels are even. -/
theorem sub_eq_ballGrowthInteraction (hχ : IsMollifier χ) {N : ℕ} (lam : ℝ)
    (τp τm : Fin N → ℝ) (c : Fin N → ℂ × ℂ) (i j : Fin N) :
    (smearedKernel χ lam ((c j).1 - (c i).1) - smearedKernel χ lam ((c j).2 - (c i).1) -
          smearedKernel χ lam ((c j).1 - (c i).2) + smearedKernel χ lam ((c j).2 - (c i).2)) -
        (twoRadiusKernel χ (τp i) (τp j) ((c j).1 - (c i).1) -
          twoRadiusKernel χ (τp i) (τm j) ((c j).2 - (c i).1) -
          twoRadiusKernel χ (τm i) (τp j) ((c j).1 - (c i).2) +
          twoRadiusKernel χ (τm i) (τm j) ((c j).2 - (c i).2)) =
      ballGrowthInteraction χ lam τp τm c i j := by
  have eg : ∀ a b : ℂ, smearedKernel χ lam (a - b) = smearedKernel χ lam (b - a) := fun a b => by
    rw [← neg_sub b a, smearedKernel_neg hχ]
  have eK : ∀ (α η : ℝ) (a b : ℂ), twoRadiusKernel χ α η (a - b) = twoRadiusKernel χ α η (b - a) :=
    fun α η a b => by rw [← neg_sub b a, twoRadiusKernel_neg hχ]
  rw [ballGrowthInteraction, eg (c i).1 (c j).1, eg (c i).2 (c j).2, eg (c i).2 (c j).1,
    eg (c i).1 (c j).2, eK _ _ (c i).1 (c j).1, eK _ _ (c i).2 (c j).2, eK _ _ (c i).2 (c j).1,
    eK _ _ (c i).1 (c j).2]
  ring

/-! ### Step 4: the diagonal terms -/

/-- The diagonal term for `i ∈ I₂` (equation (3.15)): if
`λ ≤ τ_i^±` and `|x_i - y_i| ≥ 2(τ_i^+ + τ_i^-)`, then
`½ v'_ii - (g(λ) + κ) = -½ (g(τ_i^+) + g(τ_i^-) + 2κ)`. -/
theorem ballGrowthInteraction_self_of_le (hχ : IsMollifier χ) (hlam : 0 < lam) {N : ℕ}
    {τp τm : Fin N → ℝ} (c : Fin N → ℂ × ℂ) {i : Fin N} (hp : lam ≤ τp i) (hm : lam ≤ τm i)
    (h : 2 * (τp i + τm i) ≤ ‖(c i).1 - (c i).2‖) :
    (1 / 2) * ballGrowthInteraction χ lam τp τm c i i - (logKernel lam + kappa χ) =
      -(1 / 2) * (logKernel (τp i) + logKernel (τm i) + 2 * kappa χ) := by
  have hp0 : 0 < τp i := hlam.trans_le hp
  have hm0 : 0 < τm i := hlam.trans_le hm
  have hw : τp i + τm i ≤ ‖(c i).1 - (c i).2‖ := by linarith
  have hw' : τm i + τp i ≤ ‖(c i).2 - (c i).1‖ := by rw [norm_sub_rev]; linarith
  have hl : 2 * lam ≤ ‖(c i).1 - (c i).2‖ := by linarith
  have hl' : 2 * lam ≤ ‖(c i).2 - (c i).1‖ := by rw [norm_sub_rev]; exact hl
  have hneg : logKernel ((c i).2 - (c i).1) = logKernel ((c i).1 - (c i).2) := by
    rw [← neg_sub, logKernel_neg]
  rw [ballGrowthInteraction, sub_self, sub_self, twoRadiusKernel_self, twoRadiusKernel_self,
    smearedKernel_zero hχ hlam, smearedKernel_zero hχ hp0, smearedKernel_zero hχ hm0,
    twoRadiusKernel_eq_logKernel hχ hm0 hp0 hw', twoRadiusKernel_eq_logKernel hχ hp0 hm0 hw,
    smearedKernel_eq_logKernel hχ hlam hl, smearedKernel_eq_logKernel hχ hlam hl', hneg]
  ring

/-- The diagonal term for `i ∈ I₁` (equation (3.12)): if
`τ_i^+ = τ_i^- > 0` and `χ ≤ M`, then
`½ v'_ii - (g(λ) + κ) ≥ -g_λ(x_i - y_i) - 3πM (|x_i - y_i| / τ_i^+)²`. -/
theorem ballGrowthInteraction_self_of_eq (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {N : ℕ} {τp τm : Fin N → ℝ} (c : Fin N → ℂ × ℂ) {i : Fin N}
    (hp : 0 < τp i) (heq : τp i = τm i) :
    -smearedKernel χ lam ((c i).1 - (c i).2) -
        3 * (Real.pi * M) * (‖(c i).1 - (c i).2‖ / τp i) ^ 2 ≤
      (1 / 2) * ballGrowthInteraction χ lam τp τm c i i - (logKernel lam + kappa χ) := by
  set w := (c i).1 - (c i).2 with hw
  have hyx : (c i).2 - (c i).1 = -w := (neg_sub _ _).symm
  have hT := RouteLocal.neutral_self_le_sq hχ hM hp w
  rw [ballGrowthInteraction, ← heq, sub_self, sub_self, hyx, smearedKernel_neg hχ,
    smearedKernel_zero hχ hlam]
  linarith

/-! ### Proposition 3.3 -/

/-- **Proposition 3.3** (equation (3.9)) with only the hypotheses its proof uses: for `λ > 0`,
radii `τ_i^± ≥ λ`, and a split `[N] = I₁ ⊔ I₂` with `τ_i^+ = τ_i^-` on `I₁` and
`|x_i - y_i| ≥ 2(τ_i^+ + τ_i^-)` on `I₂`, the energy is bounded below by
`-Σ_{I₁} g_λ(x_i - y_i) - ½ Σ_{I₂} (g(τ_i^+) + g(τ_i^-) + 2κ) + ½ Σ_{i ≠ j} v'_ij
  - 3πM Σ_{I₁} (|x_i - y_i| / τ_i^+)²`, for any bound `M` of `χ`. -/
theorem energy_ge_ballGrowth (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) {N : ℕ}
    (hlam : 0 < lam) (c : Fin N → ℂ × ℂ) {τp τm : Fin N → ℝ} (hp : ∀ i, lam ≤ τp i)
    (hm : ∀ i, lam ≤ τm i) {I₁ I₂ : Finset (Fin N)} (hdisj : Disjoint I₁ I₂)
    (hunion : I₁ ∪ I₂ = Finset.univ) (hI₁ : ∀ i ∈ I₁, τp i = τm i)
    (hI₂ : ∀ i ∈ I₂, 2 * (τp i + τm i) ≤ ‖(c i).1 - (c i).2‖) :
    -(∑ i ∈ I₁, smearedKernel χ lam ((c i).1 - (c i).2)) -
        (1 / 2) * ∑ i ∈ I₂, (logKernel (τp i) + logKernel (τm i) + 2 * kappa χ) +
        (1 / 2) * ∑ i, ∑ j with i ≠ j, ballGrowthInteraction χ lam τp τm c i j -
        3 * (Real.pi * M) * ∑ i ∈ I₁, (‖(c i).1 - (c i).2‖ / τp i) ^ 2 ≤
      energy χ lam c := by
  set v := ballGrowthInteraction χ lam τp τm c with hv
  set e : ℝ := logKernel lam + kappa χ with he
  -- the diagonal terms
  set f : Fin N → ℝ := fun i => (1 / 2) * v i i - e with hf
  -- Steps 1--3
  have h1 : energy χ lam c ≥ (1 / 2) * ∑ i, ∑ j, v i j - N * e := by
    have hpos := sum_twoRadiusKernel_nonneg hχ c (fun i => hlam.trans_le (hp i))
      (fun i => hlam.trans_le (hm i))
    have hsum : ∑ i, ∑ j, v i j =
        (∑ i, ∑ j, (smearedKernel χ lam ((c j).1 - (c i).1) -
          smearedKernel χ lam ((c j).2 - (c i).1) - smearedKernel χ lam ((c j).1 - (c i).2) +
          smearedKernel χ lam ((c j).2 - (c i).2))) -
        ∑ i, ∑ j, (twoRadiusKernel χ (τp i) (τp j) ((c j).1 - (c i).1) -
          twoRadiusKernel χ (τp i) (τm j) ((c j).2 - (c i).1) -
          twoRadiusKernel χ (τm i) (τp j) ((c j).1 - (c i).2) +
          twoRadiusKernel χ (τm i) (τm j) ((c j).2 - (c i).2)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => (sub_eq_ballGrowthInteraction hχ lam τp τm c i j).symm
    rw [energy_eq_sum_smearedKernel_aux, hsum]
    linarith
  -- splitting off the diagonal
  have h2 : (1 / 2) * ∑ i, ∑ j, v i j - N * e =
      (1 / 2) * ∑ i, ∑ j with i ≠ j, v i j + ∑ i, f i := by
    have hdiag : ∀ i, ∑ j, v i j = v i i + ∑ j with i ≠ j, v i j := fun i => by
      rw [Finset.filter_ne, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hN : ∑ _i : Fin N, e = N * e := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [hdiag, Finset.sum_add_distrib, hf, Finset.sum_sub_distrib, hN, ← Finset.mul_sum]
    ring
  -- Step 4: the diagonal terms on `I₁` and `I₂`
  have h3 : ∑ i, f i = ∑ i ∈ I₁, f i + ∑ i ∈ I₂, f i := by
    rw [← Finset.sum_union hdisj, hunion]
  have h4 : ∑ i ∈ I₁, (-smearedKernel χ lam ((c i).1 - (c i).2) -
      3 * (Real.pi * M) * (‖(c i).1 - (c i).2‖ / τp i) ^ 2) ≤ ∑ i ∈ I₁, f i :=
    Finset.sum_le_sum fun i hi =>
      ballGrowthInteraction_self_of_eq hχ hM hlam c (hlam.trans_le (hp i)) (hI₁ i hi)
  have h5 : ∑ i ∈ I₂, f i =
      ∑ i ∈ I₂, -(1 / 2) * (logKernel (τp i) + logKernel (τm i) + 2 * kappa χ) :=
    Finset.sum_congr rfl fun i hi =>
      ballGrowthInteraction_self_of_le hχ hlam c (hp i) (hm i) (hI₂ i hi)
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at h4
  rw [← Finset.mul_sum] at h5
  linarith

/-- **Proposition 3.3** (equation (3.9)). There is `C > 0`
depending only on `χ` such that for every configuration `c` (`c i = (x_i, y_i)`) with
`σ_N = Id`, every `λ > 0`, radii `τ_i^+, τ_i^- ≥ λ`, and every split `[N] = I₁ ⊔ I₂` with
(3.7) `|x_i - y_i| ≤ 2(τ_i^+ + τ_i^-)` and `τ_i^+ = τ_i^-` for `i ∈ I₁` and (3.8)
`|x_i - y_i| ≥ 2(τ_i^+ + τ_i^-)` for `i ∈ I₂`,

`F_λ(X_N, Y_N) ≥ -Σ_{i ∈ I₁} g_λ(x_i - y_i) - ½ Σ_{i ∈ I₂} (g(τ_i^+) + g(τ_i^-) + 2κ)
  + ½ Σ_{i ≠ j} v'_ij - C Σ_{i ∈ I₁} (|x_i - y_i| / τ_i^+)²`,

with `v'_ij = ballGrowthInteraction χ λ τ^+ τ^- c i j` as in (3.6). The hypotheses `σ_N = Id`
and `|x_i - y_i| ≤ 2(τ_i^+ + τ_i^-)` on `I₁` are not used by the proof (see
`energy_ge_ballGrowth`). -/
theorem prop_3_3 (hχ : IsMollifier χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (lam : ℝ) (c : Fin N → ℂ × ℂ) (τp τm : Fin N → ℝ)
      (I₁ I₂ : Finset (Fin N)), 0 < lam → stableMatching c = Equiv.refl _ →
      (∀ i, lam ≤ τp i) → (∀ i, lam ≤ τm i) → Disjoint I₁ I₂ → I₁ ∪ I₂ = Finset.univ →
      (∀ i ∈ I₁, ‖(c i).1 - (c i).2‖ ≤ 2 * (τp i + τm i) ∧ τp i = τm i) →
      (∀ i ∈ I₂, 2 * (τp i + τm i) ≤ ‖(c i).1 - (c i).2‖) →
      -(∑ i ∈ I₁, smearedKernel χ lam ((c i).1 - (c i).2)) -
          (1 / 2) * ∑ i ∈ I₂, (logKernel (τp i) + logKernel (τm i) + 2 * kappa χ) +
          (1 / 2) * ∑ i, ∑ j with i ≠ j, ballGrowthInteraction χ lam τp τm c i j -
          C * ∑ i ∈ I₁, (‖(c i).1 - (c i).2‖ / τp i) ^ 2 ≤
        energy χ lam c := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  refine ⟨3 * (Real.pi * max M 1), by positivity, ?_⟩
  intro N lam c τp τm I₁ I₂ hlam _ hp hm hdisj hunion hI₁ hI₂
  exact energy_ge_ballGrowth hχ (fun x => (hM x).trans (le_max_left M 1)) hlam c hp hm hdisj
    hunion (fun i hi => (hI₁ i hi).2) hI₂

end MultipoleBKT

end
