/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.UpperBound
public import MultipoleBKT.Appendix.MultipoleIntegral.LowerBound
import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Cutoff

/-!
# Bounds on the true multipole integral and its normalized partition function

See Lemma A.3 and Proposition 4.23.
The true integral uses the Hessian estimate and the specified lower chain.
For the partition function, first restrict to a finite cutoff, then compare
with the untruncated normalization using Lemma 4.12.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {lam β M : ℝ}

open MultipoleIntegral

/-- **Lemma A.3** (eq. (A.5)) for the model
`(v, ∞, 0, ∅)` and the cutoff `ε₀ = ∞`: for `1 < k ≤ p*(β)` and `M > 20` there is
`C > 0` (depending on `χ, β, M, k`) such that for every `λ > 0` there is `N₀` with
`C⁻¹ N λ^{(2-β)k} λ^{2(k-1)} ≤ I^0_{mult,∞}(S) ≤ C N λ^{(2-β)k} λ^{2(k-1)}` for all `N ≥ N₀` and
all `S` with `|S| = k`. -/
theorem multipoleIntegral_two_sided (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 < k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 20 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤ multipoleIntegral χ N β lam M S ∧
          multipoleIntegral χ N β lam M S ≤ C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  obtain ⟨Cu, hCu, hup⟩ := multipoleIntegral_le hχ hβ hk.le hkp (M := M) (by linarith)
  obtain ⟨Cl, hCl, hlow⟩ := le_multipoleIntegral hχ hβ hk.le (M := M) (by linarith)
  refine ⟨max Cu Cl, lt_max_of_lt_left hCu, fun lam hlam => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hlow lam hlam
  refine ⟨N₀, fun N hN S hS => ⟨le_trans ?_ (hN₀ N hN S hS), (hup lam hlam N S hS).trans ?_⟩⟩
  · have : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
    have h := inv_anti₀ hCl (le_max_right Cu Cl)
    calc (max Cu Cl)⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
        = (max Cu Cl)⁻¹ * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by ring
      _ ≤ Cl⁻¹ * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) :=
          mul_le_mul_of_nonneg_right h this
      _ = Cl⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by ring
  · have : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
    calc Cu * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
        = Cu * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by ring
      _ ≤ max Cu Cl * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = max Cu Cl * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by ring

/-- `C_{β,λ} ≤ 𝒵_β λ^{2-β}` for every `N`, `β > 2`, `λ > 0`. -/
theorem dipoleNormalization_le (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam) (N : ℕ) :
    dipoleNormalization χ N β lam ≤ lam ^ (2 - β) * dipoleConstant χ β := by
  rw [← integral_exp_smearedKernel hχ hlam β]
  exact integral_box_prod_sub_le N (f := fun w => Real.exp (β * smearedKernel χ lam w))
    (measurable_exp_smearedKernel hχ hlam β) (fun w => (Real.exp_pos _).le)
    (integrable_exp_smearedKernel hχ hlam hβ)

namespace MultipoleIntegral

/-- The algebra of the upper bound: from `N (Z/2) ℓ ≤ A` and `I ≤ C N ℓ^k Λ`,
`(A⁻¹)^k I ≤ C (2/Z)^k Λ / N^{k-1}`. -/
theorem gate_upper_algebra {A I N ℓ Λ C Z : ℝ} {k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) (hℓ : 0 < ℓ)
    (hZ : 0 < Z) (hA : N * (Z / 2) * ℓ ≤ A) (hI : I ≤ C * N * ℓ ^ k * Λ) (hI0 : 0 ≤ I) :
    (A⁻¹) ^ k * I ≤ C * (2 / Z) ^ k * Λ / N ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hB : 0 < N * (Z / 2) * ℓ := by positivity
  have hAinv : A⁻¹ ≤ (N * (Z / 2) * ℓ)⁻¹ := inv_anti₀ hB hA
  have hA0 : 0 ≤ A⁻¹ := inv_nonneg.2 (hB.le.trans hA)
  calc (A⁻¹) ^ (m + 1) * I ≤ ((N * (Z / 2) * ℓ)⁻¹) ^ (m + 1) * (C * N * ℓ ^ (m + 1) * Λ) :=
        mul_le_mul (pow_le_pow_left₀ hA0 hAinv _) hI hI0 (by positivity)
    _ = C * (2 / Z) ^ (m + 1) * Λ / N ^ (m + 1 - 1) := by
        have hN' : N ≠ 0 := hN.ne'
        have hℓ' : ℓ ≠ 0 := hℓ.ne'
        have hZ' : Z ≠ 0 := hZ.ne'
        rw [Nat.add_sub_cancel, inv_pow, mul_pow, mul_pow, div_pow, div_pow]
        field_simp
        ring

/-- The algebra of the lower bound: from `A ≤ N Z ℓ` and `C⁻¹ N ℓ^k Λ ≤ I`,
`Λ / (C Z^k N^{k-1}) ≤ (A⁻¹)^k I`. -/
theorem gate_lower_algebra {A I N ℓ Λ C Z : ℝ} {k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) (hℓ : 0 < ℓ)
    (hZ : 0 < Z) (hC : 0 < C) (hΛ : 0 ≤ Λ) (hA0 : 0 < A) (hA : A ≤ N * Z * ℓ)
    (hI : C⁻¹ * N * ℓ ^ k * Λ ≤ I) :
    Λ / (C * Z ^ k * N ^ (k - 1)) ≤ (A⁻¹) ^ k * I := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hAinv : (N * Z * ℓ)⁻¹ ≤ A⁻¹ := inv_anti₀ hA0 hA
  calc Λ / (C * Z ^ (m + 1) * N ^ (m + 1 - 1))
      = ((N * Z * ℓ)⁻¹) ^ (m + 1) * (C⁻¹ * N * ℓ ^ (m + 1) * Λ) := by
        have hN' : N ≠ 0 := hN.ne'
        have hℓ' : ℓ ≠ 0 := hℓ.ne'
        have hZ' : Z ≠ 0 := hZ.ne'
        have hC' : C ≠ 0 := hC.ne'
        rw [Nat.add_sub_cancel, inv_pow, mul_pow, mul_pow]
        field_simp
        ring
    _ ≤ (A⁻¹) ^ (m + 1) * I :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hAinv _) hI (by positivity)
          (pow_nonneg (inv_nonneg.2 hA0.le) _)

end MultipoleIntegral

/-- **Proposition 4.23, (4.36)–(4.37)** for `𝖬_{β,λ} = 𝖬^0_∞`, in exactly the form of the first conjunct of the frozen gate
`MultipoleBKT.proposition_4_23`: for `2 ≤ k ≤ p*(β)` there is `M₀ > 20` such that for every
`M ≥ M₀` there are `C > 0` and `λ₀ ∈ (0, 1]` such that for every `λ ∈ (0, λ₀)` there is `N₀` with
`λ^{2(k-1)} / (C N^{k-1}) ≤ 𝖬_{β,λ}(S) ≤ C λ^{2(k-1)} / N^{k-1}` for all `N ≥ N₀` and all
`S ⊆ [N]` with `|S| = k`. Here `M₀ = 21`, `λ₀ = 1`. -/
theorem multipolePartitionFunction_two_sided (χ : ℂ → ℝ) (hχ : IsMollifier χ) (β : ℝ)
    (hβ : 2 < β) :
    ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ S : Finset ℕ, S ⊆ Finset.range N → S.card = k →
            lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
                multipolePartitionFunction χ N β lam M S ∧
              multipolePartitionFunction χ N β lam M S ≤
                C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by
  intro k hk hkp
  have hk1 : 1 ≤ k := by omega
  refine ⟨21, by norm_num, fun M hM => ?_⟩
  obtain ⟨Cu, hCu, hup⟩ := multipoleIntegral_le hχ hβ hk1 hkp (M := M) (by linarith)
  obtain ⟨Cl, hCl, hlow⟩ := RouteChain.le_multipoleIntegral_via_cutoff hχ hβ hk1 (M := M) (by linarith)
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  set C : ℝ := max (Cu * (2 / Z) ^ k) (Cl * Z ^ k)
  have hC : 0 < C := lt_max_of_lt_left (by positivity)
  refine ⟨C, hC, 1, one_pos, le_rfl, fun lam hlam _ => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hlow lam hlam
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (eventually_half_le_dipoleNormalization hχ hβ hlam)
  refine ⟨max (max N₁ N₂) 1, fun N hN S _ hS => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hℓk : (lam ^ (2 - β)) ^ k = lam ^ ((2 - β) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
  have hCN := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hCN' := dipoleNormalization_le hχ hβ hlam N
  have hA0 := natCast_mul_dipoleNormalization_pos hχ hlam β hN1
  have hΛ : 0 ≤ lam ^ (2 * (k - 1)) := pow_nonneg hlam.le _
  rw [multipolePartitionFunction_eq_multipoleIntegral hχ hlam β M hN1 S, hS]
  have hI0 : 0 ≤ multipoleIntegral χ N β lam M S := by
    rw [multipoleIntegral_eq_toReal_lintegral hχ hlam N β M S]
    exact ENNReal.toReal_nonneg
  constructor
  · -- Restrict the numerator to the finite cutoff, then compare normalizations (4.36).
    have hI := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) S hS
    rw [← hℓk] at hI
    have hA : (N : ℝ) * dipoleNormalization χ N β lam ≤ N * Z * lam ^ (2 - β) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hCN') hNpos.le
    have h := gate_lower_algebra hk1 hNpos hℓ hZ hCl hΛ hA0 hA hI
    have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
    refine le_trans (div_le_div_of_nonneg_left hΛ (by positivity) ?_) h
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hNk.le
  · -- the upper bound (4.37)
    have hI := hup lam hlam N S hS
    rw [← hℓk] at hI
    have hA : (N : ℝ) * (Z / 2) * lam ^ (2 - β) ≤ N * dipoleNormalization χ N β lam := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hNpos.le
      calc Z / 2 * lam ^ (2 - β) = 1 / 2 * Z * lam ^ (2 - β) := by ring
        _ ≤ _ := hCN
    have h := gate_upper_algebra hk1 hNpos hℓ hZ hA hI hI0
    refine h.trans ?_
    have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
    rw [div_le_div_iff_of_pos_right hNk]
    have : Cu * (2 / Z) ^ k ≤ C := le_max_left _ _
    have := mul_le_mul_of_nonneg_right this hΛ
    linarith

end MultipoleBKT

end
