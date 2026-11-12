/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegralZ.Bounds
public import MultipoleBKT.Appendix.MultipoleIntegral.Bounds

/-!
# The bounds (5.65) and (5.66) on `𝖬^{+,Z}_{ε₀}(S)`

See Proposition 5.18,
eqs. (5.65) and (5.66), as derived in its proof: "Taking `w = v^Z` in
Lemma A.3 proves the estimates (5.65) and (5.66)", through the normalization identity
`𝖬^{+,Z}_{ε₀}(S) = (N C_{β,λ,ε₀})^{-|S|} I^{+,Z}_{mult,ε₀}(S)` and Lemma 4.12
(`C_{β,λ,ε₀} ≍ λ^{2-β}`, eq. (4.12)).

* `cutoffDipoleNormalization_le_rpow`: `C_{β,λ,ε₀} ≤ 𝒵_β λ^{2-β}` for every `N`;
* `plusPartitionFunction_two_sided`: for `1 ≤ k ≤ p*(β)`, `M ≥ 9` and `L ∈ ℝ` there is `C > 0`
  (depending on `χ, β, M, L, k`) such that for every `ε₀ ∈ (0, 1)` there is `λ₀ > 0` such that for
  all `p₀`, `λ ∈ (0, λ₀)` there is `N₀` with
  `λ^{2(k-1)} / (C N^{k-1}) ≤ 𝖬^{+,Z}_{ε₀}(S) ≤ C λ^{2(k-1)} / N^{k-1}` for every `N ≥ N₀`,
  every frozen configuration `(V, Z)` with `I_bad^V(Z) = V`, when `3^{p(β)} ≤ M`, and every `S`
  with `|S| = k`. This includes the singleton case `|S| = 1`.
* `multipoleIntegralPlus_two_sided_of_fixed`: Lemma A.3 for `(v^Z, τ^Z, L, Z)` with `p₀`, `ε₀`,
  `M` fixed first (`λ₀ = min(1, ε₀/2, (16(6k + 2M))⁻¹)`).
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Set Finset Metric
open TwoComponentCoulomb (box)
open MultipoleIntegral UpperBound Hierarchical

variable {χ : ℂ → ℝ} {β M : ℝ}

namespace MultipoleIntegralZ

/-- `C_{β,λ,ε₀} ≤ 𝒵_β λ^{2-β}` (Lemma 4.12), for every `N`. -/
theorem cutoffDipoleNormalization_le_rpow (hχ : IsMollifier χ) (hβ : 2 < β) {lam : ℝ}
    (hlam : 0 < lam) (N p₀ : ℕ) (ε₀ : ℝ) :
    cutoffDipoleNormalization χ N p₀ β lam ε₀ ≤ lam ^ (2 - β) * dipoleConstant χ β := by
  rw [← integral_exp_smearedKernel hχ hlam β]
  have hm : Measurable ((closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
      (fun w => Real.exp (β * smearedKernel χ lam w))) :=
    (measurable_exp_smearedKernel hχ hlam β).indicator measurableSet_closedBall
  have hint : Integrable ((closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
      (fun w => Real.exp (β * smearedKernel χ lam w))) :=
    (integrable_exp_smearedKernel hχ hlam hβ).indicator measurableSet_closedBall
  refine (integral_box_prod_sub_le N hm (fun w => indicator_nonneg
    (fun _ _ => (Real.exp_pos _).le) w) hint).trans ?_
  exact integral_mono hint (integrable_exp_smearedKernel hχ hlam hβ) fun w =>
    indicator_le_self' (fun _ _ => (Real.exp_pos _).le) w

end MultipoleIntegralZ

open MultipoleIntegralZ

/-- **Proposition 5.18, eqs. (5.65) and (5.66)** (Proposition 5.18,
; ), from Lemma A.3 for the model `(v^Z, τ^Z, L, Z)`: for
`1 ≤ k ≤ p*(β)`, `M ≥ 9` and `L ∈ ℝ` there is `C > 0` (depending on `χ, β, M, L, k`) such that
for every `ε₀ ∈ (0, 1)` there is `λ₀ > 0` such that for all `p₀` and `λ ∈ (0, λ₀)` there is `N₀`
with `λ^{2(k-1)} / (C N^{k-1}) ≤ 𝖬^{+,Z}_{ε₀}(S) ≤ C λ^{2(k-1)} / N^{k-1}` for every `N ≥ N₀`,
when `3^{p(β)} ≤ M`, for every frozen configuration `(V, Z)` with `I_bad^V(Z) = V` and every `S`
with `|S| = k`. -/
theorem plusPartitionFunction_two_sided (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 9 ≤ M) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (3 : ℝ) ^ pBeta p₀ β ≤ M →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ S : Finset ℕ, S.card = k →
          lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
              plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
            plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≤
              C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by
  obtain ⟨Ci, hCi, hint⟩ := multipoleIntegralPlus_two_sided (χ := χ) hχ hβ hk hkp hM L
  set Zβ := dipoleConstant χ β
  have hZ : 0 < Zβ := dipoleConstant_pos hχ hβ
  set C : ℝ := max (Ci * (2 / Zβ) ^ k) (Ci * Zβ ^ k)
  have hC : 0 < C := lt_max_of_lt_left (by positivity)
  refine ⟨C, hC, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨lam₁, hlam₁, hlow⟩ := lem411_lower hχ hβ hε₀
  have h6 : 0 < 16 * (6 * (k : ℝ) + 2 * M) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  refine ⟨min (min 1 (ε₀ / 2)) (min lam₁ (16 * (6 * k + 2 * M))⁻¹),
    lt_min (lt_min one_pos (by linarith)) (lt_min hlam₁ (inv_pos.2 h6)),
    fun p₀ lam hlam hlt => ?_⟩
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hlamε : lam ≤ ε₀ / 2 := (hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hlamlt : lam < lam₁ := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlamM : lam ≤ (16 * (6 * k + 2 * M))⁻¹ :=
    (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have h2 : 2 * lam ≤ ε₀ * truncationScale p₀ β lam := by
    have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
    have : ε₀ ≤ ε₀ * truncationScale p₀ β lam := le_mul_of_one_le_right hε₀.le hR1
    linarith
  obtain ⟨N₁, hN₁⟩ := hint lam hlam hlamM
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (hlow p₀ lam hlam hlamlt)
  refine ⟨max (max N₁ N₂) 1, fun N hN hM3 V Z hV S hS => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hℓk : (lam ^ (2 - β)) ^ k = lam ^ ((2 - β) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
  have hCN := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hCN' := cutoffDipoleNormalization_le_rpow hχ hβ hlam N p₀ ε₀
  have hA0 := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN1
  have hΛ : 0 ≤ lam ^ (2 * (k - 1)) := pow_nonneg hlam.le _
  obtain ⟨hIlow, hIup⟩ := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    p₀ ε₀ h2 hM3 V Z hV S hS
  rw [plusPartitionFunction_eq_multipoleIntegralPlus hχ hlam hε₀ hN1 S, hS]
  have hI0 : 0 ≤ multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S :=
    setIntegral_nonneg (MeasurableSet.univ_pi fun _ => measurableSet_box_prod N)
      fun c _ => plusIntegrand_nonneg c
  constructor
  · -- (5.65)
    rw [← hℓk] at hIlow
    have hA : (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ ≤ N * Zβ * lam ^ (2 - β) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hCN') hNpos.le
    have h := gate_lower_algebra hk hNpos hℓ hZ hCi hΛ hA0 hA hIlow
    have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
    refine le_trans (div_le_div_of_nonneg_left hΛ (by positivity) ?_) h
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hNk.le
  · -- (5.66)
    rw [← hℓk] at hIup
    have hA : (N : ℝ) * (Zβ / 2) * lam ^ (2 - β) ≤
        N * cutoffDipoleNormalization χ N p₀ β lam ε₀ := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hNpos.le
      calc Zβ / 2 * lam ^ (2 - β) = 1 / 2 * Zβ * lam ^ (2 - β) := by ring
        _ ≤ _ := hCN
    have h := gate_upper_algebra hk hNpos hℓ hZ hA hIup hI0
    refine h.trans ?_
    have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
    rw [div_le_div_iff_of_pos_right hNk]
    have : Ci * (2 / Zβ) ^ k ≤ C := le_max_left _ _
    have := mul_le_mul_of_nonneg_right this hΛ
    linarith

/-- **Lemma A.3 for `(v^Z, τ^Z, L, Z)`, with the parameters fixed first** (the quantifier order of
its consumers in Proposition 5.18): for `ε₀ > 0`, `M ≥ 9` with `3^{p(β)} ≤ M` and every
`1 ≤ k ≤ p*(β)` there are `C > 0` and `λ₀ > 0` such that for `λ ∈ (0, λ₀)` there is `N₀` with
`C⁻¹ N λ^{(2-β)k} λ^{2(k-1)} ≤ I^{+,Z}_{mult,ε₀}(S) ≤ C N λ^{(2-β)k} λ^{2(k-1)}` for every
`N ≥ N₀`, every frozen configuration `(V, Z)` with `I_bad^V(Z) = V` and every `S` with
`|S| = k`. -/
theorem multipoleIntegralPlus_two_sided_of_fixed (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ)
    (L : ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hM : 9 ≤ M) (hM3 : (3 : ℝ) ^ pBeta p₀ β ≤ M) {k : ℕ}
    (hk : 1 ≤ k) (hkp : (k : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ S : Finset ℕ, S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤
            multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S ∧
          multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S ≤
            C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  obtain ⟨C, hC, h⟩ := multipoleIntegralPlus_two_sided (χ := χ) hχ hβ hk hkp hM L
  have h6 : 0 < 16 * (6 * (k : ℝ) + 2 * M) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  refine ⟨C, hC, min (min 1 (ε₀ / 2)) (16 * (6 * k + 2 * M))⁻¹,
    lt_min (lt_min one_pos (by linarith)) (inv_pos.2 h6), fun lam hlam hlt => ?_⟩
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hlamε : lam ≤ ε₀ / 2 := (hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hlamM : lam ≤ (16 * (6 * k + 2 * M))⁻¹ := (hlt.trans_le (min_le_right _ _)).le
  have h2 : 2 * lam ≤ ε₀ * truncationScale p₀ β lam := by
    have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
    have : ε₀ ≤ ε₀ * truncationScale p₀ β lam := le_mul_of_one_le_right hε₀.le hR1
    linarith
  obtain ⟨N₀, hN₀⟩ := h lam hlam hlamM
  exact ⟨N₀, fun N hN V Z hV S hS => hN₀ N hN p₀ ε₀ h2 hM3 V Z hV S hS⟩

end MultipoleBKT

end
