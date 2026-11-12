/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Instances
public import MultipoleBKT.Appendix.MultipoleIntegral.MinusModel
public import MultipoleBKT.Appendix.MultipoleIntegral.Bounds
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Gate

/-!
# Proposition 4.23, (4.38)–(4.39) for `𝖬^-_{ε₀}` and `𝖬^0_{ε₀}`

Proposition 4.23 and
its proof (proof of Proposition 4.23): the bounds (4.38) and (4.39)

`λ^{2(|S|-1)} / (C N^{|S|-1}) ≤ 𝖬(S) ≤ C λ^{2(|S|-1)} / N^{|S|-1}`, `1 < |S| ≤ p*(β)`,

for `𝖬 ∈ {𝖬^-_{ε₀}, 𝖬^0_{ε₀}}` (the case `𝖬^0_∞` is the frozen gate), and the density comparison
`𝖬^-_{ε₀}(X) ≍ 𝖬^0_{ε₀}(X)` (blue paragraph proof of Proposition 4.23), for every `X`, without a restriction
on the block sizes.

* `C_{β,λ,ε₀} ≤ 𝒵_β λ^{2-β}` (blue, proof of Proposition 4.23) is
  `MultipoleIntegralZ.cutoffDipoleNormalization_le_rpow`;
* `minusPartitionFunction_singleton_eq`: the normalization identity
  `𝖬^-_{ε₀}(S) = (N C_{β,λ,ε₀})^{-|S|} I^-_{mult,ε₀}(S)` (proof of Proposition 4.23);
* `minusPartitionFunction_two_sided`: **(4.38)–(4.39) for `𝖬^-_{ε₀}`**, from Lemma A.3 for the model
  `(ṽ, τ̃)` (`multipoleIntegralMinus_two_sided`) and Lemma 4.12;
* `minus_zero_comparison`: **the density comparison** `e^{-c} 𝖬^0_{ε₀}(X) ≤ 𝖬^-_{ε₀}(X) ≤
  e^{c} 𝖬^0_{ε₀}(X)` with `c = C₁ m² + |L| m`, `m = ∑_{S ∈ X} |S|` (`= |V_X|` for a subpartition),
  for every `X`, from Lemma 3.10 (`|ṽ_ij - v_ij| ≤ C r_i r_j / τ₀²`) and the bound on the
  Gaussian damping, valid on the support `r_i ≤ ε₀ R̄` of `μ_{β,λ,ε₀}` when `λ ≤ ε₀ R̄`;
* `zeroPartitionFunction_two_sided`: **(4.38)–(4.39) for `𝖬^0_{ε₀}`**.

**Quantifiers.** For `2 ≤ k ≤ p*(β)`, `M > 20` and (for `𝖬^-`) the damping constant `L`, there is
`C > 0` depending on `χ, β, M, k` (and `L`), *not* on `ε₀` or `p₀`, such that for every
`ε₀ ∈ (0, 1)` there is `λ₀ ∈ (0, 1]` (depending on `ε₀`, through Lemma 4.12 and `2λ ≤ ε₀ R̄`) such
that for every `p₀`, every `λ ∈ (0, λ₀)` there is `N₀` with the bounds for all `N ≥ N₀` and all
`S` with `|S| = k`. The paper's constant depends on `β, M, |S|` only (4.39); `λ` small and
`N` large are implicit there (Lemma A.3 and Lemma 4.12).
-/

@[expose] public section

namespace MultipoleBKT

namespace BoundedLowerEps

open MeasureTheory Set Finset Metric
open TwoComponentCoulomb (box)
open Hierarchical Multipole

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

/-! ### The normalization identity for `𝖬^-_{ε₀}` -/

open scoped Classical in
/-- **The normalization identity** (proof of Proposition 4.23):
`𝖬^-_{ε₀}(S) = (N C_{β,λ,ε₀})^{-|S|} I^-_{mult,ε₀}(S)`, for `λ > 0`, `ε₀ > 0`, `N ≥ 1`. -/
theorem minusPartitionFunction_singleton_eq (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (S : Finset ℕ) :
    minusPartitionFunction χ N p₀ β lam M ε₀ L {S} =
      ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ S.card *
        multipoleIntegralMinus χ N β lam M L ε₀ (truncationScale p₀ β lam) S := by
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  set R := truncationScale p₀ β lam
  have hd : Measurable fun c : S → ℂ × ℂ =>
      ∏ i, ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      (((measurable_cutoffDensity hχ hlam β _).comp (measurable_pi_apply i)).const_mul _)
  rw [minusPartitionFunction, Finset.prod_singleton, modelPartitionFunction,
    pi_cutoffDipoleMeasure_eq hχ hlam β hε₀ hN,
    integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall fun c => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top),
    multipoleIntegralMinus, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_prod]
  have hti : ∀ i, (ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
      (closedBall (0 : ℂ) (ε₀ * R)).indicator
        (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2))).toReal =
      (N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2) := fun i =>
    ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hC.le) (cutoffDensity_nonneg β _ _))
  simp_rw [hti]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hdip : ∀ i : S, (closedBall (0 : ℂ) (ε₀ * R)).indicator
      (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2) *
        gaussianWeight p₀ β lam ε₀ L (c i) =
      Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
        Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
          (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2) := by
    intro i
    unfold gaussianWeight
    by_cases hm : (c i).1 - (c i).2 ∈ closedBall (0 : ℂ) (ε₀ * R)
    · rw [indicator_of_mem hm, indicator_of_mem hm, Pi.one_apply, mul_one, mul_div_assoc]
      ring
    · rw [indicator_of_notMem hm, indicator_of_notMem hm]
      ring
  unfold minusIntegrand minusPairWeight
  rw [← prod_congr rfl fun i _ => hdip i, prod_mul_distrib]
  simp only [R]
  ring

/-! ### (4.38)–(4.39) for `𝖬^-_{ε₀}` -/

/-- `2 λ ≤ ε₀ R̄_{β,λ}` for `λ ≤ min 1 (ε₀/2)`. -/
theorem two_mul_le_cutoff (hβ : 2 < β) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε₀ : 0 < ε₀)
    (hlamε : lam ≤ ε₀ / 2) (p₀ : ℕ) : 2 * lam ≤ ε₀ * truncationScale p₀ β lam := by
  have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
  have : ε₀ ≤ ε₀ * truncationScale p₀ β lam := le_mul_of_one_le_right hε₀.le hR1
  linarith

/-- **Proposition 4.23, (4.38)–(4.39) for `𝖬^-_{ε₀}`** (Proposition 4.23;
proof of Proposition 4.23): for `2 ≤ k ≤ p*(β)`, `M > 20` and `L ∈ ℝ` there is `C > 0` (depending on
`χ, β, M, L, k`, not on `ε₀`, `p₀`) such that for every `ε₀ ∈ (0, 1)` there is `λ₀ ∈ (0, 1]` such
that for all `p₀`, `λ ∈ (0, λ₀)` there is `N₀` with
`λ^{2(k-1)} / (C N^{k-1}) ≤ 𝖬^-_{ε₀}(S) ≤ C λ^{2(k-1)} / N^{k-1}` for `N ≥ N₀` and `|S| = k`. -/
theorem minusPartitionFunction_two_sided (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 20 < M) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, S.card = k →
          lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
              minusPartitionFunction χ N p₀ β lam M ε₀ L {S} ∧
            minusPartitionFunction χ N p₀ β lam M ε₀ L {S} ≤
              C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨Ci, hCi, hint⟩ := multipoleIntegralMinus_two_sided hχ hβ (by omega : 1 < k) hkp hM L
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  set C : ℝ := max (Ci * (2 / Z) ^ k) (Ci * Z ^ k)
  have hC : 0 < C := lt_max_of_lt_left (by positivity)
  refine ⟨C, hC, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨lam₁, hlam₁, hlow⟩ := lem411_lower hχ hβ hε₀
  refine ⟨min (min 1 (ε₀ / 2)) lam₁, lt_min (lt_min one_pos (by linarith)) hlam₁,
    (min_le_left _ _).trans (min_le_left _ _), fun p₀ lam hlam hlt => ?_⟩
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hlamε : lam ≤ ε₀ / 2 := (hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hlamlt : lam < lam₁ := hlt.trans_le (min_le_right _ _)
  have h2 := two_mul_le_cutoff hβ hlam hlam1 hε₀ hlamε p₀
  obtain ⟨N₁, hN₁⟩ := hint lam hlam
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (hlow p₀ lam hlam hlamlt)
  refine ⟨max (max N₁ N₂) 1, fun N hN S hS => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hℓk : (lam ^ (2 - β)) ^ k = lam ^ ((2 - β) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
  have hCN := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hCN' := MultipoleIntegralZ.cutoffDipoleNormalization_le_rpow hχ hβ hlam N p₀ ε₀
  have hA0 := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN1
  have hΛ : 0 ≤ lam ^ (2 * (k - 1)) := pow_nonneg hlam.le _
  obtain ⟨hIlow, hIup⟩ := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    ε₀ (truncationScale p₀ β lam) h2 S hS
  rw [minusPartitionFunction_singleton_eq hχ hlam hε₀ hN1 S, hS]
  have hI0 : 0 ≤ multipoleIntegralMinus χ N β lam M L ε₀ (truncationScale p₀ β lam) S :=
    setIntegral_nonneg (MeasurableSet.univ_pi fun _ => measurableSet_box_prod N)
      fun c _ => MultipoleIntegral.minusIntegrand_nonneg β lam M L ε₀ _ c
  constructor
  · -- (4.38)
    rw [← hℓk] at hIlow
    have hA : (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ ≤ N * Z * lam ^ (2 - β) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hCN') hNpos.le
    have h := MultipoleIntegral.gate_lower_algebra hk1 hNpos hℓ hZ hCi hΛ hA0 hA hIlow
    have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
    refine le_trans (div_le_div_of_nonneg_left hΛ (by positivity) ?_) h
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hNk.le
  · -- (4.39)
    rw [← hℓk] at hIup
    have hA : (N : ℝ) * (Z / 2) * lam ^ (2 - β) ≤
        N * cutoffDipoleNormalization χ N p₀ β lam ε₀ := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hNpos.le
      calc Z / 2 * lam ^ (2 - β) = 1 / 2 * Z * lam ^ (2 - β) := by ring
        _ ≤ _ := hCN
    have h := MultipoleIntegral.gate_upper_algebra hk1 hNpos hℓ hZ hA hIup hI0
    refine h.trans ?_
    have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
    rw [div_le_div_iff_of_pos_right hNk]
    have : Ci * (2 / Z) ^ k ≤ C := le_max_left _ _
    have := mul_le_mul_of_nonneg_right this hΛ
    linarith

/-! ### The density comparison `𝖬^- ≍ 𝖬^0` -/

open scoped Classical in
/-- The pair weights of the two models on the support: for dipoles of length at most `ε₀ R̄`
and `λ ≤ ε₀ R̄`, `e^{-β ṽ_ij} 𝟙_{𝒜_ij}` and `e^{-β v_ij} 𝟙_{𝒜_ij}` are within the factor
`e^{β C₁/64}`. -/
theorem stableWeight_comparison (hβ : 0 ≤ β) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (h310 : ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
      |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
        C₁ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / τ ^ 2)
    (hlam : 0 < lam) {R : ℝ} (hh : lam ≤ ε₀ * R) {d e : ℂ × ℂ} (hd : ‖d.1 - d.2‖ ≤ ε₀ * R)
    (he : ‖e.1 - e.2‖ ≤ ε₀ * R) :
    stableWeight β (upperBoundInteraction χ lam ε₀ R) d e ≤
        Real.exp (β * (C₁ / 64)) * stableWeight β (dipoleInteraction χ lam) d e ∧
      stableWeight β (dipoleInteraction χ lam) d e ≤
        Real.exp (β * (C₁ / 64)) * stableWeight β (upperBoundInteraction χ lam ε₀ R) d e := by
  have h1 := MultipoleIntegral.abs_upperBoundInteraction_sub_le hC₁ h310 hlam hh hd he
  rw [abs_le] at h1
  unfold stableWeight
  split_ifs
  · refine ⟨?_, ?_⟩ <;> rw [← Real.exp_add] <;> refine Real.exp_le_exp.2 ?_ <;> nlinarith
  · simp

open scoped Classical in
/-- **The density comparison, one block**: on the support of `μ_{β,λ,ε₀}^{⊗ ℕ}`, the block weights
of the models `-` and `0` are within the factor `e^{C₁ |S|² + |L| |S|}`. -/
theorem blockWeight_comparison (hβ : 0 ≤ β) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (h310 : ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
      |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
        C₁ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / τ ^ 2)
    (hlam : 0 < lam) (hh : lam ≤ ε₀ * truncationScale p₀ β lam) (S : Finset ℕ)
    (c : ℕ → ℂ × ℂ) (hc : ∀ i, c i ∈ cutoffSet N p₀ β lam ε₀) :
    blockWeightOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
        (gaussianWeight p₀ β lam ε₀ L) M lam S c ≤
      Real.exp (β * (C₁ / 64) * S.card ^ 2 + |L| * S.card) *
        blockWeightOf β (dipoleInteraction χ lam) (fun _ => 1) M lam S c ∧
    blockWeightOf β (dipoleInteraction χ lam) (fun _ => 1) M lam S c ≤
      Real.exp (β * (C₁ / 64) * S.card ^ 2 + |L| * S.card) *
        blockWeightOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
          (gaussianWeight p₀ β lam ε₀ L) M lam S c := by
  set R := truncationScale p₀ β lam
  set w₁ := upperBoundInteraction χ lam ε₀ R
  set w₀ := dipoleInteraction χ lam
  set W := Real.exp (β * (C₁ / 64))
  have hW1 : 1 ≤ W := Real.one_le_exp (by positivity)
  have hr : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R := fun i => (hc i).2
  have hcard : (pairsOn S).card ≤ S.card ^ 2 := by
    calc (pairsOn S).card ≤ (S ×ˢ S).card := card_filter_le _ _
      _ = S.card ^ 2 := by rw [card_product, sq]
  have hWp : W ^ (pairsOn S).card ≤ W ^ (S.card ^ 2) := pow_le_pow_right₀ hW1 hcard
  have hWexp : W ^ (S.card ^ 2) = Real.exp (β * (C₁ / 64) * S.card ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- the pair products
  have hP1 : ∏ p ∈ pairsOn S, stableWeight β w₁ (c p.1) (c p.2) ≤
      W ^ (pairsOn S).card * ∏ p ∈ pairsOn S, stableWeight β w₀ (c p.1) (c p.2) := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun p _ => stableWeight_nonneg β w₁ _ _) fun p _ =>
      (stableWeight_comparison hβ hC₁ h310 hlam hh (hr _) (hr _)).1
  have hP0 : ∏ p ∈ pairsOn S, stableWeight β w₀ (c p.1) (c p.2) ≤
      W ^ (pairsOn S).card * ∏ p ∈ pairsOn S, stableWeight β w₁ (c p.1) (c p.2) := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun p _ => stableWeight_nonneg β w₀ _ _) fun p _ =>
      (stableWeight_comparison hβ hC₁ h310 hlam hh (hr _) (hr _)).2
  -- the dipole weights
  have hg : ∀ i, |(-L * (‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2))| ≤ |L| := by
    intro i
    have := MultipoleIntegral.abs_damping_le (L := L) (norm_nonneg ((c i).1 - (c i).2)) (hr i)
    rwa [mul_div_assoc] at this
  have hG1 : ∏ i ∈ S, gaussianWeight p₀ β lam ε₀ L (c i) ≤ Real.exp (|L| * S.card) := by
    rw [mul_comm, Real.exp_nat_mul, ← prod_const]
    exact prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i _ =>
      Real.exp_le_exp.2 ((le_abs_self _).trans (hg i))
  have hG0 : 1 ≤ Real.exp (|L| * S.card) * ∏ i ∈ S, gaussianWeight p₀ β lam ε₀ L (c i) := by
    have : ∏ i ∈ S, Real.exp (-|L|) ≤ ∏ i ∈ S, gaussianWeight p₀ β lam ε₀ L (c i) :=
      prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i _ =>
        Real.exp_le_exp.2 (by have := hg i; rw [abs_le] at this; linarith)
    rw [prod_const, ← Real.exp_nat_mul] at this
    calc (1 : ℝ) = Real.exp (|L| * S.card) * Real.exp (S.card * -|L|) := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  have hI0 : (0 : ℝ) ≤ if ConnOn S (linkedPairs M lam c S) then 1 else 0 := by
    split_ifs <;> norm_num
  have hS1 : 0 ≤ ∏ p ∈ pairsOn S, stableWeight β w₁ (c p.1) (c p.2) :=
    prod_nonneg fun p _ => stableWeight_nonneg β w₁ _ _
  have hS0 : 0 ≤ ∏ p ∈ pairsOn S, stableWeight β w₀ (c p.1) (c p.2) :=
    prod_nonneg fun p _ => stableWeight_nonneg β w₀ _ _
  have hGn : 0 ≤ ∏ i ∈ S, gaussianWeight p₀ β lam ε₀ L (c i) :=
    prod_nonneg fun i _ => (Real.exp_pos _).le
  have hsplit : Real.exp (β * (C₁ / 64) * S.card ^ 2 + |L| * S.card) =
      W ^ (S.card ^ 2) * Real.exp (|L| * S.card) := by
    rw [hWexp, ← Real.exp_add]
  unfold blockWeightOf
  simp only [prod_const_one, mul_one]
  rw [hsplit]
  constructor
  · calc (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
          (∏ p ∈ pairsOn S, stableWeight β w₁ (c p.1) (c p.2)) *
            ∏ i ∈ S, gaussianWeight p₀ β lam ε₀ L (c i)
        ≤ (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
            (W ^ (S.card ^ 2) * ∏ p ∈ pairsOn S, stableWeight β w₀ (c p.1) (c p.2)) *
              Real.exp (|L| * S.card) := by
          gcongr
          exact hP1.trans (mul_le_mul_of_nonneg_right hWp hS0)
      _ = _ := by ring
  · calc (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
          ∏ p ∈ pairsOn S, stableWeight β w₀ (c p.1) (c p.2)
        ≤ (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
            (W ^ (S.card ^ 2) * ∏ p ∈ pairsOn S, stableWeight β w₁ (c p.1) (c p.2)) *
              (Real.exp (|L| * S.card) * ∏ i ∈ S, gaussianWeight p₀ β lam ε₀ L (c i)) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hI0
          calc ∏ p ∈ pairsOn S, stableWeight β w₀ (c p.1) (c p.2)
              ≤ W ^ (S.card ^ 2) * ∏ p ∈ pairsOn S, stableWeight β w₁ (c p.1) (c p.2) :=
                hP0.trans (mul_le_mul_of_nonneg_right hWp hS1)
            _ ≤ _ := le_mul_of_one_le_right (by positivity) hG0
      _ = _ := by ring

/-- **The density comparison** (blue paragraph, proof of Proposition 4.23): there is `C₁ ≥ 0`
depending only on `χ` (Lemma 3.10) such that for `β ≥ 0`, `ε₀ > 0`, `λ ∈ (0, ε₀ R̄]`, `N ≥ 1` and
every finite family `X` of label sets, with `m = ∑_{S ∈ X} |S|` and
`c = β C₁ m² / 64 + |L| m`, `e^{-c} 𝖬^0_{ε₀}(X) ≤ 𝖬^-_{ε₀}(X) ≤ e^{c} 𝖬^0_{ε₀}(X)`. For a
subpartition, `m = |V_X|` (no restriction on the block sizes). -/
theorem minus_zero_comparison (hχ : IsMollifier χ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (N p₀ : ℕ) (β lam M ε₀ L : ℝ), 0 ≤ β → 0 < lam → 0 < ε₀ → 1 ≤ N →
      lam ≤ ε₀ * truncationScale p₀ β lam → ∀ X : Finset (Finset ℕ),
        Real.exp (-(β * (C₁ / 64) * (∑ S ∈ X, (S.card : ℝ)) ^ 2 + |L| * ∑ S ∈ X, (S.card : ℝ))) *
            zeroPartitionFunction χ N p₀ β lam M ε₀ X ≤
          minusPartitionFunction χ N p₀ β lam M ε₀ L X ∧
        minusPartitionFunction χ N p₀ β lam M ε₀ L X ≤
          Real.exp (β * (C₁ / 64) * (∑ S ∈ X, (S.card : ℝ)) ^ 2 + |L| * ∑ S ∈ X, (S.card : ℝ)) *
            zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
  obtain ⟨C₁, hC₁, h310⟩ := lemma_3_10 hχ
  have h310' : ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
      |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
        C₁ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / τ ^ 2 := fun lam τ hlam d e hd he =>
    (h310 lam τ hlam d e hd he).1
  refine ⟨C₁, hC₁, fun N p₀ β lam M ε₀ L hβ hlam hε₀ hN hh X => ?_⟩
  have h₁ := modelHyp_minus (p₀ := p₀) hχ hlam β hε₀ hN hh L
  have h₀ := modelHyp_zero (p₀ := p₀) hχ hlam β hε₀ hN
  have := h₁.isProbabilityMeasure
  have hae : ∀ᵐ c ∂labelField (cutoffDipoleMeasure χ N p₀ β lam ε₀),
      ∀ i, c i ∈ cutoffSet N p₀ β lam ε₀ := ae_labelField_mem h₁.ae_mem
  -- one block
  have hone : ∀ S : Finset ℕ,
      Real.exp (-(β * (C₁ / 64) * S.card ^ 2 + |L| * S.card)) *
          zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
        minusPartitionFunction χ N p₀ β lam M ε₀ L {S} ∧
      minusPartitionFunction χ N p₀ β lam M ε₀ L {S} ≤
        Real.exp (β * (C₁ / 64) * S.card ^ 2 + |L| * S.card) *
          zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
    intro S
    simp only [zeroPartitionFunction, minusPartitionFunction, Finset.prod_singleton]
    rw [h₁.modelPartitionFunction_eq_integral_labelField M lam S,
      h₀.modelPartitionFunction_eq_integral_labelField M lam S, ← integral_const_mul,
      ← integral_const_mul]
    have hpt := fun c (hc : ∀ i, c i ∈ cutoffSet N p₀ β lam ε₀) =>
      blockWeight_comparison (L := L) (M := M) hβ hC₁ h310' hlam hh S c hc
    constructor
    · refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun c => mul_nonneg
        (Real.exp_pos _).le (blockWeightOf_nonneg M lam (fun _ => zero_le_one) S c))
        (h₁.integrable_blockWeightOf M lam S) (hae.mono fun c hc => ?_)
      have h := (hpt c hc).2
      rw [Real.exp_neg]
      calc (Real.exp (β * (C₁ / 64) * S.card ^ 2 + |L| * S.card))⁻¹ *
            blockWeightOf β (dipoleInteraction χ lam) (fun _ => 1) M lam S c
          ≤ (Real.exp (β * (C₁ / 64) * S.card ^ 2 + |L| * S.card))⁻¹ *
              (Real.exp (β * (C₁ / 64) * S.card ^ 2 + |L| * S.card) *
                blockWeightOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
                  (gaussianWeight p₀ β lam ε₀ L) M lam S c) :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.2 (Real.exp_pos _).le)
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
    · exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun c =>
        blockWeightOf_nonneg M lam (fun _ => (Real.exp_pos _).le) S c)
        ((h₀.integrable_blockWeightOf M lam S).const_mul _) (hae.mono fun c hc => (hpt c hc).1)
  -- the product over the blocks
  set c : Finset ℕ → ℝ := fun S => β * (C₁ / 64) * (S.card : ℝ) ^ 2 + |L| * S.card with hc
  set m : ℝ := ∑ S ∈ X, (S.card : ℝ) with hm
  have hsq : ∑ S ∈ X, (S.card : ℝ) ^ 2 ≤ m ^ 2 := by
    rw [hm, sq, Finset.sum_mul]
    refine Finset.sum_le_sum fun S hS => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun S : Finset ℕ => (S.card : ℝ))
        (fun _ _ => Nat.cast_nonneg _) hS)
      (Nat.cast_nonneg _)
  have hcsum : ∑ S ∈ X, c S ≤ β * (C₁ / 64) * m ^ 2 + |L| * m := by
    simp only [hc, Finset.sum_add_distrib, ← Finset.mul_sum]
    have : 0 ≤ β * (C₁ / 64) := by positivity
    nlinarith
  have e1 : minusPartitionFunction χ N p₀ β lam M ε₀ L X =
      ∏ S ∈ X, minusPartitionFunction χ N p₀ β lam M ε₀ L {S} := by
    simp only [minusPartitionFunction, Finset.prod_singleton]
  have e0 : zeroPartitionFunction χ N p₀ β lam M ε₀ X =
      ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
    simp only [zeroPartitionFunction, Finset.prod_singleton]
  have hz0 : ∀ S, 0 ≤ zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := fun S => by
    simp only [zeroPartitionFunction, Finset.prod_singleton]
    exact h₀.modelPartitionFunction_nonneg M lam S
  have hP0 : 0 ≤ zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
    rw [e0]; exact prod_nonneg fun S _ => hz0 S
  have hexp : ∀ f : Finset ℕ → ℝ, ∏ S ∈ X, Real.exp (f S) = Real.exp (∑ S ∈ X, f S) :=
    fun f => (Real.exp_sum X f).symm
  constructor
  · calc Real.exp (-(β * (C₁ / 64) * m ^ 2 + |L| * m)) *
          zeroPartitionFunction χ N p₀ β lam M ε₀ X
        ≤ Real.exp (∑ S ∈ X, -c S) * zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hP0
          rw [Finset.sum_neg_distrib]
          linarith
      _ = ∏ S ∈ X, (Real.exp (-c S) * zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) := by
          rw [prod_mul_distrib, hexp, e0]
      _ ≤ ∏ S ∈ X, minusPartitionFunction χ N p₀ β lam M ε₀ L {S} :=
          prod_le_prod₀ (fun S _ => mul_nonneg (Real.exp_pos _).le (hz0 S))
            fun S _ => (hone S).1
      _ = _ := e1.symm
  · calc minusPartitionFunction χ N p₀ β lam M ε₀ L X
        = ∏ S ∈ X, minusPartitionFunction χ N p₀ β lam M ε₀ L {S} := e1
      _ ≤ ∏ S ∈ X, (Real.exp (c S) * zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) :=
          prod_le_prod₀ (fun S _ => (hone S).1.trans' (mul_nonneg (Real.exp_pos _).le (hz0 S)))
            fun S _ => (hone S).2
      _ = Real.exp (∑ S ∈ X, c S) * zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
          rw [prod_mul_distrib, hexp, e0]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hcsum) hP0

/-! ### (4.38)–(4.39) for `𝖬^0_{ε₀}` -/

/-- **Proposition 4.23, (4.38)–(4.39) for `𝖬^0_{ε₀}`** (Proposition 4.23;
proof of Proposition 4.23, "this proves the `𝖬^0_{ε₀}` bounds"): for `2 ≤ k ≤ p*(β)` and `M > 20` there is
`C > 0` (depending on `χ, β, M, k`, not on `ε₀`, `p₀`) such that for every `ε₀ ∈ (0, 1)` there is
`λ₀ ∈ (0, 1]` such that for all `p₀`, `λ ∈ (0, λ₀)` there is `N₀` with
`λ^{2(k-1)} / (C N^{k-1}) ≤ 𝖬^0_{ε₀}(S) ≤ C λ^{2(k-1)} / N^{k-1}` for `N ≥ N₀` and `|S| = k`.
It follows from the bounds for `𝖬^-_{ε₀}` with `L = 0` and the density comparison. -/
theorem zeroPartitionFunction_two_sided (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 20 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, S.card = k →
          lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
              zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
              C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by
  obtain ⟨C, hC, hmin⟩ := minusPartitionFunction_two_sided hχ hβ hk hkp hM 0
  obtain ⟨C₁, hC₁, hcmp⟩ := minus_zero_comparison hχ
  set E := Real.exp (β * (C₁ / 64) * (k : ℝ) ^ 2)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨C * E, by positivity, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨lam₀, hlam₀, hlam₀1, hlam⟩ := hmin ε₀ hε₀ hε₁
  refine ⟨min lam₀ (ε₀ / 2), lt_min hlam₀ (by linarith), (min_le_left _ _).trans hlam₀1,
    fun p₀ lam hl hlt => ?_⟩
  have hlt₀ : lam < lam₀ := hlt.trans_le (min_le_left _ _)
  have hlamε : lam ≤ ε₀ / 2 := (hlt.trans_le (min_le_right _ _)).le
  have h2 := two_mul_le_cutoff hβ hl (hlt₀.le.trans hlam₀1) hε₀ hlamε p₀
  obtain ⟨N₀, hN₀⟩ := hlam p₀ lam hl hlt₀
  refine ⟨max N₀ 1, fun N hN S hS => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hlo, hup⟩ := hN₀ N (le_trans (le_max_left _ _) hN) S hS
  obtain ⟨hc1, hc2⟩ := hcmp N p₀ β lam M ε₀ 0 (by linarith) hl hε₀ hN1 (by linarith) {S}
  simp only [Finset.sum_singleton, abs_zero, zero_mul, add_zero, hS] at hc1 hc2
  have hNk : 0 < (N : ℝ) ^ (k - 1) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN1
    positivity
  have hΛ : 0 ≤ lam ^ (2 * (k - 1)) := pow_nonneg hl.le _
  rw [Real.exp_neg] at hc1
  constructor
  · -- `𝖬^0 ≥ e^{-c} 𝖬^-`
    have h := hc2.trans' hlo
    calc lam ^ (2 * (k - 1)) / (C * E * (N : ℝ) ^ (k - 1))
        = E⁻¹ * (lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1))) := by
          field_simp
      _ ≤ E⁻¹ * (E * zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hE.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hE.ne', one_mul]
  · -- `𝖬^0 ≤ e^{c} 𝖬^-`
    have h := hc1.trans hup
    calc zeroPartitionFunction χ N p₀ β lam M ε₀ {S}
        = E * (E⁻¹ * zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) := by
          rw [← mul_assoc, mul_inv_cancel₀ hE.ne', one_mul]
      _ ≤ E * (C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left h hE.le
      _ = C * E * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by ring

end BoundedLowerEps

end MultipoleBKT

end
