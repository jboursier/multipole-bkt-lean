/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.ExpansionPlus.MultipoleDiff
public import MultipoleBKT.UpperBound.BoundedUpper.External
public import MultipoleBKT.UpperBound.BoundedUpper.WeightBounds
public import MultipoleBKT.UpperBound.BoundedUpper.Integration
public import Mathlib.Algebra.Order.Chebyshev

import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.PlusRoot

/-!
# The external normalization is `1 + O(θ)`: eq. (5.105)

The paper: proof of Proposition 5.19:

"By (5.101), (5.26) and `τ_i^Z ≤ d_{i,bad}` on the support,
`0 ≤ g^Z_{ε₀}(S) - 1 ≤ C ∑_{i ∈ S} 𝔼_{𝖯^{+,ε₀,Z}_{{S}}}[r_i²/(τ_i^Z)²]`. Multiplying by
`𝖬^{+,Z}_{ε₀}(S)` and using the integration leading to (A.44), with the empty near tree when
`|S| = 1`, gives `0 ≤ 𝖬^{+,Z}_{ε₀}(S)(g^Z_{ε₀}(S) - 1) ≤ C θ_{|S|} / N^{|S|-1}`."

* `cosh_sub_one_le`: `cosh x - 1 ≤ (x²/2) e^{B²/2}` for `|x| ≤ B`.
* `cosh_extSum_sub_one_le`: on the support, `cosh(β ∑_{i ∈ S, j ∈ V} v^Z_ij) - 1 ≤
  K ∑_i (r_i/τ_i^Z)²` (eq. (5.26) and `τ_i^Z ≤ d_{i,bad}`).
* `externalNormalization_sub_one_eq`: `g^Z_{ε₀}(S) - 1 = 𝔼_{𝖯^{+,ε₀,Z}_{{S}}}[cosh(β T) - 1]`
  (the reversal symmetry).
* `plusPartitionFunction_mul_external_le`: the integration leading to eqs. (A.43), (A.44)
  (`GeneralExpansion.lintegral_plus_root_log_le`):
  `𝖬^{+,Z}_{ε₀}(S)(g^Z_{ε₀}(S) - 1) ≤ (N C_{β,λ,ε₀})^{-k}
  (C₁ ε₀^{σk-2} N λ^{(2-β)k} R̄^{-2} + C₂ ε₀^{α(β)k} |V_bad| λ^{(2-β)k})`, with `C₁, C₂`
  independent of `ε₀`.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace ExpansionPlus

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open Hierarchical MultipoleIntegral GeneralExpansion BoundedUpper Multipole

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-! ### Elementary bounds -/

/-- `cosh x - 1 ≤ (x²/2) e^{B²/2}` for `|x| ≤ B`. -/
theorem cosh_sub_one_le {x B : ℝ} (hx : |x| ≤ B) :
    Real.cosh x - 1 ≤ x ^ 2 / 2 * Real.exp (B ^ 2 / 2) := by
  have h1 := Real.cosh_le_exp_half_sq x
  set t := x ^ 2 / 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have h2 : Real.exp t - 1 ≤ t * Real.exp t := by
    have := Real.add_one_le_exp (-t)
    have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos t]
  have hxB : x ^ 2 ≤ B ^ 2 := by
    have := sq_abs x
    rw [← this]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have h3 : Real.exp t ≤ Real.exp (B ^ 2 / 2) := Real.exp_le_exp.2 (by rw [ht]; linarith)
  calc Real.cosh x - 1 ≤ Real.exp t - 1 := by linarith
    _ ≤ t * Real.exp t := h2
    _ ≤ t * Real.exp (B ^ 2 / 2) := mul_le_mul_of_nonneg_left h3 ht0

/-- `τ_e^Z ≤ d_{e,bad}` on the support (eq. (5.9): `d_{e,bad} ≥ λ`). -/
theorem goodRadiusZ_le_badDistZ (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    goodRadiusZ p₀ β lam ε₀ V Z e ≤ badDistZ p₀ β lam ε₀ V Z e := by
  have hd := lam_le_badDistZ hlam hlamh hM hVZ he hr
  unfold goodRadiusZ
  refine max_le ?_ hd
  have : 0 ≤ badDistZ p₀ β lam ε₀ V Z e := hlam.le.trans hd
  linarith

/-- **The second-order bound on the external factor** (eq. (5.101), (5.26)
and `τ_i^Z ≤ d_{i,bad}`): on the support,
`cosh(β ∑_{i ∈ S, j ∈ V} v^Z_ij) - 1 ≤ K ∑_{i ∈ S} (r_i/τ_i^Z)²`, with
`K = (β C₁)² |S| / 2 · e^{(|β| C₁ |S|)²/2}`, `C₁` the constant of (5.26). -/
theorem cosh_extSum_sub_one_le (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ {N : ℕ} (lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      0 < lam → lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M → 3 ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ (S : Finset ℕ)
      (y : ({S} : Finset (Finset ℕ)).biUnion id → ℂ × ℂ),
      (∀ i, y i ∈ supportSet N p₀ β lam ε₀ ∧ IsGoodZ p₀ β lam M ε₀ V Z (y i)) →
        Real.cosh (β * extSum χ p₀ β lam ε₀ V Z S y) - 1 ≤
          (β * C₁) ^ 2 * S.card / 2 * Real.exp ((|β| * C₁ * S.card) ^ 2 / 2) *
            ∑ i, (‖(y i).1 - (y i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i)) ^ 2 := by
  obtain ⟨C₁, hC₁, hgb⟩ := sum_abs_interactionExtZ_le hχ p₀ β
  refine ⟨C₁, hC₁, fun {N} lam M ε₀ V Z hlam hlamh hM hM3 hVZ S y hy => ?_⟩
  have hcard : Fintype.card (({S} : Finset (Finset ℕ)).biUnion id) = S.card := by
    rw [Fintype.card_coe]
    simp
  set a : ({S} : Finset (Finset ℕ)).biUnion id → ℝ := fun i =>
    ‖(y i).1 - (y i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i)
  set T := extSum χ p₀ β lam ε₀ V Z S y
  -- each dipole: `|∑_j v^Z_ij| ≤ C₁ min(a_i, 1)`
  have hterm : ∀ i, |∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j| ≤ C₁ * a i ∧
      |∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j| ≤ C₁ := by
    intro i
    obtain ⟨hK, hG⟩ := hy i
    have hr : ‖(y i).1 - (y i).2‖ ≤ ε₀ * truncationScale p₀ β lam := hK.2
    have h1 := hgb lam M ε₀ V Z hlam hlamh hM hM3 hVZ (y i) hG hr
    have hd := lam_le_badDistZ hlam hlamh hM hVZ hG hr
    have hd0 : 0 < badDistZ p₀ β lam ε₀ V Z (y i) := hlam.trans_le hd
    have hτ0 : 0 < goodRadiusZ p₀ β lam ε₀ V Z (y i) :=
      goodRadiusZ_pos (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V) (Z := Z) hlam (y i)
    have hτd := goodRadiusZ_le_badDistZ hlam hlamh hM hVZ hG hr
    have hrd := norm_le_badDistZ hlam hlamh hM hVZ hG hr
    have habs : |∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j| ≤
        C₁ * (‖(y i).1 - (y i).2‖ / badDistZ p₀ β lam ε₀ V Z (y i)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← mul_div_assoc]
      exact h1
    refine ⟨habs.trans (mul_le_mul_of_nonneg_left ?_ hC₁.le), habs.trans ?_⟩
    · exact div_le_div_of_nonneg_left (norm_nonneg _) hτ0 hτd
    · exact mul_le_of_le_one_right hC₁.le ((div_le_one hd0).2 hrd)
  have ha0 : ∀ i, 0 ≤ a i := fun i => div_nonneg (norm_nonneg _)
    (goodRadiusZ_pos (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V) (Z := Z) hlam (y i)).le
  have hT1 : |T| ≤ C₁ * ∑ i, a i := by
    unfold T extSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hterm i).1
  have hT2 : |T| ≤ C₁ * S.card := by
    unfold T extSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j|
        ≤ ∑ _i : ({S} : Finset (Finset ℕ)).biUnion id, C₁ :=
          Finset.sum_le_sum fun i _ => (hterm i).2
      _ = C₁ * S.card := by rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_comm]
  have hx : |β * T| ≤ |β| * C₁ * S.card := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hT2 (abs_nonneg β)
  have hcosh := cosh_sub_one_le hx
  have hsq : (β * T) ^ 2 ≤ (β * C₁) ^ 2 * S.card * ∑ i, a i ^ 2 := by
    have h1 : T ^ 2 ≤ (C₁ * ∑ i, a i) ^ 2 := by
      rw [← sq_abs T]
      exact pow_le_pow_left₀ (abs_nonneg T) hT1 2
    have h2 : (∑ i, a i) ^ 2 ≤ S.card * ∑ i, a i ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq
        (s := (univ : Finset (({S} : Finset (Finset ℕ)).biUnion id)))
        (f := a)
      rwa [Finset.card_univ, hcard] at this
    calc (β * T) ^ 2 = β ^ 2 * T ^ 2 := by ring
      _ ≤ β ^ 2 * (C₁ * ∑ i, a i) ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg β)
      _ = (β * C₁) ^ 2 * (∑ i, a i) ^ 2 := by ring
      _ ≤ (β * C₁) ^ 2 * (S.card * ∑ i, a i ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  have hE : 0 ≤ Real.exp ((|β| * C₁ * S.card) ^ 2 / 2) := (Real.exp_pos _).le
  calc Real.cosh (β * T) - 1 ≤ (β * T) ^ 2 / 2 * Real.exp ((|β| * C₁ * S.card) ^ 2 / 2) := hcosh
    _ ≤ (β * C₁) ^ 2 * S.card * (∑ i, a i ^ 2) / 2 * Real.exp ((|β| * C₁ * S.card) ^ 2 / 2) := by
        gcongr
    _ = _ := by ring

/-- **`g^Z_{ε₀}(S) - 1 = 𝔼_{𝖯^{+,ε₀,Z}_{{S}}}[cosh(β T) - 1]`**, `T = ∑_{i ∈ S, j ∈ V} v^Z_ij`
(eq. (5.101), the reversal symmetry), when `𝖬^{+,Z}_{ε₀}(S) > 0`. the integrand is
integrable. -/
theorem externalNormalization_sub_one_eq (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hM3 : 3 ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {S : Finset ℕ} (hS : S.Nonempty)
    (hpos : 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) :
    Integrable (fun y => Real.cosh (β * extSum χ p₀ β lam ε₀ V Z S y) - 1)
        (plusModel χ N p₀ β lam M ε₀ L V Z {S}) ∧
      externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 =
        ∫ y, (Real.cosh (β * extSum χ p₀ β lam ε₀ V Z S y) - 1)
          ∂plusModel χ N p₀ β lam M ε₀ L V Z {S} := by
  obtain ⟨C, hC, hT⟩ := abs_extSum_le hχ p₀ β
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have : IsFiniteMeasure (plusModel χ N p₀ β lam M ε₀ L V Z {S}) :=
    h.isFiniteMeasure_modelHierarchical (M := M) (lam := lam) {S}
  set P := plusModel χ N p₀ β lam M ε₀ L V Z {S}
  have hTae : ∀ᵐ y ∂P, |extSum χ p₀ β lam ε₀ V Z S y| ≤ C * S.card := by
    filter_upwards [ae_plusModel hχ hlam hε₀ hN] with y hy
    exact hT lam M ε₀ V Z hlam hlamh hM hM3 hVZ S y hy
  have hint : ∀ s : ℝ, Integrable (fun y => Real.exp (s * extSum χ p₀ β lam ε₀ V Z S y)) P := by
    intro s
    refine Integrable.of_bound (Real.measurable_exp.comp
      (measurable_const.mul (measurable_extSum hχ hlam S))).aestronglyMeasurable
      (Real.exp (|s| * (C * S.card))) ?_
    filter_upwards [hTae] with y hy
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg s)
  have hcosh : ∀ y, Real.cosh (β * extSum χ p₀ β lam ε₀ V Z S y) - 1 =
      (Real.exp (β * extSum χ p₀ β lam ε₀ V Z S y) +
        Real.exp (-β * extSum χ p₀ β lam ε₀ V Z S y)) / 2 - 1 := by
    intro y
    rw [Real.cosh_eq, neg_mul]
  have hintc : Integrable (fun y => Real.cosh (β * extSum χ p₀ β lam ε₀ V Z S y) - 1) P := by
    simp_rw [hcosh]
    exact (((hint β).add (hint (-β))).div_const 2).sub (integrable_const 1)
  refine ⟨hintc, ?_⟩
  have h1 := externalNormalization_eq_integral_exp (L := L) (M := M) hχ hlam hε₀ hN (p₀ := p₀)
    (β := β) (V := V) (Z := Z) hS
  have h2 : externalNormalization χ N p₀ β lam M ε₀ L V Z S =
      ∫ y, Real.exp (-β * extSum χ p₀ β lam ε₀ V Z S y) ∂P := rfl
  have hone := integral_one_plusModel hχ hlam hε₀ hN hpos (L := L)
  simp_rw [hcosh]
  have hA := integral_sub (μ := P)
    (f := fun y => (Real.exp (β * extSum χ p₀ β lam ε₀ V Z S y) +
      Real.exp (-β * extSum χ p₀ β lam ε₀ V Z S y)) / 2) (g := fun _ => (1 : ℝ))
    (((hint β).add (hint (-β))).div_const 2) (integrable_const 1)
  have hB := integral_div (μ := P) (2 : ℝ) (fun y => Real.exp (β * extSum χ p₀ β lam ε₀ V Z S y) +
      Real.exp (-β * extSum χ p₀ β lam ε₀ V Z S y))
  have hC := integral_add (μ := P) (hint β) (hint (-β))
  rw [hA, hB, hC, ← h1, ← h2]
  have hone' : ∫ _y, (1 : ℝ) ∂P = 1 := hone
  rw [hone']
  ring

/-! ### The integration leading to (A.44) -/

theorem restrict_extendConfig (W : Finset ℕ) (y : W → ℂ × ℂ) :
    W.restrict (extendConfig W y) = y := by
  funext i
  simp [Finset.restrict, extendConfig, i.2]

open scoped Classical in
/-- **The pointwise bound of the root integrand**: on `(Λ²)^W`, `W = V_{{S}} = S`,
`bw_S · (r_{i₀}/τ_{i₀}^Z)² · ∏_i e^{β g_λ(r_i)} 𝟙_{r_i ≤ h} ≤
W₀^{k²} Ψ^k 𝟙_{𝓑} ∏_i e^{β g_λ(r_i)} 𝟙_{r_i ≤ h} rootZ(r_{i₀}, y_{i₀})`, with `W₀` the bond
bound of `v^Z` on the support (`stableWeightZ_le`) and `Ψ = e^{16|L|}`. -/
theorem blockWeight_mul_sq_le {W₀ : ℝ} (hW₀ : 1 ≤ W₀) (hlam : 0 < lam)
    (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z)
    (hbond : ∀ d e : ℂ × ℂ, OnSupportZ p₀ β lam M ε₀ V Z d → OnSupportZ p₀ β lam M ε₀ V Z e →
      stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) d e ≤ W₀)
    {S U : Finset ℕ} (hUS : U = S) (i₀ : U) {y : U → ℂ × ℂ}
    (hy : y ∈ Set.univ.pi fun _ => box N ×ˢ box N) :
    ENNReal.ofReal (blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam S (extendConfig U y) *
        (‖(y i₀).1 - (y i₀).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i₀)) ^ 2 *
        ∏ i, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
          (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator 1
            ((y i).1 - (y i).2))) ≤
      ENNReal.ofReal (W₀ ^ (S.card * S.card) * Real.exp (16 * |L|) ^ S.card) *
        (connInd M lam y * ((∏ i, cutWeight χ β lam (ε₀ * truncationScale p₀ β lam)
          ((y i).1 - (y i).2)) * rootZ p₀ β lam M ε₀ V Z ((y i₀).1 - (y i₀).2) (y i₀).2)) := by
  set h := ε₀ * truncationScale p₀ β lam with hh
  set c := extendConfig U y with hc
  have hcy : ∀ i : U, c i = y i := fun i => by simp [hc, extendConfig, i.2]
  -- the cutoff product vanishes unless every `r_i ≤ h`
  by_cases hall : ∀ i : U, (y i).1 - (y i).2 ∈ Metric.closedBall (0 : ℂ) h
  swap
  · simp only [not_forall] at hall
    obtain ⟨i, hi⟩ := hall
    rw [prod_eq_zero (mem_univ i) (by rw [Set.indicator_of_notMem hi, mul_zero]), mul_zero,
      ENNReal.ofReal_zero]
    exact zero_le
  have hr : ∀ i : U, ‖(y i).1 - (y i).2‖ ≤ h := fun i => by
    have := hall i
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  -- the block weight vanishes unless every dipole is good
  by_cases hgood : ∀ i : U, IsGoodZ p₀ β lam M ε₀ V Z (y i)
  swap
  · simp only [not_forall] at hgood
    obtain ⟨i, hi⟩ := hgood
    have hiS : (i : ℕ) ∈ S := hUS ▸ i.2
    have hw : blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam S c = 0 := by
      unfold blockWeightOf
      refine mul_eq_zero_of_right _ (prod_eq_zero hiS ?_)
      rw [hcy i]
      unfold dipoleWeightZ
      rw [ite_eq_right hi, mul_zero]
    rw [hw, zero_mul, zero_mul, ENNReal.ofReal_zero]
    exact zero_le
  have hsupp : ∀ i : U, OnSupportZ p₀ β lam M ε₀ V Z (y i) := fun i =>
    ⟨⟨hy i trivial, hr i⟩, hgood i⟩
  -- the block weight
  have hbw : blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam S c ≤
      W₀ ^ (S.card * S.card) * Real.exp (16 * |L|) ^ S.card *
        (if ConnOn S (linkedPairs M lam c S) then 1 else 0) := by
    unfold blockWeightOf
    have hP : ∏ p ∈ pairsOn S, stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c p.1) (c p.2) ≤
        W₀ ^ (S.card * S.card) := by
      refine prod_le_pow_of_le _ hW₀ (card_pairsOn_le S)
        (fun p _ => stableWeight_nonneg β _ _ _) fun p hp => ?_
      obtain ⟨h1, h2, -⟩ := mem_pairsOn.1 hp
      have e1 : c p.1 = y ⟨p.1, hUS ▸ h1⟩ := hcy ⟨p.1, hUS ▸ h1⟩
      have e2 : c p.2 = y ⟨p.2, hUS ▸ h2⟩ := hcy ⟨p.2, hUS ▸ h2⟩
      rw [e1, e2]
      exact hbond _ _ (hsupp _) (hsupp _)
    have hΨ : ∏ i ∈ S, dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) ≤ Real.exp (16 * |L|) ^ S.card := by
      rw [← Finset.prod_const]
      refine prod_le_prod₀ (fun i _ => dipoleWeightZ_nonneg _) fun i hi => ?_
      have e1 : c i = y ⟨i, hUS ▸ hi⟩ := hcy ⟨i, hUS ▸ hi⟩
      rw [e1]
      exact BoundedUpper.dipoleWeightZ_le hlam hlamh hM hVZ L (hr _)
    have hI : (0 : ℝ) ≤ if ConnOn S (linkedPairs M lam c S) then 1 else 0 := by
      split_ifs <;> norm_num
    calc (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
          (∏ p ∈ pairsOn S, stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c p.1) (c p.2)) *
          ∏ i ∈ S, dipoleWeightZ p₀ β lam M ε₀ L V Z (c i)
        ≤ (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) * W₀ ^ (S.card * S.card) *
            Real.exp (16 * |L|) ^ S.card := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hP hI) hΨ
            (prod_nonneg fun i _ => dipoleWeightZ_nonneg _) (mul_nonneg hI (by positivity))
      _ = _ := by ring
  -- connectivity in the coordinates of `U`
  have hconn : (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) =
      (connInd M lam y).toReal := by
    have hiff : ConnOn S (linkedPairs M lam c S) ↔
        (SimpleGraph.fromRel fun i j : U => MultipoleLinked M lam (y i) (y j)).Connected := by
      rw [← hUS, ← connected_fromRel_iff c U]
      simp only [hcy]
    unfold connInd
    by_cases hC : (SimpleGraph.fromRel fun i j : U => MultipoleLinked M lam (y i) (y j)).Connected
    · simp [hC, hiff.2 hC]
    · have hC' : ¬ ConnOn S (linkedPairs M lam c S) := fun h => hC (hiff.1 h)
      simp [hC, hC']
  -- the root factor
  have hroot : rootZ p₀ β lam M ε₀ V Z ((y i₀).1 - (y i₀).2) (y i₀).2 =
      ENNReal.ofReal ((‖(y i₀).1 - (y i₀).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i₀)) ^ 2) := by
    have hyy : ((y i₀).2 + ((y i₀).1 - (y i₀).2), (y i₀).2) = y i₀ := by
      ext <;> simp
    unfold rootZ
    rw [hyy, ite_eq_left_iff.2 (fun h => absurd (hgood i₀) h),
      ite_eq_left_iff.2 (fun h => absurd (hgood i₀) h), add_zero,
      Set.indicator_of_mem (hy i₀ trivial).2, Pi.one_apply, one_mul]
  have hcut : ∏ i, cutWeight χ β lam h ((y i).1 - (y i).2) =
      ENNReal.ofReal (∏ i, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
        (Metric.closedBall (0 : ℂ) h).indicator 1 ((y i).1 - (y i).2))) := by
    rw [ENNReal.ofReal_prod_of_nonneg (s := univ) (f := fun i : U =>
      Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
        (Metric.closedBall (0 : ℂ) h).indicator 1 ((y i).1 - (y i).2)) fun i _ =>
      mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
    refine prod_congr rfl fun i _ => ?_
    unfold cutWeight
    rw [Set.indicator_of_mem (hall i), Set.indicator_of_mem (hall i), Pi.one_apply, mul_one]
  rw [hroot, hcut]
  have hP0 : 0 ≤ ∏ i, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
      (Metric.closedBall (0 : ℂ) h).indicator 1 ((y i).1 - (y i).2)) :=
    prod_nonneg fun i _ => mul_nonneg (Real.exp_pos _).le
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hsq0 : 0 ≤ (‖(y i₀).1 - (y i₀).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i₀)) ^ 2 := sq_nonneg _
  have hconn' : connInd M lam y = ENNReal.ofReal (connInd M lam y).toReal := by
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (connInd_le_one y))]
  rw [hconn', ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hconn]
  have hI : (0 : ℝ) ≤ if ConnOn S (linkedPairs M lam c S) then 1 else 0 := by
    split_ifs <;> norm_num
  calc blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z) M
        lam S c * (‖(y i₀).1 - (y i₀).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i₀)) ^ 2 *
        ∏ i, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
          (Metric.closedBall (0 : ℂ) h).indicator 1 ((y i).1 - (y i).2))
      ≤ W₀ ^ (S.card * S.card) * Real.exp (16 * |L|) ^ S.card *
          (if ConnOn S (linkedPairs M lam c S) then 1 else 0) *
          (‖(y i₀).1 - (y i₀).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i₀)) ^ 2 *
          ∏ i, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
            (Metric.closedBall (0 : ℂ) h).indicator 1 ((y i).1 - (y i).2)) := by
        gcongr
    _ = _ := by ring

open scoped Classical in
/-- **`𝖬^{+,Z}_{ε₀}(S) 𝔼_{𝖯^{+,ε₀,Z}_{{S}}}[(r_{i₀}/τ_{i₀}^Z)²]` as a root integral** (the integration
leading to (A.44)): it is at most `W₀^{k²} Ψ^k (N C_{β,λ,ε₀})^{-k}
∫ 𝟙_{𝓑} ∏_i e^{β g_λ(r_i)} 𝟙_{r_i ≤ h} rootZ(r_{i₀}, y_{i₀})`, an inequality in `[0, ∞]`. -/
theorem plusPartitionFunction_mul_integral_sq_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {W₀ : ℝ}
    (hW₀ : 1 ≤ W₀)
    (hbond : ∀ d e : ℂ × ℂ, OnSupportZ p₀ β lam M ε₀ V Z d → OnSupportZ p₀ β lam M ε₀ V Z e →
      stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) d e ≤ W₀)
    (S : Finset ℕ) (i₀ : ({S} : Finset (Finset ℕ)).biUnion id) :
    ENNReal.ofReal (plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
        ∫ y, (‖(y i₀).1 - (y i₀).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i₀)) ^ 2
          ∂plusModel χ N p₀ β lam M ε₀ L V Z {S}) ≤
      ENNReal.ofReal (W₀ ^ (S.card * S.card) * Real.exp (16 * |L|) ^ S.card *
          ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ S.card) *
        ∫⁻ y : ({S} : Finset (Finset ℕ)).biUnion id → ℂ × ℂ, connInd M lam y *
          ((∏ i, cutWeight χ β lam (ε₀ * truncationScale p₀ β lam) ((y i).1 - (y i).2)) *
            rootZ p₀ β lam M ε₀ V Z ((y i₀).1 - (y i₀).2) (y i₀).2) := by
  have hUS : (({S} : Finset (Finset ℕ)).biUnion id) = S := by simp
  set μ := cutoffDipoleMeasure χ N p₀ β lam ε₀ with hμ
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  set f : ((({S} : Finset (Finset ℕ)).biUnion id) → ℂ × ℂ) → ℝ := fun y =>
    (‖(y i₀).1 - (y i₀).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i₀)) ^ 2 with hf
  have hfm : Measurable f := by
    have hτ : Measurable fun y : (({S} : Finset (Finset ℕ)).biUnion id) → ℂ × ℂ =>
        goodRadiusZ p₀ β lam ε₀ V Z (y i₀) :=
      (continuous_goodRadiusZ p₀ β lam ε₀ V Z).measurable.comp (measurable_pi_apply i₀)
    exact (((measurable_pi_apply i₀).fst.sub (measurable_pi_apply i₀).snd).norm.div hτ).pow_const 2
  have hf0 : ∀ y, 0 ≤ f y := fun y => sq_nonneg _
  -- the density form
  have e1 := h.prod_mul_integral_modelHierarchical (M := M) (lam := lam) (X := {S}) (f := f) hfm
  simp only [Finset.prod_singleton] at e1
  set bw := blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z)
    M lam S with hbw
  set Φ : (ℕ → ℂ × ℂ) → ℝ := fun c =>
    bw c * f (((({S} : Finset (Finset ℕ)).biUnion id)).restrict c) with hΦ
  have hΦm : Measurable Φ := (h.measurable_blockWeightOf M lam S).mul
    (hfm.comp (Finset.measurable_restrict (({S} : Finset (Finset ℕ)).biUnion id)))
  have hΦdep : DependsOn Φ
      (((({S} : Finset (Finset ℕ)).biUnion id) : Finset ℕ) : Set ℕ) := by
    intro c c' hcc'
    simp only [hΦ]
    have h1 : bw c = bw c' := dependsOn_blockWeightOf M lam S fun i hi =>
      hcc' i (by rw [hUS]; exact hi)
    have h2 : ((({S} : Finset (Finset ℕ)).biUnion id)).restrict c =
        ((({S} : Finset (Finset ℕ)).biUnion id)).restrict c' := by
      funext i
      exact hcc' i i.2
    rw [h1, h2]
  have hΦ0 : ∀ c, 0 ≤ Φ c := fun c => mul_nonneg
    (blockWeightOf_nonneg M lam (fun _ => dipoleWeightZ_nonneg _) S c) (hf0 _)
  have hLHS : plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
      ∫ y, f y ∂plusModel χ N p₀ β lam M ε₀ L V Z {S} =
      ∫ y, Φ (extendConfig (({S} : Finset (Finset ℕ)).biUnion id) y)
        ∂Measure.pi (fun _ : (({S} : Finset (Finset ℕ)).biUnion id) => μ) := by
    rw [← integral_labelField_eq_pi hΦm hΦdep]
    exact e1
  rw [hLHS]
  have hle1 : ENNReal.ofReal (∫ y, Φ (extendConfig (({S} : Finset (Finset ℕ)).biUnion id) y)
        ∂Measure.pi (fun _ : (({S} : Finset (Finset ℕ)).biUnion id) => μ)) ≤
      ∫⁻ y, ENNReal.ofReal (Φ (extendConfig (({S} : Finset (Finset ℕ)).biUnion id) y))
        ∂Measure.pi (fun _ : (({S} : Finset (Finset ℕ)).biUnion id) => μ) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hΦ0 _)
      (hΦm.comp (measurable_extendConfig _)).aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  refine hle1.trans ?_
  rw [lintegral_pi_cutoff_eq (p₀ := p₀) (β := β) hχ hlam hε₀ hN
    (({S} : Finset (Finset ℕ)).biUnion id)
    (f := fun y => Φ (extendConfig (({S} : Finset (Finset ℕ)).biUnion id) y))
    (hΦm.comp (measurable_extendConfig _))]
  have hcardU : ((({S} : Finset (Finset ℕ)).biUnion id)).card = S.card := by rw [hUS]
  rw [hcardU, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal _) (ENNReal.ofReal _),
    mul_assoc]
  refine mul_le_mul' le_rfl ?_
  refine (setLIntegral_mono' (measurableSet_pi_box_prod N) fun y hy => ?_).trans
    ((setLIntegral_le_lintegral _ _).trans
      (le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)))
  have hres : ((({S} : Finset (Finset ℕ)).biUnion id)).restrict
      (extendConfig (({S} : Finset (Finset ℕ)).biUnion id) y) = y :=
    restrict_extendConfig (({S} : Finset (Finset ℕ)).biUnion id) y
  simp only [hΦ, hres, hf]
  exact blockWeight_mul_sq_le hW₀ hlam hlamh hM hVZ hbond hUS i₀ hy

/-! ### The bound on `𝖬^{+,Z}_{ε₀}(S) (g^Z_{ε₀}(S) - 1)` -/

/-- **`0 ≤ 𝖬^{+,Z}_{ε₀}(S)(g^Z_{ε₀}(S) - 1) ≤ C θ_{|S|} / N^{|S|-1}`** before the scaling
(proof of Proposition 5.19): for `β > 2`, `1 ≤ k`, `M ≥ 3`, `L`, `p₀`, there are
`C₁, C₂ ≥ 0` (depending on `χ, β, M, L, k, p₀`, not on `ε₀`) such that for `0 < λ ≤ ε₀ ≤ 1`,
`3^{p(β)} ≤ M`, `N ≥ 1`, every frozen configuration `(V, Z)` and every `S` with `|S| = k` and
`𝖬^{+,Z}_{ε₀}(S) > 0`,
`0 ≤ 𝖬^{+,Z}_{ε₀}(S)(g^Z_{ε₀}(S) - 1) ≤ (N C_{β,λ,ε₀})^{-k}
(C₁ ε₀^{σk-2} N λ^{(2-β)k} R̄^{-2} + C₂ ε₀^{α(β)k} |V_bad| λ^{(2-β)k})`. -/
theorem plusPartitionFunction_mul_external_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ}
    (hk : 1 ≤ k) (hM3 : 3 ≤ M) (L : ℝ) (p₀ : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (ε₀ lam : ℝ), 0 < lam → lam ≤ ε₀ → ε₀ ≤ 1 →
      (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ (N : ℕ), 1 ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      badPointsOn p₀ β lam M ε₀ V Z = V → ∀ S : Finset ℕ, S.card = k →
      0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S →
        0 ≤ plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
            (externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1) ∧
          plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
              (externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1) ≤
            ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ k *
              (C₁ * ε₀ ^ (tailSigma p₀ β k * k - 2) * N *
                  (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) +
                C₂ * ε₀ ^ (alphaExponent β * k) * V.card * lam ^ ((2 - β) * k)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨Cg, hCg, hcosh⟩ := cosh_extSum_sub_one_le hχ p₀ β
  obtain ⟨W₀', hW₀', hbond⟩ := stableWeightZ_le hχ β hβ0
  obtain ⟨R₁, R₂, hR₁, hR₂, hroot⟩ := lintegral_plus_root_log_le (χ := χ) hχ hβ hk hM0 p₀
  set W₀ := max W₀' 1
  have hW₀ : 1 ≤ W₀ := le_max_right _ _
  set K := (β * Cg) ^ 2 * k / 2 * Real.exp ((|β| * Cg * k) ^ 2 / 2)
  have hK : 0 ≤ K := by positivity
  set A := W₀ ^ (k * k) * Real.exp (16 * |L|) ^ k
  have hA : 0 ≤ A := by positivity
  refine ⟨K * k * A * R₁, K * k * A * R₂, by positivity, by positivity,
    fun ε₀ lam hlam hlε hε₁ hMp N hN V Z hV S hS hpos => ?_⟩
  have hε₀ : 0 < ε₀ := hlam.trans_le hlε
  have hlam1 : lam ≤ 1 := hlε.trans hε₁
  have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
  have hlamh : lam ≤ ε₀ * truncationScale p₀ β lam :=
    hlε.trans (le_mul_of_one_le_right hε₀.le hR1)
  have hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z := hV.symm.subset
  have hSne : S.Nonempty := Finset.card_pos.1 (hS ▸ hk)
  have hg1 := one_le_externalNormalization hχ hlam hε₀ hN hlamh hMp hM3 hVZ hSne hpos (L := L)
  refine ⟨mul_nonneg hpos.le (by linarith), ?_⟩
  have hbond' : ∀ d e : ℂ × ℂ, OnSupportZ p₀ β lam M ε₀ V Z d → OnSupportZ p₀ β lam M ε₀ V Z e →
      stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) d e ≤ W₀ := fun d e hd he =>
    (hbond p₀ lam M ε₀ V Z hlam hlamh hMp hVZ d e hd he).trans (le_max_left _ _)
  obtain ⟨hint, heq⟩ := externalNormalization_sub_one_eq (L := L) hχ hlam hε₀ hN hlamh hMp hM3 hVZ
    hSne hpos
  have hU : ({S} : Finset (Finset ℕ)).biUnion id = S := by simp
  have hcardU : Fintype.card (({S} : Finset (Finset ℕ)).biUnion id) = k := by
    rw [Fintype.card_coe, hU, hS]
  set P := plusModel χ N p₀ β lam M ε₀ L V Z {S}
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have : IsFiniteMeasure P := h.isFiniteMeasure_modelHierarchical (M := M) (lam := lam) {S}
  set f : ({S} : Finset (Finset ℕ)).biUnion id →
      (({S} : Finset (Finset ℕ)).biUnion id → ℂ × ℂ) → ℝ :=
    fun i₀ y => (‖(y i₀).1 - (y i₀).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (y i₀)) ^ 2 with hf
  have hfm : ∀ i₀, Measurable (f i₀) := by
    intro i₀
    have hτ : Measurable fun y : ({S} : Finset (Finset ℕ)).biUnion id → ℂ × ℂ =>
        goodRadiusZ p₀ β lam ε₀ V Z (y i₀) :=
      (continuous_goodRadiusZ p₀ β lam ε₀ V Z).measurable.comp (measurable_pi_apply i₀)
    exact (((measurable_pi_apply i₀).fst.sub (measurable_pi_apply i₀).snd).norm.div hτ).pow_const 2
  have hfint : ∀ i₀, Integrable (f i₀) P := by
    intro i₀
    refine Integrable.of_bound (hfm i₀).aestronglyMeasurable 16 ?_
    filter_upwards [ae_plusModel hχ hlam hε₀ hN] with y hy
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_div_goodRadiusZ_le hlam hlamh hMp hVZ (hy i₀).2 (hy i₀).1.2
  -- `g - 1 ≤ K ∑_i 𝔼[(r_i/τ_i)²]`
  have hstep : externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 ≤ K * ∑ i₀, ∫ y, f i₀ y ∂P := by
    rw [heq, ← integral_finsetSum _ fun i₀ _ => hfint i₀, ← integral_const_mul]
    refine integral_mono_ae hint ((integrable_finsetSum _ fun i₀ _ => hfint i₀).const_mul K) ?_
    filter_upwards [ae_plusModel hχ hlam hε₀ hN] with y hy
    have := hcosh lam M ε₀ V Z hlam hlamh hMp hM3 hVZ S y hy
    rw [hS] at this
    exact this
  -- each term
  have hterm : ∀ i₀, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S * ∫ y, f i₀ y ∂P ≤
      A * ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ k *
        (R₁ * ε₀ ^ (tailSigma p₀ β k * k - 2) * N *
            (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) +
          R₂ * ε₀ ^ (alphaExponent β * k) * V.card * lam ^ ((2 - β) * k)) := by
    intro i₀
    have h1 := plusPartitionFunction_mul_integral_sq_le (L := L) hχ hlam hε₀ hN hlamh hMp hVZ hW₀
      hbond' S i₀
    have h2 := hroot ε₀ lam hlam hlε hε₁ hMp N V Z hV (({S} : Finset (Finset ℕ)).biUnion id)
      (by rw [hU, hS]) i₀
    rw [hS] at h1
    have h3 := h1.trans (mul_le_mul' le_rfl h2)
    have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    exact h3
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  set B := A * ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ k *
        (R₁ * ε₀ ^ (tailSigma p₀ β k * k - 2) * N *
            (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) +
          R₂ * ε₀ ^ (alphaExponent β * k) * V.card * lam ^ ((2 - β) * k)) with hB
  calc plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
        (externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1)
      ≤ plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S * (K * ∑ i₀, ∫ y, f i₀ y ∂P) :=
        mul_le_mul_of_nonneg_left hstep hpos.le
    _ = K * ∑ i₀, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S * ∫ y, f i₀ y ∂P := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i₀ _ => by ring
    _ ≤ K * ∑ _i₀ : ({S} : Finset (Finset ℕ)).biUnion id, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i₀ _ => hterm i₀) hK
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, hcardU, nsmul_eq_mul, hB]
        ring

end ExpansionPlus

end UpperBound

end MultipoleBKT

end
