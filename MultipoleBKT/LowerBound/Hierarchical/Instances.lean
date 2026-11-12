/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.ActivityIntegral
public import MultipoleBKT.LowerBound.Hierarchical.ScreenedBound

/-!
# The paper's models; Corollary 4.61 (`𝖪^mult = 𝖪^0_∞`)

Definitions 4.11–4.15 (Definition 4.11) and Corollary 4.61.

The three models of Section 4 satisfy the hypotheses `ModelHyp` of
`MultipoleBKT.LowerBound.Hierarchical.Activity`:

* `modelHyp_infinity`: `(μ_{β,λ}, v, 1)` on `K = Λ²` (`ε₀ = ∞`), for `λ > 0`, `N ≥ 1`;
* `modelHyp_zero`: `(μ_{β,λ,ε₀}, v, 1)` on `K = Λ²` (the model `0`), for `ε₀ > 0`;
* `modelHyp_minus`: `(μ_{β,λ,ε₀}, ṽ, e^{-L |x - y|²/(ε₀ R̄)²})` on
  `K = Λ² ∩ {|x - y| ≤ ε₀ R̄}` (the model `-`), for `ε₀ > 0` and `λ ≤ ε₀ R̄` (the screening radius
  `τ₀ = 8 ε₀ R̄` exceeds `8λ`, as in (3.53)).

**Corollary 4.61** (`zeroActivityInf_eq_multipoleActivity`): for every subpartition `X`,
`𝖪^mult_{β,λ}(X) = 𝖪^0_∞(X)`, for `M ≥ 1` (the paper has `M > 20`), `λ > 0`, `N ≥ 1`. The proof
is the paper's, with the induction on `|X|` replaced by the compact form of the activity series:
`(∏_{S ∈ X} 𝖬(S)) 𝖪^0_∞(X)` and `(∏_{S ∈ X} 𝖬(S)) 𝖪^mult(X)` are the same connected integral
`𝔼[(∏_{B ∈ X} 𝟙_{𝓑_B} ∏_{i<j ∈ B} e^{-β v_ij} 𝟙_{𝒜_ij}) ∑_{E ∈ 𝖤^X} ∏_{ij ∈ E}
(e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1)]` (`ModelHyp.prod_mul_modelActivity` and
`MultipoleBKT.Multipole.multipoleConnIntegral_eq`), and `𝖬(S) > 0`.
-/

@[expose] public section

open MeasureTheory Finset Metric
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

/-! ### The hypotheses for the three models -/

/-- `-β v` is bounded above on `Λ² × Λ²`. -/
theorem exists_neg_mul_dipoleInteraction_le (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (N : ℕ) : ∃ C, ∀ d ∈ box N ×ˢ box N, ∀ e ∈ box N ×ˢ box N,
      -β * dipoleInteraction χ lam d e ≤ C := by
  have hc := (continuous_dipoleInteraction hχ hlam).continuousOn
    (s := (box N ×ˢ box N) ×ˢ (box N ×ˢ box N))
  obtain ⟨B, hB⟩ :=
    ((isCompact_box_prod N).prod (isCompact_box_prod N)).exists_bound_of_continuousOn hc
  refine ⟨|β| * |B|, fun d hd e he => ?_⟩
  have hv : |dipoleInteraction χ lam d e| ≤ |B| := by
    have := hB (d, e) ⟨hd, he⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self B)
  calc -β * dipoleInteraction χ lam d e ≤ |-β * dipoleInteraction χ lam d e| := le_abs_self _
    _ = |β| * |dipoleInteraction χ lam d e| := by rw [abs_mul, abs_neg]
    _ ≤ |β| * |B| := by gcongr

/-- The model `(μ_{β,λ}, v, 1)` of `ε₀ = ∞`. -/
theorem modelHyp_infinity (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hN : 1 ≤ N) :
    ModelHyp (dipoleMeasure χ N β lam) β (dipoleInteraction χ lam) (fun _ => 1)
      (box N ×ˢ box N) where
  isProbabilityMeasure := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  ae_mem := ae_mem_box_dipoleMeasure χ N β lam
  measurable_w := measurable_dipoleInteraction hχ hlam
  measurable_ψ := measurable_const
  nonneg_ψ := fun _ => zero_le_one
  bdd_w := exists_neg_mul_dipoleInteraction_le hχ hlam β N
  bdd_ψ := ⟨1, fun _ _ => le_rfl⟩

/-- The model `0`: `(μ_{β,λ,ε₀}, v, 1)`. -/
theorem modelHyp_zero (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) :
    ModelHyp (cutoffDipoleMeasure χ N p₀ β lam ε₀) β (dipoleInteraction χ lam) (fun _ => 1)
      (box N ×ˢ box N) where
  isProbabilityMeasure := isProbabilityMeasure_cutoffDipoleMeasure hχ hlam β hε₀ hN
  ae_mem := (ae_cutoffDipoleMeasure χ N p₀ β lam ε₀).mono fun _ h => h.1
  measurable_w := measurable_dipoleInteraction hχ hlam
  measurable_ψ := measurable_const
  nonneg_ψ := fun _ => zero_le_one
  bdd_w := exists_neg_mul_dipoleInteraction_le hχ hlam β N
  bdd_ψ := ⟨1, fun _ _ => le_rfl⟩

/-- The set `Λ² ∩ {|x - y| ≤ ε₀ R̄}` of the dipoles charged by `μ_{β,λ,ε₀}`. -/
def cutoffSet (N p₀ : ℕ) (β lam ε₀ : ℝ) : Set (ℂ × ℂ) :=
  {d | d ∈ box N ×ˢ box N ∧ ‖d.1 - d.2‖ ≤ ε₀ * truncationScale p₀ β lam}

theorem measurable_gaussianWeight (p₀ : ℕ) (β lam ε₀ L : ℝ) :
    Measurable (gaussianWeight p₀ β lam ε₀ L) := by
  unfold gaussianWeight
  fun_prop

/-- The model `-`: `(μ_{β,λ,ε₀}, ṽ, e^{-L |x - y|² / (ε₀ R̄)²})`, for `λ ≤ ε₀ R̄`. -/
theorem modelHyp_minus (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) (L : ℝ) :
    ModelHyp (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
      (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
      (gaussianWeight p₀ β lam ε₀ L) (cutoffSet N p₀ β lam ε₀) where
  isProbabilityMeasure := isProbabilityMeasure_cutoffDipoleMeasure hχ hlam β hε₀ hN
  ae_mem := ae_cutoffDipoleMeasure χ N p₀ β lam ε₀
  measurable_w := measurable_screenedInteraction hχ hlam _
  measurable_ψ := measurable_gaussianWeight p₀ β lam ε₀ L
  nonneg_ψ := fun _ => (Real.exp_pos _).le
  bdd_w := by
    have hR : 0 < ε₀ * truncationScale p₀ β lam := mul_pos hε₀ (Appendix.truncationScale_pos hlam)
    obtain ⟨C, hC⟩ := exists_abs_screenedInteraction_le hχ hlam
      (τ := 8 * ε₀ * truncationScale p₀ β lam) (by nlinarith)
    refine ⟨|β| * C, fun d hd e he => ?_⟩
    have hτ : 8 * ε₀ * truncationScale p₀ β lam / 8 = ε₀ * truncationScale p₀ β lam := by ring
    have hv := hC d e (by rw [hτ, norm_sub_rev]; exact hd.2) (by rw [hτ, norm_sub_rev]; exact he.2)
    unfold upperBoundInteraction
    calc -β * screenedInteraction χ lam (8 * ε₀ * truncationScale p₀ β lam) d e
        ≤ |-β * screenedInteraction χ lam (8 * ε₀ * truncationScale p₀ β lam) d e| :=
          le_abs_self _
      _ = |β| * |screenedInteraction χ lam (8 * ε₀ * truncationScale p₀ β lam) d e| := by
          rw [abs_mul, abs_neg]
      _ ≤ |β| * C := by gcongr
  bdd_ψ := by
    have hR : 0 < ε₀ * truncationScale p₀ β lam := mul_pos hε₀ (Appendix.truncationScale_pos hlam)
    refine ⟨Real.exp |L|, fun d hd => Real.exp_le_exp.2 ?_⟩
    have h1 : ‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hd.2 2
    have h0 : 0 ≤ ‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2 := by positivity
    calc -L * (‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2)
        ≤ |L| * (‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2) :=
          mul_le_mul_of_nonneg_right (neg_le_abs L) h0
      _ ≤ |L| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg L)
      _ = |L| := mul_one _

/-! ### Corollary 4.61 -/

open scoped Classical in
theorem stableWeight_dipoleInteraction (χ : ℂ → ℝ) (β lam : ℝ) (d e : ℂ × ℂ) :
    stableWeight β (dipoleInteraction χ lam) d e = stablePairWeight χ β lam d e := rfl

theorem blockWeightOf_infinity (χ : ℂ → ℝ) (β lam M : ℝ) :
    blockWeightOf β (dipoleInteraction χ lam) (fun _ => 1) M lam = blockWeight χ β lam M := by
  funext B c
  simp only [blockWeightOf, blockWeight, Finset.prod_const_one, mul_one,
    stableWeight_dipoleInteraction]

theorem unlinkedBondOf_infinity (χ : ℂ → ℝ) (β lam : ℝ) (hM : 1 ≤ M) :
    unlinkedBondOf β (dipoleInteraction χ lam) M lam = unlinkedBond χ β lam M := by
  funext d e
  rw [unlinkedBondOf, unlinkedBond, unlinkedPairWeight_eq hM, stableWeight_dipoleInteraction]
  split_ifs <;> simp

/-- **Corollary 4.61**: for
every subpartition `X`, `𝖪^mult_{β,λ}(X) = 𝖪^0_∞(X)` (the activity of Definition 4.15 at
`ε₀ = ∞`). The paper has `M > 20`; `M ≥ 1` suffices (`𝓑_ij^c ⊂ 𝒜_ij`, Remark 4.6). -/
theorem zeroActivityInf_eq_multipoleActivity (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    zeroActivityInf χ N β lam M X = multipoleActivity χ N β lam M X := by
  by_cases h2 : 2 ≤ X.card
  · have h := modelHyp_infinity hχ hlam β hN
    have hM0 : 0 < M := by linarith
    have hpos : 0 < ∏ S ∈ X, multipolePartitionFunction χ N β lam M S :=
      Finset.prod_pos fun S hS => multipolePartitionFunction_pos hχ hlam β hM0 hN (hX.1 S hS)
    have key := h.prod_mul_modelActivity (M := M) (lam := lam) hX h2
    simp only [modelPartitionFunction_dipoleMeasure] at key
    rw [blockWeightOf_infinity, unlinkedBondOf_infinity χ β lam hM] at key
    have hconn : connIntegralOf (dipoleMeasure χ N β lam) (blockWeight χ β lam M)
        (unlinkedBond χ β lam M) X = multipoleConnIntegral χ N β lam M X := rfl
    rw [hconn, multipoleConnIntegral_eq hχ hlam hN hM0 β hX h2] at key
    exact mul_left_cancel₀ hpos.ne' key
  · have h1 : X.card ≤ 1 := by omega
    rw [zeroActivityInf, modelActivity_eq_zero_of_card_le_one _ _ _ _ _ _ h1,
      multipoleActivity_eq_zero_of_card_le_one χ N β lam M h1]

end Hierarchical

end MultipoleBKT

end
