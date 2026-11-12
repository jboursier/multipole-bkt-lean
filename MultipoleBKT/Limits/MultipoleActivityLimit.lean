/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.MultIntegrable
public import MultipoleBKT.Limits.RouteBase.Activity
import MultipoleBKT.Limits.RouteDirect.BlockIntegrable

/-!
# The limits of the multipole activities

See Lemma 4.26, third
assertion (4.54): for a subpartition `X` with `|V_X| ≤ p*(β)`,
`N^{|X|-1} 𝖪^mult_{β,λ}(X)` converges.

For a subpartition `X` of `ℕ` the labels are `V_X = ⋃ X` and the blocks are the elements of `X`
(`blockOf`). The activity is a ratio of box integrals (`multipoleActivity_eq_box`):
`𝖪^mult(X) = ∑_{E ∈ 𝖤^X} ∫_{(Λ²)^{V_X}} multBox_E / ∏_{S ∈ X} ∫_{(Λ²)^S} Φ_S`. Replacing each
numerator by the box integral of the averaged integrand `symBox_E` (equal, by reversal
invariance), the box-average limit (`tendsto_boxAverage`) applies to numerator and denominator:

* `exists_tendsto_multipoleActivity`: `N^{|X|-1} 𝖪^mult(X)` converges, for `IsSubpartition X`,
  `|V_X| ≤ p*(β)`, `λ > 0`, `M ≥ 1`.
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

namespace RouteDirect

variable {X : Finset (Finset ℕ)}

open scoped Classical in
/-- Translation averaging for one full block-averaged graph numerator. -/
theorem tendsto_multBox_div {I B : Type*} [Fintype I] [LinearOrder I] [DecidableEq I]
    [Fintype B] [DecidableEq B] [Nonempty I]
    (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam) (hM : 1 ≤ M)
    (hk : (Fintype.card I : ℕ∞) ≤ pStar β) (blk : I → B) (hblk : Function.Surjective blk)
    (E : SimpleGraph I) (hinter : ∀ i j, E.Adj i j → blk i ≠ blk j)
    (hconn : ∀ b b', (nodeGraph (Sym2.map blk) E.edgeFinset).Reachable b b') (root : I) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∫ c in boxConfig I N, multBox χ β lam M blk E c)
      atTop (𝓝 (∫ c, anchorR root c * symBox χ β lam M blk E c)) := by
  have h := tendsto_boxAverage root (measurable_symBox hχ hlam blk E)
    (symBox_translate blk E)
    (integrable_anchor_symBox_log hχ hβ hlam hM hk blk hblk E hinter hconn root)
  exact h.congr fun N => by rw [integral_boxConfig_symBox hχ (by linarith) hlam hM]

open scoped Classical in
/-- The direct numerator and denominator limits, with the full block average
integrated through the separate trees and logarithmic bounds. -/
theorem tendsto_multipoleActivity_integral (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 1 ≤ M) (hX : IsSubpartition X)
    (hk : ((X.biUnion id).card : ℕ∞) ≤ pStar β) (root : X.biUnion id)
    (roots : ∀ S : X, S.val) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((X.card : ℤ) - 1) *
      multipoleActivity χ N β lam M X) atTop
        (𝓝 (multipoleIntegralCoefficient χ β lam M X root roots)) := by
  let V := X.biUnion id
  have hVne : Nonempty V := ⟨root⟩
  let i₀ : V := root
  have hkV : (Fintype.card V : ℕ∞) ≤ pStar β := by rwa [Fintype.card_coe]
  -- the limits of the block normalizations
  let I : X → ℝ := fun S => ∫ c, anchorR (roots S) c * multipoleBox χ β lam M c
  let Efil := (Finset.univ : Finset (SimpleGraph V)).filter (fun E =>
    (∀ i j : V, E.Adj i j → ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
      E.edgeSet.Nonempty ∧
      (E ⊔ SimpleGraph.fromRel fun i j : V => ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected)
  have hsub : ∀ S ∈ X, (S.card : ℕ∞) ≤ pStar β := fun S hS =>
    le_trans (by exact_mod_cast Finset.card_le_card (subset_biUnion_of_mem id hS)) hk
  -- the numerator
  have hnum : Tendsto (fun N : ℕ => ∑ E ∈ Efil,
      (1 / (N : ℝ)) * ∫ c in boxConfig V N, multBox χ β lam M (blockOf X) E c) atTop
      (𝓝 (∑ E ∈ Efil, ∫ c, anchorR i₀ c * symBox χ β lam M (blockOf X) E c)) := by
    refine tendsto_finsetSum _ fun E hE => ?_
    obtain ⟨hE1, -, hE3⟩ := (mem_filter.1 hE).2
    exact tendsto_multBox_div hχ hβ hlam hM hkV (blockOf X) (blockOf_surjective hX) E
      (adj_blockOf_ne hX hE1) (reachable_blockOf hX hE1 hE3) i₀
  -- the denominator
  have hden : Tendsto (fun N : ℕ => ∏ S ∈ X,
      (1 / (N : ℝ)) * ∫ c in boxConfig S N, multipoleBox χ β lam M c) atTop
      (𝓝 (∏ S : X, I S)) := by
    simp_rw [← Finset.prod_coe_sort X]
    refine tendsto_finsetProd _ fun S _ => ?_
    have hne : Nonempty (S : Finset ℕ) := ⟨roots S⟩
    have hk' : (Fintype.card (S : Finset ℕ) : ℕ∞) ≤ pStar β := by
      rw [Fintype.card_coe]; exact hsub S S.property
    exact tendsto_boxAverage (roots S) (measurable_multipoleBox hχ hlam β M)
      translationInvariant_multipoleBox
      (integrable_anchor_multipoleBox hχ hβ hlam (by linarith) hk' _)
  have hden0 : (∏ S : X, I S) ≠ 0 := by
    refine (prod_pos fun S _ => ?_).ne'
    exact multipoleBox_limit_pos hχ hβ hlam (by linarith) (hsub S S.property) (roots S)
  have hcoeff : ((∑ E ∈ Efil,
      ∫ c, anchorR i₀ c * symBox χ β lam M (blockOf X) E c) / ∏ S : X, I S) =
      multipoleIntegralCoefficient χ β lam M X root roots := by
    unfold multipoleIntegralCoefficient
    apply congrArg₂ (fun a b : ℝ => a / b)
    · apply sum_congr
      · ext E
        simp only [Efil, Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      · intro E _
        rfl
    · rfl
  have hlim := hnum.div hden hden0
  rw [hcoeff] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  -- the algebra
  simp only [Pi.div_apply]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hC := natCast_mul_dipoleNormalization_pos hχ hlam β hN
  have hM_eq : ∏ S ∈ X, multipolePartitionFunction χ N β lam M S =
      ((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ ^ (X.biUnion id).card *
        ∏ S ∈ X, ∫ c in boxConfig S N, multipoleBox χ β lam M c := by
    rw [card_biUnion_eq_sum hX, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    exact prod_congr rfl fun S _ => multipolePartitionFunction_eq_box hχ hlam hN S
  have hJ0 : ∏ S ∈ X, ∫ c in boxConfig S N, multipoleBox χ β lam M c ≠ 0 := by
    refine prod_ne_zero_iff.2 fun S hS => ?_
    have := multipolePartitionFunction_pos (M := M) hχ hlam β (by linarith) hN (hX.1 S hS)
    rw [multipolePartitionFunction_eq_box hχ hlam hN] at this
    exact right_ne_zero_of_mul this.ne'
  have hNC : (N : ℝ) * dipoleNormalization χ N β lam ≠ 0 := hC.ne'
  rw [multipoleActivity_eq_box hχ hlam hN hX, hM_eq, ← Finset.mul_sum, prod_mul_distrib, prod_const,
    zpow_sub_one₀ hN0.ne', zpow_natCast]
  field_simp
  rw [← mul_pow, one_div_mul_cancel hN0.ne', one_pow, one_mul]
  apply sum_congr
  · ext E
    simp only [Efil, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  · intro E _
    rfl

end RouteDirect

section Limit

variable {X : Finset (Finset ℕ)}

open scoped Classical in
/-- Direct translation averaging identifies the multipole coefficient.
See (4.54),
and the proof of Lemma 4.26. -/
theorem tendsto_multipoleActivity_integral (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 1 ≤ M) (hX : IsSubpartition X)
    (hk : ((X.biUnion id).card : ℕ∞) ≤ pStar β) (root : X.biUnion id)
    (roots : ∀ S : X, S.val) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((X.card : ℤ) - 1) *
      multipoleActivity χ N β lam M X) atTop
        (𝓝 (multipoleIntegralCoefficient χ β lam M X root roots)) := by
  exact RouteDirect.tendsto_multipoleActivity_integral hχ hβ hlam hM hX hk root roots

open scoped Classical in
/-- **Lemma 4.26, equation (4.54)**: existence follows from the explicit
integral coefficient, including the zero activity for at most one part. -/
theorem exists_tendsto_multipoleActivity (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hM : 1 ≤ M) (hX : IsSubpartition X) (hk : ((X.biUnion id).card : ℕ∞) ≤ pStar β) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => (N : ℝ) ^ ((X.card : ℤ) - 1) *
      multipoleActivity χ N β lam M X) atTop (𝓝 L) := by
  by_cases hX1 : X.card ≤ 1
  · refine ⟨0, tendsto_const_nhds.congr fun N => ?_⟩
    rw [multipoleActivity_eq_zero_of_card_le_one χ N β lam M hX1, mul_zero]
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨S, hS⟩ := hXne
  obtain ⟨i, hi⟩ := hX.1 S hS
  let root : X.biUnion id := ⟨i, mem_biUnion.mpr ⟨S, hS, hi⟩⟩
  let roots (S : X) : S.val := ⟨(hX.1 S S.property).choose, (hX.1 S S.property).choose_spec⟩
  exact ⟨multipoleIntegralCoefficient χ β lam M X root roots,
    tendsto_multipoleActivity_integral hχ hβ hlam hM hX hk root roots⟩

end Limit

end Limits

end MultipoleBKT

end
