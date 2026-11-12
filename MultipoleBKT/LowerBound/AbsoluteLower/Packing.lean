/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Majorant
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Packing of separated points and of separated blocks

The counting behind the dyadic estimates of Lemma 4.56 (proof of Lemma 4.56).

* `card_mul_sq_le_of_separated`: `q` points of the plane in a disc of radius `ρ`, pairwise at
  distance at least `δ > 0`, satisfy `q δ² ≤ (2ρ + δ)²` (comparison of the areas of disjoint discs
  of radius `δ/2`; the paper's "`q (Ms/2)² ≤ (2t + r_i + Ms/2)²`").
* `card_mul_sq_le_of_separated_blocks`: for labels in a subpartition with blocks of at most `p`
  labels, if points attached to labels of distinct blocks are `δ`-separated, then
  `|J| δ² ≤ p (2ρ + δ)²` ("adding over different blocks").
* `card_le_of_forall_sameBlock`: labels pairwise in a common block are at most `p`.
-/

@[expose] public section

open MeasureTheory

namespace MultipoleBKT

namespace AbsoluteLower

open Finset SetPartition

/-- **Packing in the plane**: points `z_k`, `k ∈ S`, in the closed disc of radius `ρ` about `z₀`,
pairwise at distance at least `δ > 0`, satisfy `|S| δ² ≤ (2ρ + δ)²`. -/
theorem card_mul_sq_le_of_separated {ι : Type*} (S : Finset ι) (z : ι → ℂ) (z₀ : ℂ) {ρ δ : ℝ}
    (hδ : 0 < δ) (hz : ∀ k ∈ S, ‖z k - z₀‖ ≤ ρ)
    (hsep : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → δ ≤ ‖z k - z l‖) :
    (S.card : ℝ) * δ ^ 2 ≤ (2 * ρ + δ) ^ 2 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
  · simp only [card_empty, Nat.cast_zero, zero_mul]
    positivity
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans (hz k₀ hk₀)
  set B : ι → Set ℂ := fun k => Metric.ball (z k) (δ / 2) with hB
  have hdisj : (S : Set ι).PairwiseDisjoint B := by
    intro k hk l hl hkl
    rw [Function.onFun, Set.disjoint_left]
    intro w hwk hwl
    have h1 := hsep k hk l hl hkl
    rw [hB, Metric.mem_ball, dist_eq_norm] at hwk hwl
    have h3 : ‖z k - z l‖ ≤ ‖w - z l‖ + ‖w - z k‖ :=
      calc ‖z k - z l‖ = ‖(w - z l) - (w - z k)‖ := by congr 1; ring
        _ ≤ ‖w - z l‖ + ‖w - z k‖ := norm_sub_le _ _
    linarith
  have hsub : (⋃ k ∈ S, B k) ⊆ Metric.ball z₀ (ρ + δ / 2) := by
    intro w hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨k, hk, hw⟩ := hw
    rw [hB, Metric.mem_ball, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖w - z₀‖ = ‖(w - z k) + (z k - z₀)‖ := by congr 1; ring
      _ ≤ ‖w - z k‖ + ‖z k - z₀‖ := norm_add_le _ _
      _ < δ / 2 + ρ := by linarith [hz k hk]
      _ = ρ + δ / 2 := by ring
  have hvol : volume (⋃ k ∈ S, B k) = ∑ k ∈ S, volume (B k) :=
    measure_biUnion_finset hdisj fun k _ => Metric.isOpen_ball.measurableSet
  have hball : ∀ (a : ℂ) {r : ℝ}, 0 ≤ r →
      volume (Metric.ball a r) = ENNReal.ofReal (r ^ 2 * Real.pi) := by
    intro a r hr
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr, ← NNReal.coe_real_pi,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  have hle := measure_mono (μ := volume) hsub
  rw [hvol, sum_congr rfl fun k _ => hball (z k) (by linarith : 0 ≤ δ / 2),
    hball z₀ (by linarith : 0 ≤ ρ + δ / 2), sum_const, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hpi := Real.pi_pos
  nlinarith

/-- Two labels lie in a common block of `X`. -/
def SameBlock (X : Finset (Finset ℕ)) (j k : ℕ) : Prop := ∃ S ∈ X, j ∈ S ∧ k ∈ S

/-- Labels pairwise in a common block of a subpartition with blocks of at most `p` labels are at
most `p`. -/
theorem card_le_of_forall_sameBlock {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {p : ℕ}
    (hp : ∀ S ∈ X, S.card ≤ p) {J : Finset ℕ} (hJ : ∀ j ∈ J, ∀ k ∈ J, SameBlock X j k) :
    J.card ≤ p := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · simp
  obtain ⟨S₀, hS₀, hj₀S₀, -⟩ := hJ j₀ hj₀ j₀ hj₀
  refine (card_le_card fun k hk => ?_).trans (hp S₀ hS₀)
  obtain ⟨S, hS, hj₀S, hkS⟩ := hJ j₀ hj₀ k hk
  rw [eq_of_isSubpartition hX hS hS₀ hj₀S hj₀S₀] at hkS
  exact hkS

/-- **Packing of separated blocks** ("adding over different blocks", proof of Lemma 4.56): if the
labels of `J ⊆ V_X` carry points `z_j` in the disc of radius `ρ` about `z₀`, and points of labels in
distinct blocks are `δ`-separated, then `|J| δ² ≤ p (2ρ + δ)²` when the blocks have at most `p`
labels. -/
theorem card_mul_sq_le_of_separated_blocks {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {p : ℕ} (hp : ∀ S ∈ X, S.card ≤ p) {J : Finset ℕ} (hJ : J ⊆ X.biUnion id) (z : ℕ → ℂ)
    (z₀ : ℂ) {ρ δ : ℝ} (hδ : 0 < δ) (hz : ∀ j ∈ J, ‖z j - z₀‖ ≤ ρ)
    (hsep : ∀ j ∈ J, ∀ k ∈ J, ¬ SameBlock X j k → δ ≤ ‖z j - z k‖) :
    (J.card : ℝ) * δ ^ 2 ≤ p * (2 * ρ + δ) ^ 2 := by
  classical
  set T := X.filter fun S => (S ∩ J).Nonempty with hT
  -- `J` is covered by the blocks of `T`
  have hcov : J ⊆ T.biUnion fun S => S ∩ J := by
    intro j hj
    obtain ⟨S, hS, hjS⟩ := mem_biUnion_id.1 (hJ hj)
    exact mem_biUnion.2 ⟨S, mem_filter.2 ⟨hS, ⟨j, mem_inter.2 ⟨hjS, hj⟩⟩⟩,
      mem_inter.2 ⟨hjS, hj⟩⟩
  have hJT : J.card ≤ p * T.card := by
    refine (card_le_card hcov).trans (card_biUnion_le.trans ?_)
    rw [mul_comm]
    refine (sum_le_sum fun S hS => (card_le_card inter_subset_left).trans
      (hp S (mem_filter.1 hS).1)).trans_eq ?_
    rw [sum_const, smul_eq_mul]
  -- representatives of the blocks
  have hrep : ∀ S ∈ T, ∃ j, j ∈ S ∩ J := fun S hS => (mem_filter.1 hS).2
  choose! rep hrepmem using hrep
  have hTpack := card_mul_sq_le_of_separated T (fun S => z (rep S)) z₀ hδ
    (fun S hS => hz _ (mem_inter.1 (hrepmem S hS)).2) fun S hS S' hS' hne => ?_
  · have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg _
    calc (J.card : ℝ) * δ ^ 2 ≤ (p * T.card : ℕ) * δ ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hJT) hδ2
      _ = p * ((T.card : ℝ) * δ ^ 2) := by push_cast; ring
      _ ≤ p * (2 * ρ + δ) ^ 2 := mul_le_mul_of_nonneg_left hTpack (Nat.cast_nonneg _)
  · refine hsep _ (mem_inter.1 (hrepmem S hS)).2 _ (mem_inter.1 (hrepmem S' hS')).2 ?_
    rintro ⟨S'', hS'', h1, h2⟩
    have e1 := eq_of_isSubpartition hX (mem_filter.1 hS).1 hS''
      (mem_inter.1 (hrepmem S hS)).1 h1
    have e2 := eq_of_isSubpartition hX (mem_filter.1 hS').1 hS''
      (mem_inter.1 (hrepmem S' hS')).1 h2
    exact hne (e1.trans e2.symm)

end AbsoluteLower

end MultipoleBKT

end
