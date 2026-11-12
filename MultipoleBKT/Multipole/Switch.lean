/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Multipole.Composition
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.BoundedBlockPartitions
public import MultipoleBKT.Frozen.TruncatedPartitionWeight

/-!
# Switching to a dipole expansion: Lemma 5.46

See the paper, Lemma 5.46, eq. (5.164):
`(N C_{β,λ})^{-N} ∑_{π ∈ 𝚷_p([N])} Ẑ(π)
= ∑_{n ≥ 0} (1/n!) ∑_{V₁, …, Vₙ ⊂ [N] disjoint, 2 ≤ |Vᵢ| ≤ p} ∏ᵢ 𝖪^dip_{β,λ}(Vᵢ)`,
with `Ẑ(π)` as in eq. (5.160).

The objects `𝚷_p([N])` and `Ẑ(π)` are the frozen definitions
`MultipoleBKT.boundedBlockPartitions` and `MultipoleBKT.truncatedPartitionWeight`.

Proof: write the sum over the families `X₁, …, Xₙ` of `Ẑ(π)` as a partition sum
over the set of blocks of `π` (`SetPartition.tsum_tuples_eq_sum`,
`SetPartition.sum_disjointFamilies`), regroup the pairs (partition, partition of its blocks) by
the coarse partition of `[N]` (`SetPartition.sum_partitionSum_partitions`), and identify the
weight of a coarse block `D` with `𝖪^dip(D)` if `2 ≤ |D| ≤ p` (equation (5.165),
`dipoleActivity_eq_sum_partitions`), with `1` if `|D| = 1` and with `0` if `|D| > p`; the right
side is the same partition sum.

* `lemma_5_46_identity`: the identity, for every `N`, `p ≥ 1`, `M ≥ 1` and `λ > 0`;
* `one_le_pBeta`: `p(β) ≥ 1` for `β > 2`, `p₀ ≥ 1`, so that the identity applies with
  `p = p(β)` (this proves the frozen `MultipoleBKT.lemma_5_46`, see `MultipoleBKT.Main.Lemma546`).
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Finset

namespace Multipole

open SetPartition

open scoped Classical

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

theorem boundedBlockPartitions_eq (N p : ℕ) :
    boundedBlockPartitions N p =
      (partitions (Finset.range N)).filter fun π => ∀ S ∈ π, S.card ≤ p := by
  ext π
  rw [boundedBlockPartitions, Finset.mem_filter, Finset.mem_filter, mem_partitions,
    Finset.mem_powerset]
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun S hS => Finset.mem_powerset.2 ?_, h1, h2, h3⟩
    rw [← h2]
    exact subset_biUnion_of_mem hS

/-- The series of `Ẑ(π)` as a partition sum over the set of blocks of `π`. -/
theorem tsum_truncated_eq_partitionSum (p : ℕ) (π : Finset (Finset ℕ)) (K : Finset (Finset ℕ) → ℝ) :
    ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter (fun X =>
            (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧
              ∀ i, 2 ≤ (X i).card ∧ ((X i).biUnion id).card ≤ p),
          ∏ i, K (X i) =
      partitionSum (fun Y => if 2 ≤ Y.card ∧ (Y.biUnion id).card ≤ p then K Y else
        if Y.card = 1 then 1 else 0) π := by
  have h5 := tsum_tuples_eq_sum π.powerset (fun Y => 2 ≤ Y.card ∧ (Y.biUnion id).card ≤ p)
    (fun Y h => Finset.card_pos.1 (by omega)) K
  rw [biUnion_powerset_id] at h5
  have hfilt : (disjointFamilies π fun Y => 2 ≤ Y.card ∧ (Y.biUnion id).card ≤ p).filter
      (· ⊆ π.powerset) = disjointFamilies π fun Y => 2 ≤ Y.card ∧ (Y.biUnion id).card ≤ p := by
    refine Finset.filter_true_of_mem fun 𝒱 h𝒱 Y hY => ?_
    exact Finset.mem_powerset.2 ((mem_disjointFamilies.1 h𝒱).1 Y hY)
  rw [hfilt, sum_disjointFamilies π _ (fun _ h => h.1) K] at h5
  rw [← h5]
  refine tsum_congr fun n => ?_
  congr 2
  ext X
  simp only [Finset.mem_filter]

/-- The right side of eq. (5.164) as a partition sum of `[N]`. -/
theorem tsum_dipole_eq_partitionSum (N p : ℕ) (K : Finset ℕ → ℝ) :
    ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter (fun V =>
            (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ p),
          ∏ i, K (V i) =
      partitionSum (fun D => if 2 ≤ D.card ∧ D.card ≤ p then K D else
        if D.card = 1 then 1 else 0) (Finset.range N) := by
  have h5 := tsum_tuples_eq_sum (Finset.range N).powerset (fun V => 2 ≤ V.card ∧ V.card ≤ p)
    (fun V h => Finset.card_pos.1 (by omega)) K
  rw [biUnion_powerset_id] at h5
  have hfilt : (disjointFamilies (Finset.range N) fun V => 2 ≤ V.card ∧ V.card ≤ p).filter
      (· ⊆ (Finset.range N).powerset) =
        disjointFamilies (Finset.range N) fun V => 2 ≤ V.card ∧ V.card ≤ p := by
    refine Finset.filter_true_of_mem fun 𝒱 h𝒱 V hV => ?_
    exact Finset.mem_powerset.2 ((mem_disjointFamilies.1 h𝒱).1 V hV)
  rw [hfilt, sum_disjointFamilies (Finset.range N) _ (fun _ h => h.1) K] at h5
  rw [← h5]
  refine tsum_congr fun n => ?_
  congr 2
  ext V
  simp only [Finset.mem_filter]

/-- **Lemma 5.46** (Lemma 5.46, eq. (5.164)): for every `N`, every `p ≥ 1` (the paper has `p = p(β)`), every `M ≥ 1` (the
paper has `M > 20`) and every `λ > 0`,
`(N C_{β,λ})^{-N} ∑_{π ∈ 𝚷_p([N])} Ẑ(π)
= ∑_{n ≥ 0} (1/n!) ∑_{V₁, …, Vₙ ⊂ [N] disjoint, 2 ≤ |Vᵢ| ≤ p} ∏ᵢ 𝖪^dip_{β,λ}(Vᵢ)`. -/
theorem lemma_5_46_identity (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M) {p : ℕ}
    (hp : 1 ≤ p) (N : ℕ) :
    (((N : ℝ) * dipoleNormalization χ N β lam) ^ N)⁻¹ *
        ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π =
      ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter (fun V =>
            (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ p),
          ∏ i, dipoleActivity χ N β lam (V i) := by
  set Mf := multipolePartitionFunction χ N β lam M with hMf
  set K := multipoleActivity χ N β lam M
  set w : Finset (Finset ℕ) → ℝ := fun Y => if 2 ≤ Y.card ∧ (Y.biUnion id).card ≤ p then K Y else
    if Y.card = 1 then 1 else 0 with hw
  set G : Finset (Finset ℕ) → ℝ := fun Y =>
    (if ∀ B ∈ Y, B.card ≤ p then 1 else 0) * ((∏ S ∈ Y, Mf S) * w Y) with hG
  -- the normalization
  have hC : ((N : ℝ) * dipoleNormalization χ N β lam) ^ N ≠ 0 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · exact pow_ne_zero _ (natCast_mul_dipoleNormalization_pos hχ hlam β hN).ne'
  -- step 1: cancel the normalization and expand the series of `Ẑ(π)`
  have h1 : (((N : ℝ) * dipoleNormalization χ N β lam) ^ N)⁻¹ *
      ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π =
        ∑ π ∈ partitions (Finset.range N), partitionSum G π := by
    rw [Finset.mul_sum, boundedBlockPartitions_eq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun π hπ => ?_
    have hπs := (mem_partitions.1 hπ).1
    unfold truncatedPartitionWeight
    rw [tsum_truncated_eq_partitionSum p π K, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel₀ hC, one_mul]
    unfold partitionSum
    rw [Finset.mul_sum]
    split_ifs with hp'
    · refine Finset.sum_congr rfl fun 𝒴 h𝒴 => ?_
      have h𝒴s := (mem_partitions.1 h𝒴).1
      have hY : ∀ Y ∈ 𝒴, G Y = (∏ S ∈ Y, Mf S) * w Y := by
        intro Y hY
        simp only [hG]
        rw [ite_eq_left fun B hB => hp' B (subset_of_mem_partitions h𝒴 hY hB), one_mul]
      rw [Finset.prod_congr rfl hY, Finset.prod_mul_distrib]
      congr 1
      have := Finset.prod_biUnion (f := fun S => Mf S) h𝒴s.2
      rw [(mem_partitions.1 h𝒴).2] at this
      exact this
    · refine (Finset.sum_eq_zero fun 𝒴 h𝒴 => ?_).symm
      push Not at hp'
      obtain ⟨S, hS, hSp⟩ := hp'
      obtain ⟨Y, hY, hSY⟩ := exists_mem_of_mem_partitions h𝒴 hS
      refine Finset.prod_eq_zero hY ?_
      simp only [hG]
      rw [ite_eq_right fun h => absurd (h S hSY) (not_le.2 hSp), zero_mul]
  -- step 2: partitions of partitions
  rw [h1, sum_partitionSum_partitions, tsum_dipole_eq_partitionSum]
  -- step 3: identify the block weights
  refine partitionSum_congr fun D hD hDne => ?_
  have hN : 1 ≤ N := by
    obtain ⟨x, hx⟩ := hDne
    have := Finset.mem_range.1 (hD hx)
    omega
  have hsplit : ∑ Y ∈ partitions D, G Y = G {D} +
      ∑ Y ∈ (partitions D).filter (fun Y => 2 ≤ Y.card), G Y := by
    rw [← Finset.sum_filter_add_sum_filter_not (partitions D) (fun Y => 2 ≤ Y.card), add_comm]
    congr 1
    have hone : (partitions D).filter (fun Y => ¬ 2 ≤ Y.card) = {{D}} := by
      ext Y
      simp only [Finset.mem_filter, Finset.mem_singleton, not_le]
      constructor
      · rintro ⟨hY, h2⟩
        exact eq_singleton_of_mem_partitions hY
          (by have := card_pos_of_mem_partitions hY hDne; omega)
      · rintro rfl
        exact ⟨singleton_mem_partitions hDne, by simp⟩
    rw [hone, Finset.sum_singleton]
  rw [hsplit]
  have hGD : G {D} = if D.card ≤ p then Mf D else 0 := by
    have hw1 : w {D} = 1 := by
      simp only [hw, Finset.card_singleton]
      norm_num
    have hcond : (∀ B ∈ ({D} : Finset (Finset ℕ)), B.card ≤ p) ↔ D.card ≤ p := by simp
    simp only [hG]
    rw [hw1, Finset.prod_singleton, mul_one]
    by_cases hDp : D.card ≤ p
    · rw [ite_eq_left (hcond.2 hDp), ite_eq_left hDp, one_mul]
    · rw [ite_eq_right (fun h => hDp (hcond.1 h)), ite_eq_right hDp, zero_mul]
  by_cases hDp : D.card ≤ p
  · have hGY : ∀ Y ∈ (partitions D).filter (fun Y => 2 ≤ Y.card), G Y = (∏ S ∈ Y, Mf S) * K Y := by
      intro Y hY
      rw [Finset.mem_filter] at hY
      have hVY : (Y.biUnion id).card ≤ p := by rw [(mem_partitions.1 hY.1).2]; exact hDp
      simp only [hG, hw]
      rw [ite_eq_left fun B hB =>
          (Finset.card_le_card (subset_of_mem_partitions hY.1 hB)).trans hDp,
        one_mul, ite_eq_left ⟨hY.2, hVY⟩]
    rw [hGD, ite_eq_left hDp, Finset.sum_congr rfl hGY]
    rcases Nat.lt_or_ge D.card 2 with h2 | h2
    · have h1 : D.card = 1 := by
        have := Finset.card_pos.2 hDne
        omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
      have hnone : (partitions ({i} : Finset ℕ)).filter (fun Y => 2 ≤ Y.card) = ∅ := by
        refine Finset.filter_false_of_mem fun Y hY h2Y => ?_
        have hsub : Y ⊆ {{i}} := fun B hB => Finset.mem_singleton.2
          ((Finset.subset_singleton_iff.1 (subset_of_mem_partitions hY hB)).resolve_left
            ((mem_partitions.1 hY).1.1 B hB).ne_empty)
        have := Finset.card_le_card hsub
        rw [Finset.card_singleton] at this
        omega
      rw [hnone, Finset.sum_empty, add_zero, hMf,
        multipolePartitionFunction_singleton hχ hlam β M hN i]
      simp
    · rw [← dipoleActivity_eq_sum_partitions hχ hlam hN hM β h2, ite_eq_left ⟨h2, hDp⟩]
  · have hGY : ∀ Y ∈ (partitions D).filter (fun Y => 2 ≤ Y.card), G Y = 0 := by
      intro Y hY
      rw [Finset.mem_filter] at hY
      have hVY : ¬ (Y.biUnion id).card ≤ p := by rw [(mem_partitions.1 hY.1).2]; exact hDp
      have hwY : w Y = 0 := by
        simp only [hw]
        rw [ite_eq_right fun h => hVY h.2, ite_eq_right (by omega : ¬ Y.card = 1)]
      simp only [hG]
      rw [hwY, mul_zero, mul_zero]
    rw [hGD, ite_eq_right hDp, Finset.sum_eq_zero hGY, add_zero,
      ite_eq_right fun h => hDp h.2, ite_eq_right (by omega : ¬ D.card = 1)]

/-! ### `p(β) ≥ 1` -/

/-- `p(β) ≥ 1` for `β > 2` and `p₀ ≥ 1`: `β > 2 = β₁`, and `p*(β) < ∞` for `β < 4`. -/
theorem one_le_pBeta {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ} (hβ : 2 < β) : 1 ≤ pBeta p₀ β := by
  unfold pBeta
  split_ifs with h4
  · have h1 : (1 : ℕ∞) ≤ pStar β := by
      unfold pStar
      refine le_iSup₂_of_le (f := fun (q : ℕ) (_ : 1 ≤ q ∧ transitionBeta q < β) => (q : ℕ∞)) 1
        ⟨le_rfl, ?_⟩ (by simp)
      unfold transitionBeta
      norm_num
      linarith
    have hfin : pStar β ≠ ⊤ := by
      have hbound : pStar β ≤ ((⌊2 / (4 - β)⌋₊ : ℕ) : ℕ∞) := by
        unfold pStar
        refine iSup₂_le fun q hq => ?_
        rw [Nat.cast_le]
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.1
        have hq2 := hq.2
        unfold transitionBeta at hq2
        refine Nat.le_floor ?_
        rw [le_div_iff₀ (by linarith)]
        have : 2 / (q : ℝ) > 4 - β := by linarith
        rw [gt_iff_lt, lt_div_iff₀ (by linarith)] at this
        linarith
      exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbound
    have := ENat.natCast_toNat hfin
    rw [← this] at h1
    exact_mod_cast h1
  · exact hp₀

end Multipole

end MultipoleBKT

end
