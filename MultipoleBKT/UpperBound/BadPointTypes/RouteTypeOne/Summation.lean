/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneCount
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeOne.Counting

/-!
# Integration and the final positive/negative block sum

The paper: Lemma 5.40,
(5.131) and Step 6. Apply the fixed-data integral estimate.
The two factorial denominators correspond to positive and negative blocks.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open Finset

open scoped Classical in
/-- The final sum over positive and negative block counts in Step 6. -/
noncomputable def typeOneSeries (q n : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Finset.range (2 * n + 1), ∑ b ∈ Finset.range (2 * n + 1),
    if n ≤ (q + 1) * (a + b) then x ^ (a + b) / (a.factorial * b.factorial) else 0

theorem typeOneSeries_nonneg (q n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ typeOneSeries q n x := by
  unfold typeOneSeries
  refine sum_nonneg fun a _ => sum_nonneg fun b _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

namespace RouteTypeOne

variable {n : ℕ}

open scoped Classical in
/-- Scales are assigned only to overcrowded roots, as in Step 5. -/
noncomputable def scales (K : ℕ) (kind : Charge n → Fin 4) : Finset (Charge n → ℕ) :=
  Fintype.piFinset fun v => if kind v = 0 then range (K + 1) else {0}

/-- Changing the root scales preserves the geometric-data validity conditions. -/
theorem valid_scales {q K : ℕ} {B : Base n} (hB : B ∈ bases q) {sc : Charge n → ℕ}
    (hsc : sc ∈ scales K B.1) : TypeOneValid q (B.1, B.2, sc) := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := (mem_filter.1 hB).2.1
  refine ⟨h1, h2, h3, h4, h5, fun v hv => ?_⟩
  have h := Fintype.mem_piFinset.1 hsc v
  simpa only [ite_eq_right hv, mem_singleton] using h

/-- Positive and negative blocks together are the overcrowded roots and long singletons. -/
theorem blocks_add {q : ℕ} {B : Base n} (hB : B ∈ bases q) :
    blocks B true + blocks B false = kindCount B.1 0 + kindCount B.1 1 := by
  classical
  have hV := (mem_filter.1 hB).2.1
  have he (s : Bool) : roots (badSet (unscaled B) s) (partition (unscaled B) s) =
      (univ.filter fun v => B.1 v = 0 ∨ B.1 v = 1).filter (fun v => positive v = s) := by
    apply Finset.ext
    intro v
    rw [mem_roots_partition hV]
    simp only [mem_filter, mem_univ, true_and, unscaled]
    tauto
  have hneg : ((univ.filter fun v => B.1 v = 0 ∨ B.1 v = 1).filter
      fun v => positive v = false) = ((univ.filter fun v => B.1 v = 0 ∨ B.1 v = 1).filter
      fun v => ¬positive v = true) := by
    congr 1
    funext v
    cases positive v <;> simp
  rw [blocks, blocks, he, he, hneg, card_filter_add_card_filter_not]
  have hd : Disjoint (univ.filter fun v => B.1 v = 0) (univ.filter fun v => B.1 v = 1) := by
    apply disjoint_left.2
    intro v hv hw
    have he := (mem_filter.1 hv).2
    have hw := (mem_filter.1 hw).2
    rw [he] at hw
    norm_num at hw
  rw [filter_or, card_union_of_disjoint hd]
  rfl

/-- Each same-sign block count is at most `n`. -/
theorem blocks_le {q : ℕ} {B : Base n} (_hB : B ∈ bases q) (s : Bool) : blocks B s ≤ n := by
  exact (card_le_card (filter_subset _ _)).trans
    ((card_le_card (badSet_subset (unscaled B) s)).trans_eq (card_charges s))

/-- Every dipole has a bad charge, giving the constraint in the final series. -/
theorem block_constraint {q : ℕ} {B : Base n} (hB : B ∈ bases q) :
    n ≤ (q + 1) * (blocks B true + blocks B false) := by
  classical
  have hV := (mem_filter.1 hB).2.1
  have hc := hV.counts
  have hs := kindCount_sum B.1
  rw [blocks_add hB]
  change kindCount B.1 2 = q * kindCount B.1 0 ∧ kindCount B.1 3 ≤ n at hc
  nlinarith

/-- (5.131): after the scale sums, a fixed choice of bad sets, partners and
partitions contributes one factor `x` per positive or negative block. -/
theorem integrated_base_le {q : ℕ} {B : Base n} (hB : B ∈ bases q)
    {X Y Kg M x ν : ℝ} (hM : 1 ≤ M) (hν : 0 < ν) (hx : 0 ≤ x)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hKg0 : 0 ≤ Kg)
    (hX : X ≤ M * x * ν ^ (q + 1)) (hY : Y ≤ M * x * ν) (hKg : Kg ≤ M * ν) :
    X ^ kindCount B.1 0 * Y ^ kindCount B.1 1 * Kg ^ kindCount B.1 3 ≤
      M ^ (2 * n) * ν ^ (2 * n) * x ^ (blocks B true + blocks B false) := by
  classical
  have hV := (mem_filter.1 hB).2.1
  have hc := hV.counts
  have hs := kindCount_sum B.1
  change kindCount B.1 2 = q * kindCount B.1 0 ∧ kindCount B.1 3 ≤ n at hc
  have htot : (q + 1) * kindCount B.1 0 + kindCount B.1 1 + kindCount B.1 3 = 2 * n := by
    nlinarith [hc.1]
  rw [blocks_add hB]
  calc X ^ kindCount B.1 0 * Y ^ kindCount B.1 1 * Kg ^ kindCount B.1 3
      ≤ (M * x * ν ^ (q + 1)) ^ kindCount B.1 0 * (M * x * ν) ^ kindCount B.1 1 *
          (M * ν) ^ kindCount B.1 3 := by gcongr
    _ = M ^ (kindCount B.1 0 + kindCount B.1 1 + kindCount B.1 3) *
        ν ^ ((q + 1) * kindCount B.1 0 + kindCount B.1 1 + kindCount B.1 3) *
        x ^ (kindCount B.1 0 + kindCount B.1 1) := by ring
    _ ≤ M ^ (2 * n) * ν ^ (2 * n) * x ^ (kindCount B.1 0 + kindCount B.1 1) := by
      rw [htot]
      have hexp : kindCount B.1 0 + kindCount B.1 1 + kindCount B.1 3 ≤ 2 * n := by
        nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hM hexp) (by positivity)) (by positivity)

/-- Summing the fixed-data estimate in the written order gives the final constrained
double sum over positive and negative block counts. -/
theorem sum_integrated_bases_le {q : ℕ} (hq : 1 ≤ q) {X Y Kg M x ν : ℝ}
    (hM : 1 ≤ M) (hν : 0 < ν) (hx : 0 ≤ x)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hKg0 : 0 ≤ Kg)
    (hX : X ≤ M * x * ν ^ (q + 1)) (hY : Y ≤ M * x * ν) (hKg : Kg ≤ M * ν) :
    ∑ B ∈ bases (n := n) q, X ^ kindCount B.1 0 * Y ^ kindCount B.1 1 * Kg ^ kindCount B.1 3 ≤
      4 ^ n * (n : ℝ) ^ (2 * n) * M ^ (2 * n) * ν ^ (2 * n) * typeOneSeries q n x := by
  classical
  have hmap : ∀ B ∈ bases (n := n) q, (blocks B true, blocks B false) ∈
      range (2 * n + 1) ×ˢ range (2 * n + 1) := by
    intro B hB
    exact mem_product.2 ⟨mem_range.2 (by have := blocks_le hB true; omega),
      mem_range.2 (by have := blocks_le hB false; omega)⟩
  rw [← sum_fiberwise_of_maps_to hmap, sum_product]
  unfold typeOneSeries
  rw [mul_sum]
  apply sum_le_sum
  intro k _
  rw [mul_sum]
  apply sum_le_sum
  intro l _
  have he : ((bases (n := n) q).filter fun B => (blocks B true, blocks B false) = (k,l)) =
      blockFiber q k l := by
    ext B
    simp only [blockFiber, mem_filter, Prod.mk.injEq]
  rw [he]
  by_cases hkl : n ≤ (q + 1) * (k + l)
  · rw [ite_eq_left hkl]
    calc ∑ B ∈ blockFiber (n := n) q k l,
          X ^ kindCount B.1 0 * Y ^ kindCount B.1 1 * Kg ^ kindCount B.1 3
        ≤ ∑ _B ∈ blockFiber (n := n) q k l, M ^ (2 * n) * ν ^ (2 * n) * x ^ (k + l) := by
          apply sum_le_sum
          intro B hB
          obtain ⟨hB, hk, hl⟩ := mem_filter.1 hB
          simpa only [hk, hl] using integrated_base_le hB hM hν hx hX0 hY0 hKg0 hX hY hKg
      _ = ((blockFiber (n := n) q k l).card : ℝ) *
          (M ^ (2 * n) * ν ^ (2 * n) * x ^ (k + l)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (4 ^ n * (n : ℝ) ^ (2 * n) / (k.factorial * l.factorial)) *
          (M ^ (2 * n) * ν ^ (2 * n) * x ^ (k + l)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial * l.factorial)]
          have hc := card_blockFiber_mul_factorials_le (n := n) hq k l
          have hc' : (blockFiber (n := n) q k l).card * (k.factorial * l.factorial) ≤
              4 ^ n * n ^ (2 * n) := by simpa only [mul_assoc] using hc
          exact_mod_cast hc'
      _ = 4 ^ n * (n : ℝ) ^ (2 * n) * M ^ (2 * n) * ν ^ (2 * n) *
          (x ^ (k + l) / (k.factorial * l.factorial)) := by ring
  · rw [ite_eq_right hkl, mul_zero]
    have hz : blockFiber (n := n) q k l = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro B hB
      obtain ⟨hB, hk, hl⟩ := mem_filter.1 hB
      exact hkl (by simpa only [hk, hl] using block_constraint hB)
    rw [hz, sum_empty]

end RouteTypeOne

end MultipoleBKT.BadPointTypes

end
