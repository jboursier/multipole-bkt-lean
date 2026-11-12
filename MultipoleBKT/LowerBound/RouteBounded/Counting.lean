/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.ActivityIntegral

/-!
# Factorial cancellation for the bounded lower activity

(4.73),
proof of Proposition 4.23. Count unordered families by the connected components
of their Mayer edge union. The empty family has one ordering, since 0! = 1.
The separation edges are counted only after this cancellation.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open Finset Hierarchical Multipole SetPartition
open scoped Classical

/-- There are exactly `binom(k,2)` available unordered pairs. -/
theorem card_pairsOn (V : Finset ℕ) : (pairsOn V).card = V.card.choose 2 :=
  card_product_filter_lt

/-- Restricting the Mayer union to a group recovers its edge set.
(4.73), proof of Proposition 4.23. -/
theorem mayer_union_inter_group {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hd : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m))
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l)) (l : Fin n) :
    univ.biUnion Es ∩ interPairs (Xs l) = Es l := by
  ext p
  constructor
  · rintro hp
    obtain ⟨m, _, hm⟩ := mem_biUnion.1 (mem_inter.1 hp).1
    by_cases hml : m = l
    · simpa [hml] using hm
    · have hh := disjoint_biUnion_of_disjoint hX (hXs m) (hXs l) (hd m l hml)
      exact False.elim (disjoint_left.1 hh
        (mem_pairsOn.1 (interPairs_subset_pairsOn ((mem_relEdgeSets.1 (hEs m)).1 hm))).1
        (mem_pairsOn.1 (interPairs_subset_pairsOn (mem_inter.1 hp).2)).1)
  · intro hp
    exact mem_inter.2 ⟨mem_biUnion.2 ⟨l, mem_univ _, hp⟩, (mem_relEdgeSets.1 (hEs l)).1 hp⟩

/-- The group is exactly the connected component relative to `X` of any
of its labels. Together with `mayer_union_inter_group`, this recovers
both the group and its edges from the union.
(4.73), proof of Proposition 4.23. -/
theorem mayer_group_eq_component {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hd : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m))
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l))
    (l : Fin n) {B : Finset ℕ} (hB : B ∈ Xs l) {a : ℕ} (ha : a ∈ B) :
    reachedBlocks X (univ.biUnion Es) a = Xs l := by
  have hEX : univ.biUnion Es ⊆ interPairs X := biUnion_subset.2 fun m _ =>
    (mem_relEdgeSets.1 (hEs m)).1.trans (interPairs_subset_of_subset hX (hXs m))
  apply (reachedBlocks_eq_iff hX hEX (hXs l) hB ha).2
  constructor
  · intro p hp
    obtain ⟨m, _, hm⟩ := mem_biUnion.1 hp
    by_cases hml : m = l
    · exact mem_union_left _ (hml ▸ (mem_relEdgeSets.1 (hEs m)).1 hm)
    · apply mem_union_right
      apply interPairs_subset_of_subset (isSubpartition_mono hX sdiff_subset) _
        ((mem_relEdgeSets.1 (hEs m)).1 hm)
      intro B hBm
      exact mem_sdiff.2 ⟨hXs m hBm, fun hBl =>
        disjoint_left.1 (hd m l hml) hBm hBl⟩
  · rw [mayer_union_inter_group hX hXs hd hEs]
    exact (mem_relEdgeSets.1 (hEs l)).2.2

/-- Counting connected components, including the unused singleton blocks.
The underlying component expansion restricts the edge union to each
component, so it counts each unordered family with its edge sets once.
(4.73), proof of Proposition 4.23. -/
theorem count_unordered_mayer_families {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    (∑ Ys ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
      ∏ Y ∈ Ys, ((relEdgeSets Y).card : ℝ)) = 2 ^ (interPairs X).card := by
  rw [sum_disjointFamilies X (fun Y => 2 ≤ Y.card) (fun _ h => h)]
  have hw : ∀ Y ⊆ X,
      (if 2 ≤ Y.card then ((relEdgeSets Y).card : ℝ) else if Y.card = 1 then 1 else 0) =
        relConnSum (fun _ => (1 : ℝ)) Y := by
    intro Y hY
    rw [relConnSum_eq_sum_relEdgeSets₀]
    simp only [prod_const_one, sum_const, nsmul_eq_mul, mul_one]
    rw [relEdgeSets₀_eq (isSubpartition_mono hX hY)]
    by_cases h2 : 2 ≤ Y.card
    · simp [h2, show Y.card ≠ 1 by omega]
    · simp [h2]
      split_ifs <;> simp_all [relEdgeSets_eq_empty_of_card_le_one (by omega : Y.card ≤ 1)]
  unfold partitionSum
  rw [sum_congr rfl (fun Ys hYs => prod_congr rfl (fun Y hY =>
    hw Y (subset_of_mem_partitions hYs hY)))]
  have hc := sum_powerset_interPairs_eq_partitionSum (fun _ => (1 : ℝ)) hX X Subset.rfl
  simpa [partitionSum] using hc.symm

/-- A fixed unordered family with fixed connected edge sets has exactly
`n!` ordered presentations. The statement includes the empty family.
(4.73), proof of Proposition 4.23. -/
theorem card_orderings_with_edges {X : Finset (Finset ℕ)}
    {Ys : Finset (Finset (Finset ℕ))} (hYs : Ys ∈ disjointFamilies X (fun Y => 2 ≤ Y.card))
    {n : ℕ} (hn : Ys.card = n) (E : Finset (Finset ℕ) → Finset (ℕ × ℕ))
    (hE : ∀ Y ∈ Ys, E Y ∈ relEdgeSets Y) :
    let tuples := (Fintype.piFinset fun _ : Fin n => X.powerset).filter
      (fun Xs => ((∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, 2 ≤ (Xs i).card) ∧
        univ.image Xs = Ys)
    (tuples.sigma fun Xs => (Fintype.piFinset fun l => relEdgeSets (Xs l)).filter
      (fun Es => ∀ l, Es l = E (Xs l))).card = n.factorial := by
  dsimp only
  rw [card_sigma]
  have hYs' := mem_disjointFamilies.1 hYs
  have hc := card_filter_image_eq Ys hn X.powerset
    (fun Y hY => mem_powerset.2 (hYs'.1 Y hY))
    (fun Xs : Fin n → Finset (Finset ℕ) =>
      (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, 2 ≤ (Xs i).card)
    (fun Xs hinj himage => ⟨fun i j hij => hYs'.2.1
      (himage ▸ mem_image_of_mem Xs (mem_univ i))
      (himage ▸ mem_image_of_mem Xs (mem_univ j)) (fun heq => hij (hinj heq)),
      fun i => hYs'.2.2 _ (himage ▸ mem_image_of_mem Xs (mem_univ i))⟩)
    (fun Xs hXs => injective_of_disjoint hXs.1 fun i => card_pos.1
      (lt_of_lt_of_le (by norm_num) (hXs.2 i)))
  calc
    _ = ∑ _Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ((∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, 2 ≤ (Xs i).card) ∧
          univ.image Xs = Ys), 1 := by
      apply sum_congr rfl
      intro Xs hXs
      have himage := (mem_filter.1 hXs).2.2
      have he : (Fintype.piFinset fun l => relEdgeSets (Xs l)).filter
          (fun Es => ∀ l, Es l = E (Xs l)) = {fun l => E (Xs l)} := by
        ext Es
        simp only [mem_filter, Fintype.mem_piFinset, mem_singleton]
        constructor
        · exact fun h => funext h.2
        · rintro rfl
          exact ⟨fun l => hE _ (himage ▸ mem_image_of_mem Xs (mem_univ l)), fun _ => rfl⟩
      rw [he, card_singleton]
    _ = _ := by simpa using hc

/-- At fixed length, each unordered family has exactly `n!` orderings,
with its independent connected edge choices retained in the product.
This also includes length zero. (4.73), proof of Proposition 4.23. -/
theorem count_ordered_mayer_families (X : Finset (Finset ℕ)) (n : ℕ) :
    (∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
      (fun Xs => (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, 2 ≤ (Xs i).card),
      ∏ i, ((relEdgeSets (Xs i)).card : ℝ)) =
    (n.factorial : ℝ) * ∑ Ys ∈ (disjointFamilies X (fun Y => 2 ≤ Y.card)).filter
      (fun Ys => Ys.card = n), ∏ Y ∈ Ys, ((relEdgeSets Y).card : ℝ) := by
  have hc := sum_tuples_eq_factorial_mul X.powerset (fun Y => 2 ≤ Y.card)
    (fun Y h => card_pos.1 (by omega)) (fun Y => ((relEdgeSets Y).card : ℝ)) n
  rw [biUnion_powerset_id] at hc
  convert hc using 3
  ext Ys
  simp only [mem_filter]
  constructor
  · rintro ⟨hYs, hn⟩
    exact ⟨hYs, (fun Y hY => mem_powerset.2 ((mem_disjointFamilies.1 hYs).1 Y hY)), hn⟩
  · rintro ⟨hYs, _, hn⟩
    exact ⟨hYs, hn⟩

/-- Cancelling the factorial counts all possible Mayer unions once.
(4.73), proof of Proposition 4.23. -/
theorem factorial_mayer_count {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    (∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ _Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l), (1 : ℝ)) =
      2 ^ (interPairs X).card := by
  have hinner (n : ℕ) :
      (∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ _Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l), (1 : ℝ)) =
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, 2 ≤ (Xs i).card),
        ∏ i, ((relEdgeSets (Xs i)).card : ℝ) := by
    simp only [sum_const, nsmul_eq_mul, mul_one, Fintype.card_piFinset, Nat.cast_prod]
    rw [← filter_filter]
    symm
    apply sum_filter_of_ne
    intro Xs _ hne i
    by_contra hi
    exact hne (prod_eq_zero (mem_univ i) (by
      rw [relEdgeSets_eq_empty_of_card_le_one (by omega), card_empty, Nat.cast_zero]))
  have hcancel (n : ℕ) : 1 / (n.factorial : ℝ) *
      (n.factorial : ℝ) = 1 := by
    exact one_div_mul_cancel (by exact_mod_cast n.factorial_ne_zero)
  simp_rw [hinner, count_ordered_mayer_families, ← mul_assoc, hcancel, one_mul]
  rw [← count_unordered_mayer_families hX]
  apply sum_fiberwise_of_maps_to
    (s := disjointFamilies X (fun Y => 2 ≤ Y.card)) (g := Finset.card)
  intro Ys hYs
  have hYs' := mem_disjointFamilies.1 hYs
  have hsub : Ys.biUnion id ⊆ X := biUnion_subset.2 fun Y hY => hYs'.1 Y hY
  exact mem_range.2 (Nat.lt_succ_of_le
    ((card_le_card_biUnion hYs'.2.1 (fun Y hY =>
      (show 0 < Y.card from lt_of_lt_of_le (by norm_num) (hYs'.2.2 Y hY)) |> card_pos.1)).trans
        (card_le_card hsub)))

/-- The total weights of the grouped terms are bounded by the number of
pairs of edge sets, after cancelling the orderings of the Mayer families.
(4.73), proof of Proposition 4.23. -/
theorem factorial_grouped_count_le {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {k : ℕ} (hk : (X.biUnion id).card ≤ k) :
    (∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ _Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
          ∑ _F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)), (1 : ℝ)) ≤
      2 ^ (2 * k.choose 2) := by
  have hp : (pairsOn (X.biUnion id)).card ≤ k.choose 2 := by
    rw [card_pairsOn]
    exact Nat.choose_le_choose 2 hk
  have hF (n : ℕ) (Xs : Fin n → Finset (Finset ℕ))
      (hXs : ∀ l, Xs l ⊆ X) :
      ((relEdgeSets₀ (coarsen X (univ.image Xs))).card : ℝ) ≤ 2 ^ k.choose 2 := by
    have hcoarse : (coarsen X (univ.image Xs)).biUnion id = X.biUnion id :=
      biUnion_coarsen (fun Y hY => by
      obtain ⟨l, _, rfl⟩ := mem_image.1 hY
      exact hXs l)
    have hs : relEdgeSets₀ (coarsen X (univ.image Xs)) ⊆
        (pairsOn (X.biUnion id)).powerset := fun F hF => mem_powerset.2 (by
      have := (mem_relEdgeSets₀.1 hF).1.trans interPairs_subset_pairsOn
      rwa [hcoarse] at this)
    exact_mod_cast (card_le_card hs).trans (by rw [card_powerset]; exact Nat.pow_le_pow_right (by norm_num) hp)
  calc
    _ ≤ ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l), (2 : ℝ) ^ k.choose 2 := by
      apply sum_le_sum
      intro n _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro Xs hXs
      apply sum_le_sum
      intro Es _
      simpa using hF n Xs (fun l => mem_powerset.1 (Fintype.mem_piFinset.1 (mem_filter.1 hXs).1 l))
    _ = 2 ^ k.choose 2 * 2 ^ (interPairs X).card := by
      rw [← factorial_mayer_count hX]
      simp only [mul_sum]
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro Xs _
      apply sum_congr rfl
      intro Es _
      ring
    _ ≤ 2 ^ k.choose 2 * 2 ^ k.choose 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num) ((card_le_card interPairs_subset_pairsOn).trans hp)) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

end MultipoleBKT.LowerBound.RouteBounded

end
