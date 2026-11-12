/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Mobius
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Disjoint families, ordered tuples and partition sums

Two regroupings used in §4.11 and §5.8 of the paper (Corollary 4.61; Lemma 5.46):

* `SetPartition.sum_disjointFamilies`: a sum over the families `{V₁, …, Vₙ}` of pairwise disjoint
  subsets of `U` satisfying `P` (with `P V → |V| ≥ 2`) of `∏ w(Vᵢ)` is the partition sum of `U`
  with block weight `w` on the blocks satisfying `P`, `1` on singletons and `0` otherwise: complete
  a family by the singletons of the uncovered points;
* `SetPartition.tsum_tuples_eq_sum_disjointFamilies`: the series
  `∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ disjoint, P(Xᵢ)} ∏ K(Xᵢ)` over ordered tuples (the form of the
 frozen statements) is the finite sum over the sets `{X₁, …, Xₙ}`, when `P` excludes
  the empty set: a disjoint tuple of nonempty sets is injective, and each `n`-set has `n!`
  orderings.
-/

@[expose] public section

namespace MultipoleBKT

open Finset

namespace SetPartition

variable {α : Type*} [DecidableEq α]

/-! ### Disjoint families and partitions -/

section DisjointFamilies

open scoped Classical in
/-- The families of pairwise disjoint subsets of `U` satisfying `P`. -/
noncomputable def disjointFamilies (U : Finset α) (P : Finset α → Prop) :
    Finset (Finset (Finset α)) :=
  U.powerset.powerset.filter fun 𝒱 => (𝒱 : Set (Finset α)).PairwiseDisjoint id ∧ ∀ V ∈ 𝒱, P V

omit [DecidableEq α] in
theorem mem_disjointFamilies {U : Finset α} {P : Finset α → Prop} {𝒱 : Finset (Finset α)} :
    𝒱 ∈ disjointFamilies U P ↔
      (∀ V ∈ 𝒱, V ⊆ U) ∧ (𝒱 : Set (Finset α)).PairwiseDisjoint id ∧ ∀ V ∈ 𝒱, P V := by
  classical
  unfold disjointFamilies
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun V hV => Finset.mem_powerset.1 (h1 hV), h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun V hV => Finset.mem_powerset.2 (h1 V hV), h2, h3⟩

variable {U : Finset α} {P : Finset α → Prop}

/-- The completion of a disjoint family by the singletons of the uncovered points. -/
def complete (U : Finset α) (𝒱 : Finset (Finset α)) : Finset (Finset α) :=
  𝒱 ∪ (U \ 𝒱.biUnion id).image singleton

theorem complete_mem_partitions (hP : ∀ V, P V → 2 ≤ V.card) {𝒱 : Finset (Finset α)}
    (h𝒱 : 𝒱 ∈ disjointFamilies U P) : complete U 𝒱 ∈ partitions U := by
  rw [mem_disjointFamilies] at h𝒱
  have h𝒱s : IsSubpartition 𝒱 := ⟨fun V hV => Finset.card_pos.1
    (lt_of_lt_of_le (by norm_num) (hP V (h𝒱.2.2 V hV))), h𝒱.2.1⟩
  rw [mem_partitions, complete]
  refine ⟨isSubpartition_union h𝒱s (isSubpartition_image_singleton _) ?_, ?_⟩
  · rw [biUnion_image_singleton]
    exact Finset.disjoint_sdiff
  · rw [biUnion_union_id, biUnion_image_singleton, Finset.union_sdiff_of_subset]
    intro x hx
    obtain ⟨V, hV, hxV⟩ := mem_biUnion_id.1 hx
    exact h𝒱.1 V hV hxV

theorem filter_complete (hP : ∀ V, P V → 2 ≤ V.card) {𝒱 : Finset (Finset α)}
    (h𝒱 : 𝒱 ∈ disjointFamilies U P) [DecidablePred P] : (complete U 𝒱).filter P = 𝒱 := by
  rw [mem_disjointFamilies] at h𝒱
  ext V
  rw [Finset.mem_filter, complete, Finset.mem_union]
  constructor
  · rintro ⟨hV | hV, hPV⟩
    · exact hV
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hV
      have := hP _ hPV
      simp at this
  · intro hV
    exact ⟨Or.inl hV, h𝒱.2.2 V hV⟩

theorem complete_filter {ρ : Finset (Finset α)} (hρ : ρ ∈ partitions U) [DecidablePred P]
    (h1 : ∀ D ∈ ρ, P D ∨ D.card = 1) : complete U (ρ.filter P) = ρ := by
  have hρs := (mem_partitions.1 hρ).1
  ext D
  rw [complete, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hD | ⟨x, hx, rfl⟩)
    · exact (Finset.mem_filter.1 hD).1
    · rw [Finset.mem_sdiff, mem_biUnion_id] at hx
      obtain ⟨D, hD, hxD⟩ := exists_mem_of_mem_partitions hρ hx.1
      rcases h1 D hD with hPD | hD1
      · exact absurd ⟨D, Finset.mem_filter.2 ⟨hD, hPD⟩, hxD⟩ hx.2
      · obtain ⟨y, rfl⟩ := Finset.card_eq_one.1 hD1
        rw [Finset.mem_singleton.1 hxD]
        exact hD
  · intro hD
    by_cases hPD : P D
    · exact Or.inl (Finset.mem_filter.2 ⟨hD, hPD⟩)
    · right
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 ((h1 D hD).resolve_left hPD)
      refine ⟨x, Finset.mem_sdiff.2 ⟨subset_of_mem_partitions hρ hD
        (Finset.mem_singleton_self x), fun hx => ?_⟩, rfl⟩
      obtain ⟨V, hV, hxV⟩ := mem_biUnion_id.1 hx
      rw [Finset.mem_filter] at hV
      rw [eq_of_isSubpartition hρs hV.1 hD hxV (Finset.mem_singleton_self x)] at hV
      exact hPD hV.2

/-- **Disjoint families as partitions.** If `P V` forces `|V| ≥ 2`, the sum over families of
pairwise disjoint subsets of `U` satisfying `P` of `∏ w(V)` is the partition sum of `U` with block
weight `w` on the blocks satisfying `P`, `1` on the singletons and `0` on the other blocks. -/
theorem sum_disjointFamilies {R : Type*} [CommSemiring R] (U : Finset α) (P : Finset α → Prop)
    [DecidablePred P] (hP : ∀ V, P V → 2 ≤ V.card) (w : Finset α → R) :
    ∑ 𝒱 ∈ disjointFamilies U P, ∏ V ∈ 𝒱, w V =
      partitionSum (fun D => if P D then w D else if D.card = 1 then 1 else 0) U := by
  classical
  unfold partitionSum
  rw [← Finset.sum_filter_of_ne (s := partitions U) (p := fun ρ => ∀ D ∈ ρ, P D ∨ D.card = 1)
    (fun ρ _ hρ => ?_)]
  · refine Finset.sum_nbij' (complete U) (fun ρ => ρ.filter P) ?_ ?_ ?_ ?_ ?_
    · intro 𝒱 h𝒱
      refine Finset.mem_filter.2 ⟨complete_mem_partitions hP h𝒱, fun D hD => ?_⟩
      rw [complete, Finset.mem_union] at hD
      rcases hD with hD | hD
      · exact Or.inl ((mem_disjointFamilies.1 h𝒱).2.2 D hD)
      · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hD
        exact Or.inr (Finset.card_singleton x)
    · intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hρs := (mem_partitions.1 hρ.1).1
      rw [mem_disjointFamilies]
      refine ⟨fun V hV => subset_of_mem_partitions hρ.1 (Finset.mem_filter.1 hV).1, ?_,
        fun V hV => (Finset.mem_filter.1 hV).2⟩
      exact hρs.2.subset (Finset.coe_subset.2 (Finset.filter_subset _ _))
    · intro 𝒱 h𝒱
      exact filter_complete hP h𝒱
    · intro ρ hρ
      rw [Finset.mem_filter] at hρ
      exact complete_filter hρ.1 hρ.2
    · intro 𝒱 h𝒱
      have h𝒱' := mem_disjointFamilies.1 h𝒱
      rw [complete, Finset.prod_union]
      · rw [Finset.prod_eq_one (s := (U \ 𝒱.biUnion id).image singleton) fun D hD => ?_, mul_one]
        · exact Finset.prod_congr rfl fun V hV => (ite_eq_left (h𝒱'.2.2 V hV)).symm
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hD
        have : ¬ P {x} := fun h => by simpa using hP _ h
        simp [this]
      · rw [Finset.disjoint_left]
        intro V hV hV'
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hV'
        simpa using hP _ (h𝒱'.2.2 _ hV)
  · intro D hD
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.1 hcon
    exact hρ (Finset.prod_eq_zero hD (by rw [ite_eq_right h1, ite_eq_right h2]))

end DisjointFamilies

/-! ### Ordered tuples and sets -/

section Tuples

variable {β : Type*} [DecidableEq β]

omit [DecidableEq β] in
theorem injective_of_disjoint {n : ℕ} {X : Fin n → Finset β}
    (hd : ∀ i j, i ≠ j → Disjoint (X i) (X j)) (hne : ∀ i, (X i).Nonempty) :
    Function.Injective X := by
  intro i j hij
  by_contra h
  have := hd i j h
  rw [hij, disjoint_self, Finset.bot_eq_empty] at this
  exact (hne j).ne_empty this

open scoped Classical in
/-- The number of orderings of an `n`-element set. -/
theorem card_filter_image_eq {n : ℕ} (𝒱 : Finset (Finset β)) (h𝒱 : 𝒱.card = n)
    (S : Finset (Finset β)) (h𝒱S : 𝒱 ⊆ S) (Q : (Fin n → Finset β) → Prop)
    (hQ : ∀ X : Fin n → Finset β, Function.Injective X → Finset.univ.image X = 𝒱 → Q X)
    (hQinj : ∀ X : Fin n → Finset β, Q X → Function.Injective X) :
    ((Fintype.piFinset fun _ : Fin n => S).filter
      (fun X => Q X ∧ Finset.univ.image X = 𝒱)).card = n.factorial := by
  have e₀ : Fin n ≃ 𝒱 := (Finset.equivFinOfCardEq h𝒱).symm
  have hfact : Fintype.card (Fin n ≃ 𝒱) = n.factorial := by
    rw [Fintype.card_equiv e₀, Fintype.card_fin]
  rw [← hfact, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun e _ i => (e i : Finset β)) (fun e _ => ?_) (fun e₁ _ e₂ _ h => ?_)
    (fun X hX => ?_)
  · have hinj : Function.Injective fun i => (e i : Finset β) :=
      fun i j hij => e.injective (Subtype.ext hij)
    have himage : Finset.univ.image (fun i => (e i : Finset β)) = 𝒱 := by
      ext V
      rw [Finset.mem_image]
      constructor
      · rintro ⟨i, -, rfl⟩
        exact (e i).2
      · intro hV
        exact ⟨e.symm ⟨V, hV⟩, Finset.mem_univ _, by simp⟩
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => h𝒱S (e i).2,
      hQ _ hinj himage, himage⟩
  · exact Equiv.ext fun i => Subtype.ext (congrFun h i)
  · rw [Finset.mem_filter] at hX
    have hinj := hQinj X hX.2.1
    have hmem : ∀ i, X i ∈ 𝒱 := fun i => hX.2.2 ▸ Finset.mem_image_of_mem X (Finset.mem_univ i)
    have hbij : Function.Bijective fun i => (⟨X i, hmem i⟩ : 𝒱) := by
      refine ⟨fun i j hij => hinj (congrArg Subtype.val hij), fun V => ?_⟩
      have hV : (V : Finset β) ∈ Finset.univ.image X := by
        rw [hX.2.2]
        exact V.2
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hV
      exact ⟨i, Subtype.ext hi⟩
    exact ⟨Equiv.ofBijective _ hbij, Finset.mem_univ _, rfl⟩

open scoped Classical in
/-- For a fixed number `n` of entries, the sum over disjoint tuples is `n!` times the sum over
`n`-sets. -/
theorem sum_tuples_eq_factorial_mul (S : Finset (Finset β)) (P : Finset β → Prop)
    (hP : ∀ x, P x → x.Nonempty) {R : Type*} [CommSemiring R] (K : Finset β → R) (n : ℕ) :
    ∑ X ∈ (Fintype.piFinset fun _ : Fin n => S).filter
        (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i)), ∏ i, K (X i) =
      (n.factorial : R) * ∑ 𝒱 ∈ (disjointFamilies (S.biUnion id) P).filter
        (fun 𝒱 => 𝒱 ⊆ S ∧ 𝒱.card = n), ∏ x ∈ 𝒱, K x := by
  set A := (Fintype.piFinset fun _ : Fin n => S).filter
    (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i))
  set B := (disjointFamilies (S.biUnion id) P).filter (fun 𝒱 => 𝒱 ⊆ S ∧ 𝒱.card = n)
  have hinjA : ∀ X ∈ A, Function.Injective X := fun X hX =>
    injective_of_disjoint (Finset.mem_filter.1 hX).2.1
      fun i => hP _ ((Finset.mem_filter.1 hX).2.2 i)
  have hmaps : ∀ X ∈ A, Finset.univ.image X ∈ B := by
    intro X hX
    rw [Finset.mem_filter] at hX
    have hinj := injective_of_disjoint hX.2.1 fun i => hP _ (hX.2.2 i)
    refine Finset.mem_filter.2 ⟨mem_disjointFamilies.2 ⟨fun V hV => ?_, fun V hV W hW hVW => ?_,
      fun V hV => ?_⟩, fun V hV => ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV
      exact subset_biUnion_of_mem (Fintype.mem_piFinset.1 hX.1 i)
    · rw [Finset.mem_coe, Finset.mem_image] at hV hW
      obtain ⟨i, -, rfl⟩ := hV
      obtain ⟨j, -, rfl⟩ := hW
      exact hX.2.1 i j (fun h => hVW (h ▸ rfl))
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV
      exact hX.2.2 i
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV
      exact Fintype.mem_piFinset.1 hX.1 i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have h1 : ∀ X ∈ A, ∏ i, K (X i) = ∏ x ∈ Finset.univ.image X, K x := fun X hX => by
    rw [Finset.prod_image fun i _ j _ h => hinjA X hX h]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun 𝒱 h𝒱 => ?_
  rw [Finset.sum_congr rfl fun X hX => by rw [(Finset.mem_filter.1 hX).2], Finset.sum_const,
    nsmul_eq_mul, Finset.filter_filter]
  congr 1
  rw [Finset.mem_filter, mem_disjointFamilies] at h𝒱
  have hcard := card_filter_image_eq 𝒱 h𝒱.2.2 S h𝒱.2.1
    (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i))
    (fun X hinj himage => ⟨fun i j hij => ?_, fun i => ?_⟩)
    (fun X hX => injective_of_disjoint hX.1 fun i => hP _ (hX.2 i))
  · convert congrArg (Nat.cast : ℕ → R) hcard using 3
    ext X
    simp only [Finset.mem_filter]
  · have hi : X i ∈ 𝒱 := himage ▸ Finset.mem_image_of_mem X (Finset.mem_univ i)
    have hj : X j ∈ 𝒱 := himage ▸ Finset.mem_image_of_mem X (Finset.mem_univ j)
    exact h𝒱.1.2.1 hi hj (fun h => hij (hinj h))
  · exact h𝒱.1.2.2 _ (himage ▸ Finset.mem_image_of_mem X (Finset.mem_univ i))

open scoped Classical in
/-- **Ordered tuples and sets.** If `P` excludes the empty set,
`∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ∈ S disjoint, P(Xᵢ)} ∏ K(Xᵢ) = ∑_{𝒱 ⊆ S disjoint, P} ∏_{x ∈ 𝒱} K(x)`;
in particular the series has finitely many nonzero terms. -/
theorem tsum_tuples_eq_sum (S : Finset (Finset β)) (P : Finset β → Prop)
    (hP : ∀ x, P x → x.Nonempty) (K : Finset β → ℝ) :
    ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => S).filter
          (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i)), ∏ i, K (X i) =
      ∑ 𝒱 ∈ (disjointFamilies (S.biUnion id) P).filter (· ⊆ S), ∏ x ∈ 𝒱, K x := by
  have hterm : ∀ n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => S).filter
        (fun X => (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∀ i, P (X i)), ∏ i, K (X i) =
      ∑ 𝒱 ∈ (disjointFamilies (S.biUnion id) P).filter (fun 𝒱 => 𝒱 ⊆ S ∧ 𝒱.card = n),
        ∏ x ∈ 𝒱, K x := by
    intro n
    rw [sum_tuples_eq_factorial_mul S P hP K n, ← mul_assoc, one_div,
      inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]
  rw [tsum_congr hterm, tsum_eq_sum (s := Finset.range (S.card + 1)) fun n hn => ?_]
  · rw [← Finset.sum_fiberwise_of_maps_to (s := (disjointFamilies (S.biUnion id) P).filter (· ⊆ S))
      (t := Finset.range (S.card + 1)) (g := Finset.card) fun 𝒱 h𝒱 => ?_]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.filter_filter]
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Finset.card_le_card (Finset.mem_filter.1 h𝒱).2
  · refine Finset.sum_eq_zero fun 𝒱 h𝒱 => ?_
    rw [Finset.mem_filter] at h𝒱
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hn
    exact absurd (h𝒱.2.2 ▸ Finset.card_le_card h𝒱.2.1) (not_le.2 hn)

end Tuples

end SetPartition

end MultipoleBKT

end
