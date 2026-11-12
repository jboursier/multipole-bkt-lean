/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.Counting
public import MultipoleBKT.Limits.ProfileIndependence
public import MultipoleBKT.Cluster.Hypertree
public import MultipoleBKT.Frozen.CanonicalPartition
public import MultipoleBKT.RateFunction.Canonical

/-!
# Proposition 5.45: grouping cluster sums over a partition by the union of the polymers

The first steps of the hypertree calculation (4.155), used in the proof of Proposition 5.45
for the polymer gas of `Ẑ(π)` (eq. (5.160)). The polymers are sets `X ⊂ π` of blocks of a
partition `π`, with `2 ≤ |X|` and `|V_X| ≤ p`, and the activity `K(X)` depends only on the block
profile of `X` (Lemma 4.26; for `𝖪^mult` this is
`MultipoleBKT.Limits.multipoleActivity_eq_of_blockProfile_eq`).

* `clusterWeight p K X = 𝟙_{G(X) connected, 2 ≤ |X_i|, |V_{X_i}| ≤ p} ∏ᵢ K(X_i) I(G(X))`, the
  summand of the connected cluster sum;
* `unionSum p K m`: the sum of `clusterWeight` over the families with union the canonical partition
  `Y(m)` (Definition 2.14);
* `sum_piFinset_clusterWeight_eq` (eq. (4.153) and the count before (4.154)):
  for a partition `A` into blocks of sizes at most `p` with `n_i` blocks of size `i + 1`,
  `∑_{X_1, …, X_n ⊂ A} clusterWeight(X) = ∑_m ∏ᵢ C(n_i, m_i) · unionSum(m)`, where `m` runs over a
  finite box independent of `A`. The families with a given union `Y ⊂ A` are transported to
  `Y(m)`, `m` the profile of `Y`, by a size-preserving bijection of the blocks.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace PropFiveFortyFive

variable {n : ℕ}

/-! ### Relabeling families -/

section Relabel

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
theorem injOn_union_of_injOn_biUnion {X : Fin n → Finset α} {f : α → β}
    (hf : Set.InjOn f ↑(univ.biUnion X)) (i j : Fin n) : Set.InjOn f (↑(X i) ∪ ↑(X j)) := by
  refine hf.mono ?_
  intro a ha
  simp only [Set.mem_union, mem_coe] at ha
  simp only [coe_biUnion, coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, mem_coe]
  rcases ha with ha | ha
  · exact ⟨i, ha⟩
  · exact ⟨j, ha⟩

/-- The connection graph is invariant under a relabeling injective on the union. -/
theorem connectionGraph_image {X : Fin n → Finset α} {f : α → β}
    (hf : Set.InjOn f ↑(univ.biUnion X)) :
    connectionGraph (fun i => (X i).image f) = connectionGraph X := by
  ext i j
  simp only [connectionGraph, SimpleGraph.fromRel_adj]
  rw [← image_inter_of_injOn _ _ (injOn_union_of_injOn_biUnion hf i j),
    ← image_inter_of_injOn _ _ (injOn_union_of_injOn_biUnion hf j i)]
  simp only [image_nonempty]

omit [DecidableEq β] in
theorem injOn_of_subset_biUnion {X : Fin n → Finset α} {f : α → β}
    (hf : Set.InjOn f ↑(univ.biUnion X)) (i : Fin n) : Set.InjOn f ↑(X i) := by
  refine hf.mono ?_
  intro a ha
  simp only [coe_biUnion, coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, mem_coe]
  exact ⟨i, ha⟩

end Relabel

/-! ### Block profiles under relabeling -/

section Profile

theorem blockProfile_image {Y : Finset (Finset ℕ)} {f : Finset ℕ → Finset ℕ}
    (hf : Set.InjOn f ↑Y) (hcard : ∀ S ∈ Y, (f S).card = S.card) :
    blockProfile (Y.image f) = blockProfile Y := by
  unfold blockProfile
  rw [image_val_of_injOn hf, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun S hS => hcard S hS

theorem blockProfile_apply (X : Finset (Finset ℕ)) (k : ℕ) :
    blockProfile X k = (X.filter fun S => S.card = k).card := by
  unfold blockProfile
  rw [Multiset.toFinsupp_apply, Multiset.count_map, card_def, filter_val]
  congr 1
  exact Multiset.filter_congr fun S _ => eq_comm

/-- Families with sizes in `[1, p]` and the same block counts have the same block profile. -/
theorem blockProfile_eq_of_blockCount_eq {p : ℕ} {Y Y' : Finset (Finset ℕ)}
    (hY : ∀ S ∈ Y, 1 ≤ S.card ∧ S.card ≤ p) (hY' : ∀ S ∈ Y', 1 ≤ S.card ∧ S.card ≤ p)
    (h : blockCount p Y = blockCount p Y') : blockProfile Y = blockProfile Y' := by
  ext k
  rw [blockProfile_apply, blockProfile_apply]
  by_cases hk : 1 ≤ k ∧ k ≤ p
  · have := congrFun h ⟨k - 1, by omega⟩
    simp only [blockCount] at this
    rwa [show k - 1 + 1 = k by omega] at this
  · rw [filter_false_of_mem fun S hS (hSk : S.card = k) =>
        hk ⟨hSk ▸ (hY S hS).1, hSk ▸ (hY S hS).2⟩,
      filter_false_of_mem fun S hS (hSk : S.card = k) =>
        hk ⟨hSk ▸ (hY' S hS).1, hSk ▸ (hY' S hS).2⟩]

end Profile

/-! ### The canonical partition -/

section Canonical

variable {p : ℕ}

theorem mem_canonicalPartition {m : Fin p → ℕ} {S : Finset ℕ} :
    S ∈ canonicalPartition m ↔ ∃ i : Fin p, ∃ j < m i,
      Ico (∑ l with l < i, ((l : ℕ) + 1) * m l + j * ((i : ℕ) + 1))
        (∑ l with l < i, ((l : ℕ) + 1) * m l + (j + 1) * ((i : ℕ) + 1)) = S := by
  unfold canonicalPartition
  simp only [mem_biUnion, mem_univ, true_and, mem_image, mem_range]

theorem card_Ico_canonical (m : Fin p → ℕ) (i : Fin p) (j : ℕ) :
    (Ico (∑ l with l < i, ((l : ℕ) + 1) * m l + j * ((i : ℕ) + 1))
      (∑ l with l < i, ((l : ℕ) + 1) * m l + (j + 1) * ((i : ℕ) + 1))).card = (i : ℕ) + 1 := by
  rw [Nat.card_Ico, add_mul, one_mul]
  omega

theorem card_mem_Icc_of_mem_canonicalPartition {m : Fin p → ℕ} :
    ∀ S ∈ canonicalPartition m, 1 ≤ S.card ∧ S.card ≤ p := by
  intro S hS
  obtain ⟨i, j, -, rfl⟩ := mem_canonicalPartition.1 hS
  rw [card_Ico_canonical]
  exact ⟨by omega, i.2⟩

/-- `Y(m)` has `m_i` blocks of size `i + 1`. -/
theorem blockCount_canonicalPartition (m : Fin p → ℕ) :
    blockCount p (canonicalPartition m) = m := by
  funext i
  simp only [blockCount]
  have hfilt : (canonicalPartition m).filter (fun S => S.card = (i : ℕ) + 1) =
      (range (m i)).image fun j =>
        Ico (∑ l with l < i, ((l : ℕ) + 1) * m l + j * ((i : ℕ) + 1))
          (∑ l with l < i, ((l : ℕ) + 1) * m l + (j + 1) * ((i : ℕ) + 1)) := by
    ext S
    rw [mem_filter, mem_canonicalPartition, mem_image]
    constructor
    · rintro ⟨⟨i', j, hj, rfl⟩, hcard⟩
      rw [card_Ico_canonical] at hcard
      have hii : i' = i := Fin.ext (by omega)
      subst hii
      exact ⟨j, mem_range.2 hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨i, j, mem_range.1 hj, rfl⟩, card_Ico_canonical m i j⟩
  rw [hfilt, card_image_of_injOn, card_range]
  intro j _ j' _ h
  simp only at h
  set o := ∑ l with l < i, ((l : ℕ) + 1) * m l
  have hj : o + j * ((i : ℕ) + 1) ∈
      Ico (o + j' * ((i : ℕ) + 1)) (o + (j' + 1) * ((i : ℕ) + 1)) := by
    rw [← h, mem_Ico, add_mul, one_mul]
    omega
  have hj' : o + j' * ((i : ℕ) + 1) ∈
      Ico (o + j * ((i : ℕ) + 1)) (o + (j + 1) * ((i : ℕ) + 1)) := by
    rw [h, mem_Ico, add_mul, one_mul]
    omega
  rw [mem_Ico] at hj hj'
  have h2 : j * ((i : ℕ) + 1) = j' * ((i : ℕ) + 1) := by omega
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) h2

theorem isSubpartition_canonicalPartition (m : Fin p → ℕ) : IsSubpartition (canonicalPartition m) :=
  isSubpartition_of_subset_canonicalPartition (subset_refl _)

end Canonical

/-! ### The cluster weight -/

section ClusterWeight

open scoped Classical in
/-- The weight of a family `X = (X_1, …, X_n)` of sets of blocks in the connected cluster sum of
the polymer gas of `Ẑ(π)`:
`𝟙_{G(X) connected, 2 ≤ |X_i|, |V_{X_i}| ≤ p} ∏ᵢ K(X_i) I(G(X))`. -/
noncomputable def clusterWeight (p : ℕ) (K : Finset (Finset ℕ) → ℝ)
    (X : Fin n → Finset (Finset ℕ)) : ℝ :=
  if (connectionGraph X).Connected ∧ ∀ i, 2 ≤ (X i).card ∧ ((X i).biUnion id).card ≤ p then
    (∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)
  else 0

/-- Profile invariance of an activity on subpartitions. -/
def IsProfileInvariant (K : Finset (Finset ℕ) → ℝ) : Prop :=
  ∀ X X' : Finset (Finset ℕ), IsSubpartition X → IsSubpartition X' →
    blockProfile X = blockProfile X' → K X = K X'

theorem card_biUnion_id_eq_sum {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    (X.biUnion id).card = ∑ S ∈ X, S.card :=
  card_biUnion fun _ hS _ hS' h => hX.2 hS hS' h

/-- `|X| ≤ |V_X|` for a subpartition. -/
theorem card_le_card_biUnion {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    X.card ≤ (X.biUnion id).card := by
  rw [card_biUnion_id_eq_sum hX, card_eq_sum_ones]
  exact sum_le_sum fun S hS => card_pos.2 (hX.1 S hS)

theorem clusterWeight_image {p : ℕ} {K : Finset (Finset ℕ) → ℝ} (hK : IsProfileInvariant K)
    {X : Fin n → Finset (Finset ℕ)} {f : Finset ℕ → Finset ℕ}
    (hU : IsSubpartition (univ.biUnion X)) (hU' : IsSubpartition ((univ.biUnion X).image f))
    (hf : Set.InjOn f ↑(univ.biUnion X)) (hcard : ∀ S ∈ univ.biUnion X, (f S).card = S.card) :
    clusterWeight p K (fun i => (X i).image f) = clusterWeight p K X := by
  have hsub : ∀ i, X i ⊆ univ.biUnion X := fun i => subset_biUnion_of_mem X (mem_univ i)
  have hsubP : ∀ i, IsSubpartition (X i) := fun i => SetPartition.isSubpartition_mono hU (hsub i)
  have hsubP' : ∀ i, IsSubpartition ((X i).image f) := fun i =>
    SetPartition.isSubpartition_mono hU' (image_subset_image (hsub i))
  have hinj := injOn_of_subset_biUnion hf
  have hcard_i : ∀ i, ((X i).image f).card = (X i).card := fun i => card_image_of_injOn (hinj i)
  have hV : ∀ i, (((X i).image f).biUnion id).card = ((X i).biUnion id).card := by
    intro i
    rw [card_biUnion_id_eq_sum (hsubP' i), card_biUnion_id_eq_sum (hsubP i),
      sum_image (hinj i)]
    exact sum_congr rfl fun S hS => hcard S (hsub i hS)
  have hprof : ∀ i, blockProfile ((X i).image f) = blockProfile (X i) := fun i =>
    blockProfile_image (hinj i) fun S hS => hcard S (hsub i hS)
  have hKi : ∀ i, K ((X i).image f) = K (X i) := fun i =>
    hK _ _ (hsubP' i) (hsubP i) (hprof i)
  have hcond : ((connectionGraph fun i => (X i).image f).Connected ∧
      ∀ i, 2 ≤ ((X i).image f).card ∧ (((X i).image f).biUnion id).card ≤ p) ↔
      ((connectionGraph X).Connected ∧ ∀ i, 2 ≤ (X i).card ∧ ((X i).biUnion id).card ≤ p) := by
    rw [connectionGraph_image hf]
    simp only [hcard_i, hV]
  unfold clusterWeight
  by_cases h : (connectionGraph X).Connected ∧ ∀ i, 2 ≤ (X i).card ∧ ((X i).biUnion id).card ≤ p
  · rw [ite_eq_left (hcond.2 h), ite_eq_left h, connectionGraph_image hf]
    simp only [hKi]
  · rw [ite_eq_right (fun h' => h (hcond.1 h')), ite_eq_right h]

end ClusterWeight

/-! ### Grouping by the union -/

section Union

variable {p : ℕ}

open scoped Classical in
/-- The sum of the cluster weights over the families `X_1, …, X_n ⊂ Y(m)` with
`X_1 ∪ ⋯ ∪ X_n = Y(m)`. -/
noncomputable def unionSum (p n : ℕ) (K : Finset (Finset ℕ) → ℝ) (m : Fin p → ℕ) : ℝ :=
  ∑ X ∈ (Fintype.piFinset fun _ : Fin n => (canonicalPartition m).powerset).filter
      (fun X => univ.biUnion X = canonicalPartition m), clusterWeight p K X

/-- The box `{m : m_i ≤ n p}` containing the profiles of the unions of `n` polymers. -/
def profileBox (p n : ℕ) : Finset (Fin p → ℕ) :=
  Fintype.piFinset fun _ : Fin p => range (n * p + 1)

theorem image_image_eq_self' {s U : Finset (Finset ℕ)} {f g : Finset ℕ → Finset ℕ} (hs : s ⊆ U)
    (hgf : ∀ a ∈ U, g (f a) = a) : (s.image f).image g = s := by
  rw [image_image]
  conv_rhs => rw [← image_id (s := s)]
  exact image_congr fun a ha => hgf a (hs ha)

open scoped Classical in
/-- **Relabeling the union.** For subpartitions `Y`, `Y'` with the same block profile, the sums of
the cluster weights over the families with union `Y`, resp. `Y'`, agree. -/
theorem sum_union_eq_of_blockProfile_eq {K : Finset (Finset ℕ) → ℝ} (hK : IsProfileInvariant K)
    {Y Y' : Finset (Finset ℕ)} (hY : IsSubpartition Y) (hY' : IsSubpartition Y')
    (hprof : blockProfile Y = blockProfile Y') :
    ∑ X ∈ (Fintype.piFinset fun _ : Fin n => Y.powerset).filter (fun X => univ.biUnion X = Y),
        clusterWeight p K X =
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => Y'.powerset).filter (fun X => univ.biUnion X = Y'),
        clusterWeight p K X := by
  obtain ⟨-, σ, hσ, -⟩ := Limits.exists_blockEquiv hY hY' hprof
  let f : Finset ℕ → Finset ℕ := fun a => if ha : a ∈ Y then (σ ⟨a, ha⟩ : Finset ℕ) else a
  let g : Finset ℕ → Finset ℕ := fun b => if hb : b ∈ Y' then (σ.symm ⟨b, hb⟩ : Finset ℕ) else b
  have hfU : ∀ a ∈ Y, f a ∈ Y' := fun a ha => by simp only [f, ha, dite_true]; exact (σ _).2
  have hgW : ∀ b ∈ Y', g b ∈ Y := fun b hb => by simp only [g, hb, dite_true]; exact (σ.symm _).2
  have hgf : ∀ a ∈ Y, g (f a) = a := fun a ha => by
    simp only [f, ha, dite_true, g, (σ _).2, Subtype.coe_eta, Equiv.symm_apply_apply]
  have hfg : ∀ b ∈ Y', f (g b) = b := fun b hb => by
    simp only [g, hb, dite_true, f, (σ.symm _).2, Subtype.coe_eta, Equiv.apply_symm_apply]
  have hfinj : Set.InjOn f ↑Y := fun a ha a' ha' h => by
    rw [← hgf a ha, ← hgf a' ha', h]
  have himU : Y.image f = Y' := by
    ext b
    simp only [mem_image]
    exact ⟨fun ⟨a, ha, hab⟩ => hab ▸ hfU a ha, fun hb => ⟨g b, hgW b hb, hfg b hb⟩⟩
  have himW : Y'.image g = Y := by
    ext a
    simp only [mem_image]
    exact ⟨fun ⟨b, hb, hba⟩ => hba ▸ hgW b hb, fun ha => ⟨f a, hfU a ha, hgf a ha⟩⟩
  have hfcard : ∀ a ∈ Y, (f a).card = a.card := fun a ha => by
    simp only [f, ha, dite_true]
    exact hσ ⟨a, ha⟩
  have hsub : ∀ {Z : Finset (Finset ℕ)} {X : Fin n → Finset (Finset ℕ)}, univ.biUnion X = Z →
      ∀ i, X i ⊆ Z := fun {_} {X} hX i => hX ▸ subset_biUnion_of_mem X (mem_univ i)
  refine Finset.sum_nbij' (fun X i => (X i).image f) (fun X i => (X i).image g) ?_ ?_ ?_ ?_ ?_
  · intro X hX
    simp only [mem_filter, Fintype.mem_piFinset, mem_powerset] at hX ⊢
    refine ⟨fun i => ?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
      exact hfU a (hX.1 i ha)
    · rw [← Finset.biUnion_image, hX.2, himU]
  · intro X hX
    simp only [mem_filter, Fintype.mem_piFinset, mem_powerset] at hX ⊢
    refine ⟨fun i => ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      exact hgW b (hX.1 i hb)
    · rw [← Finset.biUnion_image, hX.2, himW]
  · intro X hX
    simp only [mem_filter, Fintype.mem_piFinset] at hX
    funext i
    exact image_image_eq_self' (hsub hX.2 i) hgf
  · intro X hX
    simp only [mem_filter, Fintype.mem_piFinset] at hX
    funext i
    exact image_image_eq_self' (hsub hX.2 i) hfg
  · intro X hX
    simp only [mem_filter] at hX
    refine (clusterWeight_image hK ?_ ?_ ?_ ?_).symm
    · rw [hX.2]; exact hY
    · rw [hX.2, himU]; exact hY'
    · rw [hX.2]; exact hfinj
    · rw [hX.2]; exact hfcard

open scoped Classical in
/-- A family `X` with nonzero cluster weight and union `Y(m)` has `m_i ≤ n p`. -/
theorem unionSum_eq_zero_of_notMem {K : Finset (Finset ℕ) → ℝ} {m : Fin p → ℕ}
    (hm : m ∉ profileBox p n) : unionSum p n K m = 0 := by
  refine sum_eq_zero fun X hX => ?_
  rw [mem_filter, Fintype.mem_piFinset] at hX
  unfold clusterWeight
  rw [ite_eq_right]
  rintro ⟨-, hP⟩
  apply hm
  rw [profileBox, Fintype.mem_piFinset]
  intro i
  rw [mem_range, Nat.lt_succ_iff]
  have hXi : ∀ j, (X j).card ≤ p := fun j =>
    (card_le_card_biUnion (isSubpartition_of_subset_canonicalPartition
      (mem_powerset.1 (hX.1 j)))).trans (hP j).2
  have h1 : (canonicalPartition m).card ≤ n * p := by
    rw [← hX.2]
    calc (univ.biUnion X).card ≤ ∑ j, (X j).card := card_biUnion_le
      _ ≤ ∑ _j : Fin n, p := sum_le_sum fun j _ => hXi j
      _ = n * p := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [card_canonicalPartition] at h1
  exact (single_le_sum (fun j _ => Nat.zero_le (m j)) (mem_univ i)).trans h1

open scoped Classical in
/-- **Grouping by the union** (eqs. (4.153), (4.154)): for a subpartition `A` with
blocks of sizes at most `p`,
`∑_{X_1, …, X_n ⊂ A} clusterWeight(X) = ∑_{m ∈ box} ∏ᵢ C(#_{i+1} A, m_i) · unionSum(m)`. -/
theorem sum_piFinset_clusterWeight_eq {K : Finset (Finset ℕ) → ℝ} (hK : IsProfileInvariant K)
    {A : Finset (Finset ℕ)} (hA : IsSubpartition A) (hAp : ∀ S ∈ A, S.card ≤ p) :
    ∑ X ∈ Fintype.piFinset (fun _ : Fin n => A.powerset), clusterWeight p K X =
      ∑ m ∈ profileBox p n,
        (∏ i, ((blockCount p A i).choose (m i) : ℝ)) * unionSum p n K m := by
  have hA1 : ∀ S ∈ A, 1 ≤ S.card ∧ S.card ≤ p := fun S hS =>
    ⟨card_pos.2 (hA.1 S hS), hAp S hS⟩
  -- group by the union
  have hmaps : ∀ X ∈ Fintype.piFinset (fun _ : Fin n => A.powerset),
      univ.biUnion X ∈ A.powerset := by
    intro X hX
    rw [Fintype.mem_piFinset] at hX
    rw [mem_powerset]
    exact biUnion_subset.mpr fun i _ => mem_powerset.mp (hX i)
  rw [← sum_fiberwise_of_maps_to hmaps]
  -- transport each fibre to the canonical partition of its profile
  have hfib : ∀ Y ∈ A.powerset,
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun X => univ.biUnion X = Y), clusterWeight p K X =
        unionSum p n K (blockCount p Y) := by
    intro Y hY
    rw [mem_powerset] at hY
    have hYP : IsSubpartition Y := SetPartition.isSubpartition_mono hA hY
    have hY1 : ∀ S ∈ Y, 1 ≤ S.card ∧ S.card ≤ p := fun S hS => hA1 S (hY hS)
    unfold unionSum
    rw [← sum_union_eq_of_blockProfile_eq hK hYP (isSubpartition_canonicalPartition _)
      (blockProfile_eq_of_blockCount_eq hY1 card_mem_Icc_of_mem_canonicalPartition
        (blockCount_canonicalPartition _).symm)]
    refine sum_congr ?_ fun _ _ => rfl
    ext X
    simp only [mem_filter, Fintype.mem_piFinset, mem_powerset]
    refine ⟨fun h => ⟨fun i => h.2 ▸ subset_biUnion_of_mem X (mem_univ i), h.2⟩,
      fun h => ⟨fun i => (h.1 i).trans hY, h.2⟩⟩
  rw [sum_congr rfl hfib]
  -- group by the profile
  rw [← sum_filter_of_ne (p := fun Y => blockCount p Y ∈ profileBox p n) (fun Y _ hY => by
    by_contra hm
    exact hY (unionSum_eq_zero_of_notMem hm))]
  have hmaps' : ∀ Y ∈ A.powerset.filter (fun Y => blockCount p Y ∈ profileBox p n),
      blockCount p Y ∈ profileBox p n := fun Y hY => (mem_filter.1 hY).2
  rw [← sum_fiberwise_of_maps_to hmaps']
  refine sum_congr rfl fun m hm => ?_
  rw [sum_congr rfl fun Y hY => by rw [(mem_filter.1 hY).2], sum_const, nsmul_eq_mul]
  congr 1
  rw [filter_filter]
  have hfilt : (A.powerset.filter fun Y => blockCount p Y ∈ profileBox p n ∧ blockCount p Y = m) =
      A.powerset.filter fun Y => blockCount p Y = m := by
    refine filter_congr fun Y _ => ?_
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hm, h⟩
  rw [hfilt, card_powerset_filter_blockCount hA1]
  push_cast
  rfl

end Union

end PropFiveFortyFive

end MultipoleBKT

end
