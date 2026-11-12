/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.RouteExchange.Relabel
public import MultipoleBKT.Main.PropFiveFortyFive.Grouping

/-!
# Permutations between fixed choices

The paper: (5.60) and (5.61). Equal-size bad sets are related by a permutation. Within their
complement, the block-preserving bijection for equal profiles extends to a
permutation of all dipole labels.
-/

@[expose] public section

open Finset

namespace MultipoleBKT.UpperBound.RouteExchange

open Hierarchical Multipole SetPartition TheoremTwo PropFiveFortyFive

variable {N p : ℕ} {n : Fin p → ℕ}

/-- The admissible good partitions on the complement of a fixed bad-label set. -/
noncomputable def choices (V : Finset (Fin N)) (p : ℕ) (n : Fin p → ℕ) :
    Finset (Finset (Finset ℕ)) := by
  classical
  exact (partitions ((univ \ V).map Fin.valEmbedding)).filter
    (fun π => (∀ S ∈ π, S.card ≤ p) ∧ blockCount p π = n)

/-- The literal partition factor in (5.61). -/
theorem card_choices {V : Finset (Fin N)}
    (hV : V.card = N - ∑ i : Fin p, ((i : ℕ) + 1) * n i)
    (hn : ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N) :
    (choices V p n).card = (∑ i : Fin p, ((i : ℕ) + 1) * n i).factorial / profileWeight n := by
  classical
  have hcard : ((univ \ V).map Fin.valEmbedding).card =
      ∑ i : Fin p, ((i : ℕ) + 1) * n i := by
    rw [card_map, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hV]
    omega
  have h := card_partitions_filter_mul p ((univ \ V).map Fin.valEmbedding) n hcard.symm
  rw [hcard] at h
  rw [choices, ← h, Nat.mul_div_cancel _ (profileWeight_pos n)]

/-- There is an admissible fixed choice whenever the profile fits in `[N]`. -/
theorem choices_nonempty {V : Finset (Fin N)}
    (hV : V.card = N - ∑ i : Fin p, ((i : ℕ) + 1) * n i)
    (hn : ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N) : (choices V p n).Nonempty := by
  classical
  have hcard : ((univ \ V).map Fin.valEmbedding).card =
      ∑ i : Fin p, ((i : ℕ) + 1) * n i := by
    rw [card_map, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hV]
    omega
  have h := card_partitions_filter_mul p ((univ \ V).map Fin.valEmbedding) n hcard.symm
  by_contra hempty
  have hz : (choices V p n).card = 0 := card_eq_zero.2 (not_nonempty_iff_eq_empty.1 hempty)
  change (choices V p n).card * profileWeight n = _ at h
  rw [hz, zero_mul] at h
  exact (Nat.factorial_ne_zero _) h.symm

/-- Partitions of the good labels with equal profile are related by a label
permutation preserving the bad-label set. -/
theorem exists_perm_choices {V : Finset (Fin N)} {π π' : Finset (Finset ℕ)}
    (hπ : π ∈ choices V p n) (hπ' : π' ∈ choices V p n) :
    ∃ e : Equiv.Perm (Fin N), V.map e.toEmbedding = V ∧ mapBlocks e π = π' := by
  classical
  obtain ⟨hπp, hπle, hπn⟩ := mem_filter.1 hπ
  obtain ⟨hπp', hπle', hπn'⟩ := mem_filter.1 hπ'
  have hπs := (mem_partitions.1 hπp).1
  have hπs' := (mem_partitions.1 hπp').1
  have hprof : blockProfile π = blockProfile π' :=
    blockProfile_eq_of_blockCount_eq
      (fun S hS => ⟨card_pos.2 (hπs.1 S hS), hπle S hS⟩)
      (fun S hS => ⟨card_pos.2 (hπs'.1 S hS), hπle' S hS⟩)
      (hπn.trans hπn'.symm)
  obtain ⟨a, σ, -, ha⟩ := Limits.exists_blockEquiv hπs hπs' hprof
  have hb : π.biUnion id = (univ \ V).map Fin.valEmbedding := (mem_partitions.1 hπp).2
  have hb' : π'.biUnion id = (univ \ V).map Fin.valEmbedding := (mem_partitions.1 hπp').2
  have hlt : ∀ i ∈ π.biUnion id, i < N := by
    intro i hi
    rw [hb] at hi
    obtain ⟨j, -, rfl⟩ := mem_map.1 hi
    exact j.isLt
  have hlt' : ∀ i ∈ π'.biUnion id, i < N := by
    intro i hi
    rw [hb'] at hi
    obtain ⟨j, -, rfl⟩ := mem_map.1 hi
    exact j.isLt
  let f : π.biUnion id → Fin N := fun i => ⟨i, hlt i i.2⟩
  let f' : π'.biUnion id → Fin N := fun i => ⟨i, hlt' i i.2⟩
  have hf : Function.Injective f := fun i j h => Subtype.ext (congrArg Fin.val h)
  have hf' : Function.Injective f' := fun i j h => Subtype.ext (congrArg Fin.val h)
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f (f' ∘ a) hf (hf'.comp a.injective)
  have hmap : mapBlocks e π = π' := by
    have hS : ∀ S : π, (S : Finset ℕ).map (natPerm e).toEmbedding = (σ S : Finset ℕ) := by
      intro S
      ext j
      constructor
      · intro hj
        obtain ⟨i, hi, rfl⟩ := mem_map.1 hj
        have hiU : i ∈ π.biUnion id := mem_biUnion.2 ⟨S, S.2, hi⟩
        have hab : (a ⟨i, hiU⟩ : ℕ) ∈ (σ S : Finset ℕ) := by
          have hbS : Limits.blockOf π (⟨i, hiU⟩ : π.biUnion id) = S := (Limits.blockOf_eq_iff hπs _ S).2 hi
          exact (Limits.blockOf_eq_iff hπs' _ (σ S)).1 (by rw [ha, hbS])
        have heq := congrArg Fin.val (he ⟨i, hiU⟩)
        rw [← natPerm_apply e (f ⟨i, hiU⟩)] at heq
        exact heq.symm ▸ hab
      · intro hj
        have hjU : j ∈ π'.biUnion id := mem_biUnion.2 ⟨σ S, (σ S).2, hj⟩
        obtain ⟨i, hi⟩ := a.surjective ⟨j, hjU⟩
        have hbi : Limits.blockOf π i = S := by
          apply σ.injective
          rw [← ha, hi]
          exact (Limits.blockOf_eq_iff hπs' _ (σ S)).2 hj
        have hiS := (Limits.blockOf_eq_iff hπs i S).1 hbi
        refine mem_map.2 ⟨i, hiS, ?_⟩
        have heq := congrArg Fin.val (he i)
        change (e (f i) : ℕ) = (a i : ℕ) at heq
        rw [hi] at heq
        exact (natPerm_apply e (f i)).trans heq
    ext S
    simp only [mapBlocks, mem_image]
    constructor
    · rintro ⟨T, hT, rfl⟩
      rw [hS ⟨T, hT⟩]
      exact (σ _).2
    · intro hS'
      obtain ⟨T, hT⟩ := σ.surjective ⟨S, hS'⟩
      exact ⟨T, T.2, (hS T).trans (congrArg Subtype.val hT)⟩
  have hgood : (univ \ V).map e.toEmbedding = univ \ V := by
    ext j
    constructor
    · rintro hj
      obtain ⟨i, hi, rfl⟩ := mem_map.1 hj
      have hiU : (i : ℕ) ∈ π.biUnion id := by rw [hb]; exact mem_map.2 ⟨i, hi, rfl⟩
      have heq := he ⟨i, hiU⟩
      have ht : f' (a ⟨i, hiU⟩) ∈ univ \ V := by
        have hu := hb'.subset (a ⟨i, hiU⟩).2
        obtain ⟨k, hk, heq'⟩ := mem_map.1 hu
        exact (Fin.ext heq' : k = f' (a ⟨i, hiU⟩)) ▸ hk
      exact heq.symm ▸ ht
    · intro hj
      have hjU : (j : ℕ) ∈ π'.biUnion id := by rw [hb']; exact mem_map.2 ⟨j, hj, rfl⟩
      obtain ⟨i, hi⟩ := a.surjective ⟨j, hjU⟩
      have hiG : f i ∈ univ \ V := by
        have hu := hb.subset i.2
        obtain ⟨k, hk, heq⟩ := mem_map.1 hu
        exact (Fin.ext heq : k = f i) ▸ hk
      exact mem_map.2 ⟨f i, hiG, (he i).trans (congrArg f' hi)⟩
  refine ⟨e, ?_, hmap⟩
  have hcomp := congrArg (fun G : Finset (Fin N) => univ \ G) hgood
  simpa only [map_sdiff, map_univ_equiv, sdiff_sdiff_self_left, univ_inter] using hcomp

end MultipoleBKT.UpperBound.RouteExchange

end
