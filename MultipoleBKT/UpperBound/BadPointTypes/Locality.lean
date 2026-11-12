/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Clustering

/-!
# Locality of the `q`-clustering under the deletion of whole clusters

The paper: Definition 5.1 (Definition 5.1, frozen as `sameSignClustering`), as used in the proof of Lemma 5.39
(Lemma 5.39,: "Deleting all type-3 dipoles preserves the bad classes and radii
on `B`", and: "The restriction to `V_bad^1` preserves its clustering and radii").

`clustering_sdiff_of_union`: if `G ⊆ I` is a union of clusters of the run on `I` (every cluster
lies in `G` or avoids it), the run on `I ∖ G` outputs exactly the clusters of the run on `I`
that avoid `G`, with the same removal values. Along the recursion: the thresholds can only
increase when labels are removed; a removed singleton outside `G` is still removed at the same
value; an overcrowded centre whose cluster avoids `G` is still overcrowded without `G` (its
neighbours are its cluster), and is still the overcrowded centre with the smallest `r`; clusters
inside `G` are simply skipped. (The special case where the clusters meeting `G` are singletons is
the locality of Remark 5.17.)
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset TheoremTwo UpperBound

variable {N : ℕ} {q : ℕ} {h : ℝ} {z : Fin N → ℂ} {r : Fin N → ℝ}

/-! ### One overcrowding step -/

/-- In the overcrowding branch (`τ ≠ h`, no `r_i/4 = τ`), `τ ≥ 0` and some ball is overcrowded
at `τ`. -/
theorem overcrowding_spec {I : Finset (Fin N)} (hI : I.Nonempty)
    (hτh : clusterTau q h z r I hI ≠ h)
    (hs : ¬ (I.filter fun i => r i / 4 = clusterTau q h z r I hI).Nonempty) :
    0 ≤ clusterTau q h z r I hI ∧ (crowdedSet q z I (clusterTau q h z r I hI)).Nonempty := by
  classical
  obtain ⟨i₀, hi₀, hi₀inf⟩ := Finset.exists_mem_eq_inf' hI r
  have hnotinf : clusterTau q h z r I hI ≠ I.inf' hI r / 4 := by
    intro heq
    exact hs ⟨i₀, Finset.mem_filter.2 ⟨hi₀, by rw [heq, hi₀inf]⟩⟩
  set S := {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty} with hS
  have hτS : S.Nonempty ∧ clusterTau q h z r I hI = sInf S := by
    unfold clusterTau at hτh hnotinf ⊢
    by_cases hne : S.Nonempty
    · rw [ite_eq_left hne] at hτh hnotinf ⊢
      refine ⟨hne, ?_⟩
      rcases min_choice (min h (I.inf' hI r / 4)) (sInf S) with h1 | h1
      · rw [h1] at hτh hnotinf
        rcases min_choice h (I.inf' hI r / 4) with h2 | h2
        · exact absurd h2 hτh
        · exact absurd h2 hnotinf
      · exact h1
    · rw [ite_eq_right hne] at hτh hnotinf
      rcases min_choice h (I.inf' hI r / 4) with h2 | h2
      · exact absurd h2 hτh
      · exact absurd h2 hnotinf
  obtain ⟨hne, hτ⟩ := hτS
  have hmem := (sInf_crowded_le_iff q z I hne (sInf S)).1 le_rfl
  rw [hτ]
  exact ⟨hmem.1, hmem.2⟩

/-- The chosen centre lies in `I` and minimises the key. -/
theorem chosen_spec {I : Finset (Fin N)} (hI : I.Nonempty) (τ : ℝ) :
    clusterChosen q z r I τ hI ∈ I ∧
      ∀ j ∈ I, clusterKey q z r I τ (clusterChosen q z r I τ hI) ≤ clusterKey q z r I τ j := by
  classical
  obtain ⟨j₀, hj₀, hj₀k⟩ := Finset.mem_image.1
    ((I.image (clusterKey q z r I τ)).min'_mem (hI.image _))
  have hc : clusterChosen q z r I τ hI = j₀ := by
    simp only [clusterChosen, ← hj₀k]; rfl
  rw [hc]
  refine ⟨hj₀, fun j hj => ?_⟩
  rw [hj₀k]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hj)

open scoped Classical in
theorem clusterKey_eq_of_crowded {I : Finset (Fin N)} {τ : ℝ} {j : Fin N}
    (hj : j ∈ crowdedSet q z I τ) : clusterKey q z r I τ j = toLex (false, toLex (r j, j)) := by
  simp [clusterKey, hj]

/-- The chosen centre is overcrowded when some centre is. -/
theorem chosen_mem_crowdedSet {I : Finset (Fin N)} (hI : I.Nonempty) {τ : ℝ}
    (hne : (crowdedSet q z I τ).Nonempty) :
    clusterChosen q z r I τ hI ∈ crowdedSet q z I τ := by
  classical
  obtain ⟨c, hc⟩ := hne
  have hcI : c ∈ I := (Finset.mem_filter.1 (by rw [crowdedSet_eq] at hc; exact hc)).1
  have hle := (chosen_spec (q := q) (z := z) (r := r) hI τ).2 c hcI
  by_contra hnot
  simp only [clusterKey, Prod.Lex.toLex_le_toLex, hnot, hc, not_false_eq_true, decide_true,
    not_true_eq_false, decide_false] at hle
  rcases hle with hlt | ⟨heq, -⟩
  · exact absurd hlt (by decide)
  · exact absurd heq (by decide)

/-- The cluster of an overcrowding step: the chosen centre and the labels whose balls meet its
ball. -/
theorem mem_clusterJ_iff_chosen {I : Finset (Fin N)} (hI : I.Nonempty) {τ : ℝ} {j : Fin N} :
    j ∈ clusterJ q z r I τ hI ↔
      j = clusterChosen q z r I τ hI ∨
        (j ∈ I ∧ ‖z (clusterChosen q z r I τ hI) - z j‖ ≤ 2 * τ) := by
  classical
  unfold clusterJ
  rw [Finset.mem_insert, Finset.mem_filter, closedBall_inter_nonempty_iff, norm_sub_rev]

/-! ### Locality -/

open scoped Classical in
theorem filter_image_singleton_disjoint (I G : Finset (Fin N)) (h : ℝ) :
    ((I.image fun i => (({i} : Finset (Fin N)), h)).filter fun p => Disjoint p.1 G) =
      (I \ G).image fun i => (({i} : Finset (Fin N)), h) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hG⟩
    exact ⟨i, ⟨hi, Finset.disjoint_singleton_left.1 hG⟩, rfl⟩
  · rintro ⟨i, ⟨hi, hG⟩, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, Finset.disjoint_singleton_left.2 hG⟩

open scoped Classical in
/-- **Locality of the clustering**: if `G ⊆ I` is a union of clusters of the run on `I`, the
run on `I ∖ G` outputs exactly the clusters (with their removal values) of the run on `I` that
avoid `G`. -/
theorem clustering_sdiff_of_union :
    ∀ (I G : Finset (Fin N)), G ⊆ I →
      (∀ p ∈ sameSignClustering q h z r I, p.1 ⊆ G ∨ Disjoint p.1 G) →
      sameSignClustering q h z r (I \ G) =
        (sameSignClustering q h z r I).filter fun p => Disjoint p.1 G := by
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
  intro G hGI hunion
  rcases I.eq_empty_or_nonempty with rfl | hI
  · rw [Finset.subset_empty.1 hGI]
    simp [sameSignClustering_of_empty]
  have hrun := sameSignClustering_eq_of_nonempty q h z r I hI
  set τ := clusterTau q h z r I hI with hτdef
  by_cases hτh : τ = h
  · -- the last step: all singletons at `h`
    rw [hrun, ite_eq_left hτh, filter_image_singleton_disjoint]
    rcases (I \ G).eq_empty_or_nonempty with he | hne
    · rw [he, sameSignClustering_of_empty, Finset.image_empty]
    rw [sameSignClustering_eq_of_nonempty q h z r (I \ G) hne]
    have hτ' : clusterTau q h z r (I \ G) hne = h := by
      refine le_antisymm (clusterTau_le_left hne) ?_
      calc h = τ := hτh.symm
        _ ≤ clusterTau q h z r (I \ G) hne := clusterTau_mono hI hne Finset.sdiff_subset
    rw [ite_eq_left hτ']
  rw [hrun, ite_eq_right hτh] at hunion ⊢
  by_cases hs : (I.filter fun i => r i / 4 = τ).Nonempty
  · -- a singleton step
    rw [dite_eq_left hs] at hunion ⊢
    set i := (I.filter fun i => r i / 4 = τ).min' hs with hidef
    have hiI : i ∈ I := (Finset.mem_filter.1 (Finset.min'_mem _ hs)).1
    have hiτ : r i / 4 = τ := (Finset.mem_filter.1 (Finset.min'_mem _ hs)).2
    have hsub : I.erase i ⊂ I := Finset.erase_ssubset hiI
    have hunion' : ∀ p ∈ sameSignClustering q h z r (I.erase i), p.1 ⊆ G ∨ Disjoint p.1 G :=
      fun p hp => hunion p (Finset.mem_insert_of_mem hp)
    have hclust : ∀ p ∈ sameSignClustering q h z r (I.erase i), i ∉ p.1 := fun p hp hip =>
      (Finset.notMem_erase i I) (fst_subset_of_mem_clustering hp hip)
    by_cases hiG : i ∈ G
    · -- a singleton inside `G`: the run on `I ∖ G` does not see it
      have hG' : G.erase i ⊆ I.erase i := Finset.erase_subset_erase i hGI
      have key := ih _ hsub (G.erase i) hG' fun p hp => by
        rcases hunion' p hp with h1 | h1
        · exact Or.inl fun g hg => Finset.mem_erase.2 ⟨fun hgi => hclust p hp (hgi ▸ hg), h1 hg⟩
        · exact Or.inr (Finset.disjoint_of_subset_right (Finset.erase_subset i G) h1)
      have hset : I.erase i \ G.erase i = I \ G := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hki, hkI⟩, hkG⟩
          exact ⟨hkI, fun hk => hkG ⟨hki, hk⟩⟩
        · rintro ⟨hkI, hkG⟩
          exact ⟨⟨fun hk => hkG (hk ▸ hiG), hkI⟩, fun hk => hkG hk.2⟩
      rw [← hset, key, Finset.filter_insert, ite_eq_right (by
        rw [Finset.disjoint_singleton_left]; exact not_not.2 hiG)]
      refine Finset.filter_congr fun p hp => ?_
      rw [← Finset.disjoint_erase_comm, Finset.erase_eq_of_notMem (hclust p hp)]
    · -- a singleton outside `G`: removed at the same value in the run on `I ∖ G`
      have hiIG : i ∈ I \ G := Finset.mem_sdiff.2 ⟨hiI, hiG⟩
      have hne : (I \ G).Nonempty := ⟨i, hiIG⟩
      have hτ' : clusterTau q h z r (I \ G) hne = τ :=
        le_antisymm (hiτ ▸ clusterTau_le_div hne hiIG)
          (clusterTau_mono hI hne Finset.sdiff_subset)
      have hs' : ((I \ G).filter fun i => r i / 4 = clusterTau q h z r (I \ G) hne).Nonempty :=
        ⟨i, Finset.mem_filter.2 ⟨hiIG, by rw [hτ', hiτ]⟩⟩
      have hmin : ((I \ G).filter fun i => r i / 4 = clusterTau q h z r (I \ G) hne).min' hs' =
          i := by
        refine le_antisymm (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hiIG, by rw [hτ', hiτ]⟩)) ?_
        refine Finset.min'_le _ _ (Finset.mem_filter.2 ⟨?_, ?_⟩)
        · exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 (Finset.min'_mem _ hs')).1).1
        · rw [(Finset.mem_filter.1 (Finset.min'_mem _ hs')).2, hτ']
      rw [sameSignClustering_eq_of_nonempty q h z r (I \ G) hne,
        ite_eq_right (by rw [hτ']; exact hτh), dite_eq_left hs', hmin, hτ']
      have hG' : G ⊆ I.erase i := fun g hg =>
        Finset.mem_erase.2 ⟨fun h => hiG (h ▸ hg), hGI hg⟩
      have key := ih _ hsub G hG' hunion'
      have hset : (I \ G).erase i = I.erase i \ G := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_sdiff]
        tauto
      rw [hset, key, Finset.filter_insert, ite_eq_left (by
        rw [Finset.disjoint_singleton_left]; exact hiG)]
  · -- an overcrowding step
    rw [dite_eq_right hs] at hunion ⊢
    obtain ⟨hτ0, hcrowd⟩ := overcrowding_spec (q := q) (h := h) (z := z) (r := r) hI hτh hs
    set c := clusterChosen q z r I τ hI with hcdef
    set J := clusterJ q z r I τ hI with hJdef
    have hcI : c ∈ I := (chosen_spec (q := q) (z := z) (r := r) hI τ).1
    have hcc : c ∈ crowdedSet q z I τ := chosen_mem_crowdedSet hI hcrowd
    have hJsub : J ⊆ I := by
      intro j hj
      rcases (mem_clusterJ_iff_chosen hI).1 hj with rfl | hj
      · exact hcI
      · exact hj.1
    have hcJ : c ∈ J := Finset.mem_insert_self _ _
    have hJne : J.Nonempty := ⟨c, hcJ⟩
    have hunion' : ∀ p ∈ sameSignClustering q h z r (I \ J), p.1 ⊆ G ∨ Disjoint p.1 G :=
      fun p hp => hunion p (Finset.mem_insert_of_mem hp)
    have hJp : J ⊆ G ∨ Disjoint J G := hunion _ (Finset.mem_insert_self _ _)
    rcases hJp with hJG | hJG
    · -- a cluster inside `G` is skipped
      have hG' : G \ J ⊆ I \ J := Finset.sdiff_subset_sdiff hGI le_rfl
      have hdisjJ : ∀ p ∈ sameSignClustering q h z r (I \ J), Disjoint p.1 J := fun p hp =>
        Finset.disjoint_of_subset_left (fst_subset_of_mem_clustering hp) Finset.sdiff_disjoint
      have key := ih _ (sdiff_ssubset_of_nonempty hJsub hJne) (G \ J) hG' fun p hp => by
        rcases hunion' p hp with h1 | h1
        · exact Or.inl fun g hg => Finset.mem_sdiff.2
            ⟨h1 hg, Finset.disjoint_left.1 (hdisjJ p hp) hg⟩
        · exact Or.inr (Finset.disjoint_of_subset_right Finset.sdiff_subset h1)
      have hset : (I \ J) \ (G \ J) = I \ G := by
        ext k
        simp only [Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨hkI, hkJ⟩, hkGJ⟩
          exact ⟨hkI, fun hkG => hkGJ ⟨hkG, hkJ⟩⟩
        · rintro ⟨hkI, hkG⟩
          exact ⟨⟨hkI, fun hkJ => hkG (hJG hkJ)⟩, fun hk => hkG hk.1⟩
      rw [← hset, key, Finset.filter_insert, ite_eq_right (fun hdis =>
        (Finset.disjoint_left.1 hdis hcJ) (hJG hcJ))]
      refine Finset.filter_congr fun p hp => ?_
      constructor
      · intro h1
        rw [Finset.disjoint_left] at h1 ⊢
        intro a ha haG
        exact h1 ha (Finset.mem_sdiff.2 ⟨haG, Finset.disjoint_left.1 (hdisjJ p hp) ha⟩)
      · intro h1
        exact Finset.disjoint_of_subset_right Finset.sdiff_subset h1
    · -- a cluster avoiding `G` is formed at the same step
      set T := I.filter fun j => j ≠ c ∧ ‖z c - z j‖ ≤ 2 * τ with hTdef
      have hT : q ≤ T.card := by
        rw [crowdedSet_eq, Finset.mem_filter] at hcc
        exact hcc.2
      have hTJ : T ⊆ J := by
        intro j hj
        rw [Finset.mem_filter] at hj
        exact (mem_clusterJ_iff_chosen hI).2 (Or.inr ⟨hj.1, hj.2.2⟩)
      have hcIG : c ∈ I \ G :=
        Finset.mem_sdiff.2 ⟨hcI, Finset.disjoint_left.1 hJG hcJ⟩
      have hne : (I \ G).Nonempty := ⟨c, hcIG⟩
      have hcc' : c ∈ crowdedSet q z (I \ G) τ := by
        rw [crowdedSet_eq, Finset.mem_filter]
        refine ⟨hcIG, hT.trans (Finset.card_le_card fun j hj => ?_)⟩
        have hjJ : j ∈ J := hTJ hj
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨Finset.mem_sdiff.2 ⟨hj.1, Finset.disjoint_left.1 hJG hjJ⟩, hj.2⟩
      have hτ' : clusterTau q h z r (I \ G) hne = τ := by
        refine le_antisymm ?_ (clusterTau_mono hI hne Finset.sdiff_subset)
        have hS : {t : ℝ | 0 ≤ t ∧ (crowdedSet q z (I \ G) t).Nonempty}.Nonempty :=
          ⟨τ, hτ0, c, hcc'⟩
        unfold clusterTau
        rw [ite_eq_left hS]
        exact (min_le_right _ _).trans (csInf_le ⟨0, fun t ht => ht.1⟩ ⟨hτ0, c, hcc'⟩)
      have hs' : ¬ ((I \ G).filter fun i => r i / 4 = clusterTau q h z r (I \ G) hne).Nonempty := by
        rintro ⟨i, hi⟩
        rw [Finset.mem_filter, hτ'] at hi
        exact hs ⟨i, Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hi.1).1, hi.2⟩⟩
      have hchosen : clusterChosen q z r (I \ G) τ hne = c := by
        obtain ⟨hc'I, hc'min⟩ := chosen_spec (q := q) (z := z) (r := r) hne τ
        have hc'c := chosen_mem_crowdedSet (r := r) hne ⟨c, hcc'⟩
        have hc'c₀ := crowdedSet_subset_of_subset (q := q) (z := z) Finset.sdiff_subset τ hc'c
        have h1 := hc'min c hcIG
        have h2 := (chosen_spec (q := q) (z := z) (r := r) hI τ).2 _ (Finset.mem_sdiff.1 hc'I).1
        rw [← hcdef] at h2
        rw [clusterKey_eq_of_crowded hc'c, clusterKey_eq_of_crowded hcc'] at h1
        rw [clusterKey_eq_of_crowded hcc, clusterKey_eq_of_crowded hc'c₀] at h2
        have := le_antisymm h1 h2
        simpa using congrArg (fun k => (ofLex (ofLex k).2).2) this
      have hJ' : clusterJ q z r (I \ G) τ hne = J := by
        ext j
        rw [mem_clusterJ_iff_chosen hne, mem_clusterJ_iff_chosen hI, hchosen]
        constructor
        · rintro (h | ⟨hj, hd⟩)
          · exact Or.inl h
          · exact Or.inr ⟨(Finset.mem_sdiff.1 hj).1, hd⟩
        · rintro (h | ⟨hj, hd⟩)
          · exact Or.inl h
          · have hjJ : j ∈ J := (mem_clusterJ_iff_chosen hI).2 (Or.inr ⟨hj, hd⟩)
            exact Or.inr ⟨Finset.mem_sdiff.2 ⟨hj, Finset.disjoint_left.1 hJG hjJ⟩, hd⟩
      rw [sameSignClustering_eq_of_nonempty q h z r (I \ G) hne,
        ite_eq_right (by rw [hτ']; exact hτh), dite_eq_right hs', hτ', hJ']
      have hG' : G ⊆ I \ J := fun g hg =>
        Finset.mem_sdiff.2 ⟨hGI hg, fun hgJ => Finset.disjoint_left.1 hJG hgJ hg⟩
      have key := ih _ (sdiff_ssubset_of_nonempty hJsub hJne) G hG' hunion'
      have hset : (I \ G) \ J = (I \ J) \ G := by
        ext k
        simp only [Finset.mem_sdiff]
        tauto
      rw [hset, key, Finset.filter_insert, ite_eq_left hJG]

end BadPointTypes

end MultipoleBKT

end
