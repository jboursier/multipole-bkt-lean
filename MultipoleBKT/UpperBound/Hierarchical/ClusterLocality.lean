/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.BadSetOn
public import MultipoleBKT.Matching.RouteGeneric.Exceptional

/-!
# Locality of the `q`-clustering

The paper: Definition 5.1 and its null-set convention, and the locality
and relabeling paragraph after Definition 5.1. The locality also justifies the
dependence of frozen bad radii on bad coordinates in Remark 5.17 and
Lemma 5.16. We prove the following.

* `sameSignClustering_sdiff` (**locality**): if `q ≥ 1`, `G ⊆ I` and every cluster of the run on `I`
  meeting `G` is a singleton, then the run on `I ∖ G` outputs exactly the clusters of the run on `I`
  that avoid `G`, with the same removal values. (The thresholds `τ` can only increase when labels
  are removed; a crowded centre whose cluster avoids `G` is still crowded without `G`, and it is
  still the crowded centre with the smallest `r`.)
* `card_eq_one_or_of_mem_clustering` (**the convention of Section 5.2**): if the distances
  `|z_i - z_j|`, `i ≠ j`, are pairwise distinct (`SameSignGeneric z`), every cluster is a singleton
  or has exactly `q + 1` elements.
* `ae_sameSignGeneric`: Lebesgue-almost every configuration has pairwise distinct same-sign
  distances, for the positive and for the negative charges
  (`RouteGeneric.volume_distance_eq`).
-/

@[expose] public section

open Finset MeasureTheory

namespace MultipoleBKT

namespace UpperBound

open TheoremTwo

variable {N : ℕ} {q : ℕ} {h : ℝ} {z : Fin N → ℂ} {r : Fin N → ℝ}

/-! ### One overcrowding step -/

section Step

/-- In the overcrowding branch (`τ ≠ h`, no `r_i/4 = τ`), `τ` is the first overcrowding time:
`0 ≤ τ`, some ball is overcrowded at `τ`, and no ball is overcrowded before. -/
theorem crowding_step {I : Finset (Fin N)} (hI : I.Nonempty) (hτh : clusterTau q h z r I hI ≠ h)
    (hs : ¬ (I.filter fun i => r i / 4 = clusterTau q h z r I hI).Nonempty) :
    0 ≤ clusterTau q h z r I hI ∧ (crowdedSet q z I (clusterTau q h z r I hI)).Nonempty ∧
      ∀ t, 0 ≤ t → (crowdedSet q z I t).Nonempty → clusterTau q h z r I hI ≤ t := by
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
  refine ⟨hmem.1, hmem.2, fun t ht htc => csInf_le ⟨0, fun s hs => hs.1⟩ ⟨ht, htc⟩⟩

theorem clusterChosen_spec {I : Finset (Fin N)} (hI : I.Nonempty) (τ : ℝ) :
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
theorem clusterKey_of_mem {I : Finset (Fin N)} {τ : ℝ} {j : Fin N}
    (hj : j ∈ crowdedSet q z I τ) : clusterKey q z r I τ j = toLex (false, toLex (r j, j)) := by
  simp [clusterKey, hj]

/-- The chosen centre is overcrowded when some centre is. -/
theorem clusterChosen_mem_crowdedSet {I : Finset (Fin N)} (hI : I.Nonempty) {τ : ℝ}
    (hne : (crowdedSet q z I τ).Nonempty) :
    clusterChosen q z r I τ hI ∈ crowdedSet q z I τ := by
  classical
  obtain ⟨c, hc⟩ := hne
  have hcI : c ∈ I := (Finset.mem_filter.1 (by rw [crowdedSet_eq] at hc; exact hc)).1
  have hle := (clusterChosen_spec (q := q) (z := z) (r := r) hI τ).2 c hcI
  by_contra hnot
  simp only [clusterKey, Prod.Lex.toLex_le_toLex, hnot, hc, not_false_eq_true, decide_true,
    not_true_eq_false, decide_false] at hle
  rcases hle with hlt | ⟨heq, -⟩
  · exact absurd hlt (by decide)
  · exact absurd heq (by decide)

/-- The cluster of an overcrowding step contains the chosen centre and the labels whose balls
meet its ball. -/
theorem mem_clusterJ_iff {I : Finset (Fin N)} (hI : I.Nonempty) {τ : ℝ} {j : Fin N} :
    j ∈ clusterJ q z r I τ hI ↔
      j = clusterChosen q z r I τ hI ∨
        (j ∈ I ∧ ‖z (clusterChosen q z r I τ hI) - z j‖ ≤ 2 * τ) := by
  classical
  unfold clusterJ
  rw [Finset.mem_insert, Finset.mem_filter, closedBall_inter_nonempty_iff, norm_sub_rev]

end Step

/-! ### Locality -/

section Locality

open scoped Classical in
/-- The singletons `({i}, h)`, `i ∈ I`, avoiding `G` are those of `I ∖ G`. -/
theorem filter_image_singleton (I G : Finset (Fin N)) (h : ℝ) :
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
/-- **Locality of the clustering** (Remark 5.17, made precise): if `q ≥ 1`, `G ⊆ I` and every
cluster of the run on `I` that meets `G` is a singleton, the run on `I ∖ G` outputs exactly the
clusters (with their removal values) of the run on `I` that avoid `G`. -/
theorem sameSignClustering_sdiff (hq : 1 ≤ q) :
    ∀ (I G : Finset (Fin N)), G ⊆ I →
      (∀ p ∈ sameSignClustering q h z r I, ∀ g ∈ G, g ∈ p.1 → p.1.card = 1) →
      sameSignClustering q h z r (I \ G) =
        (sameSignClustering q h z r I).filter fun p => Disjoint p.1 G := by
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
  intro G hGI hsing
  rcases I.eq_empty_or_nonempty with rfl | hI
  · rw [Finset.subset_empty.1 hGI]
    simp [sameSignClustering_of_empty]
  -- the clusters of the later steps lie in the run on `I`
  have hrun := sameSignClustering_eq_of_nonempty q h z r I hI
  set τ := clusterTau q h z r I hI with hτdef
  by_cases hτh : τ = h
  · -- the last step: all singletons at `h`
    rw [hrun, ite_eq_left hτh, filter_image_singleton]
    rcases (I \ G).eq_empty_or_nonempty with he | hne
    · rw [he, sameSignClustering_of_empty, Finset.image_empty]
    rw [sameSignClustering_eq_of_nonempty q h z r (I \ G) hne]
    have hτ' : clusterTau q h z r (I \ G) hne = h := by
      refine le_antisymm (clusterTau_le_left hne) ?_
      calc h = τ := hτh.symm
        _ ≤ clusterTau q h z r (I \ G) hne := clusterTau_mono hI hne Finset.sdiff_subset
    rw [ite_eq_left hτ']
  rw [hrun, ite_eq_right hτh] at hsing ⊢
  by_cases hs : (I.filter fun i => r i / 4 = τ).Nonempty
  · -- a singleton step
    rw [dite_eq_left hs] at hsing ⊢
    set i := (I.filter fun i => r i / 4 = τ).min' hs with hidef
    have hiI : i ∈ I := (Finset.mem_filter.1 (Finset.min'_mem _ hs)).1
    have hiτ : r i / 4 = τ := (Finset.mem_filter.1 (Finset.min'_mem _ hs)).2
    have hsub : I.erase i ⊂ I := Finset.erase_ssubset hiI
    have hsing' : ∀ p ∈ sameSignClustering q h z r (I.erase i), ∀ g ∈ G, g ∈ p.1 →
        p.1.card = 1 := fun p hp g hg hgp => hsing p (Finset.mem_insert_of_mem hp) g hg hgp
    have hclust : ∀ p ∈ sameSignClustering q h z r (I.erase i), i ∉ p.1 := fun p hp hip =>
      (Finset.notMem_erase i I) (fst_subset_of_mem_clustering hp hip)
    by_cases hiG : i ∈ G
    · -- a good singleton: the run on `I ∖ G` does not see it
      have hG' : G.erase i ⊆ I.erase i := Finset.erase_subset_erase i hGI
      have key := ih _ hsub (G.erase i) hG' fun p hp g hg hgp =>
        hsing' p hp g (Finset.mem_of_mem_erase hg) hgp
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
    · -- a bad singleton: it is removed at the same time in the run on `I ∖ G`
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
      rw [sameSignClustering_eq_of_nonempty q h z r (I \ G) hne, ite_eq_right (by rw [hτ']; exact hτh),
        dite_eq_left hs', hmin, hτ']
      have hG' : G ⊆ I.erase i := fun g hg =>
        Finset.mem_erase.2 ⟨fun h => hiG (h ▸ hg), hGI hg⟩
      have key := ih _ hsub G hG' hsing'
      have hset : (I \ G).erase i = I.erase i \ G := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_sdiff]
        tauto
      rw [hset, key, Finset.filter_insert, ite_eq_left (by
        rw [Finset.disjoint_singleton_left]; exact hiG)]
  · -- an overcrowding step
    rw [dite_eq_right hs] at hsing ⊢
    obtain ⟨hτ0, hcrowd, hfirst⟩ := crowding_step (q := q) (h := h) (z := z) (r := r) hI hτh hs
    set c := clusterChosen q z r I τ hI with hcdef
    set J := clusterJ q z r I τ hI with hJdef
    have hcI : c ∈ I := (clusterChosen_spec (q := q) (z := z) (r := r) hI τ).1
    have hcc : c ∈ crowdedSet q z I τ := clusterChosen_mem_crowdedSet hI hcrowd
    -- the neighbours of `c`
    set T := I.filter fun j => j ≠ c ∧ ‖z c - z j‖ ≤ 2 * τ with hTdef
    have hT : q ≤ T.card := by
      rw [crowdedSet_eq, Finset.mem_filter] at hcc
      exact hcc.2
    have hTJ : insert c T ⊆ J := by
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact Finset.mem_insert_self _ _
      · rw [Finset.mem_filter] at hj
        exact (mem_clusterJ_iff hI).2 (Or.inr ⟨hj.1, hj.2.2⟩)
    have hJcard : 2 ≤ J.card := by
      have hcT : c ∉ T := fun h => (Finset.mem_filter.1 h).2.1 rfl
      have := Finset.card_le_card hTJ
      rw [Finset.card_insert_of_notMem hcT] at this
      omega
    have hJG : Disjoint J G := by
      rw [Finset.disjoint_left]
      intro g hgJ hgG
      have := hsing _ (Finset.mem_insert_self _ _) g hgG hgJ
      simp only at this
      omega
    have hJsub : J ⊆ I := by
      intro j hj
      rcases (mem_clusterJ_iff hI).1 hj with rfl | hj
      · exact hcI
      · exact hj.1
    have hcIG : c ∈ I \ G :=
      Finset.mem_sdiff.2 ⟨hcI, Finset.disjoint_left.1 hJG (Finset.mem_insert_self _ _)⟩
    have hne : (I \ G).Nonempty := ⟨c, hcIG⟩
    -- `c` is still overcrowded without `G`
    have hcc' : c ∈ crowdedSet q z (I \ G) τ := by
      rw [crowdedSet_eq, Finset.mem_filter]
      refine ⟨hcIG, hT.trans (Finset.card_le_card fun j hj => ?_)⟩
      have hjJ : j ∈ J := hTJ (Finset.mem_insert_of_mem hj)
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
    -- the chosen centre is the same
    have hchosen : clusterChosen q z r (I \ G) τ hne = c := by
      obtain ⟨hc'I, hc'min⟩ := clusterChosen_spec (q := q) (z := z) (r := r) hne τ
      have hc'c := clusterChosen_mem_crowdedSet (r := r) hne ⟨c, hcc'⟩
      have hc'c₀ := crowdedSet_subset_of_subset (q := q) (z := z) Finset.sdiff_subset τ hc'c
      have h1 := hc'min c hcIG
      have h2 := (clusterChosen_spec (q := q) (z := z) (r := r) hI τ).2 _ (Finset.mem_sdiff.1 hc'I).1
      rw [← hcdef] at h2
      rw [clusterKey_of_mem hc'c, clusterKey_of_mem hcc'] at h1
      rw [clusterKey_of_mem hcc, clusterKey_of_mem hc'c₀] at h2
      have := le_antisymm h1 h2
      simpa using congrArg (fun k => (ofLex (ofLex k).2).2) this
    have hJ' : clusterJ q z r (I \ G) τ hne = J := by
      ext j
      rw [mem_clusterJ_iff hne, mem_clusterJ_iff hI, hchosen]
      constructor
      · rintro (h | ⟨hj, hd⟩)
        · exact Or.inl h
        · exact Or.inr ⟨(Finset.mem_sdiff.1 hj).1, hd⟩
      · rintro (h | ⟨hj, hd⟩)
        · exact Or.inl h
        · have hjJ : j ∈ J := (mem_clusterJ_iff hI).2 (Or.inr ⟨hj, hd⟩)
          exact Or.inr ⟨Finset.mem_sdiff.2 ⟨hj, Finset.disjoint_left.1 hJG hjJ⟩, hd⟩
    rw [sameSignClustering_eq_of_nonempty q h z r (I \ G) hne, ite_eq_right (by rw [hτ']; exact hτh),
      dite_eq_right hs', hτ', hJ']
    have hG' : G ⊆ I \ J := fun g hg =>
      Finset.mem_sdiff.2 ⟨hGI hg, fun hgJ => Finset.disjoint_left.1 hJG hgJ hg⟩
    have hJne : J.Nonempty := ⟨c, Finset.mem_insert_self _ _⟩
    have key := ih _ (sdiff_ssubset_of_nonempty hJsub hJne) G hG' fun p hp g hg hgp =>
      hsing p (Finset.mem_insert_of_mem hp) g hg hgp
    have hset : (I \ G) \ J = (I \ J) \ G := by
      ext k
      simp only [Finset.mem_sdiff]
      tauto
    rw [hset, key, Finset.filter_insert, ite_eq_left hJG]

end Locality

/-! ### The size of the clusters -/

section Size

/-- The distances `|z_i - z_j|`, `i ≠ j`, are pairwise distinct (as unordered pairs). -/
def SameSignGeneric (z : Fin N → ℂ) : Prop :=
  ∀ i j k l : Fin N, i ≠ j → k ≠ l → ‖z i - z j‖ = ‖z k - z l‖ →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k)

/-- **The convention of Section 5.2**: for pairwise distinct same-sign distances, every cluster of an
overcrowding step has exactly `q + 1` elements, so every cluster is a singleton or has `q + 1`
elements. -/
theorem card_eq_one_or_of_mem_clustering (hq : 1 ≤ q) (hz : SameSignGeneric z) :
    ∀ (I : Finset (Fin N)), ∀ p ∈ sameSignClustering q h z r I,
      p.1.card = 1 ∨ p.1.card = q + 1 := by
  classical
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp [sameSignClustering_of_empty]
  have hrun := sameSignClustering_eq_of_nonempty q h z r I hI
  set τ := clusterTau q h z r I hI with hτdef
  by_cases hτh : τ = h
  · rw [hrun, ite_eq_left hτh]
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact Or.inl (Finset.card_singleton i)
  rw [hrun, ite_eq_right hτh]
  by_cases hs : (I.filter fun i => r i / 4 = τ).Nonempty
  · rw [dite_eq_left hs]
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact Or.inl (Finset.card_singleton _)
    · exact ih _ (Finset.erase_ssubset (Finset.mem_filter.1 (Finset.min'_mem _ hs)).1) p hp
  rw [dite_eq_right hs]
  obtain ⟨hτ0, hcrowd, hfirst⟩ := crowding_step (q := q) (h := h) (z := z) (r := r) hI hτh hs
  set c := clusterChosen q z r I τ hI
  have hcI : c ∈ I := (clusterChosen_spec (q := q) (z := z) (r := r) hI τ).1
  have hcc : c ∈ crowdedSet q z I τ := clusterChosen_mem_crowdedSet hI hcrowd
  set T := I.filter fun j => j ≠ c ∧ ‖z c - z j‖ ≤ 2 * τ with hTdef
  have hT : q ≤ T.card := by
    rw [crowdedSet_eq, Finset.mem_filter] at hcc
    exact hcc.2
  -- exactly `q` neighbours
  have hTq : T.card ≤ q := by
    by_contra hlt
    push Not at hlt
    have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨j₀, hj₀T, hj₀max⟩ := Finset.exists_max_image T (fun j => ‖z c - z j‖) hTne
    have hj₀ := Finset.mem_filter.1 hj₀T
    set T' := T.erase j₀
    have hT'card : q ≤ T'.card := by
      rw [Finset.card_erase_of_mem hj₀T]
      omega
    have hT'ne : T'.Nonempty := Finset.card_pos.1 (by omega)
    set t' := T'.sup' hT'ne (fun j => ‖z c - z j‖) / 2
    have hlt' : ∀ j ∈ T', ‖z c - z j‖ < ‖z c - z j₀‖ := by
      intro j hj
      have hjT := Finset.mem_of_mem_erase hj
      have hj := Finset.mem_filter.1 hjT
      have hjj₀ : j ≠ j₀ := Finset.ne_of_mem_erase ‹j ∈ T'›
      refine lt_of_le_of_ne (hj₀max j hjT) fun heq => ?_
      rcases hz c j c j₀ (Ne.symm hj.2.1) (Ne.symm hj₀.2.1) heq with ⟨-, h⟩ | ⟨h, -⟩
      · exact hjj₀ h
      · exact hj₀.2.1 h.symm
    have ht'τ : t' < τ := by
      have : T'.sup' hT'ne (fun j => ‖z c - z j‖) < 2 * τ := by
        rw [Finset.sup'_lt_iff]
        exact fun j hj => (hlt' j hj).trans_le hj₀.2.2
      simp only [t']
      linarith
    have ht'0 : 0 ≤ t' := by
      obtain ⟨j, hj⟩ := hT'ne
      have := Finset.le_sup' (fun j => ‖z c - z j‖) hj
      simp only [t']
      linarith [norm_nonneg (z c - z j)]
    have hcrowd' : c ∈ crowdedSet q z I t' := by
      rw [crowdedSet_eq, Finset.mem_filter]
      refine ⟨hcI, hT'card.trans (Finset.card_le_card fun j hj => ?_)⟩
      have hjT := Finset.mem_of_mem_erase hj
      have hj' := Finset.mem_filter.1 hjT
      refine Finset.mem_filter.2 ⟨hj'.1, hj'.2.1, ?_⟩
      have := Finset.le_sup' (fun j => ‖z c - z j‖) hj
      simp only [t']
      linarith
    exact absurd (hfirst t' ht'0 ⟨c, hcrowd'⟩) (not_le.2 ht'τ)
  intro p hp
  rcases Finset.mem_insert.1 hp with rfl | hp
  · right
    have hJ : clusterJ q z r I τ hI = insert c T := by
      ext j
      rw [mem_clusterJ_iff hI, Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (h | ⟨hj, hd⟩)
        · exact Or.inl h
        · by_cases hjc : j = c
          · exact Or.inl hjc
          · exact Or.inr ⟨hj, hjc, hd⟩
      · rintro (h | ⟨hj, -, hd⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hj, hd⟩
    have hcT : c ∉ T := fun h => (Finset.mem_filter.1 h).2.1 rfl
    simp only
    rw [hJ, Finset.card_insert_of_notMem hcT]
    omega
  · have hJsub : clusterJ q z r I τ hI ⊆ I := by
      intro j hj
      rcases (mem_clusterJ_iff hI).1 hj with rfl | hj
      · exact hcI
      · exact hj.1
    exact ih _ (sdiff_ssubset_of_nonempty hJsub ⟨c, Finset.mem_insert_self _ _⟩) p hp

/-- Lebesgue-almost every configuration has pairwise distinct same-sign distances, for the
positive and for the negative charges. -/
theorem ae_sameSignGeneric :
    ∀ᵐ c ∂(volume : Measure (Fin N → ℂ × ℂ)),
      SameSignGeneric (fun i => (c i).1) ∧ SameSignGeneric (fun i => (c i).2) := by
  filter_upwards [RouteGeneric.ae_outsideExceptional (ι := Fin N) 0] with c hc
  exact ⟨hc.2.1, hc.2.2.1⟩

end Size

end UpperBound

end MultipoleBKT

end
