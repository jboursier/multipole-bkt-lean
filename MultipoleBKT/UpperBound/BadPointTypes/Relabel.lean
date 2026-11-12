/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.Locality
public import MultipoleBKT.Matching.RouteGeneric.Exceptional

/-!
# Relabelling the `q`-clustering

The paper: Definition 5.1
(Definition 5.1, frozen as `sameSignClustering`). A sub-configuration on the labels
`V ⊆ [n]` (as in the partition functions `Z^{(1)}_{bad,N₁}`, `Z^{(2)}_{bad,N₂}` of Lemma 5.39,
eq. (5.113), whose labels are `V^1_bad`, `V^2_bad`) is written on `Fin |V|` through the
increasing enumeration `e : Fin |V| ↪o Fin n` of `V`. The clustering only uses the order of the
labels to break ties, so it commutes with `e` (`clustering_map`):
`run_{z}(e(I)) = e(run_{z ∘ e}(I))`. For arbitrary embeddings, distinct
dipole lengths eliminate the final index tie breaker (`clustering_embedding`).
The exceptional set includes the stopping coincidences from Section 4.1.

Combined with the locality of `Locality.lean`, when the complement of `V` is a union of
clusters of the run on `[n]`, the clusters and removal values of the sub-configuration are those
of the full configuration (`exists_cluster_comp_iff`, `clusterRemovalValue_comp`).
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset TheoremTwo UpperBound

variable {m n : ℕ} {q : ℕ} {h : ℝ}

section Map

variable (e : Fin m ↪o Fin n) (z : Fin n → ℂ) (r : Fin n → ℝ)

theorem crowdedSet_map (I : Finset (Fin m)) (t : ℝ) :
    crowdedSet q z (I.map e.toEmbedding) t =
      (crowdedSet q (z ∘ e) I t).map e.toEmbedding := by
  classical
  rw [crowdedSet_eq, crowdedSet_eq, Finset.filter_map]
  congr 1
  refine Finset.filter_congr fun a _ => ?_
  rw [Function.comp_apply, Finset.filter_map, Finset.card_map]
  have : (I.filter ((fun j => j ≠ e.toEmbedding a ∧ ‖z (e.toEmbedding a) - z j‖ ≤ 2 * t) ∘
      e.toEmbedding)) = I.filter fun b => b ≠ a ∧ ‖(z ∘ e) a - (z ∘ e) b‖ ≤ 2 * t := by
    refine Finset.filter_congr fun b _ => ?_
    simp only [Function.comp_apply, RelEmbedding.coe_toEmbedding, ne_eq,
      e.injective.eq_iff]
  rw [this]

theorem clusterTau_map {I : Finset (Fin m)} (hI : I.Nonempty)
    (hI' : (I.map e.toEmbedding).Nonempty) :
    clusterTau q h z r (I.map e.toEmbedding) hI' = clusterTau q h (z ∘ e) (r ∘ e) I hI := by
  have hset : {t : ℝ | 0 ≤ t ∧ (crowdedSet q z (I.map e.toEmbedding) t).Nonempty} =
      {t : ℝ | 0 ≤ t ∧ (crowdedSet q (z ∘ e) I t).Nonempty} := by
    ext t
    simp only [Set.mem_ofPred_eq, crowdedSet_map, Finset.map_nonempty]
  have hinf : (I.map e.toEmbedding).inf' hI' r = I.inf' hI (r ∘ e) := by
    rw [Finset.inf'_map]
    rfl
  unfold clusterTau
  rw [hset, hinf]

/-- The relabelling of the keys `(j ∉ crowded, r_j, j)`; it is monotone. -/
def keyMap (k : Bool ×ₗ (ℝ ×ₗ Fin m)) : Bool ×ₗ (ℝ ×ₗ Fin n) :=
  toLex ((ofLex k).1, toLex ((ofLex (ofLex k).2).1, e (ofLex (ofLex k).2).2))

theorem keyMap_monotone : Monotone (keyMap e) := by
  intro k k' hkk'
  rw [Prod.Lex.le_iff] at hkk'
  unfold keyMap
  rw [Prod.Lex.toLex_le_toLex]
  rcases hkk' with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h1, ?_⟩
    rw [Prod.Lex.le_iff] at h2
    show toLex _ ≤ toLex _
    rw [Prod.Lex.toLex_le_toLex]
    rcases h2 with h3 | ⟨h3, h4⟩
    · exact Or.inl h3
    · exact Or.inr ⟨h3, e.le_iff_le.2 h4⟩

theorem clusterKey_map (I : Finset (Fin m)) (τ : ℝ) (a : Fin m) :
    clusterKey q z r (I.map e.toEmbedding) τ (e a) =
      keyMap e (clusterKey q (z ∘ e) (r ∘ e) I τ a) := by
  classical
  unfold clusterKey keyMap
  simp only [ofLex_toLex, crowdedSet_map]
  congr 2
  have hmem : e.toEmbedding a ∈ (crowdedSet q (z ∘ e) I τ).map e.toEmbedding ↔
      a ∈ crowdedSet q (z ∘ e) I τ := Finset.mem_map' e.toEmbedding
  exact decide_eq_decide.2 (not_congr hmem)

theorem min'_congr_set {α : Type*} [LinearOrder α] {s t : Finset α} (hst : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.min' hs = t.min' ht := by
  subst hst
  rfl

theorem clusterChosen_map {I : Finset (Fin m)} (hI : I.Nonempty)
    (hI' : (I.map e.toEmbedding).Nonempty) (τ : ℝ) :
    clusterChosen q z r (I.map e.toEmbedding) τ hI' = e (clusterChosen q (z ∘ e) (r ∘ e) I τ hI) := by
  classical
  have himage : (I.map e.toEmbedding).image (clusterKey q z r (I.map e.toEmbedding) τ) =
      (I.image (clusterKey q (z ∘ e) (r ∘ e) I τ)).image (keyMap e) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, (clusterKey_map e z r I τ a).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨e a, ⟨a, ha, rfl⟩, clusterKey_map e z r I τ a⟩
  have hne : ((I.image (clusterKey q (z ∘ e) (r ∘ e) I τ)).image (keyMap e)).Nonempty :=
    (hI.image _).image _
  unfold clusterChosen
  rw [min'_congr_set himage _ hne, Finset.min'_image (keyMap_monotone e)]
  rfl

theorem clusterJ_map {I : Finset (Fin m)} (hI : I.Nonempty)
    (hI' : (I.map e.toEmbedding).Nonempty) (τ : ℝ) :
    clusterJ q z r (I.map e.toEmbedding) τ hI' =
      (clusterJ q (z ∘ e) (r ∘ e) I τ hI).map e.toEmbedding := by
  classical
  unfold clusterJ
  rw [clusterChosen_map e z r hI hI', Finset.map_insert, Finset.filter_map]
  rfl

/-- **The clustering commutes with order embeddings.** -/
theorem clustering_map : ∀ I : Finset (Fin m),
    sameSignClustering q h z r (I.map e.toEmbedding) =
      (sameSignClustering q h (z ∘ e) (r ∘ e) I).image
        fun p => (p.1.map e.toEmbedding, p.2) := by
  classical
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp [sameSignClustering_of_empty]
  have hI' : (I.map e.toEmbedding).Nonempty := hI.map
  rw [sameSignClustering_eq_of_nonempty q h z r _ hI',
    sameSignClustering_eq_of_nonempty q h (z ∘ e) (r ∘ e) I hI, clusterTau_map e z r hI hI']
  set τ := clusterTau q h (z ∘ e) (r ∘ e) I hI with hτ
  by_cases hτh : τ = h
  · rw [ite_eq_left hτh, ite_eq_left hτh, Finset.image_image, Finset.map_eq_image,
      Finset.image_image]
    refine Finset.image_congr fun a _ => ?_
    simp
  rw [ite_eq_right hτh, ite_eq_right hτh]
  have hfilt : ((I.map e.toEmbedding).filter fun i => r i / 4 = τ) =
      (I.filter fun a => (r ∘ e) a / 4 = τ).map e.toEmbedding := by
    rw [Finset.filter_map]
    rfl
  by_cases hs : (I.filter fun a => (r ∘ e) a / 4 = τ).Nonempty
  · have hs' : ((I.map e.toEmbedding).filter fun i => r i / 4 = τ).Nonempty := by
      rw [hfilt]; exact hs.map
    rw [dite_eq_left hs, dite_eq_left hs']
    set a := (I.filter fun a => (r ∘ e) a / 4 = τ).min' hs with ha
    have haI : a ∈ I := (Finset.mem_filter.1 (Finset.min'_mem _ hs)).1
    have hmin : ((I.map e.toEmbedding).filter fun i => r i / 4 = τ).min' hs' = e a := by
      refine (min'_congr_set hfilt hs' hs.map).trans ?_
      rw [min'_congr_set (Finset.map_eq_image e.toEmbedding _) hs.map (hs.image _),
        Finset.min'_image (show Monotone (⇑e.toEmbedding) from e.monotone)]
      rfl
    rw [hmin]
    have herase : (I.map e.toEmbedding).erase (e a) = (I.erase a).map e.toEmbedding := by
      rw [Finset.map_erase]
      rfl
    rw [herase, ih _ (Finset.erase_ssubset haI), Finset.image_insert]
    congr 1
  · have hs' : ¬ ((I.map e.toEmbedding).filter fun i => r i / 4 = τ).Nonempty := by
      rw [hfilt, Finset.map_nonempty]; exact hs
    rw [dite_eq_right hs, dite_eq_right hs', clusterJ_map e z r hI hI']
    set J := clusterJ q (z ∘ e) (r ∘ e) I τ hI with hJ
    have hJI : J ⊆ I := by
      intro j hj
      rcases (mem_clusterJ_iff_chosen hI).1 hj with rfl | hj
      · exact (chosen_spec (q := q) (z := z ∘ e) (r := r ∘ e) hI τ).1
      · exact hj.1
    have hJne : J.Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
    rw [← Finset.map_sdiff, ih _ (sdiff_ssubset_of_nonempty hJI hJne), Finset.image_insert]

end Map

/-! ### Arbitrary relabelings outside the exceptional set -/

section Embedding

variable (e : Fin m ↪ Fin n) (z : Fin n → ℂ) (r : Fin n → ℝ)

theorem crowdedSet_embedding (I : Finset (Fin m)) (t : ℝ) :
    crowdedSet q z (I.map e) t =
      (crowdedSet q (z ∘ e) I t).map e := by
  classical
  rw [crowdedSet_eq, crowdedSet_eq, Finset.filter_map]
  congr 1
  refine Finset.filter_congr fun a _ => ?_
  rw [Function.comp_apply, Finset.filter_map, Finset.card_map]
  have : (I.filter ((fun j => j ≠ e a ∧ ‖z (e a) - z j‖ ≤ 2 * t) ∘
      e)) = I.filter fun b => b ≠ a ∧ ‖(z ∘ e) a - (z ∘ e) b‖ ≤ 2 * t := by
    refine Finset.filter_congr fun b _ => ?_
    simp only [Function.comp_apply, ne_eq,
      e.injective.eq_iff]
  rw [this]

theorem clusterTau_embedding {I : Finset (Fin m)} (hI : I.Nonempty)
    (hI' : (I.map e).Nonempty) :
    clusterTau q h z r (I.map e) hI' = clusterTau q h (z ∘ e) (r ∘ e) I hI := by
  have hset : {t : ℝ | 0 ≤ t ∧ (crowdedSet q z (I.map e) t).Nonempty} =
      {t : ℝ | 0 ≤ t ∧ (crowdedSet q (z ∘ e) I t).Nonempty} := by
    ext t
    simp only [Set.mem_ofPred_eq, crowdedSet_embedding, Finset.map_nonempty]
  have hinf : (I.map e).inf' hI' r = I.inf' hI (r ∘ e) := by
    rw [Finset.inf'_map]
  unfold clusterTau
  rw [hset, hinf]


/-- With distinct dipole lengths, the final index tie breaker is never used.
See the paper, Definition 5.1. -/
theorem clusterKey_embedding_le (hr : Function.Injective r) (I : Finset (Fin m))
    (τ : ℝ) (a b : Fin m) :
    clusterKey q z r (I.map e) τ (e a) ≤ clusterKey q z r (I.map e) τ (e b) ↔
      clusterKey q (z ∘ e) (r ∘ e) I τ a ≤ clusterKey q (z ∘ e) (r ∘ e) I τ b := by
  classical
  by_cases hab : a = b
  · subst b
    exact iff_of_true le_rfl le_rfl
  have hrab : r (e a) ≠ r (e b) := fun h => hab (e.injective (hr h))
  simp only [clusterKey, crowdedSet_embedding, Finset.mem_map', Function.comp_apply,
    Prod.Lex.toLex_le_toLex, hrab, false_and, or_false]

/-- The crowded centre is intrinsic when dipole lengths are distinct. -/
theorem clusterChosen_embedding (hr : Function.Injective r) {I : Finset (Fin m)}
    (hI : I.Nonempty) (hI' : (I.map e).Nonempty) (τ : ℝ) :
    clusterChosen q z r (I.map e) τ hI' = e (clusterChosen q (z ∘ e) (r ∘ e) I τ hI) := by
  classical
  obtain ⟨hc, hmin⟩ := chosen_spec (q := q) (z := z) (r := r) hI' τ
  obtain ⟨b, hb, heq⟩ := Finset.mem_map.1 hc
  obtain ⟨ha, hmina⟩ := chosen_spec (q := q) (z := z ∘ e) (r := r ∘ e) hI τ
  have hba := (clusterKey_embedding_le e z r hr I τ b (clusterChosen q (z ∘ e) (r ∘ e) I τ hI)).1
    (by rw [heq]; exact hmin _ (Finset.mem_map_of_mem _ ha))
  have he := le_antisymm (hmina b hb) hba
  have heab := congrArg (fun k : Bool ×ₗ (ℝ ×ₗ Fin m) => (ofLex (ofLex k).2).2) he
  change clusterChosen q (z ∘ e) (r ∘ e) I τ hI = b at heab
  rw [← heq, heab]

theorem clusterJ_embedding (hr : Function.Injective r) {I : Finset (Fin m)}
    (hI : I.Nonempty) (hI' : (I.map e).Nonempty) (τ : ℝ) :
    clusterJ q z r (I.map e) τ hI' =
      (clusterJ q (z ∘ e) (r ∘ e) I τ hI).map e := by
  classical
  unfold clusterJ
  rw [clusterChosen_embedding e z r hr hI hI', Finset.map_insert, Finset.filter_map]
  rfl

/-- The recursion commutes with every embedding when dipole lengths are distinct.
This includes every permutation off the polynomial exceptional set of Section 4.1. -/
theorem clustering_embedding (hr : Function.Injective r) : ∀ I : Finset (Fin m),
    sameSignClustering q h z r (I.map e) =
      (sameSignClustering q h (z ∘ e) (r ∘ e) I).image
        fun p => (p.1.map e, p.2) := by
  classical
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp [sameSignClustering_of_empty]
  have hI' : (I.map e).Nonempty := hI.map
  rw [sameSignClustering_eq_of_nonempty q h z r _ hI',
    sameSignClustering_eq_of_nonempty q h (z ∘ e) (r ∘ e) I hI,
    clusterTau_embedding e z r hI hI']
  set τ := clusterTau q h (z ∘ e) (r ∘ e) I hI
  by_cases hτh : τ = h
  · rw [ite_eq_left hτh, ite_eq_left hτh, Finset.image_image, Finset.map_eq_image,
      Finset.image_image]
    refine Finset.image_congr fun a _ => ?_
    simp
  rw [ite_eq_right hτh, ite_eq_right hτh]
  have hfilt : ((I.map e).filter fun i => r i / 4 = τ) =
      (I.filter fun a => (r ∘ e) a / 4 = τ).map e := by
    rw [Finset.filter_map]
    rfl
  by_cases hs : (I.filter fun a => (r ∘ e) a / 4 = τ).Nonempty
  · have hs' : ((I.map e).filter fun i => r i / 4 = τ).Nonempty := by
      rw [hfilt]; exact hs.map
    rw [dite_eq_left hs, dite_eq_left hs']
    set a := (I.filter fun a => (r ∘ e) a / 4 = τ).min' hs
    have ha := Finset.mem_filter.1 (Finset.min'_mem _ hs)
    have hb := Finset.mem_filter.1 (Finset.min'_mem _ hs')
    have hmin : ((I.map e).filter fun i => r i / 4 = τ).min' hs' = e a := by
      apply hr
      change r _ = (r ∘ e) a
      linarith [ha.2, hb.2]
    rw [hmin, ← Finset.map_erase, ih _ (Finset.erase_ssubset ha.1), Finset.image_insert]
    congr 1
  · have hs' : ¬ ((I.map e).filter fun i => r i / 4 = τ).Nonempty := by
      rw [hfilt, Finset.map_nonempty]; exact hs
    rw [dite_eq_right hs, dite_eq_right hs', clusterJ_embedding e z r hr hI hI']
    set J := clusterJ q (z ∘ e) (r ∘ e) I τ hI
    have hJI : J ⊆ I := by
      intro j hj
      rcases (mem_clusterJ_iff_chosen hI).1 hj with rfl | hj
      · exact (chosen_spec (q := q) (z := z ∘ e) (r := r ∘ e) hI τ).1
      · exact hj.1
    have hJne : J.Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
    rw [← Finset.map_sdiff, ih _ (sdiff_ssubset_of_nonempty hJI hJne), Finset.image_insert]

/-- Every permutation commutes with clustering outside the full polynomial
exceptional set, including stopping-threshold coincidences. -/
theorem clustering_permutation {c : Fin n → ℂ × ℂ} (hc : RouteGeneric.OutsideExceptional h c)
    (π : Equiv.Perm (Fin n)) (z : Fin n → ℂ) (I : Finset (Fin n)) :
    sameSignClustering q h z (fun i => ‖(c i).1 - (c i).2‖) (I.map π.toEmbedding) =
      (sameSignClustering q h (z ∘ π) (fun i => ‖(c (π i)).1 - (c (π i)).2‖) I).image
        fun p => (p.1.map π.toEmbedding, p.2) := by
  apply clustering_embedding
  intro i j hij
  exact congrArg Prod.fst (hc.1 (show
    (fun p : Fin n × Fin n => ‖(c p.1).1 - (c p.2).2‖) (i, i) =
    (fun p : Fin n × Fin n => ‖(c p.1).1 - (c p.2).2‖) (j, j) from hij))

/-- Arbitrary relabeling holds almost everywhere, simultaneously for every
permutation, sign, and initial label set. -/
theorem ae_clustering_permutation (q : ℕ) (h : ℝ) :
    ∀ᵐ c ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℂ × ℂ)),
      ∀ (π : Equiv.Perm (Fin n)) (z : Fin n → ℂ) (I : Finset (Fin n)),
      sameSignClustering q h z (fun i => ‖(c i).1 - (c i).2‖) (I.map π.toEmbedding) =
        (sameSignClustering q h (z ∘ π) (fun i => ‖(c (π i)).1 - (c (π i)).2‖) I).image
          fun p => (p.1.map π.toEmbedding, p.2) := by
  filter_upwards [RouteGeneric.ae_outsideExceptional (ι := Fin n) h] with c hc
  exact fun π z I => clustering_permutation hc π z I

end Embedding

/-! ### Sub-configurations -/

section Sub

variable (e : Fin m ↪o Fin n) {z : Fin n → ℂ} {r : Fin n → ℝ}

open scoped Classical in
/-- If the complement of the range of `e` is a union of clusters of the run on `[n]`, the run on
the range of `e` is the set of clusters of the run on `[n]` that lie in the range. -/
theorem clustering_range (hunion : ∀ p ∈ sameSignClustering q h z r univ,
      p.1 ⊆ univ \ univ.map e.toEmbedding ∨ Disjoint p.1 (univ \ univ.map e.toEmbedding)) :
    sameSignClustering q h z r (univ.map e.toEmbedding) =
      (sameSignClustering q h z r univ).filter
        fun p => Disjoint p.1 (univ \ univ.map e.toEmbedding) := by
  have h := clustering_sdiff_of_union (q := q) (h := h) (z := z) (r := r) univ
    (univ \ univ.map e.toEmbedding) (Finset.subset_univ _) hunion
  rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] at h
  exact h

/-- The clusters of the sub-configuration containing `a` correspond to the clusters of the full
configuration containing `e a`, with the same cardinality and removal value. -/
theorem exists_cluster_comp_iff (hunion : ∀ p ∈ sameSignClustering q h z r univ,
      p.1 ⊆ univ \ univ.map e.toEmbedding ∨ Disjoint p.1 (univ \ univ.map e.toEmbedding))
    (P : ℕ → ℝ → Prop) (a : Fin m) :
    (∃ p ∈ sameSignClustering q h (z ∘ e) (r ∘ e) univ, a ∈ p.1 ∧ P p.1.card p.2) ↔
      ∃ p ∈ sameSignClustering q h z r univ, e a ∈ p.1 ∧ P p.1.card p.2 := by
  classical
  have hrange := clustering_range e hunion
  rw [clustering_map e z r univ] at hrange
  constructor
  · rintro ⟨p, hp, hap, hP⟩
    have hmem : (p.1.map e.toEmbedding, p.2) ∈
        (sameSignClustering q h z r univ).filter
          fun p => Disjoint p.1 (univ \ univ.map e.toEmbedding) := by
      rw [← hrange]
      exact Finset.mem_image_of_mem _ hp
    refine ⟨_, (Finset.mem_filter.1 hmem).1, Finset.mem_map_of_mem _ hap, ?_⟩
    rw [Finset.card_map]
    exact hP
  · rintro ⟨p, hp, hap, hP⟩
    have hdisj : Disjoint p.1 (univ \ univ.map e.toEmbedding) := by
      rcases hunion p hp with h1 | h1
      · exfalso
        have := h1 hap
        rw [Finset.mem_sdiff] at this
        exact this.2 (Finset.mem_map_of_mem _ (Finset.mem_univ a))
      · exact h1
    have hmem : p ∈ (sameSignClustering q h z r univ).filter
        fun p => Disjoint p.1 (univ \ univ.map e.toEmbedding) :=
      Finset.mem_filter.2 ⟨hp, hdisj⟩
    rw [← hrange] at hmem
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hmem
    refine ⟨p', hp', ?_, ?_⟩
    · have : e.toEmbedding a ∈ p'.1.map e.toEmbedding := hap
      exact (Finset.mem_map' _).1 this
    · rw [Finset.card_map] at hP
      exact hP

/-- The removal values of the sub-configuration are those of the full configuration. -/
theorem clusterRemovalValue_comp (hunion : ∀ p ∈ sameSignClustering q h z r univ,
      p.1 ⊆ univ \ univ.map e.toEmbedding ∨ Disjoint p.1 (univ \ univ.map e.toEmbedding))
    (a : Fin m) :
    clusterRemovalValue q h (z ∘ e) (r ∘ e) a = clusterRemovalValue q h z r (e a) := by
  obtain ⟨p, hp, hap, hval⟩ := exists_mem_clustering_univ (q := q) (h := h) (z := z ∘ e)
    (r := r ∘ e) a
  obtain ⟨p', hp', hap', hval'⟩ := (exists_cluster_comp_iff e hunion
    (fun _ v => v = clusterRemovalValue q h (z ∘ e) (r ∘ e) a) a).1 ⟨p, hp, hap, hval⟩
  rw [clusterRemovalValue_eq hp' hap', hval']

theorem clusterRadius_comp (hunion : ∀ p ∈ sameSignClustering q h z r univ,
      p.1 ⊆ univ \ univ.map e.toEmbedding ∨ Disjoint p.1 (univ \ univ.map e.toEmbedding))
    (lam : ℝ) (a : Fin m) :
    clusterRadius q h lam (z ∘ e) (r ∘ e) a = clusterRadius q h lam z r (e a) := by
  unfold clusterRadius
  rw [clusterRemovalValue_comp e hunion]

end Sub

end BadPointTypes

end MultipoleBKT

end
