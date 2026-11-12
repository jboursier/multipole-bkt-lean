/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.MeasurableClustering

/-!
# Invariants of the `q`-clustering (Definition 5.1)

The paper: Definition 5.1, frozen as `MultipoleBKT.sameSignClustering`: one run on the remaining labels `I`
outputs the pairs `(cluster, removal value)`. The paper uses, "by construction" and without
stating them, the following invariants, proved here by strong induction on
`I` along the recursion of the frozen definition.

* **Partition** (`fst_subset_of_mem_clustering`, `fst_nonempty_of_mem_clustering`,
  `exists_mem_clustering`, `eq_of_mem_clustering`): every cluster is a nonempty subset of `I`,
  every label of `I` lies in a cluster, and in only one.
* **Bounds** (`snd_le_of_mem_clustering`, `snd_le_div_of_mem_clustering`): every removal value
  is at most the cutoff `h = ε₀ R̄` and at most `r_i / 4` for every member `i` of its cluster.
* **Nondecreasing removal** (`clusterTau_le_snd_of_mem_clustering`, `clusterTau_mono`): the
  threshold `τ` of the first step is at most every removal value, and it can only increase when
  labels are removed; hence the removal values along the iteration are nondecreasing.
* **No crowding before removal** (`card_filter_lt_of_mem_clustering`): if `i` is removed at
  `τ_i` and `0 ≤ s < τ_i`, the ball `B(z_i, s)` meets fewer than `q` balls `B(z_j, s)` with
  `j ≠ i` still present at scale `s` (removed at a value `> s`).

For the full run (`I = [N]`) the removal value of `i` is `clusterRemovalValue` (the value of the
unique cluster containing `i`); the paper's radius is `τ_i^± = max(λ, removal value)`
(`clusterRadius`, Definition 5.1). The invariants are restated for it
(`clusterRemovalValue_le`, `clusterRemovalValue_le_div`, `card_lt_of_lt_clusterRemovalValue`).
-/

@[expose] public section

open Finset Metric

namespace MultipoleBKT

namespace UpperBound

open TheoremTwo

variable {N : ℕ} (q : ℕ) (h : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ)

/-! ### One step of the clustering -/

section Step

variable {q h z r}

theorem clusterTau_le_left {I : Finset (Fin N)} (hI : I.Nonempty) :
    clusterTau q h z r I hI ≤ h := by
  unfold clusterTau
  split_ifs
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact min_le_left _ _

theorem clusterTau_le_inf' {I : Finset (Fin N)} (hI : I.Nonempty) :
    clusterTau q h z r I hI ≤ I.inf' hI r / 4 := by
  unfold clusterTau
  split_ifs
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact min_le_right _ _

theorem clusterTau_le_div {I : Finset (Fin N)} (hI : I.Nonempty) {i : Fin N} (hi : i ∈ I) :
    clusterTau q h z r I hI ≤ r i / 4 :=
  (clusterTau_le_inf' hI).trans (by gcongr; exact Finset.inf'_le _ hi)

/-- Below the threshold `τ` of a step, no ball of the remaining labels is overcrowded. -/
theorem not_mem_crowdedSet_of_lt {I : Finset (Fin N)} (hI : I.Nonempty) {s : ℝ} (hs : 0 ≤ s)
    (hsτ : s < clusterTau q h z r I hI) (i : Fin N) : i ∉ crowdedSet q z I s := by
  intro hi
  have hne : {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty}.Nonempty := ⟨s, hs, i, hi⟩
  have hle : clusterTau q h z r I hI ≤ s := by
    unfold clusterTau
    rw [ite_eq_left hne]
    exact (min_le_right _ _).trans (csInf_le ⟨0, fun t ht => ht.1⟩ ⟨hs, i, hi⟩)
  exact absurd hsτ (not_lt.mpr hle)

/-- The number of balls `B(z_j, s)`, `j ∈ I ∖ {i}`, meeting `B(z_i, s)` is less than `q` when
`i ∈ I` and `0 ≤ s < τ`. -/
theorem card_filter_lt_of_lt_clusterTau {I : Finset (Fin N)} (hI : I.Nonempty) {s : ℝ}
    (hs : 0 ≤ s) (hsτ : s < clusterTau q h z r I hI) {i : Fin N} (hi : i ∈ I) :
    (I.filter fun j => j ≠ i ∧ ‖z i - z j‖ ≤ 2 * s).card < q := by
  classical
  have h1 := not_mem_crowdedSet_of_lt hI hs hsτ i
  rw [crowdedSet_eq, Finset.mem_filter, not_and, not_le] at h1
  convert h1 hi using 3

/-- More labels can only make a ball crowded earlier. -/
theorem crowdedSet_subset_of_subset {I I' : Finset (Fin N)} (hII' : I' ⊆ I) (t : ℝ) :
    crowdedSet q z I' t ⊆ crowdedSet q z I t := by
  classical
  intro i hi
  rw [crowdedSet_eq, Finset.mem_filter] at hi ⊢
  refine ⟨hII' hi.1, hi.2.trans (Finset.card_le_card fun j hj => ?_)⟩
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hII' hj.1, hj.2⟩

/-- **Nondecreasing thresholds**: the
threshold `τ` can only increase when labels are removed. -/
theorem clusterTau_mono {I I' : Finset (Fin N)} (hI : I.Nonempty) (hI' : I'.Nonempty)
    (hII' : I' ⊆ I) : clusterTau q h z r I hI ≤ clusterTau q h z r I' hI' := by
  have hinf : I.inf' hI r ≤ I'.inf' hI' r :=
    Finset.le_inf' hI' _ fun i hi => Finset.inf'_le _ (hII' hi)
  have hsub : {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I' t).Nonempty} ⊆
      {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty} := fun t ht =>
    ⟨ht.1, ht.2.mono (crowdedSet_subset_of_subset hII' t)⟩
  have hdiv : I.inf' hI r / 4 ≤ I'.inf' hI' r / 4 := by gcongr
  unfold clusterTau
  split_ifs with h1 h2 h2
  · refine min_le_min (min_le_min le_rfl hdiv) (csInf_le_csInf ⟨0, fun t ht => ht.1⟩ h2 hsub)
  · exact (min_le_left _ _).trans (min_le_min le_rfl hdiv)
  · exact absurd (h2.mono hsub) h1
  · exact min_le_min le_rfl hdiv

variable (q h z r) in
/-- The two shapes of one step of the clustering: either `τ = h` and every remaining label is a
singleton removed at `h`, or a nonempty cluster `J ⊆ I` is removed at `τ` and the run continues
on `I ∖ J` (the singleton step is the case `J = {i}`). -/
theorem clustering_cases {I : Finset (Fin N)} (hI : I.Nonempty) :
    (clusterTau q h z r I hI = h ∧ sameSignClustering q h z r I = I.image fun i => ({i}, h)) ∨
      ∃ J ⊆ I, J.Nonempty ∧ sameSignClustering q h z r I =
        insert (J, clusterTau q h z r I hI) (sameSignClustering q h z r (I \ J)) := by
  classical
  rw [sameSignClustering_eq_of_nonempty q h z r I hI]
  split_ifs with hτ hs
  · exact Or.inl ⟨hτ, rfl⟩
  · right
    set i₀ := (I.filter fun i => r i / 4 = clusterTau q h z r I hI).min' hs
    have hi₀ : i₀ ∈ I := (Finset.mem_filter.mp (Finset.min'_mem _ hs)).1
    refine ⟨{i₀}, Finset.singleton_subset_iff.mpr hi₀, Finset.singleton_nonempty _, ?_⟩
    rw [Finset.sdiff_singleton_eq_erase]
  · right
    set J := clusterJ q z r I (clusterTau q h z r I hI) hI
    have hchosen : clusterChosen q z r I (clusterTau q h z r I hI) hI ∈ I := by
      obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp
        ((I.image (clusterKey q z r I (clusterTau q h z r I hI))).min'_mem (hI.image _))
      have : clusterChosen q z r I (clusterTau q h z r I hI) hI = j := by
        simp only [clusterChosen, ← hjk]; rfl
      exact this ▸ hj
    refine ⟨J, fun j hj => ?_, ⟨_, Finset.mem_insert_self _ _⟩, rfl⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hchosen
    · exact (Finset.mem_filter.mp hj).1

theorem sdiff_ssubset_of_nonempty {I J : Finset (Fin N)} (hJI : J ⊆ I) (hJ : J.Nonempty) :
    I \ J ⊂ I := by
  obtain ⟨j, hj⟩ := hJ
  exact (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr
    ⟨j, hJI hj, fun h' => (Finset.mem_sdiff.mp h').2 hj⟩

end Step

/-! ### The partition property -/

section Partition

variable {q h z r}

/-- Every cluster is a nonempty subset of the remaining labels. -/
theorem fst_subset_and_nonempty_of_mem_clustering (I : Finset (Fin N)) :
    ∀ p ∈ sameSignClustering q h z r I, p.1 ⊆ I ∧ p.1.Nonempty := by
  classical
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp [sameSignClustering_of_empty]
  rcases clustering_cases q h z r hI with ⟨-, heq⟩ | ⟨J, hJI, hJ, heq⟩
  · rw [heq]
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨Finset.singleton_subset_iff.mpr hi, Finset.singleton_nonempty _⟩
  · rw [heq]
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨hJI, hJ⟩
    · obtain ⟨h1, h2⟩ := ih _ (sdiff_ssubset_of_nonempty hJI hJ) p hp
      exact ⟨h1.trans Finset.sdiff_subset, h2⟩

theorem fst_subset_of_mem_clustering {I : Finset (Fin N)} {p : Finset (Fin N) × ℝ}
    (hp : p ∈ sameSignClustering q h z r I) : p.1 ⊆ I :=
  (fst_subset_and_nonempty_of_mem_clustering I p hp).1

theorem fst_nonempty_of_mem_clustering {I : Finset (Fin N)} {p : Finset (Fin N) × ℝ}
    (hp : p ∈ sameSignClustering q h z r I) : p.1.Nonempty :=
  (fst_subset_and_nonempty_of_mem_clustering I p hp).2

/-- Every remaining label lies in some cluster. -/
theorem exists_mem_clustering (I : Finset (Fin N)) :
    ∀ i ∈ I, ∃ p ∈ sameSignClustering q h z r I, i ∈ p.1 := by
  classical
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp
  rcases clustering_cases q h z r hI with ⟨-, heq⟩ | ⟨J, hJI, hJ, heq⟩
  · rw [heq]
    intro i hi
    exact ⟨({i}, h), Finset.mem_image_of_mem _ hi, Finset.mem_singleton_self i⟩
  · rw [heq]
    intro i hi
    by_cases hiJ : i ∈ J
    · exact ⟨_, Finset.mem_insert_self _ _, hiJ⟩
    · obtain ⟨p, hp, hip⟩ := ih _ (sdiff_ssubset_of_nonempty hJI hJ) i
        (Finset.mem_sdiff.mpr ⟨hi, hiJ⟩)
      exact ⟨p, Finset.mem_insert_of_mem hp, hip⟩

/-- A label lies in only one cluster. -/
theorem eq_of_mem_clustering (I : Finset (Fin N)) :
    ∀ p ∈ sameSignClustering q h z r I, ∀ p' ∈ sameSignClustering q h z r I,
      ∀ i ∈ p.1, i ∈ p'.1 → p = p' := by
  classical
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp [sameSignClustering_of_empty]
  rcases clustering_cases q h z r hI with ⟨-, heq⟩ | ⟨J, hJI, hJ, heq⟩
  · rw [heq]
    intro p hp p' hp' i hi hi'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hp'
    rw [Finset.mem_singleton] at hi hi'
    rw [← hi, ← hi']
  · rw [heq]
    have hss := sdiff_ssubset_of_nonempty hJI hJ
    -- a cluster of the later steps avoids `J`
    have hout : ∀ p ∈ sameSignClustering q h z r (I \ J), ∀ i ∈ p.1, i ∉ J := fun p hp i hi =>
      (Finset.mem_sdiff.mp (fst_subset_of_mem_clustering hp hi)).2
    intro p hp p' hp' i hi hi'
    rcases Finset.mem_insert.mp hp with rfl | hp <;> rcases Finset.mem_insert.mp hp' with rfl | hp'
    · rfl
    · exact absurd hi (hout _ hp' i hi')
    · exact absurd hi' (hout _ hp i hi)
    · exact ih _ hss p hp p' hp' i hi hi'

end Partition

/-! ### Bounds on the removal values -/

section Bounds

variable {q h z r}

/-- Every removal value is at most the cutoff `h` and at most `r_i / 4` for each member `i` of
its cluster. -/
theorem snd_le_of_mem_clustering' (I : Finset (Fin N)) :
    ∀ p ∈ sameSignClustering q h z r I, ∀ i ∈ p.1, p.2 ≤ h ∧ p.2 ≤ r i / 4 := by
  classical
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp [sameSignClustering_of_empty]
  rcases clustering_cases q h z r hI with ⟨hτ, heq⟩ | ⟨J, hJI, hJ, heq⟩
  · rw [heq]
    intro p hp i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨le_rfl, hτ ▸ clusterTau_le_div hI ha⟩
  · rw [heq]
    intro p hp i hi
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨clusterTau_le_left hI, clusterTau_le_div hI (hJI hi)⟩
    · exact ih _ (sdiff_ssubset_of_nonempty hJI hJ) p hp i hi

theorem snd_le_of_mem_clustering {I : Finset (Fin N)} {p : Finset (Fin N) × ℝ}
    (hp : p ∈ sameSignClustering q h z r I) : p.2 ≤ h := by
  obtain ⟨i, hi⟩ := fst_nonempty_of_mem_clustering hp
  exact (snd_le_of_mem_clustering' I p hp i hi).1

theorem snd_le_div_of_mem_clustering {I : Finset (Fin N)} {p : Finset (Fin N) × ℝ}
    (hp : p ∈ sameSignClustering q h z r I) {i : Fin N} (hi : i ∈ p.1) : p.2 ≤ r i / 4 :=
  (snd_le_of_mem_clustering' I p hp i hi).2

/-- **Nondecreasing removal values**: the threshold of the first step is at most every removal
value; with `clusterTau_mono`, the
removal values along the iteration are nondecreasing. -/
theorem clusterTau_le_snd_of_mem_clustering (I : Finset (Fin N)) (hI : I.Nonempty) :
    ∀ p ∈ sameSignClustering q h z r I, clusterTau q h z r I hI ≤ p.2 := by
  classical
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases clustering_cases q h z r hI with ⟨hτ, heq⟩ | ⟨J, hJI, hJ, heq⟩
  · rw [heq]
    intro p hp
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
    exact hτ.le
  · rw [heq]
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact le_rfl
    · have hss := sdiff_ssubset_of_nonempty hJI hJ
      have hne : (I \ J).Nonempty := by
        obtain ⟨i, hi⟩ := fst_nonempty_of_mem_clustering hp
        exact ⟨i, fst_subset_of_mem_clustering hp hi⟩
      exact (clusterTau_mono hI hne Finset.sdiff_subset).trans (ih _ hss hne p hp)

end Bounds

/-! ### No crowding before removal -/

section NoCrowding

variable {q h z r}

/-- **No crowding before removal**:
if `i` is removed at the value `p.2` and `0 ≤ s < p.2`, then fewer than `q` labels `j ≠ i` of
`I` that are still present at scale `s` (removed at a value `> s`) have
`B(z_j, s) ∩ B(z_i, s) ≠ ∅`, i.e. `|z_i - z_j| ≤ 2s`. -/
theorem card_filter_lt_of_mem_clustering (I : Finset (Fin N)) :
    ∀ p ∈ sameSignClustering q h z r I, ∀ i ∈ p.1, ∀ s : ℝ, 0 ≤ s → s < p.2 →
      (I.filter fun j => j ≠ i ∧ ‖z i - z j‖ ≤ 2 * s ∧
        ∃ p' ∈ sameSignClustering q h z r I, j ∈ p'.1 ∧ s < p'.2).card < q := by
  classical
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp [sameSignClustering_of_empty]
  -- below the first threshold, `i ∈ I` is not crowded
  have hbase : ∀ i ∈ I, ∀ s : ℝ, 0 ≤ s → s < clusterTau q h z r I hI →
      (I.filter fun j => j ≠ i ∧ ‖z i - z j‖ ≤ 2 * s ∧
        ∃ p' ∈ sameSignClustering q h z r I, j ∈ p'.1 ∧ s < p'.2).card < q := by
    intro i hi s hs hsτ
    refine lt_of_le_of_lt (Finset.card_le_card fun j hj => ?_)
      (card_filter_lt_of_lt_clusterTau hI hs hsτ hi)
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.1, hj.2.2.1⟩
  rcases clustering_cases q h z r hI with ⟨hτ, heq⟩ | ⟨J, hJI, hJ, heq⟩
  · intro p hp i hi s hs hsp
    rw [heq] at hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_singleton] at hi
    subst hi
    exact hbase _ ha s hs (by rw [hτ]; exact hsp)
  · have hss := sdiff_ssubset_of_nonempty hJI hJ
    intro p hp i hi s hs hsp
    have hp' := hp
    rw [heq] at hp'
    rcases Finset.mem_insert.mp hp' with rfl | hpI
    · exact hbase i (hJI hi) s hs hsp
    · have hiI : i ∈ I \ J := fst_subset_of_mem_clustering hpI hi
      rcases lt_or_ge s (clusterTau q h z r I hI) with hsτ | hτs
      · exact hbase i (Finset.mem_sdiff.mp hiI).1 s hs hsτ
      · refine lt_of_le_of_lt (Finset.card_le_card fun j hj => ?_) (ih _ hss p hpI i hi s hs hsp)
        rw [Finset.mem_filter] at hj ⊢
        obtain ⟨-, hji, hdist, p', hp'mem, hjp', hsp'⟩ := hj
        rw [heq] at hp'mem
        rcases Finset.mem_insert.mp hp'mem with rfl | hp'I
        · exact absurd hsp' (not_lt.mpr hτs)
        · exact ⟨fst_subset_of_mem_clustering hp'I hjp', hji, hdist, p', hp'I, hjp', hsp'⟩

end NoCrowding

/-! ### The removal value of a label in the full run -/

section Removal

/-- The removal value of `i` in the full `q`-clustering (Definition 5.1): the value of
`τ` at which `B(z_i, ·)` is removed, i.e. the second component of the unique pair of
`sameSignClustering q h z r [N]` whose cluster contains `i` (`clusterRemovalValue_eq`). -/
noncomputable def clusterRemovalValue (q : ℕ) (h : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ)
    (i : Fin N) : ℝ :=
  sSup (Prod.snd '' {p | p ∈ sameSignClustering q h z r Finset.univ ∧ i ∈ p.1})

/-- The radius `τ_i = max(λ, removal value)` of Definition 5.1; `τ_i^+` for `z = x`,
`τ_i^-` for `z = y`. -/
noncomputable def clusterRadius (q : ℕ) (h lam : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ)
    (i : Fin N) : ℝ :=
  max lam (clusterRemovalValue q h z r i)

variable {q h z r}

theorem clusterRemovalValue_eq {p : Finset (Fin N) × ℝ}
    (hp : p ∈ sameSignClustering q h z r Finset.univ) {i : Fin N} (hi : i ∈ p.1) :
    clusterRemovalValue q h z r i = p.2 := by
  have hset : Prod.snd '' {p' | p' ∈ sameSignClustering q h z r Finset.univ ∧ i ∈ p'.1} =
      {p.2} := by
    ext t
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p', ⟨hp', hip'⟩, rfl⟩
      rw [eq_of_mem_clustering _ p' hp' p hp i hip' hi]
    · rintro rfl
      exact ⟨p, ⟨hp, hi⟩, rfl⟩
  rw [clusterRemovalValue, hset, csSup_singleton]

/-- Every label has a cluster in the full run, removed at its removal value. -/
theorem exists_mem_clustering_univ (i : Fin N) :
    ∃ p ∈ sameSignClustering q h z r Finset.univ, i ∈ p.1 ∧
      p.2 = clusterRemovalValue q h z r i := by
  obtain ⟨p, hp, hip⟩ := exists_mem_clustering Finset.univ i (Finset.mem_univ i)
  exact ⟨p, hp, hip, (clusterRemovalValue_eq hp hip).symm⟩

/-- The removal value is at most the cutoff `h = ε₀ R̄`. -/
theorem clusterRemovalValue_le (i : Fin N) : clusterRemovalValue q h z r i ≤ h := by
  obtain ⟨p, hp, -, hpi⟩ := exists_mem_clustering_univ (q := q) (h := h) (z := z) (r := r) i
  exact hpi ▸ snd_le_of_mem_clustering hp

/-- The removal value of `i` is at most `r_i / 4`. -/
theorem clusterRemovalValue_le_div (i : Fin N) : clusterRemovalValue q h z r i ≤ r i / 4 := by
  obtain ⟨p, hp, hip, hpi⟩ := exists_mem_clustering_univ (q := q) (h := h) (z := z) (r := r) i
  exact hpi ▸ snd_le_div_of_mem_clustering hp hip

/-- **No crowding before removal**, for the full run: if `0 ≤ s < τ_i` (removal values), fewer
than `q` labels `j ≠ i` with `τ_j > s` have `|z_i - z_j| ≤ 2s`. -/
theorem card_lt_of_lt_clusterRemovalValue {i : Fin N} {s : ℝ} (hs : 0 ≤ s)
    (hsi : s < clusterRemovalValue q h z r i) :
    (Finset.univ.filter fun j => j ≠ i ∧ ‖z i - z j‖ ≤ 2 * s ∧
      s < clusterRemovalValue q h z r j).card < q := by
  classical
  obtain ⟨p, hp, hip, hpi⟩ := exists_mem_clustering_univ (q := q) (h := h) (z := z) (r := r) i
  refine lt_of_le_of_lt (Finset.card_le_card fun j hj => ?_)
    (card_filter_lt_of_mem_clustering Finset.univ p hp i hip s hs (hpi ▸ hsi))
  rw [Finset.mem_filter] at hj ⊢
  obtain ⟨p', hp', hjp', hp'j⟩ := exists_mem_clustering_univ (q := q) (h := h) (z := z) (r := r) j
  exact ⟨hj.1, hj.2.1, hj.2.2.1, p', hp', hjp', hp'j ▸ hj.2.2.2⟩

theorem le_clusterRadius (lam : ℝ) (i : Fin N) : lam ≤ clusterRadius q h lam z r i :=
  le_max_left _ _

/-- `τ_i ≤ max(r_i / 4, λ)` ("by construction", Remark 5.10). -/
theorem clusterRadius_le_max_div (lam : ℝ) (i : Fin N) :
    clusterRadius q h lam z r i ≤ max (r i / 4) lam :=
  max_le (le_max_right _ _) ((clusterRemovalValue_le_div i).trans (le_max_left _ _))

/-- `τ_i ≤ ε₀ R̄` when `λ ≤ ε₀ R̄` (Definition 5.8). -/
theorem clusterRadius_le (lam : ℝ) (hlam : lam ≤ h) (i : Fin N) :
    clusterRadius q h lam z r i ≤ h :=
  max_le hlam (clusterRemovalValue_le i)

/-- If `τ_i > λ`, then `τ_i` is the removal value. -/
theorem clusterRadius_eq_of_lt {lam : ℝ} {i : Fin N} (h' : lam < clusterRadius q h lam z r i) :
    clusterRadius q h lam z r i = clusterRemovalValue q h z r i := by
  unfold clusterRadius at h' ⊢
  rcases le_total lam (clusterRemovalValue q h z r i) with h1 | h1
  · exact max_eq_right h1
  · rw [max_eq_left h1] at h'
    exact absurd h' (lt_irrefl _)

end Removal

end UpperBound

end MultipoleBKT

end
