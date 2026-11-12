/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Clustering

/-!
# The shape of the clusters of Definition 5.1

The paper: Definition 5.1
(Definition 5.1, frozen as `sameSignClustering`) and the remark after it: "up to the
removal of a set of measure 0, we will assume that at each overcrowding step, the selected ball
intersects exactly `q` other balls". The proof of Lemma 5.40 uses it in the form
"at the disappearance parameter, clusters are either of cardinality 1 or of cardinality
`q(β) + 1`".

`clusterShape`: if no charge is at the same distance from two other charges
(`NoIsosceles`, almost everywhere by `ae_noIsosceles_config` in `TypeOneAssembly.lean`), every
cluster `(S, τ)` produced by the clustering is

* a singleton `{i}`, removed at `τ = r_i / 4` if `r_i ≤ h` and at `τ ≥ h / 4` if `r_i > h`; or
* an overcrowded cluster with exactly `q + 1` elements, all within `2τ` of a centre in `S`.

At an overcrowding step the selected centre `c` meets at least `q` balls at the threshold `τ`,
and fewer than `q` balls at any smaller radius (otherwise the threshold would be smaller). The
extra balls touch `B(z_c, τ)` exactly, i.e. lie at distance exactly `2τ` from `z_c`, and two
such charges would form an isosceles coincidence.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset Metric TheoremTwo UpperBound MeasureTheory

variable {n : ℕ}

/-- No charge is at the same distance from two other charges. -/
def NoIsosceles (z : Fin n → ℂ) : Prop :=
  ∀ i j j' : Fin n, j ≠ i → j' ≠ i → j ≠ j' → ‖z i - z j‖ ≠ ‖z i - z j'‖

/-- The threshold of a step is nonnegative when `h ≥ 0` and the lengths are nonnegative. -/
theorem clusterTau_nonneg {q : ℕ} {h : ℝ} (hh : 0 ≤ h) {z : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ i, 0 ≤ r i) {I : Finset (Fin n)} (hI : I.Nonempty) :
    0 ≤ clusterTau q h z r I hI := by
  have hinf : 0 ≤ I.inf' hI r / 4 := by
    have := Finset.le_inf' hI r (a := 0) fun i _ => hr i
    linarith
  unfold clusterTau
  split_ifs with hne
  · refine le_min (le_min hh hinf) (le_csInf hne fun t ht => ht.1)
  · exact le_min hh hinf

/-- **The shape of the clusters** (Definition 5.1 and Lemma 5.40): without isosceles coincidences, every
cluster is a singleton removed at `r_i / 4` (if `r_i ≤ h`) or at least at `h / 4` (if `r_i > h`),
or an overcrowded cluster of exactly `q + 1` charges within `2τ` of one of them. -/
theorem clusterShape {q : ℕ} (hq : 1 ≤ q) {h : ℝ} (hh : 0 < h) {z : Fin n → ℂ}
    {r : Fin n → ℝ} (hr : ∀ i, 0 ≤ r i) (hz : NoIsosceles z) :
    ∀ (I : Finset (Fin n)), ∀ p ∈ sameSignClustering q h z r I,
      (∃ i, p.1 = {i} ∧ (r i ≤ h → p.2 = r i / 4) ∧ (h < r i → h / 4 ≤ p.2)) ∨
        (p.1.card = q + 1 ∧ ∃ c ∈ p.1, ∀ j ∈ p.1, ‖z j - z c‖ ≤ 2 * p.2) := by
  classical
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp [sameSignClustering_of_empty]
  rw [sameSignClustering_eq_of_nonempty q h z r I hI]
  set τ := clusterTau q h z r I hI with hτ
  have hτ0 : 0 ≤ τ := clusterTau_nonneg hh.le hr hI
  split_ifs with h1 h2
  · -- the cutoff step: singletons removed at `h`
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hp
    left
    refine ⟨i, rfl, fun hri => ?_, fun _ => by dsimp only; linarith⟩
    exfalso
    have : τ ≤ r i / 4 := clusterTau_le_div hI hi
    rw [h1] at this
    linarith
  · -- the singleton step
    intro p hp
    rcases mem_insert.1 hp with rfl | hp
    · left
      set i := (I.filter fun i => r i / 4 = τ).min' h2
      have hi : r i / 4 = τ := (mem_filter.1 (min'_mem _ h2)).2
      refine ⟨i, rfl, fun _ => hi.symm, fun hri => ?_⟩
      dsimp only
      rw [← hi]
      linarith
    · have hiI : (I.filter fun i => r i / 4 = τ).min' h2 ∈ I :=
        (mem_filter.1 (min'_mem _ h2)).1
      exact ih _ (erase_ssubset hiI) p hp
  · -- the overcrowding step
    -- some ball is overcrowded at some radius, and `τ` is the first such radius
    have hne : {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty}.Nonempty := by
      by_contra hne
      have hτ' : τ = min h (I.inf' hI r / 4) := by
        rw [hτ]; unfold clusterTau; rw [ite_eq_right hne]
      rcases min_choice h (I.inf' hI r / 4) with hm | hm
      · exact h1 (hτ'.trans hm)
      · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_inf' hI r
        exact h2 ⟨i, mem_filter.2 ⟨hi, by rw [← hieq, ← hm, hτ']⟩⟩
    have hτs : τ = sInf {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty} := by
      have hτ' : τ = min (min h (I.inf' hI r / 4))
          (sInf {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty}) := by
        rw [hτ]; unfold clusterTau; rw [ite_eq_left hne]
      rcases min_choice (min h (I.inf' hI r / 4))
        (sInf {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty}) with hm | hm
      · exfalso
        rcases min_choice h (I.inf' hI r / 4) with hm' | hm'
        · exact h1 (hτ'.trans (hm.trans hm'))
        · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_inf' hI r
          exact h2 ⟨i, mem_filter.2 ⟨hi, by rw [← hieq, ← hm', ← hm, hτ']⟩⟩
      · exact hτ'.trans hm
    have hcrowd : (crowdedSet q z I τ).Nonempty :=
      ((sInf_crowded_le_iff q z I hne τ).1 (le_of_eq hτs.symm)).2
    -- the chosen centre is crowded
    set c := clusterChosen q z r I τ hI with hc
    have hcmem : c ∈ I ∧ c ∈ crowdedSet q z I τ := by
      obtain ⟨j, hj, hjk⟩ := mem_image.1 ((I.image (clusterKey q z r I τ)).min'_mem (hI.image _))
      have hcj : c = j := by
        simp only [hc, clusterChosen, ← hjk, clusterKey]
        rfl
      obtain ⟨j₀, hj₀⟩ := hcrowd
      have hj₀I : j₀ ∈ I := (mem_filter.1 hj₀).1
      have hle : clusterKey q z r I τ j ≤ clusterKey q z r I τ j₀ := by
        rw [hjk]
        exact min'_le _ _ (mem_image_of_mem _ hj₀I)
      refine ⟨hcj ▸ hj, ?_⟩
      by_contra hcn
      have hk1 : clusterKey q z r I τ j₀ = toLex (false, toLex (r j₀, j₀)) := by
        simp [clusterKey, hj₀]
      have hk2 : clusterKey q z r I τ j = toLex (true, toLex (r j, j)) := by
        simp [clusterKey, ← hcj, hcn]
      rw [hk1, hk2, Prod.Lex.le_iff] at hle
      simp at hle
      exact absurd hle (by decide)
    obtain ⟨hcI, hcc⟩ := hcmem
    -- the neighbours of the centre
    set B := I.filter fun j => j ≠ c ∧ ‖z c - z j‖ ≤ 2 * τ with hB
    have hqB : q ≤ B.card := by
      rw [crowdedSet_eq, mem_filter] at hcc
      exact hcc.2
    have hJ : clusterJ q z r I τ hI = insert c B := by
      ext j
      simp only [clusterJ, ← hc, mem_insert, mem_filter, hB, closedBall_inter_nonempty_iff]
      constructor
      · rintro (rfl | ⟨hjI, hjd⟩)
        · exact Or.inl rfl
        · by_cases hjc : j = c
          · exact Or.inl hjc
          · exact Or.inr ⟨hjI, hjc, by rw [norm_sub_rev]; exact hjd⟩
      · rintro (rfl | ⟨hjI, -, hjd⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨hjI, by rw [norm_sub_rev]; exact hjd⟩
    have hcB : c ∉ B := fun h' => (mem_filter.1 h').2.1 rfl
    -- fewer than `q` neighbours strictly inside `2τ`
    set A := I.filter fun j => j ≠ c ∧ ‖z c - z j‖ < 2 * τ with hA
    have hAq : A.card < q := by
      by_contra hAq
      push Not at hAq
      have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
      set s := A.sup' hAne (fun j => ‖z c - z j‖) / 2 with hs
      have hs0 : 0 ≤ s := by
        obtain ⟨j, hj⟩ := hAne
        have := Finset.le_sup' (fun j => ‖z c - z j‖) hj
        have : 0 ≤ ‖z c - z j‖ := norm_nonneg _
        rw [hs]
        linarith
      have hsτ : s < τ := by
        rw [hs]
        obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hAne (fun j => ‖z c - z j‖)
        rw [hjeq]
        have := (mem_filter.1 hj).2.2
        linarith
      have hmem : c ∈ crowdedSet q z I s := by
        rw [crowdedSet_eq, mem_filter]
        refine ⟨hcI, hAq.trans (Finset.card_le_card fun j hj => ?_)⟩
        have hjA : j ∈ A := hj
        rw [mem_filter] at hj ⊢
        refine ⟨hj.1, hj.2.1, ?_⟩
        have := Finset.le_sup' (fun j => ‖z c - z j‖) hjA
        rw [hs]
        linarith
      exact not_mem_crowdedSet_of_lt hI hs0 (hτ ▸ hsτ) c hmem
    -- at most one neighbour at distance exactly `2τ`
    have hE : (B \ A).card ≤ 1 := by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      by_contra hab
      have ha' := mem_sdiff.1 ha
      have hb' := mem_sdiff.1 hb
      have hda : ‖z c - z a‖ = 2 * τ := by
        refine le_antisymm (mem_filter.1 ha'.1).2.2 (not_lt.1 fun hlt => ha'.2 ?_)
        exact mem_filter.2 ⟨(mem_filter.1 ha'.1).1, (mem_filter.1 ha'.1).2.1, hlt⟩
      have hdb : ‖z c - z b‖ = 2 * τ := by
        refine le_antisymm (mem_filter.1 hb'.1).2.2 (not_lt.1 fun hlt => hb'.2 ?_)
        exact mem_filter.2 ⟨(mem_filter.1 hb'.1).1, (mem_filter.1 hb'.1).2.1, hlt⟩
      exact hz c a b (mem_filter.1 ha'.1).2.1 (mem_filter.1 hb'.1).2.1 hab (hda.trans hdb.symm)
    have hAB : A ⊆ B := fun j hj => by
      rw [mem_filter] at hj ⊢
      exact ⟨hj.1, hj.2.1, hj.2.2.le⟩
    have hBcard : B.card ≤ q := by
      have := Finset.card_sdiff_add_card_eq_card hAB
      omega
    intro p hp
    rcases mem_insert.1 hp with rfl | hp
    · right
      dsimp only
      rw [hJ]
      refine ⟨by rw [card_insert_of_notMem hcB]; omega, c, mem_insert_self c B, fun j hj => ?_⟩
      rcases mem_insert.1 hj with rfl | hj
      · simp [hτ0]
      · rw [norm_sub_rev]
        exact (mem_filter.1 hj).2.2
    · have hJI : clusterJ q z r I τ hI ⊆ I := by
        rw [hJ]
        exact insert_subset hcI (filter_subset _ _)
      exact ih _ (sdiff_ssubset hJI ⟨c, by rw [hJ]; exact mem_insert_self c B⟩) p hp

end BadPointTypes

end MultipoleBKT

end
