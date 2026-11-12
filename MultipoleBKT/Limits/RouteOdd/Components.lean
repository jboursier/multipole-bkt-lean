/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteOdd.Forest

/-!
# Assemble the odd components after endpoint deletion

See (A.30) and the
following paragraph. Each component first uses its own maximum
radius and its own exceptional ear. Only then are the component tails combined.
-/

@[expose] public section

namespace MultipoleBKT.Limits

open Finset SimpleGraph

variable {β ε : Type*} [Fintype β] [DecidableEq β] [DecidableEq ε]

open scoped Classical in
/-- Apply the written ear estimate separately in each odd component, then bound
the product of component tails by the one global tail. Isolated vertices
contribute an empty tree and tail one.
See the proof of Lemma A.5. -/
theorem componentwise_odd_forest (ends : ε → Sym2 β) {F : Finset ε}
    (hloop : ∀ e ∈ F, ¬ (ends e).IsDiag) (hcut : CutEven ends F)
    (root : (nodeGraph ends F).ConnectedComponent → β)
    (hroot : ∀ C, (nodeGraph ends F).connectedComponentMk (root C) = C)
    (s : β → ℝ) (hs : ∀ v, 0 < s v) {R : ℝ} (hR : ∀ v, s v ≤ R)
    (d a : ε → ℝ) (hd : ∀ e ∈ F, 0 < d e)
    (ha0 : ∀ e ∈ F, 0 ≤ a e) (ha1 : ∀ e ∈ F, a e ≤ 1)
    (ha : ∀ e ∈ F, ∀ v w, ends e = s(v, w) →
      a e ≤ s v * s w / (d e * max (d e) (max (s v) (s w)))) :
    let Z := univ.filter (fun v => v ∈ Set.range root)
    ∃ A ⊆ F, A.card = (univ \ Z).card ∧
      (∀ v, ∃ z ∈ Z, (nodeGraph ends A).Reachable z v) ∧
      ∏ e ∈ F, a e ≤ (∏ v ∈ univ \ Z, s v ^ 2) *
        globalTail R d A * ∏ e ∈ A, (d e ^ 2)⁻¹ := by
  intro Z
  classical
  let : Fintype (nodeGraph ends F).ConnectedComponent := Fintype.ofFinite _
  let q := (nodeGraph ends F).connectedComponentMk
  let V := fun C => univ.filter (fun v => q v = C)
  let I := fun C => (V C).erase (root C)
  let FC := fun C => F.filter (fun e => ∀ v ∈ ends e, q v = C)
  have hFC : ∀ C, FC C ⊆ F := fun C => filter_subset _ _
  have hends : ∀ e ∈ F, ∀ v w, ends e = s(v, w) → q v = q w := by
    intro e he v w hev
    have hvw : v ≠ w := fun h => hloop e he (by simp [hev, h])
    exact ConnectedComponent.sound (nodeGraph_adj_of_mem he hev hvw).reachable
  have hFsplit : (univ.biUnion FC) = F := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨C, he⟩
      exact hFC C he
    · intro he
      obtain ⟨⟨v, w⟩, hev⟩ := Quot.exists_rep (ends e)
      refine ⟨q v, mem_filter.2 ⟨he, ?_⟩⟩
      have hq := hends e he v w hev.symm
      intro z hz
      rw [← hev, Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · rfl
      · exact hq.symm
  have hFCdisj : (↑(univ : Finset (nodeGraph ends F).ConnectedComponent) :
      Set (nodeGraph ends F).ConnectedComponent).PairwiseDisjoint FC := by
    intro C _ D _ hCD
    refine disjoint_left.2 fun e heC heD => ?_
    obtain ⟨⟨v, w⟩, hev⟩ := Quot.exists_rep (ends e)
    have hv : v ∈ ends e := hev ▸ Sym2.mem_mk_left v w
    exact hCD (((mem_filter.1 heC).2 v hv).symm.trans ((mem_filter.1 heD).2 v hv))
  have hcutC : ∀ C, CutEven ends (FC C) := by
    intro C A
    have heq : (FC C).filter (fun e => Crosses A (ends e)) =
        F.filter (fun e => Crosses (A ∩ V C) (ends e)) := by
      ext e
      simp only [FC, mem_filter, and_assoc]
      by_cases he : e ∈ F
      · simp only [he, true_and]
        obtain ⟨⟨v, w⟩, hev⟩ := Quot.exists_rep (ends e)
        have hq := hends e he v w hev.symm
        rw [← hev]
        simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, crosses_mk, mem_inter,
          V, mem_filter, mem_univ, true_and]
        rw [← hq]
        by_cases hv : q v = C <;> simp [hv]
      · simp [he]
    rw [heq]
    exact hcut (A ∩ V C)
  have hreachC : ∀ C v w, (nodeGraph ends F).Reachable v w → q v = C →
      (nodeGraph ends (FC C)).Reachable v w := by
    intro C v w ⟨p⟩
    induction p with
    | nil => exact fun _ => Reachable.refl _
    | @cons v u w hvu p ih =>
      intro hv
      obtain ⟨hne, e, he, hev⟩ := nodeGraph_adj.1 hvu
      have hqu := hends e he v u hev
      have heC : e ∈ FC C := mem_filter.2 ⟨he, by
        intro z hz
        rw [hev, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hv
        · exact hqu.symm.trans hv⟩
      exact (nodeGraph_adj_of_mem heC hev hne).reachable.trans (ih (hqu.symm.trans hv))
  -- The radius of each component is its actual maximum, before enlarging to `R`.
  have hmax : ∀ C, ∃ v ∈ V C, ∀ w ∈ V C, s w ≤ s v := by
    intro C
    exact exists_max_image (V C) s ⟨root C, by simp [V, q, hroot]⟩
  choose vmax hvmax hmax using hmax
  let r := fun C => s (vmax C)
  have hcomp : ∀ C, ∃ A ⊆ FC C, A.card = (I C).card ∧
      (∀ v, q v = C → (nodeGraph ends A).Reachable (root C) v) ∧
      ∏ e ∈ FC C, a e ≤ (∏ v ∈ I C, s v ^ 2) *
        globalTail (r C) d A * ∏ e ∈ A, (d e ^ 2)⁻¹ := by
    intro C
    let ZC := univ \ I C
    have hZC : ∀ v, ∃ z ∈ ZC, (nodeGraph ends (FC C)).Reachable z v := by
      intro v
      by_cases hv : v ∈ I C
      · refine ⟨root C, by simp [ZC, I], hreachC C _ _ ?_ (hroot C)⟩
        exact ConnectedComponent.exact ((hroot C).trans ((mem_filter.1 (mem_erase.1 hv).2).2).symm)
      · exact ⟨v, mem_sdiff.2 ⟨mem_univ _, hv⟩, Reachable.refl _⟩
    obtain ⟨A, hAF, hAc, hAr, hb⟩ := odd_forest_singleTail ends
      (fun e he => hloop e (hFC C he)) (hcutC C) ZC hZC s hs
      (fun e he v hv => hmax C v (mem_filter.2 ⟨mem_univ _, (mem_filter.1 he).2 v hv⟩))
      d a (fun e he => hd e (hFC C he)) (fun e he => ha0 e (hFC C he))
      (fun e he => ha1 e (hFC C he)) (fun e he => ha e (hFC C he))
    have hI : univ \ ZC = I C := by
      ext v
      simp [ZC]
    rw [hI] at hAc hb
    refine ⟨A, hAF, hAc, ?_, hb⟩
    · intro v hv
      obtain ⟨z, hz, hzv⟩ := hAr v
      have hqz : q z = C := (ConnectedComponent.sound
        (hzv.mono (nodeGraph_mono (hAF.trans (hFC C))))).trans hv
      have hzroot : z = root C := by
        by_contra hn
        exact (mem_sdiff.1 hz).2 (mem_erase.2 ⟨hn, mem_filter.2 ⟨mem_univ _, hqz⟩⟩)
      exact hzroot ▸ hzv
  choose A hA hAc hAr hAb using hcomp
  let AF := univ.biUnion A
  have hAF : AF ⊆ F := by
    intro e he
    obtain ⟨C, -, he⟩ := mem_biUnion.1 he
    exact hFC C (hA C he)
  have hAdisj : (↑(univ : Finset (nodeGraph ends F).ConnectedComponent) :
      Set (nodeGraph ends F).ConnectedComponent).PairwiseDisjoint A := by
    intro C hC D hD hCD
    exact (hFCdisj hC hD hCD).mono (hA C) (hA D)
  have hIdisj : (↑(univ : Finset (nodeGraph ends F).ConnectedComponent) :
      Set (nodeGraph ends F).ConnectedComponent).PairwiseDisjoint I := by
    intro C _ D _ hCD
    refine disjoint_left.2 fun v hvC hvD => hCD ?_
    exact ((mem_filter.1 (mem_erase.1 hvC).2).2).symm.trans
      ((mem_filter.1 (mem_erase.1 hvD).2).2)
  have hIsplit : univ.biUnion I = univ \ Z := by
    ext v
    simp only [mem_biUnion, mem_univ, true_and, I, V, mem_erase, mem_filter,
      mem_sdiff, Z, not_exists, Set.mem_range, true_and]
    constructor
    · rintro ⟨C, hne, hvC⟩ D hD
      apply hne
      have : D = C := (hroot D).symm.trans ((congrArg q hD).trans hvC)
      simpa [this] using hD.symm
    · intro hv
      exact ⟨q v, fun h => hv (q v) h.symm, rfl⟩
  refine ⟨AF, hAF, ?_, ?_, ?_⟩
  · rw [show AF = univ.biUnion A from rfl, card_biUnion hAdisj, ← hIsplit,
      card_biUnion hIdisj]
    exact sum_congr rfl fun C _ => hAc C
  · intro v
    exact ⟨root (q v), by simp [Z], (hAr (q v) v rfl).mono
      (nodeGraph_mono (subset_biUnion_of_mem A (mem_univ (q v))))⟩
  · calc ∏ e ∈ F, a e = ∏ C, ∏ e ∈ FC C, a e := by
          conv_lhs => rw [← hFsplit, prod_biUnion hFCdisj]
      _ ≤ ∏ C, (∏ v ∈ I C, s v ^ 2) * globalTail (r C) d (A C) * ∏ e ∈ A C, (d e ^ 2)⁻¹ :=
          prod_le_prod₀ (fun C _ => prod_nonneg fun e he => ha0 e (hFC C he)) (fun C _ => hAb C)
      _ = (∏ v ∈ univ \ Z, s v ^ 2) * (∏ C, globalTail (r C) d (A C)) *
          ∏ e ∈ AF, (d e ^ 2)⁻¹ := by
        rw [prod_mul_distrib, prod_mul_distrib, ← prod_biUnion hIdisj, hIsplit,
          ← prod_biUnion hAdisj]
      _ ≤ _ := by
        gcongr
        exact prod_globalTail_le_biUnion univ r R d A (fun C _ => (hs _).le)
          (fun C _ => hR _)

end MultipoleBKT.Limits

end
