/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Ear
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Odd forests with one global tail

See (A.30).
We add ears to covered blocks, delete one edge from each ear, and retain one tail
on the union. No even edge is added to the cut-even graph.
-/

@[expose] public section

namespace MultipoleBKT.Limits

open Finset SimpleGraph

variable {β ε : Type*} [Fintype β] [DecidableEq β] [DecidableEq ε]

open scoped Classical in
omit [DecidableEq ε] in
/-- The simple graph of a loop-free edge family has no more edges than the family. -/
theorem nodeGraph_card_le (ends : ε → Sym2 β) (T : Finset ε) :
    (nodeGraph ends T).edgeFinset.card ≤ T.card := by
  classical
  have hsub : (nodeGraph ends T).edgeFinset ⊆ T.image ends := by
    intro z hz
    induction z using Sym2.ind with
    | h v w =>
      obtain ⟨-, e, he, hez⟩ := nodeGraph_adj.1 (mem_edgeFinset.1 hz)
      exact mem_image.2 ⟨e, he, hez⟩
  exact (card_le_card hsub).trans (card_image_le)

omit [DecidableEq ε] in
/-- A connected family with one fewer edge than vertices is a tree. -/
theorem nodeGraph_isTree_of_card (ends : ε → Sym2 β) (T : Finset ε) (root : β)
    (hr : ∀ v, (nodeGraph ends T).Reachable root v) (hc : T.card + 1 = Fintype.card β) :
    (nodeGraph ends T).IsTree := by
  classical
  have : Nonempty β := ⟨root⟩
  have hconn : (nodeGraph ends T).Connected :=
    (connected_iff _).2 ⟨fun v w => (hr v).symm.trans (hr w), inferInstance⟩
  refine isTree_iff_connected_and_card.2 ⟨hconn, ?_⟩
  have hlow := hconn.card_vert_le_card_edgeSet_add_one
  have hupp := nodeGraph_card_le ends T
  have heq : Nat.card (nodeGraph ends T).edgeSet = (nodeGraph ends T).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  simp only [heq, Nat.card_eq_fintype_card] at hlow ⊢
  omega

open scoped Classical in
/-- The displayed component estimate (A.30), with its sum over odd trees and
one maximal-distance tail. The predicate `far` carries the far-edge indicators.
A maximal-radius root gives the exact factor `∏ s_v² / R²`. The edge count ensures
one original edge per quotient edge, as in Definition 4.10. -/
theorem odd_tree_singleTail_sum (ends : ε → Sym2 β) {F : Finset ε}
    (hloop : ∀ e ∈ F, ¬ (ends e).IsDiag) (hcut : CutEven ends F) (root : β)
    (hr : ∀ v, (nodeGraph ends F).Reachable root v) (s : β → ℝ) (hs : ∀ v, 0 < s v)
    {R : ℝ} (hR : ∀ v, s v ≤ R) (hroot : s root = R) (d a : ε → ℝ)
    (hd : ∀ e ∈ F, 0 < d e) (ha0 : ∀ e ∈ F, 0 ≤ a e) (ha1 : ∀ e ∈ F, a e ≤ 1)
    (ha : ∀ e ∈ F, ∀ v w, ends e = s(v, w) →
      a e ≤ s v * s w / (d e * max (d e) (max (s v) (s w))))
    (far : ε → Prop) (hzero : ∀ e ∈ F, ¬ far e → a e = 0) :
    ∏ e ∈ F, a e ≤ ((∏ v, s v ^ 2) / R ^ 2) *
      ∑ T ∈ F.powerset.filter (fun T =>
        (nodeGraph ends T).IsTree ∧ T.card + 1 = Fintype.card β),
        globalTail R d T * ∏ e ∈ T, if far e then (d e ^ 2)⁻¹ else 0 := by
  classical
  have hterm0 : ∀ T : Finset ε, 0 ≤ globalTail R d T *
      ∏ e ∈ T, if far e then (d e ^ 2)⁻¹ else 0 := fun T =>
    mul_nonneg (globalTail_nonneg R d T) (prod_nonneg fun e _ => by split_ifs <;> positivity)
  have hrad0 : 0 ≤ (∏ v, s v ^ 2) / R ^ 2 := by positivity
  by_cases hpos : 0 < ∏ e ∈ F, a e
  · have hfar : ∀ e ∈ F, far e := by
      intro e he
      by_contra hn
      have hz := prod_eq_zero he (hzero e he hn)
      linarith
    obtain ⟨L, hL, hvalid, hb⟩ := odd_forest_singleTail_average ends hloop hcut {root}
      (fun v => ⟨root, mem_singleton_self _, hr v⟩) s hs (fun f _ v _ => hR v) d a hd ha0 ha1 ha
    have hrad : ∏ v ∈ univ \ {root}, s v ^ 2 = (∏ v, s v ^ 2) / R ^ 2 := by
      rw [sdiff_singleton_eq_erase, ← prod_erase_mul _ _ (mem_univ root), hroot]
      exact (mul_div_cancel_right₀ _ (pow_pos (hroot ▸ hs root) 2).ne').symm
    rw [hrad] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left (deletionAverage_le L hL _ _ ?_) hrad0)
    intro T hTL
    obtain ⟨hTF, hcard, hreach⟩ := hvalid T hTL
    have hcard' : T.card + 1 = Fintype.card β := by
      rw [sdiff_singleton_eq_erase, card_erase_of_mem (mem_univ root), card_univ] at hcard
      have : Nonempty β := ⟨root⟩
      have := Fintype.card_pos (α := β)
      omega
    have hT : (nodeGraph ends T).IsTree := nodeGraph_isTree_of_card ends T root
      (fun v => by
        obtain ⟨z, hz, hr⟩ := hreach v
        rw [mem_singleton] at hz
        exact hz ▸ hr) hcard'
    have hmem : T ∈ F.powerset.filter (fun T =>
        (nodeGraph ends T).IsTree ∧ T.card + 1 = Fintype.card β) :=
      mem_filter.2 ⟨mem_powerset.2 hTF, hT, hcard'⟩
    have heq : (∏ e ∈ T, if far e then (d e ^ 2)⁻¹ else 0) = ∏ e ∈ T, (d e ^ 2)⁻¹ :=
      prod_congr rfl fun e he => ite_eq_left (hfar e (hTF he))
    rw [← heq]
    exact single_le_sum (fun T _ => hterm0 T) hmem
  · exact (le_of_not_gt hpos).trans (mul_nonneg hrad0 (sum_nonneg fun T _ => hterm0 T))

end MultipoleBKT.Limits

end
