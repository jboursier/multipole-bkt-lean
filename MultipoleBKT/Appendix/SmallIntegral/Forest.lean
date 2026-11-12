/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Ear
public import MultipoleBKT.Limits.Majorant
public import MultipoleBKT.Appendix.OrderingTree

/-!
# Spanning forests for the logarithmic tree integrals

See Lemma A.4, (A.21) and (A.25).
A connected loop-free edge set with one fewer edge than vertices is a tree.
This edge-count criterion assembles the retained near, odd and even trees.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open Finset SimpleGraph
open Limits

/-! ### Trees by counting edges -/

section Counting

variable {V : Type*} [Fintype V]

open scoped Classical in
/-- A connected graph `fromEdgeSet A` (`A` without loops) with `|A| + 1 ≤ |V|` is a tree with
edge set `A`, and `|A| + 1 = |V|`. -/
theorem isTree_fromEdgeSet_of_card {A : Finset (Sym2 V)} (hdiag : ∀ e ∈ A, ¬ e.IsDiag)
    (hconn : (fromEdgeSet (A : Set (Sym2 V))).Connected) (hcard : A.card + 1 ≤ Fintype.card V) :
    (fromEdgeSet (A : Set (Sym2 V))).IsTree ∧
      (fromEdgeSet (A : Set (Sym2 V))).edgeFinset = A ∧ A.card + 1 = Fintype.card V := by
  have hE : (fromEdgeSet (A : Set (Sym2 V))).edgeFinset = A := by
    ext e
    rw [mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe]
    exact ⟨fun h => h.1, fun h => ⟨h, hdiag e h⟩⟩
  have hncard : Nat.card (fromEdgeSet (A : Set (Sym2 V))).edgeSet = A.card := by
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card, hE]
  have hle := hconn.card_vert_le_card_edgeSet_add_one
  rw [hncard, Nat.card_eq_fintype_card] at hle
  have heq : A.card + 1 = Fintype.card V := le_antisymm hcard hle
  refine ⟨isTree_iff_connected_and_card.2 ⟨hconn, ?_⟩, hE, heq⟩
  rw [hncard, Nat.card_eq_fintype_card, heq]

end Counting

end SmallIntegral

end MultipoleBKT

end
