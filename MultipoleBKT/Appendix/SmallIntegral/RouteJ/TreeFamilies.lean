/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.RetainedTrees
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Counting

/-!
# The original sum over a near tree in each block

See Lemma A.4, (A.21) and (A.22).
The family retains the original fibre trees. Its cardinality is bounded using
the Prüfer count on every nonsingleton block.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open Finset SimpleGraph Limits
open scoped Classical

/-- A tree in every block fibre, as in the paper family `(R_S)`. -/
abbrev NearTreeFamily {V B : Type*} (blk : V → B) :=
  ∀ b, {T : SimpleGraph {i // blk i = b} // T.IsTree}

/-- Cayley's count also gives a uniform bound for singleton or empty fibres. -/
theorem card_tree_type_le {W : Type*} [Fintype W] [DecidableEq W] {k : ℕ}
    (hk : 2 ≤ k) (hW : Fintype.card W ≤ k) :
    Fintype.card {T : SimpleGraph W // T.IsTree} ≤ k ^ k := by
  by_cases hw2 : 2 ≤ Fintype.card W
  · rw [Fintype.card_subtype]
    have hc := card_trees hw2
    change ((univ : Finset (SimpleGraph W)).filter IsTree).card ≤ _
    rw [hc]
    exact (Nat.pow_le_pow_left hW _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  · have : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have h1 : Fintype.card (SimpleGraph W) = 1 := Fintype.card_unique
    have hs := Fintype.card_subtype_le (fun T : SimpleGraph W => T.IsTree)
    rw [h1] at hs
    exact hs.trans (Nat.one_le_pow _ _ (by omega))

/-- The finite near-tree sum has a bound depending only on the cluster size.
The coarse bound is deliberately larger than the product of Cayley counts. -/
theorem card_nearTreeFamily_le {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] [DecidableEq B] (blk : V → B) {k : ℕ} (hk : 2 ≤ k)
    (hV : Fintype.card V ≤ k) (hB : Fintype.card B ≤ k) :
    Fintype.card (NearTreeFamily blk) ≤ (k ^ k) ^ k := by
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _b : B, k ^ k := Finset.prod_le_prod fun b _ =>
      card_tree_type_le hk ((Fintype.card_subtype_le _).trans hV)
    _ = (k ^ k) ^ Fintype.card B := by simp
    _ ≤ (k ^ k) ^ k := Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) hB

/-- Choose the near trees without altering either far-edge family. -/
theorem exists_linked_nearTreeFamily {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] [DecidableEq B] (blk : V → B) (M lam : ℝ) (c : V → ℂ × ℂ)
    (hB : ∀ b, ((nearGraph M lam c).induce {i | blk i = b}).Connected) :
    ∃ R : NearTreeFamily blk, ∀ i j, s(i, j) ∈ nearForest blk (fun b => (R b).val) →
      MultipoleLinked M lam (c i) (c j) := by
  have he (b : B) := (hB b).exists_isTree_le
  choose T hTle hT using he
  refine ⟨fun b => ⟨T b, hT b⟩, fun i j hij => ?_⟩
  obtain ⟨b, e, he, heq⟩ := (mem_nearForest blk (fun b => T b) _).mp hij
  induction e using Sym2.ind with
  | h a d =>
    have hadj := hTle b (mem_edgeFinset.mp he)
    rw [comap_adj, nearGraph_adj] at hadj
    simp only [Sym2.map_mk, Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj.2
    · exact multipoleLinked_comm.mp hadj.2

/-- The connected-block indicator is bounded by the sum of products
of near-edge indicators over the retained near-tree families.
See (A.21). -/
theorem connected_blocks_le_nearTreeFamily {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] [DecidableEq B] (blk : V → B) (M lam : ℝ) (c : V → ℂ × ℂ) :
    (if ∀ b, ((nearGraph M lam c).induce {i | blk i = b}).Connected then (1 : ℝ) else 0) ≤
      ∑ R : NearTreeFamily blk, ∏ e ∈ nearForest blk (fun b => (R b).val), linkE M lam c e := by
  have hnonneg (R : NearTreeFamily blk) :
      0 ≤ ∏ e ∈ nearForest blk (fun b => (R b).val), linkE M lam c e :=
    prod_nonneg fun e _ => linkE_nonneg c e
  split_ifs with hc
  · obtain ⟨R, hR⟩ := exists_linked_nearTreeFamily blk M lam c hc
    have hp : (∏ e ∈ nearForest blk (fun b => (R b).val), linkE M lam c e) = 1 := by
      apply prod_eq_one
      intro e he
      induction e using Sym2.ind with
      | h i j => exact ite_eq_left (hR i j he)
    rw [← hp]
    exact single_le_sum (fun R _ => hnonneg R) (mem_univ R)
  · exact sum_nonneg fun R _ => hnonneg R

end MultipoleBKT.SmallIntegral.RouteJ

end
