/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.UrsellComplete
public import MultipoleBKT.Frozen.Hypertrees
public import MultipoleBKT.Frozen.HypertreeWeight

/-!
# Incidence counts for hypertrees

The incidence sets and their double-counting identities used in the proof of
(4.150).
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

section Counting

variable {V ι : Type*} [Fintype V]

/-- A connected hypergraph with nonempty hyperedges `P_k` (`k ∈ s`) on the vertex type `V`
satisfies `|V| ≤ ∑ₖ (|P_k| - 1) + 1`: a spanning star in each hyperedge gives a connected
graph with at most `∑ₖ (|P_k| - 1)` edges. -/
theorem card_le_sum_card_sub_one (s : Finset ι) (P : ι → Finset V)
    (hne : ∀ k ∈ s, (P k).Nonempty)
    (hconn : (SimpleGraph.fromRel fun x y => ∃ k ∈ s, x ∈ P k ∧ y ∈ P k).Connected) :
    (Fintype.card V : ℤ) ≤ ∑ k ∈ s, (((P k).card : ℤ) - 1) + 1 := by
  classical
  have : Nonempty V := hconn.nonempty
  choose! c hc using hne
  let star : ι → SimpleGraph V := fun k => SimpleGraph.fromRel fun x y => x = c k ∧ y ∈ P k
  have hstar : ∀ k ∈ s, ∀ z ∈ P k, (s.sup star).Reachable (c k) z := by
    intro k hk z hz
    by_cases h : c k = z
    · rw [h]
    · refine Adj.reachable ?_
      have hadj : (star k).Adj (c k) z := by
        simp only [star, fromRel_adj, true_and]
        exact ⟨h, Or.inl hz⟩
      exact (le_sup (f := star) hk : star k ≤ s.sup star) hadj
  have hS : (s.sup star).Connected := by
    refine connected_of_forall_adj_reachable hconn fun x y hxy => ?_
    rw [fromRel_adj] at hxy
    rcases hxy.2 with ⟨k, hk, hx, hy⟩ | ⟨k, hk, hy, hx⟩
    · exact (hstar k hk x hx).symm.trans (hstar k hk y hy)
    · exact (hstar k hk x hx).symm.trans (hstar k hk y hy)
  have hcard_star : ∀ k ∈ s, ((star k).edgeFinset.card : ℤ) ≤ (P k).card - 1 := by
    intro k hk
    have hsub : (star k).edgeFinset ⊆ ((P k).erase (c k)).image fun y => s(c k, y) := by
      intro e he
      induction e using Sym2.ind with
      | h x y =>
        rw [mem_edgeFinset, mem_edgeSet] at he
        simp only [star, fromRel_adj] at he
        obtain ⟨hne, h⟩ := he
        rw [mem_image]
        rcases h with ⟨rfl, hy⟩ | ⟨rfl, hx⟩
        · exact ⟨y, mem_erase.mpr ⟨hne.symm, hy⟩, rfl⟩
        · exact ⟨x, mem_erase.mpr ⟨hne, hx⟩, Sym2.eq_swap⟩
    have h1 := (card_le_card hsub).trans card_image_le
    rw [card_erase_of_mem (hc k hk)] at h1
    have h2 : 1 ≤ (P k).card := card_pos.mpr ⟨c k, hc k hk⟩
    omega
  have hsubS : (s.sup star).edgeFinset ⊆ s.biUnion fun k => (star k).edgeFinset := by
    intro e he
    rw [mem_edgeFinset] at he
    obtain ⟨k, hk, hek⟩ := exists_mem_edgeSet_of_mem_finsetSup s star he
    exact mem_biUnion.mpr ⟨k, hk, mem_edgeFinset.mpr hek⟩
  have hcardS : ((s.sup star).edgeFinset.card : ℤ) ≤ ∑ k ∈ s, (((P k).card : ℤ) - 1) := by
    have h1 := (card_le_card hsubS).trans card_biUnion_le
    calc ((s.sup star).edgeFinset.card : ℤ) ≤ ∑ k ∈ s, ((star k).edgeFinset.card : ℤ) := by
          exact_mod_cast h1
      _ ≤ _ := sum_le_sum hcard_star
  have hV := hS.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← card_edgeFinset_eq_ncard] at hV
  have hV' : (Fintype.card V : ℤ) ≤ ((s.sup star).edgeFinset.card : ℤ) + 1 := by exact_mod_cast hV
  linarith

end Counting

section Hypertree

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- The set `{i ∈ [n] : a ∈ X_i}` of indices of the sets containing `a`. -/
def incidence (X : Fin n → Finset α) (a : α) : Finset (Fin n) :=
  univ.filter fun i => a ∈ X i

@[simp]
theorem mem_incidence {X : Fin n → Finset α} {a : α} {i : Fin n} :
    i ∈ incidence X a ↔ a ∈ X i := by
  simp [incidence]

theorem incidence_nonempty {X : Fin n → Finset α} {a : α} (ha : a ∈ univ.biUnion X) :
    (incidence X a).Nonempty := by
  obtain ⟨i, -, hi⟩ := mem_biUnion.mp ha
  exact ⟨i, mem_incidence.mpr hi⟩

theorem connectionGraph_adj {X : Fin n → Finset α} {i j : Fin n} :
    (connectionGraph X).Adj i j ↔ i ≠ j ∧ ∃ a, a ∈ X i ∧ a ∈ X j := by
  rw [connectionGraph, fromRel_adj, inter_comm (X j), or_self]
  simp only [Finset.Nonempty, mem_inter]

/-- Double counting: `∑ₐ |C_a| = ∑ᵢ |X_i|`. -/
theorem sum_card_incidence (X : Fin n → Finset α) :
    ∑ a ∈ univ.biUnion X, (incidence X a).card = ∑ i, (X i).card := by
  simp only [incidence, card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← card_filter]
  congr 1
  ext a
  simp only [mem_filter, and_iff_right_iff_imp]
  exact fun ha => mem_biUnion.mpr ⟨i, mem_univ _, ha⟩

/-- The connection graph of a hypertree is connected. -/
theorem connectionGraph_connected_of_mem_hypertrees {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) : (connectionGraph X).Connected := by
  classical
  simp only [hypertrees, mem_filter] at hX
  exact hX.2.2.1

/-- For a hypertree, `∑ₐ (|C_a| - 1) = n - 1`. -/
theorem sum_card_incidence_sub_one {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) :
    ∑ a ∈ univ.biUnion X, (((incidence X a).card : ℤ) - 1) = n - 1 := by
  classical
  have h := hX
  simp only [hypertrees, mem_filter] at h
  have h3 := h.2.2.2
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, ← Nat.cast_sum, sum_card_incidence,
    Nat.cast_sum]
  linarith

end Hypertree

end MultipoleBKT

end
