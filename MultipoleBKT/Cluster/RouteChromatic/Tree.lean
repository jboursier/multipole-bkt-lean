/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.RouteChromatic.Incidence
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The incidence tree of a hypertree

The graph on the indices and the elements is connected and has one fewer edge
than vertices. This is the first step of the proof of (4.150).
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- The bipartite incidence graph on the indices and the union of their sets. -/
def incidenceGraph (X : Fin n → Finset α) :
    SimpleGraph (Fin n ⊕ (univ.biUnion X : Finset α)) where
  Adj u v := match u, v with
    | .inl i, .inr a => a.val ∈ X i
    | .inr a, .inl i => a.val ∈ X i
    | _, _ => False
  symm := ⟨by rintro (i | a) (j | b) <;> simp_all⟩
  loopless := ⟨by rintro (i | a) <;> simp⟩

/-- The edges of the incidence graph are exactly the pairs `(i,a)` with `a ∈ X_i`. -/
private noncomputable def incidenceEdgeEquiv (X : Fin n → Finset α) :
    (Σ i : Fin n, {a : (univ.biUnion X : Finset α) // a.val ∈ X i}) ≃
      (incidenceGraph X).edgeSet := by
  classical
  let f : (Σ i : Fin n, {a : (univ.biUnion X : Finset α) // a.val ∈ X i}) →
      (incidenceGraph X).edgeSet := fun p => ⟨s(Sum.inl p.1, Sum.inr p.2.val), p.2.prop⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    have h' := congrArg Subtype.val h
    simp only [f, Sym2.eq_iff, Sum.inl.injEq,
      Sum.inr.injEq, Sum.inl_ne_inr, false_and, or_false] at h'
    rcases h' with ⟨rfl, hab⟩
    exact congrArg (Sigma.mk i) (Subtype.ext hab)
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h u v =>
      cases u with
      | inl i =>
        cases v with
        | inl j => exact False.elim he
        | inr a => exact ⟨⟨i, ⟨a, he⟩⟩, rfl⟩
      | inr a =>
        cases v with
        | inl i => exact ⟨⟨i, ⟨a, he⟩⟩, Subtype.ext Sym2.eq_swap⟩
        | inr b => exact False.elim he

/-- The number of incidence edges is the sum of the set sizes. -/
theorem card_incidenceGraph_edges (X : Fin n → Finset α) :
    Nat.card (incidenceGraph X).edgeSet = ∑ i, (X i).card := by
  classical
  rw [← Nat.card_congr (incidenceEdgeEquiv X), Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine sum_congr rfl fun i _ => ?_
  let e : {a : (univ.biUnion X : Finset α) // a.val ∈ X i} ≃ X i :=
    { toFun := fun a => ⟨a.val.val, a.prop⟩
      invFun := fun a => ⟨⟨a.val, mem_biUnion.mpr ⟨i, mem_univ _, a.prop⟩⟩, a.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]

/-- Connectivity of the connection graph lifts to the incidence graph. -/
theorem incidenceGraph_connected {X : Fin n → Finset α}
    (hX : (connectionGraph X).Connected) : (incidenceGraph X).Connected := by
  classical
  have hindices : ∀ i j, (incidenceGraph X).Reachable (.inl i) (.inl j) := by
    intro i j
    obtain ⟨p⟩ := hX i j
    induction p with
    | nil => exact Reachable.refl _
    | @cons i j k hij p ih =>
      obtain ⟨-, a, hai, haj⟩ := connectionGraph_adj.mp hij
      let a' : (univ.biUnion X : Finset α) := ⟨a, mem_biUnion.mpr ⟨i, mem_univ _, hai⟩⟩
      exact (Adj.reachable (G := incidenceGraph X) (u := .inl i) (v := .inr a') hai).trans
        ((Adj.reachable (G := incidenceGraph X) (u := .inr a') (v := .inl j) haj).trans ih)
  obtain ⟨r⟩ := hX.nonempty
  have : Nonempty (Fin n ⊕ (univ.biUnion X : Finset α)) := ⟨.inl r⟩
  have hroot : ∀ v, (incidenceGraph X).Reachable (.inl r) v := by
    rintro (i | a)
    · exact hindices r i
    · obtain ⟨i, -, hi⟩ := mem_biUnion.mp a.prop
      exact (hindices r i).trans (Adj.reachable (G := incidenceGraph X) hi)
  exact ⟨fun u v => (hroot u).symm.trans (hroot v)⟩

/-- The incidence graph of a hypertree is a tree, by connectivity and the edge count.
See equation (4.150). -/
theorem incidenceGraph_isTree_of_mem_hypertrees {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) : (incidenceGraph X).IsTree := by
  classical
  refine isTree_iff_connected_and_card.mpr
    ⟨incidenceGraph_connected (connectionGraph_connected_of_mem_hypertrees hX), ?_⟩
  rw [card_incidenceGraph_edges, Nat.card_eq_fintype_card, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_coe]
  have h := (mem_filter.mp hX).2.2.2
  rw [← Nat.cast_sum] at h
  omega

end MultipoleBKT

end
