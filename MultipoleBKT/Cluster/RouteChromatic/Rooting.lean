/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.RouteChromatic.Tree

/-!
# Rooting the incidence tree

We orient the incidence tree away from an index root. Each element has a parent
index and each other index is a child of exactly one element. This makes precise
the rooting used in (4.150).
-/

@[expose] public section

namespace MultipoleBKT.RouteChromatic

open Finset SimpleGraph

/-- Rooted incidence data. The children of an element are all its incident indices
except its parent. The branch map assigns every nonroot index to its unique parent
element, and depth strictly increases from parent index to child index. -/
structure Rooting {V A : Type*} [DecidableEq V] (C : A → Finset V) (r : V) where
  parent : A → V
  parent_mem : ∀ a, parent a ∈ C a
  branch : {i : V // i ≠ r} → A
  branch_mem : ∀ i, i.val ∈ C (branch i)
  branch_ne : ∀ i, i.val ≠ parent (branch i)
  child_ne_root : ∀ a i, i ∈ C a → i ≠ parent a → i ≠ r
  branch_eq : ∀ a i (hi : i ∈ C a) (hne : i ≠ parent a),
    branch ⟨i, child_ne_root a i hi hne⟩ = a
  depth : V → ℕ
  parent_lt : ∀ a i, i ∈ C a → i ≠ parent a → depth (parent a) < depth i

/-- Orienting a finite tree from `r` accounts for every edge exactly once. -/
private theorem exists_tree_orientation {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (r : V) :
    ∃ p : {v : V // v ≠ r} → V,
      (∀ v, G.Adj v.val (p v)) ∧
      (∀ v, G.dist r (p v) < G.dist r v.val) ∧
      ∀ u v, G.Adj u v →
        (∃ hu : u ≠ r, p ⟨u, hu⟩ = v) ∨ (∃ hv : v ≠ r, p ⟨v, hv⟩ = u) := by
  classical
  have key : ∀ v : V, v ≠ r → ∃ w, G.Adj v w ∧ G.dist r w < G.dist r v := by
    intro v hv
    obtain ⟨q, hq⟩ := hG.connected.exists_walk_length_eq_dist v r
    cases q with
    | nil => exact False.elim (hv rfl)
    | cons h q =>
      refine ⟨_, h, ?_⟩
      rw [Walk.length_cons] at hq
      have hd := dist_le q
      rw [dist_comm (u := r), dist_comm (u := r), ← hq]
      exact Nat.lt_succ_of_le hd
  choose p hp hd using (fun v : {v : V // v ≠ r} => key v.val v.prop)
  let f : {v : V // v ≠ r} → G.edgeSet := fun v => ⟨s(v.val, p v), hp v⟩
  have hf : Function.Injective f := by
    intro u v h
    have h' := congrArg Subtype.val h
    simp only [f, Sym2.eq_iff] at h'
    rcases h' with ⟨huv, -⟩ | ⟨hup, hpv⟩
    · exact Subtype.ext huv
    · have hdu := hd u
      have hdv := hd v
      rw [hpv] at hdu
      rw [← hup] at hdv
      omega
  have hcard : Fintype.card {v : V // v ≠ r} = Fintype.card G.edgeSet := by
    have hc := hG.card_edgeFinset
    rw [edgeFinset_card] at hc
    have hc' : Fintype.card {v : V // v ≠ r} = Fintype.card V - 1 := by
      simp [Fintype.card_subtype_compl]
    omega
  have hsurj := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩ |>.surjective
  refine ⟨p, hp, hd, ?_⟩
  intro u v huv
  obtain ⟨w, hw⟩ := hsurj ⟨s(u, v), huv⟩
  have h' := congrArg Subtype.val hw
  simp only [f, Sym2.eq_iff] at h'
  rcases h' with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · left
    subst u
    exact ⟨w.prop, hv⟩
  · right
    subst v
    exact ⟨w.prop, hu⟩

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- Root the hypertree incidence graph at any index. Every child belongs to a
unique parent element, and lies strictly below that element's parent index.
See equation (4.150). -/
theorem exists_rooting {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) (r : Fin n) :
    Nonempty (Rooting (fun a : (univ.biUnion X : Finset α) => incidence X a.val) r) := by
  classical
  let U := (univ.biUnion X : Finset α)
  let G := incidenceGraph X
  obtain ⟨p, hp, hd, he⟩ := exists_tree_orientation G
    (incidenceGraph_isTree_of_mem_hypertrees hX) (.inl r)
  have ha : ∀ a : U, ∃ i, p ⟨.inr a, Sum.inr_ne_inl⟩ = .inl i ∧ a.val ∈ X i := by
    intro a
    have h := hp ⟨.inr a, Sum.inr_ne_inl⟩
    cases hpa : p ⟨.inr a, Sum.inr_ne_inl⟩ with
    | inl i => exact ⟨i, rfl, by rw [hpa] at h; exact h⟩
    | inr b => rw [hpa] at h; exact False.elim h
  choose parent hparent hmem using ha
  have hi : ∀ i : {i : Fin n // i ≠ r}, ∃ a : U,
      p ⟨.inl i.val, fun h => i.prop (Sum.inl.inj h)⟩ = .inr a ∧ a.val ∈ X i.val := by
    intro i
    have h := hp ⟨.inl i.val, fun h => i.prop (Sum.inl.inj h)⟩
    cases hpi : p ⟨.inl i.val, fun h => i.prop (Sum.inl.inj h)⟩ with
    | inl j => rw [hpi] at h; exact False.elim h
    | inr a => exact ⟨a, rfl, by rw [hpi] at h; exact h⟩
  choose branch hbranch hbmem using hi
  have hbne : ∀ i, i.val ≠ parent (branch i) := by
    intro i heq
    have h1 := hd ⟨.inr (branch i), Sum.inr_ne_inl⟩
    have h2 := hd ⟨.inl i.val, fun h => i.prop (Sum.inl.inj h)⟩
    simp only [hparent, ← heq] at h1
    simp only [hbranch] at h2
    omega
  have hchild : ∀ (a : U) i, a.val ∈ X i → i ≠ parent a →
      ∃ hi : i ≠ r, branch ⟨i, hi⟩ = a := by
    intro a i hai hine
    rcases he (.inl i) (.inr a) hai with ⟨hi, hpi⟩ | ⟨ha, hpa⟩
    · have hir : i ≠ r := fun h => hi (congrArg Sum.inl h)
      refine ⟨hir, ?_⟩
      have h := hbranch ⟨i, hir⟩
      rw [hpi] at h
      exact (Sum.inr.inj h).symm
    · rw [hparent a] at hpa
      exact False.elim (hine (Sum.inl.inj hpa).symm)
  refine ⟨{ parent := parent
            parent_mem := fun a => mem_incidence.mpr (hmem a)
            branch := branch
            branch_mem := fun i => mem_incidence.mpr (hbmem i)
            branch_ne := hbne
            child_ne_root := fun a i hi hne => (hchild a i (mem_incidence.mp hi) hne).choose
            branch_eq := fun a i hi hne => (hchild a i (mem_incidence.mp hi) hne).choose_spec
            depth := fun i => G.dist (.inl r) (.inl i)
            parent_lt := ?_ }⟩
  intro a i hai hine
  obtain ⟨hir, hba⟩ := hchild a i (mem_incidence.mp hai) hine
  have h1 := hd ⟨.inr a, Sum.inr_ne_inl⟩
  have h2 := hd ⟨.inl i, fun h => hir (Sum.inl.inj h)⟩
  dsimp only at h2
  simp only [hparent] at h1
  rw [hbranch ⟨i, hir⟩, hba] at h2
  exact h1.trans h2

end MultipoleBKT.RouteChromatic

end
