/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RoutePrufer.DegreeTrees
public import Mathlib.Data.Subtype

/-!
# The invertible leaf step for Prüfer encoding

Remove a specified leaf and record its unique neighbour. The inverse attaches the leaf
at the recorded neighbour. This is the tree step of the bijection cited in Lemma A.9.
-/

@[expose] public section

namespace MultipoleBKT.Cayley

universe u

open SimpleGraph Finset
open scoped Classical

variable {V : Type u} [Fintype V] {k : V → ℕ} {v : V}

theorem prune_mem (hk : k v = 0) (p : {i // i ≠ v}) (hkp : 1 ≤ k p.1)
    {T : SimpleGraph V} (hT : T ∈ degTrees k) (hadj : T.Adj v p.1) :
    T.comap Subtype.val ∈ degTrees (decAt k v p) := by
  simp only [mem_degTrees] at hT ⊢
  obtain ⟨htree, hdeg⟩ := hT
  have hv : deg T v = 1 := by rw [hdeg v, hk]
  refine ⟨isTree_comap htree hv, fun j => ?_⟩
  have h1 := deg_eq_comap_add T v j
  obtain ⟨w, hw, hwu⟩ := (deg_eq_one_iff T v).mp hv
  have hpw : p.1 = w := hwu _ hadj
  have h2 : T.Adj j.1 v ↔ j = p := by
    constructor
    · intro h
      exact Subtype.ext ((hwu _ h.symm).trans hpw.symm)
    · rintro rfl
      exact hadj.symm
  rw [hdeg j.1] at h1
  unfold decAt
  by_cases h : j = p
  · subst h
    simp only [h2, ite_true] at h1 ⊢
    omega
  · simp only [h2, h, ite_false] at h1 ⊢
    omega

theorem graft_mem (hk : k v = 0) (p : {i // i ≠ v}) (hkp : 1 ≤ k p.1)
    {T' : SimpleGraph {i // i ≠ v}} (hT' : T' ∈ degTrees (decAt k v p)) :
    addLeaf v p T' ∈ degTrees k := by
  simp only [mem_degTrees] at hT' ⊢
  obtain ⟨htree, hdeg⟩ := hT'
  refine ⟨isTree_addLeaf htree, fun i => ?_⟩
  by_cases hi : i = v
  · subst hi
    rw [deg_addLeaf_left, hk]
  · have := deg_addLeaf (p := p) (T' := T') ⟨i, hi⟩
    simp only at this
    rw [this, hdeg]
    unfold decAt
    by_cases h : (⟨i, hi⟩ : {i // i ≠ v}) = p
    · have : i = p.1 := congrArg Subtype.val h
      subst this
      simp only [h, ite_true]
      omega
    · simp only [h, ite_false]
      omega

/-- The possible recorded neighbours of a leaf. -/
abbrev Parents (k : V → ℕ) (v : V) := {p : {i // i ≠ v} // 1 ≤ k p.1}

/-- The unique neighbour of a prescribed leaf. -/
noncomputable def leafParent (hk : k v = 0) (T : {T // T ∈ degTrees k}) : {i // i ≠ v} :=
  let h := (deg_eq_one_iff T.1 v).mp (by rw [(mem_degTrees.mp T.2).2 v, hk])
  ⟨h.choose, h.choose_spec.1.ne'⟩

theorem leafParent_adj (hk : k v = 0) (T : {T // T ∈ degTrees k}) :
    T.1.Adj v (leafParent hk T).1 :=
  ((deg_eq_one_iff T.1 v).mp (by rw [(mem_degTrees.mp T.2).2 v, hk])).choose_spec.1

theorem leafParent_pos (hk : k v = 0) (hV : 3 ≤ Fintype.card V)
    (T : {T // T ∈ degTrees k}) : 1 ≤ k (leafParent hk T).1 := by
  let p := leafParent hk T
  have hv : deg T.1 v = 1 := by rw [(mem_degTrees.mp T.2).2 v, hk]
  have hcard := card_subtype_ne_add_one v
  have : Nontrivial {i // i ≠ v} := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos := one_le_deg_of_isTree (isTree_comap (mem_degTrees.mp T.2).1 hv) p
  have hdeg := deg_eq_comap_add T.1 v p
  rw [(mem_degTrees.mp T.2).2 p.1, ite_eq_left (leafParent_adj hk T).symm] at hdeg
  change 1 ≤ k p.1
  omega

/-- One step of Prüfer encoding, with leaf attachment as its explicit inverse. -/
noncomputable def treeStep (hk : k v = 0) (hV : 3 ≤ Fintype.card V) :
    {T // T ∈ degTrees k} ≃
      (Σ p : Parents k v, {T' // T' ∈ degTrees (decAt k v p.1)}) where
  toFun T := ⟨⟨leafParent hk T, leafParent_pos hk hV T⟩,
    ⟨T.1.comap Subtype.val, prune_mem hk _ (leafParent_pos hk hV T) T.2 (leafParent_adj hk T)⟩⟩
  invFun Q := ⟨addLeaf v Q.1.1 Q.2.1, graft_mem hk _ Q.1.2 Q.2.2⟩
  left_inv T := by
    apply Subtype.ext
    exact addLeaf_comap (by rw [(mem_degTrees.mp T.2).2 v, hk]) (leafParent_adj hk T)
  right_inv Q := by
    obtain ⟨p, T'⟩ := Q
    have hp : leafParent hk ⟨addLeaf v p.1 T'.1, graft_mem hk _ p.2 T'.2⟩ = p.1 := by
      apply Subtype.ext
      exact (addLeaf_adj_left (v := v) (p := p.1) (T' := T'.1) _).mp
        (leafParent_adj hk ⟨addLeaf v p.1 T'.1, graft_mem hk _ p.2 T'.2⟩)
    apply Sigma.ext (Subtype.ext hp)
    dsimp only
    apply (Subtype.heq_iff_coe_eq (fun G => by rw [hp])).mpr
    exact comap_addLeaf

end MultipoleBKT.Cayley

end
