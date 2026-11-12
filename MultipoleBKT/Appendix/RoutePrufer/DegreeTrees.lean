/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RoutePrufer.Basic

/-!
# Degree-prescribed trees and the leaf step

The tree side of Prüfer's bijection in Lemma A.9.
-/

@[expose] public section

namespace MultipoleBKT.Cayley

universe u

open SimpleGraph Finset
open scoped Classical

/-! ### Trees with a prescribed degree sequence -/

section DegTrees

variable {V : Type u} [Fintype V]

/-- The trees on `V` in which vertex `i` has degree `k i + 1`. -/
noncomputable def degTrees (k : V → ℕ) : Finset (SimpleGraph V) :=
  Finset.univ.filter fun T => T.IsTree ∧ ∀ i, deg T i = k i + 1

theorem mem_degTrees {k : V → ℕ} {T : SimpleGraph V} :
    T ∈ degTrees k ↔ T.IsTree ∧ ∀ i, deg T i = k i + 1 := by
  simp [degTrees]

/-- Decrease `k` by one at `p` and restrict to `V ∖ {v}`. -/
noncomputable def decAt (k : V → ℕ) (v : V) (p : {i // i ≠ v}) : {i // i ≠ v} → ℕ :=
  fun j => k j.1 - if j = p then 1 else 0

end DegTrees

/-! ### The degree-sequence count -/

section Count

variable {V : Type u} [Fintype V]

theorem isTree_top (hV : Fintype.card V = 2) : (⊤ : SimpleGraph V).IsTree := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  rw [isTree_iff_connected_and_card]
  refine ⟨connected_top, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card,
    card_edgeFinset_top_eq_card_choose_two, hV]
  rfl

/-- On two vertices, the only tree is the single edge. -/
theorem degTrees_zero_of_card_two (hV : Fintype.card V = 2) :
    degTrees (0 : V → ℕ) = {⊤} := by
  ext T
  simp only [mem_degTrees, mem_singleton]
  constructor
  · rintro ⟨hT, -⟩
    have h1 := hT.card_edgeFinset
    have h2 : #(⊤ : SimpleGraph V).edgeFinset = 1 := by
      rw [card_edgeFinset_top_eq_card_choose_two, hV]
      rfl
    have hsub : T.edgeFinset ⊆ (⊤ : SimpleGraph V).edgeFinset := edgeFinset_mono le_top
    exact edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le hsub (by omega))
  · rintro rfl
    refine ⟨isTree_top hV, fun i => ?_⟩
    rw [deg_eq_degree, (SimpleGraph.IsRegularOfDegree.top (V := V)).degree_eq i, hV]
    rfl

end Count

end MultipoleBKT.Cayley

end
