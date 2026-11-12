/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteOdd.Forest
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# The separate even quotient tree

See the proof of Lemma A.5. Contract the odd components, then select a tree of even edges.
Parallel edges remain distinct until the tree has been selected.
-/

@[expose] public section

namespace MultipoleBKT.Limits

open Finset SimpleGraph

variable {β ε : Type*} [Fintype β] [DecidableEq β] [DecidableEq ε]

omit [DecidableEq β] in
/-- Select actual multigraph edges over a simple spanning tree. -/
theorem exists_edge_tree (ends : ε → Sym2 β) (E : Finset ε)
    (hc : (nodeGraph ends E).Connected) :
    ∃ T ⊆ E, (nodeGraph ends T).IsTree ∧ T.card + 1 = Fintype.card β := by
  classical
  obtain ⟨G, hGE, hG⟩ := hc.exists_isTree_le
  have hpick : ∀ z : G.edgeFinset, ∃ e ∈ E, ends e = z.val := by
    rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | h v w => exact (nodeGraph_adj.1 (hGE (mem_edgeFinset.1 hz))).2
  choose pick hpE hpends using hpick
  let T : Finset ε := univ.image pick
  have hp_inj : Function.Injective pick := by
    intro z z' h
    apply Subtype.ext
    rw [← hpends z, ← hpends z', h]
  have heq : nodeGraph ends T = G := by
    ext v w
    rw [nodeGraph_adj]
    constructor
    · rintro ⟨hne, e, he, hew⟩
      obtain ⟨z, -, rfl⟩ := mem_image.1 he
      have hz := z.property
      rw [← hpends z, hew] at hz
      exact mem_edgeFinset.1 hz
    · intro hvw
      let z : G.edgeFinset := ⟨s(v, w), mem_edgeFinset.2 hvw⟩
      exact ⟨G.ne_of_adj hvw, pick z, mem_image_of_mem _ (mem_univ _), hpends z⟩
  refine ⟨T, ?_, heq ▸ hG, ?_⟩
  · intro e he
    obtain ⟨z, -, rfl⟩ := mem_image.1 he
    exact hpE z
  · rw [show T = univ.image pick from rfl, card_image_of_injective _ hp_inj, card_univ, Fintype.card_coe]
    exact hG.card_edgeFinset

omit [Fintype β] [DecidableEq β] in
private theorem reachable_map_sdiff {γ : Type*} [DecidableEq γ] (ends : ε → Sym2 β)
    (q : β → γ) (E F : Finset ε)
    (hF : ∀ e ∈ F, ∀ v w, ends e = s(v, w) → q v = q w)
    {v w : β} (hr : (nodeGraph ends E).Reachable v w) :
    (nodeGraph (Sym2.map q ∘ ends) (E \ F)).Reachable (q v) (q w) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Reachable.refl _
  | @cons v u w hvu p ih =>
    obtain ⟨-, e, he, hev⟩ := nodeGraph_adj.1 hvu
    have hstep : (nodeGraph (Sym2.map q ∘ ends) (E \ F)).Reachable (q v) (q u) := by
      by_cases hef : e ∈ F
      · rw [hF e hef v u hev]
      · by_cases hqu : q v = q u
        · rw [hqu]
        · exact (nodeGraph_adj_of_mem (mem_sdiff.2 ⟨he, hef⟩)
            (by simp only [Function.comp_apply, hev, Sym2.map_mk]) hqu).reachable
    exact hstep.trans ih

/-- The tree on the coarse odd components uses only even edges. The quotient includes
isolated odd vertices, as required by `Coarse_X(X₁,…,Xₙ)` in the paper. -/
theorem exists_even_quotient_tree (ends : ε → Sym2 β) (E F : Finset ε)
    (hc : (nodeGraph ends E).Connected) :
    ∃ B ⊆ E \ F,
      (nodeGraph (Sym2.map (nodeGraph ends F).connectedComponentMk ∘ ends) B).IsTree ∧
      B.card + 1 = Nat.card (nodeGraph ends F).ConnectedComponent := by
  classical
  let : Fintype (nodeGraph ends F).ConnectedComponent := Fintype.ofFinite _
  let q := (nodeGraph ends F).connectedComponentMk
  have hF : ∀ e ∈ F, ∀ v w, ends e = s(v, w) → q v = q w := by
    intro e he v w hev
    by_cases hvw : v = w
    · rw [hvw]
    · exact ConnectedComponent.sound (nodeGraph_adj_of_mem he hev hvw).reachable
  have hreach : ∀ C D : (nodeGraph ends F).ConnectedComponent,
      (nodeGraph (Sym2.map q ∘ ends) (E \ F)).Reachable C D := by
    intro C D
    obtain ⟨v, rfl⟩ := C.exists_rep
    obtain ⟨w, rfl⟩ := D.exists_rep
    exact reachable_map_sdiff ends q E F hF (hc.preconnected v w)
  have hconn : (nodeGraph (Sym2.map q ∘ ends) (E \ F)).Connected :=
    (connected_iff _).2 ⟨hreach, Nonempty.map q hc.nonempty⟩
  simpa only [Nat.card_eq_fintype_card] using exists_edge_tree _ _ hconn

end MultipoleBKT.Limits

end
