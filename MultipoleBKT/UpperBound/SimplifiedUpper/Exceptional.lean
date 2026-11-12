/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.Pseudoforest
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Pseudoforests and the recording of the exceptional edges

The paper: proof of Lemma 5.36: "For fixed retained `T`, record the
skeleton bridges, a subset of `T`. Cutting these edges in `(V_X, T)/X` gives components `C ⊂ X`.
Recording also the exceptional edge or none in each component gives at most
`2^{|T|} ∏_C (1 + binom(|V_C|, 2)) ≤ 4^k` possibilities. Deleting the recorded exceptional edges
from `F` leaves a pseudoforest with weights `ḡ_ij`, and the records reconstruct `F`."

* `isPseudoforest_iSup`: a union of vertex-disjoint pseudoforests is a pseudoforest.
  `IsPseudoforest.map`: the image of a pseudoforest under an embedding is a pseudoforest.
* `ValidSimpleExc H D` excludes diagonal pairs from the peeling interface's `ValidExc`.
  `card_validSimpleExc_le_prod` counts one optional edge per component, and
  `prod_component_choices_le` bounds their product by `2^{|V|}`.
* `card_le_le_pow`: a graph `T` has at most `2^{|T|}` subgraphs (the record of the skeleton
  bridges, as the subgraph of `T` they leave).
* `eq_of_reachable_of_forall_adj`: a function constant along the edges of `G` is constant on its
  components.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Finset SimpleGraph Peeling

/-! ### Pseudoforests -/

section Pseudoforest

variable {V : Type*}

/-- **A union of vertex-disjoint pseudoforests is a pseudoforest.** -/
theorem isPseudoforest_iSup {ι : Type*} (G : ι → SimpleGraph V)
    (hG : ∀ l, IsPseudoforest (G l))
    (hdisj : ∀ (l l' : ι) (v w w' : V), (G l).Adj v w → (G l').Adj v w' → l = l') :
    IsPseudoforest (⨆ l, G l) := by
  classical
  choose φ hφ1 hφ2 using hG
  refine ⟨fun v => if h : ∃ l, (φ l v).isSome then φ h.choose v else none, ?_, ?_⟩
  · intro i j hij
    dsimp only at hij
    split_ifs at hij with h
    exact (iSup_adj).2 ⟨_, hφ1 _ i j hij⟩
  · intro e he
    rw [edgeSet_iSup, Set.mem_iUnion] at he
    obtain ⟨l, hl⟩ := he
    obtain ⟨i, ⟨j, hij, rfl⟩, huniq⟩ := hφ2 l _ hl
    have hex : ∃ l', (φ l' i).isSome := ⟨l, by rw [hij]; rfl⟩
    have hch : hex.choose = l := by
      obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.1 hex.choose_spec
      exact hdisj _ _ i j' j (hφ1 _ i j' hj') (hφ1 l i j hij)
    refine ⟨i, ⟨j, ?_, rfl⟩, ?_⟩
    · dsimp only
      rw [dite_eq_left hex, hch, hij]
    · rintro i' ⟨j', hj', heq⟩
      dsimp only at hj'
      split_ifs at hj' with h'
      have hadj' := hφ1 _ i' j' hj'
      have hl' : h'.choose = l := by
        have : (G l).Adj i' j' := by
          rw [← mem_edgeSet, heq]
          exact hl
        exact hdisj _ _ i' j' j' hadj' this
      rw [hl'] at hj'
      exact huniq i' ⟨j', hj', heq⟩

/-- **The image of a pseudoforest under an embedding is a pseudoforest.** -/
theorem IsPseudoforest.map {W : Type*} (f : W ↪ V) {G : SimpleGraph W} (hG : IsPseudoforest G) :
    IsPseudoforest (G.map f) := by
  classical
  obtain ⟨φ, h1, h2⟩ := hG
  refine ⟨fun v => if h : ∃ w, f w = v then (φ h.choose).map f else none, ?_, ?_⟩
  · intro i j hij
    dsimp only at hij
    split_ifs at hij with h
    obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.1 hij
    rw [map_adj]
    exact ⟨h.choose, w', h1 _ _ hw', h.choose_spec, rfl⟩
  · intro e he
    rw [edgeSet_map, Set.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨u, ⟨v, huv, rfl⟩, huniq⟩ := h2 e' he'
    have hex : ∃ w, f w = f u := ⟨u, rfl⟩
    have hch : hex.choose = u := f.injective hex.choose_spec
    refine ⟨f u, ⟨f v, ?_, rfl⟩, ?_⟩
    · dsimp only
      rw [dite_eq_left hex, hch, huv]
      rfl
    · rintro i' ⟨j', hj', heq⟩
      dsimp only at hj'
      split_ifs at hj' with h'
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hj'
      have hi' : f h'.choose = i' := h'.choose_spec
      have hs : s(h'.choose, x) = s(u, v) := by
        apply Sym2.map.injective f.injective
        rw [Sym2.map_mk, Sym2.map_mk, hi']
        exact heq
      have := huniq h'.choose ⟨x, hx, hs⟩
      rw [← hi', this]

end Pseudoforest

/-! ### Reachability -/

section Reach

variable {V α : Type*}

/-- A function constant along the edges of `G` is constant on the components of `G`. -/
theorem eq_of_reachable_of_forall_adj {G : SimpleGraph V} {f : V → α}
    (hf : ∀ u v, G.Adj u v → f u = f v) {x y : V} (h : G.Reachable x y) : f x = f y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hf _ _ hadj).trans ih

end Reach

/-! ### The record of the exceptional edges -/

section Exceptional

variable {V : Type*}

/-- `D` is an admissible record of exceptional edges for the partition into the components of `H`:
the endpoints of each edge of `D` lie in one component of `H`, and two edges of `D` meeting a common
component are equal. -/
def ValidExc (H : SimpleGraph V) (D : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ D, ∀ x ∈ e, ∀ y ∈ e, H.Reachable x y) ∧
    ∀ e ∈ D, ∀ e' ∈ D, ∀ x ∈ e, ∀ y ∈ e', H.Reachable x y → e = e'

/-- The paper records edges of a simple graph, so diagonal pairs are excluded. -/
def ValidSimpleExc (H : SimpleGraph V) (D : Finset (Sym2 V)) : Prop :=
  ValidExc H D ∧ ∀ e ∈ D, ¬ e.IsDiag

open scoped Classical in
/-- The non-diagonal pairs in an exceptional-edge record. -/
noncomputable def simpleExcRecord (D : Finset (Sym2 V)) : Finset (Sym2 V) :=
  D.filter fun e => ¬ e.IsDiag

open scoped Classical in
/-- Removing diagonal pairs preserves the exceptional record and its reconstructed graph.
This converts the larger record type supplied by the peeling interface into the written one. -/
theorem ValidExc.simple_record {H : SimpleGraph V} {D : Finset (Sym2 V)}
    (hD : ValidExc H D) :
    ValidSimpleExc H (simpleExcRecord D) ∧
      fromEdgeSet (simpleExcRecord D : Set (Sym2 V)) =
        fromEdgeSet (D : Set (Sym2 V)) := by
  unfold simpleExcRecord
  refine ⟨⟨⟨?_, ?_⟩, fun e he => (mem_filter.1 he).2⟩, ?_⟩
  · intro e he
    exact hD.1 e (mem_filter.1 he).1
  · intro e he e' he'
    exact hD.2 e (mem_filter.1 he).1 e' (mem_filter.1 he').1
  · ext u v
    simp only [fromEdgeSet_adj, mem_coe, mem_filter, Sym2.mk_isDiag_iff]
    tauto

/-- Given the remaining pseudoforest and the exceptional-edge record, their union
reconstructs the removed graph (Lemma 5.36, the paper). -/
theorem eq_of_deleteEdges_eq_of_record {F₁ F₂ : SimpleGraph V} {D : Set (Sym2 V)}
    (h₁ : D ⊆ F₁.edgeSet) (h₂ : D ⊆ F₂.edgeSet)
    (h : F₁.deleteEdges D = F₂.deleteEdges D) : F₁ = F₂ := by
  have restore (F : SimpleGraph V) (hD : D ⊆ F.edgeSet) :
      F.deleteEdges D ⊔ fromEdgeSet D = F := by
    ext u v
    simp only [sup_adj, deleteEdges_adj, fromEdgeSet_adj]
    constructor
    · rintro (⟨huv, _⟩ | ⟨huv, _⟩)
      · exact huv
      · exact hD huv
    · intro huv
      by_cases he : s(u, v) ∈ D
      · exact Or.inr ⟨he, huv.ne⟩
      · exact Or.inl ⟨huv, he⟩
  rw [← restore F₁ h₁, ← restore F₂ h₂, h]

/-- One optional edge on `n` vertices has at most `2^n` choices.
The paper: Lemma 5.36. -/
theorem one_add_choose_two_le_two_pow (n : ℕ) : 1 + n.choose 2 ≤ 2 ^ n := by
  by_cases hn : 2 ≤ n
  · calc 1 + n.choose 2 = ∑ i ∈ ({0, 2} : Finset ℕ), n.choose i := by simp
         _ ≤ ∑ i ∈ range (n + 1), n.choose i := by
           apply sum_le_sum_of_subset
           intro i hi
           simp only [mem_insert, mem_singleton] at hi
           rcases hi with rfl | rfl <;> simp only [mem_range] <;> omega
         _ = 2 ^ n := Nat.sum_range_choose n
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> norm_num

open scoped Classical in
/-- The vertices `V_C` of a component obtained after cutting the recorded bridges. -/
noncomputable def componentVertices [Fintype V] (H : SimpleGraph V)
    (C : H.ConnectedComponent) : Finset V :=
  univ.filter fun v => H.connectedComponentMk v = C

open scoped Classical in
/-- The written component count: choose at most one non-diagonal edge in each component.
The paper: Lemma 5.36. -/
theorem card_validSimpleExc_le_prod [Fintype V] (H : SimpleGraph V) :
    ((univ : Finset (Finset (Sym2 V))).filter (ValidSimpleExc H)).card ≤
      ∏ C : H.ConnectedComponent, (1 + (componentVertices H C).card.choose 2) := by
  set κ := H.ConnectedComponent
  set P : κ → Sym2 V → Prop := fun k e => ∀ x ∈ e, H.connectedComponentMk x = k with hP
  set K : κ → Finset V := componentVertices H with hK
  set A : κ → Finset (Sym2 V) := fun k => (K k).offDiag.image Sym2.mk.uncurry with hA
  set φ : Finset (Sym2 V) → (κ → Finset (Sym2 V)) := fun D k => D.filter (P k) with hφ
  have hcomp : ∀ D, ValidSimpleExc H D → ∀ e ∈ D, ∀ x ∈ e,
      P (H.connectedComponentMk x) e := by
    intro D hD e he x hx y hy
    exact (ConnectedComponent.eq.2 (hD.1.1 e he x hx y hy)).symm
  have hinj : Set.InjOn φ ((univ : Finset (Finset (Sym2 V))).filter (ValidSimpleExc H)) := by
    intro D hD D' hD' heq
    have hD1 := (mem_filter.1 hD).2
    have hD'1 := (mem_filter.1 hD').2
    ext e
    constructor
    · intro he
      obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
        induction e using Sym2.ind with
        | h a b => exact ⟨a, Sym2.mem_mk_left a b⟩
      have h1 : e ∈ φ D (H.connectedComponentMk x) := mem_filter.2 ⟨he, hcomp D hD1 e he x hx⟩
      rw [heq] at h1
      exact (mem_filter.1 h1).1
    · intro he
      obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
        induction e using Sym2.ind with
        | h a b => exact ⟨a, Sym2.mem_mk_left a b⟩
      have h1 : e ∈ φ D' (H.connectedComponentMk x) := mem_filter.2 ⟨he, hcomp D' hD'1 e he x hx⟩
      rw [← heq] at h1
      exact (mem_filter.1 h1).1
  have hmaps : ∀ D ∈ (univ : Finset (Finset (Sym2 V))).filter (ValidSimpleExc H),
      φ D ∈ Fintype.piFinset fun k => (A k).powerset.filter (·.card ≤ 1) := by
    intro D hD
    have hD1 := (mem_filter.1 hD).2
    refine Fintype.mem_piFinset.2 fun k => mem_filter.2 ⟨mem_powerset.2 fun e he => ?_, ?_⟩
    · have hek := (mem_filter.1 he).2
      have hne := hD1.2 e (mem_filter.1 he).1
      induction e using Sym2.ind with
      | h a b =>
        exact mem_image.2 ⟨(a, b), mem_offDiag.2 ⟨mem_filter.2 ⟨mem_univ _,
          hek a (Sym2.mem_mk_left a b)⟩, mem_filter.2 ⟨mem_univ _,
          hek b (Sym2.mem_mk_right a b)⟩, hne⟩, rfl⟩
    · refine card_le_one.2 fun e he e' he' => ?_
      obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
        induction e using Sym2.ind with
        | h a b => exact ⟨a, Sym2.mem_mk_left a b⟩
      obtain ⟨y, hy⟩ : ∃ y, y ∈ e' := by
        induction e' using Sym2.ind with
        | h a b => exact ⟨a, Sym2.mem_mk_left a b⟩
      have hxk := (mem_filter.1 he).2 x hx
      have hyk := (mem_filter.1 he').2 y hy
      exact hD1.1.2 e (mem_filter.1 he).1 e' (mem_filter.1 he').1 x hx y hy
        (ConnectedComponent.eq.1 (hxk.trans hyk.symm))
  have hsmall : ∀ k, ((A k).powerset.filter (·.card ≤ 1)).card ≤
      1 + (K k).card.choose 2 := by
    intro k
    have hsub : (A k).powerset.filter (·.card ≤ 1) ⊆ insert ∅ ((A k).image singleton) := by
      intro s hs
      rw [mem_filter, mem_powerset] at hs
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs.2 with h0 | h1
      · rw [card_eq_zero] at h0
        exact h0 ▸ mem_insert_self _ _
      · obtain ⟨e, rfl⟩ := card_eq_one.1 h1
        exact mem_insert_of_mem (mem_image_of_mem _ (hs.1 (mem_singleton_self e)))
    calc ((A k).powerset.filter (·.card ≤ 1)).card ≤ (insert ∅ ((A k).image singleton)).card :=
          card_le_card hsub
      _ ≤ ((A k).image singleton).card + 1 := card_insert_le _ _
      _ ≤ (A k).card + 1 := Nat.add_le_add_right card_image_le 1
      _ = 1 + (K k).card.choose 2 := by rw [hA, Sym2.card_image_offDiag]; omega
  calc ((univ : Finset (Finset (Sym2 V))).filter (ValidSimpleExc H)).card
      ≤ (Fintype.piFinset fun k => (A k).powerset.filter (·.card ≤ 1)).card :=
        card_le_card_of_injOn φ hmaps hinj
    _ = ∏ k, ((A k).powerset.filter (·.card ≤ 1)).card := Fintype.card_piFinset _
    _ ≤ ∏ k, (1 + (K k).card.choose 2) := prod_le_prod fun k _ => hsmall k

open scoped Classical in
/-- The product of optional-edge choices costs at most `2^|V|`, since the components
partition the vertices (Lemma 5.36, the paper). -/
theorem prod_component_choices_le [Fintype V] (H : SimpleGraph V) :
    (∏ C : H.ConnectedComponent, (1 + (componentVertices H C).card.choose 2)) ≤
      2 ^ Fintype.card V := by
  have hsum : ∑ C, (componentVertices H C).card = Fintype.card V := by
    rw [← card_univ (α := V)]
    exact (card_eq_sum_card_fiberwise (f := H.connectedComponentMk) fun x _ => mem_univ _).symm
  calc (∏ C, (1 + (componentVertices H C).card.choose 2))
      ≤ ∏ C, 2 ^ (componentVertices H C).card :=
        prod_le_prod fun C _ => one_add_choose_two_le_two_pow _
    _ = 2 ^ Fintype.card V := by rw [prod_pow_eq_pow_sum, hsum]

open scoped Classical in
/-- A graph `T` on a finite type has at most `2^{|T|}` subgraphs. -/
theorem card_le_le_pow [Fintype V] (T : SimpleGraph V) (s : Finset (SimpleGraph V))
    (hs : ∀ H ∈ s, H ≤ T) : s.card ≤ 2 ^ T.edgeFinset.card := by
  calc s.card ≤ T.edgeFinset.powerset.card := by
        refine card_le_card_of_injOn (fun H => H.edgeFinset) (fun H hH => ?_) ?_
        · exact mem_powerset.2 (edgeFinset_mono (hs H hH))
        · intro H _ H' _ h
          exact edgeFinset_inj.1 h
    _ = 2 ^ T.edgeFinset.card := card_powerset _

open scoped Classical in
/-- The printed `4^k` inequality, for every possible bridge cut of the fixed tree.
The subgraphs left after the cuts encode the bridge subsets by complementation in `T`.
The paper: Lemma 5.36. -/
theorem bridge_component_choices_le_four_pow [Fintype V] (T H : SimpleGraph V)
    (hT : T.edgeFinset.card ≤ Fintype.card V) :
    2 ^ T.edgeFinset.card *
      (∏ C : H.ConnectedComponent, (1 + (componentVertices H C).card.choose 2)) ≤
        4 ^ Fintype.card V := by
  calc _ ≤ 2 ^ T.edgeFinset.card * 2 ^ Fintype.card V :=
          Nat.mul_le_mul_left _ (prod_component_choices_le H)
       _ ≤ 2 ^ Fintype.card V * 2 ^ Fintype.card V :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hT)
       _ = 4 ^ Fintype.card V := by rw [← mul_pow]; norm_num

end Exceptional

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
