/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.CoreForest.Bridges

/-!
# The 2-core relative to a partition and the pendant trees (Definitions 5.25–5.26)

The paper: Definition 5.25 and the
core decomposition relative to a partition (Definition 5.26). The claims packaged in
these definitions are stated without proof in the paper; they are proved here.

As in `MultipoleBKT.UpperBound.CoreForest.Bridges`, the vertices carry a block map `b : V → β`
(for a subpartition `X`: the blocks `[·]^X`) and `E` is an edge set. The degree of a block `S`
inside a family `F` of blocks is the number of oriented edges `(x, y)` of `E` with `x ∈ S` and
`y ∈ V_F`; for `F ∋ S` and `E ⊆ ℰ^inter` it is the degree of `S` in the subgraph induced by `V_F`
(Definition 4.10 (7), restricted to `V_F`).

* `degIn b E F S`, `IsTwoClosed b E F`: every block of `F` has degree at least `2` inside `F`;
* `twoCore b E`: the parts `X'` of the 2-core `C_2(G, X)`, the union of all `2`-closed families.
  It is `2`-closed (`isTwoClosed_twoCore`) and contains every `2`-closed family
  (`subset_twoCore`): it is the unique maximal one. The paper's algorithm ("repeatedly delete
  every block whose current degree is `< 2`") computes it, in any order:
  `twoCore_subset_erase` (a deletion never removes a core block) and `twoCore_eq_of_isTwoClosed`
  (the deletion stops exactly at the core).
* `coreEdges b E`: the edges of `C_2(G, X)` (both ends in core blocks); `pendantEdges b E`: the
  other edges, i.e. the edges of the pendant trees.
* `eq_of_reachable_pendant`: two core blocks joined by pendant edges are equal: each pendant tree
  is attached to the core at a single block (its attachment multipole).
* `exists_reachable_pendant_of_reachable`, `reachable_core_of_reachable`: for `G = E ∪ ℰ^intra`
  connected and a nonempty core, every block is joined by pendant edges to a core block
  (`exists_attachment`), and the 2-core is connected relative to its blocks
  (`reachable_coreEdges`), as the paper states (Section 5.6, "empty or connected").
-/

@[expose] public section

namespace MultipoleBKT

namespace CoreForest

open Finset SimpleGraph

/-- An inner vertex of a path has two distinct neighbours on the path. -/
theorem exists_adj_adj_of_mem_support {β : Type*} {G : SimpleGraph β} {u v : β}
    {p : G.Walk u v} (hp : p.IsPath) {s : β} (hs : s ∈ p.support) (hsu : s ≠ u) (hsv : s ≠ v) :
    ∃ a c, a ≠ c ∧ G.Adj s a ∧ G.Adj s c ∧ a ∈ p.support ∧ c ∈ p.support := by
  induction p with
  | nil =>
    rw [Walk.support_nil, List.mem_singleton] at hs
    exact absurd hs hsu
  | @cons u w v h q ih =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons, List.mem_cons] at hs
    have hsq : s ∈ q.support := hs.resolve_left hsu
    by_cases hsw : s = w
    · subst hsw
      have hnil : ¬ q.Nil := fun hn => hsv hn.eq
      refine ⟨u, q.snd, fun he => hp.2 (he ▸ q.getVert_mem_support 1), h.symm,
        q.adj_snd hnil, ?_, ?_⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (q.getVert_mem_support 1)
    · obtain ⟨a, c, hac, ha, hc, has, hcs⟩ := ih hp.1 hsq hsw hsv
      exact ⟨a, c, hac, ha, hc, List.mem_cons_of_mem _ has, List.mem_cons_of_mem _ hcs⟩

section Core

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] (b : V → β) (E : SimpleGraph V)

open scoped Classical in
/-- The degree of the block `S` inside the family `F`: the number of oriented edges `(x, y)` of `E`
with `x ∈ S` and `y` in a block of `F`. -/
noncomputable def degIn (F : Finset β) (S : β) : ℕ :=
  (univ.filter fun p : V × V => b p.1 = S ∧ b p.2 ∈ F ∧ E.Adj p.1 p.2).card

/-- Every block of `F` has degree at least `2` inside `F`. -/
def IsTwoClosed (F : Finset β) : Prop := ∀ S ∈ F, 2 ≤ degIn b E F S

open scoped Classical in
/-- The blocks `X'` of the 2-core `C_2(G, X)` (Definition 5.26 (1)): the
largest family of blocks in which every block has degree at least `2`, the union of all such
families. -/
noncomputable def twoCore : Finset β :=
  ((univ : Finset β).powerset.filter (IsTwoClosed b E)).sup id

/-- The edges of the 2-core `C_2(G, X)`: the edges of `E` with both ends in core blocks. -/
def coreEdges : SimpleGraph V :=
  E ⊓ SimpleGraph.fromRel fun u v => b u ∈ twoCore b E ∧ b v ∈ twoCore b E

/-- The edges of the pendant trees: the edges of `E` with an end outside the core. -/
def pendantEdges : SimpleGraph V := E \ coreEdges b E

variable {b E}

omit [Fintype β] in
theorem degIn_mono {F F' : Finset β} (h : F ⊆ F') (S : β) : degIn b E F S ≤ degIn b E F' S := by
  classical
  unfold degIn
  refine Finset.card_le_card fun p hp => ?_
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, h hp.2.2.1, hp.2.2.2⟩

omit [Fintype β] in
theorem IsTwoClosed.union {F F' : Finset β} (h : IsTwoClosed b E F) (h' : IsTwoClosed b E F') :
    IsTwoClosed b E (F ∪ F') := by
  intro S hS
  rcases Finset.mem_union.1 hS with hS | hS
  · exact (h S hS).trans (degIn_mono Finset.subset_union_left S)
  · exact (h' S hS).trans (degIn_mono Finset.subset_union_right S)

theorem isTwoClosed_twoCore : IsTwoClosed b E (twoCore b E) := by
  classical
  unfold twoCore
  refine Finset.sup_induction (p := IsTwoClosed b E) (fun S hS => absurd hS (Finset.notMem_empty S))
    (fun F hF F' hF' => hF.union hF') fun F hF => ?_
  exact (Finset.mem_filter.1 hF).2

theorem subset_twoCore {F : Finset β} (h : IsTwoClosed b E F) : F ⊆ twoCore b E := by
  classical
  unfold twoCore
  exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (subset_univ F), h⟩)

/-- One step of the peeling algorithm never removes a core block: if `F` contains the core and
`S ∈ F` has degree `< 2` inside `F`, the core is contained in `F ∖ {S}`. -/
theorem twoCore_subset_erase {F : Finset β} (hF : twoCore b E ⊆ F) {S : β} (hdeg : degIn b E F S < 2) :
    twoCore b E ⊆ F.erase S := by
  intro T hT
  refine Finset.mem_erase.2 ⟨fun hTS => ?_, hF hT⟩
  subst hTS
  exact absurd ((isTwoClosed_twoCore T hT).trans (degIn_mono hF T)) (not_le.2 hdeg)

/-- The peeling algorithm stops exactly at the core: a `2`-closed family containing the core is the
core. -/
theorem twoCore_eq_of_isTwoClosed {F : Finset β} (hF : twoCore b E ⊆ F) (h : IsTwoClosed b E F) :
    twoCore b E = F :=
  Finset.Subset.antisymm hF (subset_twoCore h)

theorem coreEdges_adj {u v : V} :
    (coreEdges b E).Adj u v ↔ E.Adj u v ∧ b u ∈ twoCore b E ∧ b v ∈ twoCore b E := by
  rw [coreEdges, inf_adj, fromRel_adj]
  constructor
  · rintro ⟨h, -, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, h'.2, h'.1⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, h.ne, Or.inl h'⟩

theorem pendantEdges_adj {u v : V} :
    (pendantEdges b E).Adj u v ↔ E.Adj u v ∧ (b u ∉ twoCore b E ∨ b v ∉ twoCore b E) := by
  rw [pendantEdges, sdiff_adj, coreEdges_adj]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨h, ?_⟩
    by_contra hc
    push Not at hc
    exact h' ⟨h, hc⟩
  · rintro ⟨h, h'⟩
    refine ⟨h, fun hc => ?_⟩
    rcases h' with h' | h'
    · exact h' hc.2.1
    · exact h' hc.2.2

theorem coreEdges_le : coreEdges b E ≤ E := fun _ _ h => (coreEdges_adj.1 h).1

theorem pendantEdges_le : pendantEdges b E ≤ E := fun _ _ h => (pendantEdges_adj.1 h).1

theorem coreEdges_sup_pendantEdges : coreEdges b E ⊔ pendantEdges b E = E := by
  rw [pendantEdges, sup_sdiff_self_right, sup_eq_right.2 coreEdges_le]

/-- **The pendant trees are attached at a single block**: two core blocks joined by a walk of
pendant edges are equal. (Otherwise the blocks along a path joining them, together with the core,
would form a larger `2`-closed family.) -/
theorem eq_of_reachable_pendant {A A' : β} (hA : A ∈ twoCore b E) (hA' : A' ∈ twoCore b E)
    (h : (blockQuotient b (pendantEdges b E)).Reachable A A') : A = A' := by
  classical
  by_contra hne
  obtain ⟨q, hq⟩ := h.exists_isPath
  set F := twoCore b E ∪ q.support.toFinset with hF
  have hclosed : IsTwoClosed b E F := by
    intro S hS
    by_cases hSc : S ∈ twoCore b E
    · exact (isTwoClosed_twoCore S hSc).trans (degIn_mono Finset.subset_union_left S)
    · have hSq : S ∈ q.support := by
        rcases Finset.mem_union.1 hS with h | h
        · exact absurd h hSc
        · exact List.mem_toFinset.1 h
      have hSA : S ≠ A := fun h => hSc (h ▸ hA)
      have hSA' : S ≠ A' := fun h => hSc (h ▸ hA')
      obtain ⟨a, c, hac, ha, hc, haq, hcq⟩ := exists_adj_adj_of_mem_support hq hSq hSA hSA'
      obtain ⟨-, x, y, hx, hy, hxy⟩ := blockQuotient_adj.1 ha
      obtain ⟨-, x', y', hx', hy', hxy'⟩ := blockQuotient_adj.1 hc
      unfold degIn
      rw [Nat.succ_le_iff, Finset.one_lt_card]
      refine ⟨(x, y), ?_, (x', y'), ?_, fun he => hac ?_⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, Finset.mem_union_right _
          (List.mem_toFinset.2 (hy ▸ haq)), pendantEdges_le hxy⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hx', Finset.mem_union_right _
          (List.mem_toFinset.2 (hy' ▸ hcq)), pendantEdges_le hxy'⟩
      · rw [← hy, ← hy']
        exact congrArg (fun p : V × V => b p.2) he
  have hsub := subset_twoCore hclosed
  have hnil : ¬ q.Nil := fun hn => hne hn.eq
  obtain ⟨-, x, y, hx, hy, hxy⟩ := blockQuotient_adj.1 (q.adj_snd hnil)
  have hsnd : q.snd ∈ twoCore b E :=
    hsub (Finset.mem_union_right _ (List.mem_toFinset.2 (q.getVert_mem_support 1)))
  rcases (pendantEdges_adj.1 hxy).2 with h | h
  · exact h (hx ▸ hA)
  · exact h (hy ▸ hsnd)

/-- A walk of the quotient of `E` ending at a core block `A`: if it starts at a core block `S`,
the core joins `S` to `A`; otherwise pendant edges join `S` to a core block `A₁` which the core
joins to `A`. -/
theorem reachable_core_of_walk {A S : β} (hA : A ∈ twoCore b E) (p : (blockQuotient b E).Walk S A) :
    (S ∈ twoCore b E → (blockQuotient b (coreEdges b E)).Reachable S A) ∧
      (S ∉ twoCore b E → ∃ A₁ ∈ twoCore b E,
        (blockQuotient b (pendantEdges b E)).Reachable S A₁ ∧
          (blockQuotient b (coreEdges b E)).Reachable A₁ A) := by
  induction p with
  | nil => exact ⟨fun _ => Reachable.refl _, fun h => absurd hA h⟩
  | @cons S S' A hSS' q ih =>
    obtain ⟨hne, x, y, hx, hy, hxy⟩ := blockQuotient_adj.1 hSS'
    have ih := ih hA
    by_cases hS' : S' ∈ twoCore b E
    · have hcore' := ih.1 hS'
      constructor
      · intro hS
        have hc : (coreEdges b E).Adj x y := coreEdges_adj.2 ⟨hxy, hx ▸ hS, hy ▸ hS'⟩
        exact (blockQuotient_adj.2 ⟨hne, x, y, hx, hy, hc⟩).reachable.trans hcore'
      · intro hS
        have hp : (pendantEdges b E).Adj x y := pendantEdges_adj.2 ⟨hxy, Or.inl (hx ▸ hS)⟩
        exact ⟨S', hS', (blockQuotient_adj.2 ⟨hne, x, y, hx, hy, hp⟩).reachable, hcore'⟩
    · obtain ⟨A₁, hA₁, hS'A₁, hA₁A⟩ := ih.2 hS'
      have hp : (pendantEdges b E).Adj x y := pendantEdges_adj.2 ⟨hxy, Or.inr (hy ▸ hS')⟩
      have hSA₁ : (blockQuotient b (pendantEdges b E)).Reachable S A₁ :=
        (blockQuotient_adj.2 ⟨hne, x, y, hx, hy, hp⟩).reachable.trans hS'A₁
      constructor
      · intro hS
        rw [eq_of_reachable_pendant hS hA₁ hSA₁]
        exact hA₁A
      · exact fun _ => ⟨A₁, hA₁, hSA₁, hA₁A⟩

/-- **Every block is attached to the core** when `G = E ∪ ℰ^intra` is connected and the core is
nonempty: pendant edges join it to a core block (unique by `eq_of_reachable_pendant`). -/
theorem exists_attachment (hG : (E ⊔ sameBlockGraph b).Connected) {A : β}
    (hA : A ∈ twoCore b E) (hAb : ∃ y, b y = A) (x : V) :
    ∃ A₁ ∈ twoCore b E, (blockQuotient b (pendantEdges b E)).Reachable (b x) A₁ := by
  obtain ⟨y, rfl⟩ := hAb
  obtain ⟨p⟩ := reachable_blockQuotient_of_reachable (hG.preconnected x y)
  by_cases hx : b x ∈ twoCore b E
  · exact ⟨b x, hx, Reachable.refl _⟩
  · obtain ⟨A₁, hA₁, h, -⟩ := (reachable_core_of_walk hA p).2 hx
    exact ⟨A₁, hA₁, h⟩

/-- **The 2-core is connected relative to its blocks** when `G = E ∪ ℰ^intra` is connected
(Definition 5.26 (1)). -/
theorem reachable_coreEdges (hG : (E ⊔ sameBlockGraph b).Connected) {x y : V}
    (hx : b x ∈ twoCore b E) (hy : b y ∈ twoCore b E) :
    (blockQuotient b (coreEdges b E)).Reachable (b x) (b y) := by
  obtain ⟨p⟩ := reachable_blockQuotient_of_reachable (hG.preconnected x y)
  exact (reachable_core_of_walk hy p).1 hx

end Core

end CoreForest

end MultipoleBKT

end
