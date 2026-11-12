/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Parity.Eulerian
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Lex

/-!
# 2-edge-connected graphs relative to a partition (Definitions 4.36 and 4.38)

Definition 4.36 is
`MultipoleBKT.Parity.IsRelTwoEdgeConnected` and `MultipoleBKT.Parity.IsRelMinTwoEdgeConnected`. We formalize Definition 4.38 and the facts
about these notions that the peeling uses.

* `MultipoleBKT.Peeling.IsPeeledSkeleton X E E'`: `E'` is an inclusion-minimal subset of `E`
  whose multigraph quotient is connected and bridgeless (Definition 4.38: `Peeled_X(E) = E'`).
  `peeledSkeleton` implements the specified choice: order each unordered edge by its
  smaller endpoint followed by its larger endpoint, sort the edge lists, and take their
  lexicographic minimum. `peeledSkeleton_eq_iff` proves the characterization uniquely.
  The subsequent graph arguments remain valid for every admissible skeleton.
* `MultipoleBKT.Peeling.TwoEdgeConnOn b E`, `MultipoleBKT.Peeling.MinTwoEdgeConnOn b E`: the same
  notions for a generic block map `b` (connectivity of `E ∪ (same-block edges)`).

The main facts:

* `MultipoleBKT.Peeling.exists_isPeeledSkeleton`: a skeleton exists when `E` is 2-edge-connected
  relative to `X` (the paper's selection is well defined);
* `MultipoleBKT.Peeling.IsPeeledSkeleton.isRelMinTwoEdgeConnected`: a skeleton is minimally
  2-edge-connected relative to `X`. The paper uses this when it applies Definition 4.43 to
  `Peeled_X(E)` (Definition 4.44) without stating it;
* `MultipoleBKT.Peeling.isRelMinTwoEdgeConnected_iff_minimal`: minimal 2-edge-connectivity (no
  single edge can be deleted) is inclusion-minimality;
* `MultipoleBKT.Peeling.isRelTwoEdgeConnected_iff_on`,
  `MultipoleBKT.Peeling.isRelMinTwoEdgeConnected_iff_on`: the notions for the block map `[·]^X`.
-/

@[expose] public section

namespace MultipoleBKT

namespace Peeling

open Finset SimpleGraph

section Generic

variable {V β : Type*} (b : V → β)

/-- `E` is 2-edge-connected relative to the blocks of `b`: `(V, E ∪ same-block edges)` is
connected and stays connected when any one edge of `E` is deleted. -/
def TwoEdgeConnOn (E : SimpleGraph V) : Prop :=
  (E ⊔ sameBlockGraph b).Connected ∧
    ∀ e ∈ E.edgeSet, (E.deleteEdges {e} ⊔ sameBlockGraph b).Connected

/-- `E` is minimally 2-edge-connected relative to the blocks of `b`. -/
def MinTwoEdgeConnOn (E : SimpleGraph V) : Prop :=
  TwoEdgeConnOn b E ∧ ∀ e ∈ E.edgeSet, ¬ TwoEdgeConnOn b (E.deleteEdges {e})

variable {b}

/-- 2-edge-connectivity relative to the blocks is preserved by adding edges. -/
theorem TwoEdgeConnOn.mono {E E' : SimpleGraph V} (h : TwoEdgeConnOn b E) (hle : E ≤ E') :
    TwoEdgeConnOn b E' := by
  refine ⟨h.1.mono (sup_le_sup_right hle _), fun e he => ?_⟩
  by_cases heE : e ∈ E.edgeSet
  · exact (h.2 e heE).mono (sup_le_sup_right (deleteEdges_mono hle) _)
  · refine h.1.mono (sup_le_sup_right ?_ _)
    intro u v huv
    rw [deleteEdges_adj]
    exact ⟨hle huv, fun hmem => heE (by rw [Set.mem_singleton_iff] at hmem; exact hmem ▸ huv)⟩

/-- No single edge can be deleted iff no proper subgraph is 2-edge-connected. -/
theorem minTwoEdgeConnOn_iff_minimal {E : SimpleGraph V} :
    MinTwoEdgeConnOn b E ↔ TwoEdgeConnOn b E ∧ ∀ E' ≤ E, TwoEdgeConnOn b E' → E' = E := by
  constructor
  · rintro ⟨h2, hmin⟩
    refine ⟨h2, fun E' hle h2' => ?_⟩
    by_contra hne
    obtain ⟨e, heE, heE'⟩ : ∃ e ∈ E.edgeSet, e ∉ E'.edgeSet := by
      by_contra hall
      push Not at hall
      exact hne (le_antisymm hle (edgeSet_subset_edgeSet.mp hall))
    refine hmin e heE (h2'.mono fun u v huv => ?_)
    rw [deleteEdges_adj]
    exact ⟨hle huv, fun hmem => heE' (by rw [Set.mem_singleton_iff] at hmem; exact hmem ▸ huv)⟩
  · rintro ⟨h2, hmin⟩
    refine ⟨h2, fun e he h2' => ?_⟩
    have := hmin _ (deleteEdges_le _) h2'
    have he' : e ∈ (E.deleteEdges {e}).edgeSet := by rw [this]; exact he
    rw [edgeSet_deleteEdges] at he'
    exact he'.2 rfl

end Generic

section Subpartition

variable (X : Finset (Finset ℕ))

/-- `E'` is an admissible value of `Peeled_X(E)` (Definition 4.38): an
inclusion-minimal subset of `E` whose multigraph quotient by `X` is connected and has no bridge,
i.e. which is 2-edge-connected relative to `X` (`MultipoleBKT.Parity.IsRelTwoEdgeConnected`,
Definition 4.36(1)). -/
def IsPeeledSkeleton (E E' : SimpleGraph (X.biUnion id)) : Prop :=
  E' ≤ E ∧ Parity.IsRelTwoEdgeConnected X E' ∧
    ∀ E'' ≤ E', Parity.IsRelTwoEdgeConnected X E'' → E'' = E'

variable {X}

theorem forall_edgeSet_iff {V : Type*} {E : SimpleGraph V} {P : Sym2 V → Prop} :
    (∀ e ∈ E.edgeSet, P e) ↔ ∀ u v, E.Adj u v → P s(u, v) := by
  refine ⟨fun h u v huv => h _ huv, fun h e he => ?_⟩
  induction e using Sym2.ind with
  | h u v => exact h u v he

/-- Definition 4.36(1) for the block map `[·]^X`. -/
theorem isRelTwoEdgeConnected_iff_on (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)} :
    Parity.IsRelTwoEdgeConnected X E ↔
      E ≤ interEdges X ∧ X.card ≠ 1 ∧ TwoEdgeConnOn (blockOf hX) E := by
  simp only [Parity.IsRelTwoEdgeConnected, TwoEdgeConnOn, forall_edgeSet_iff,
    isRelConnected_iff, isRelConnected₀_iff hX, ← intraEdges_eq hX]
  constructor
  · rintro ⟨⟨⟨hle, hc⟩, h1⟩, h2⟩
    exact ⟨hle, h1, hc, fun u v huv => (h2 u v huv).1.2⟩
  · rintro ⟨hle, h1, hc, h2⟩
    exact ⟨⟨⟨hle, hc⟩, h1⟩, fun u v huv => ⟨⟨(deleteEdges_le _).trans hle, h2 u v huv⟩, h1⟩⟩

/-- Definition 4.36(2) for the block map `[·]^X`. -/
theorem isRelMinTwoEdgeConnected_iff_on (hX : IsSubpartition X)
    {E : SimpleGraph (X.biUnion id)} :
    Parity.IsRelMinTwoEdgeConnected X E ↔
      E ≤ interEdges X ∧ X.card ≠ 1 ∧ MinTwoEdgeConnOn (blockOf hX) E := by
  simp only [Parity.IsRelMinTwoEdgeConnected, MinTwoEdgeConnOn, forall_edgeSet_iff,
    isRelTwoEdgeConnected_iff_on hX]
  constructor
  · rintro ⟨⟨hle, h1, h2⟩, hmin⟩
    exact ⟨hle, h1, h2, fun u v huv h2' => hmin u v huv ⟨(deleteEdges_le _).trans hle, h1, h2'⟩⟩
  · rintro ⟨hle, h1, h2, hmin⟩
    exact ⟨⟨hle, h1, h2⟩, fun u v huv ⟨_, _, h2'⟩ => hmin u v huv h2'⟩

/-- Minimal 2-edge-connectivity relative to `X` (no single edge can be deleted) is
inclusion-minimality. -/
theorem isRelMinTwoEdgeConnected_iff_minimal (hX : IsSubpartition X)
    {E : SimpleGraph (X.biUnion id)} :
    Parity.IsRelMinTwoEdgeConnected X E ↔
      Parity.IsRelTwoEdgeConnected X E ∧
        ∀ E' ≤ E, Parity.IsRelTwoEdgeConnected X E' → E' = E := by
  constructor
  · intro h
    have hmin' := (isRelMinTwoEdgeConnected_iff_on hX).mp h
    refine ⟨h.1, fun E' hle h2' => ?_⟩
    rw [isRelTwoEdgeConnected_iff_on hX] at h2'
    exact (minTwoEdgeConnOn_iff_minimal.mp hmin'.2.2).2 E' hle h2'.2.2
  · rintro ⟨h2, hmin⟩
    refine ⟨h2, fun u v huv h2' => ?_⟩
    have := hmin _ (deleteEdges_le _) h2'
    have he' : s(u, v) ∈ (E.deleteEdges {s(u, v)}).edgeSet := by rw [this]; exact huv
    rw [edgeSet_deleteEdges] at he'
    exact he'.2 rfl

/-- A skeleton `Peeled_X(E)` is minimally 2-edge-connected relative to `X`. -/
theorem IsPeeledSkeleton.isRelMinTwoEdgeConnected (hX : IsSubpartition X)
    {E E' : SimpleGraph (X.biUnion id)} (h : IsPeeledSkeleton X E E') :
    Parity.IsRelMinTwoEdgeConnected X E' :=
  (isRelMinTwoEdgeConnected_iff_minimal hX).mpr ⟨h.2.1, h.2.2⟩

/-- `Peeled_X(E)` is well defined: when `E` is 2-edge-connected relative to `X`, an
inclusion-minimal 2-edge-connected subset exists. -/
theorem exists_isPeeledSkeleton {E : SimpleGraph (X.biUnion id)}
    (h : Parity.IsRelTwoEdgeConnected X E) : ∃ E', IsPeeledSkeleton X E E' := by
  obtain ⟨E', ⟨hle, h2⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {E' : SimpleGraph (X.biUnion id) | E' ≤ E ∧ Parity.IsRelTwoEdgeConnected X E'}
    ⟨E, le_rfl, h⟩
  refine ⟨E', hle, h2, fun E'' hE'' h2'' => ?_⟩
  by_contra hne
  exact hmin E'' ⟨hE''.trans hle, h2''⟩ (lt_of_le_of_ne hE'' hne)

/-! ### The deterministic lexicographic selection -/

/-- An unordered edge is ordered by its smaller endpoint, then its larger endpoint. -/
def skeletonEdgeKey (e : Sym2 (X.biUnion id)) : Lex (X.biUnion id × X.biUnion id) :=
  toLex (e.inf, e.sup)

theorem skeletonEdgeKey_injective : Function.Injective (skeletonEdgeKey (X := X)) := by
  intro e f h
  apply Sym2.inf_eq_inf_and_sup_eq_sup.mp
  exact Prod.ext_iff.mp (congrArg ofLex h)

open scoped Classical in
/-- The increasing list of edges, with the endpoint order used in
Definition 4.38. -/
noncomputable def skeletonEdgeList (E : SimpleGraph (X.biUnion id)) :
    List (Lex (X.biUnion id × X.biUnion id)) :=
  (E.edgeFinset.image skeletonEdgeKey).sort

theorem skeletonEdgeList_injective :
    Function.Injective (skeletonEdgeList (X := X)) := by
  classical
  intro E F h
  apply edgeFinset_inj.mp
  apply Finset.image_injective skeletonEdgeKey_injective
  have hh := congrArg List.toFinset h
  simpa only [skeletonEdgeList, sort_toFinset] using hh

/-- Lexicographic order of increasing edge lists. This is separate from graph inclusion. -/
@[instance_reducible] noncomputable def skeletonLexOrder (X : Finset (Finset ℕ)) :
    LinearOrder (SimpleGraph (X.biUnion id)) :=
  LinearOrder.lift' skeletonEdgeList skeletonEdgeList_injective

open scoped Classical in
/-- The first inclusion-minimal bridgeless connected skeleton in lexicographic order.
Its domain is precisely the two-edge-connected graphs, so no default value is required.
This is `Peeled_X(E)` in Definition 4.38. -/
noncomputable def peeledSkeleton (E : SimpleGraph (X.biUnion id))
    (hE : Parity.IsRelTwoEdgeConnected X E) : SimpleGraph (X.biUnion id) :=
  letI := skeletonLexOrder X
  ((univ : Finset (SimpleGraph (X.biUnion id))).filter (IsPeeledSkeleton X E)).min'
    (by obtain ⟨F, hF⟩ := exists_isPeeledSkeleton hE; exact ⟨F, mem_filter.mpr ⟨mem_univ _, hF⟩⟩)

/-- The selected graph is an admissible skeleton. -/
theorem peeledSkeleton_spec (E : SimpleGraph (X.biUnion id))
    (hE : Parity.IsRelTwoEdgeConnected X E) :
    IsPeeledSkeleton X E (peeledSkeleton E hE) := by
  classical
  let := skeletonLexOrder X
  exact (mem_filter.mp (min'_mem _ _)).2

/-- The selected skeleton precedes every admissible skeleton in lexicographic order. -/
theorem peeledSkeleton_lex_le (E : SimpleGraph (X.biUnion id))
    (hE : Parity.IsRelTwoEdgeConnected X E) {F : SimpleGraph (X.biUnion id)}
    (hF : IsPeeledSkeleton X E F) :
    skeletonEdgeList (peeledSkeleton E hE) ≤ skeletonEdgeList F := by
  classical
  let := skeletonLexOrder X
  exact min'_le _ _ (mem_filter.mpr ⟨mem_univ _, hF⟩)

/-- Admissibility and the lexicographic rule characterize the selection uniquely. -/
theorem peeledSkeleton_eq_iff (E : SimpleGraph (X.biUnion id))
    (hE : Parity.IsRelTwoEdgeConnected X E) (F : SimpleGraph (X.biUnion id)) :
    F = peeledSkeleton E hE ↔ IsPeeledSkeleton X E F ∧
      ∀ H, IsPeeledSkeleton X E H → skeletonEdgeList F ≤ skeletonEdgeList H := by
  constructor
  · rintro rfl
    exact ⟨peeledSkeleton_spec E hE, fun _ h => peeledSkeleton_lex_le E hE h⟩
  · rintro ⟨hF, hmin⟩
    apply skeletonEdgeList_injective
    exact le_antisymm (hmin _ (peeledSkeleton_spec E hE)) (peeledSkeleton_lex_le E hE hF)

end Subpartition

end Peeling

end MultipoleBKT

end
