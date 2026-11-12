/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.Ear
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Pseudoforests (Definition 4.48) and the sum over pseudoforests (eq. (4.69))

We formalize Definition 4.48 and the bound (4.69) of Lemma 4.49(1).

The paper defines `PF(V)` as the edge sets whose components have at most one cycle, and states
(citing [MR1154585]) that equivalently `(V, F)` admits an orientation in which every vertex has
out-degree at most `1`. Both directions of the equivalence are used in Lemma 4.49 only through
the orientation; we take the orientation characterization as the definition:
`MultipoleBKT.Peeling.IsPseudoforest F` asks for a partial map `φ : V → Option V` (the head of the
out-edge of each vertex) whose arcs are edges of `F`, every edge of `F` being the arc of exactly
one vertex.

* `MultipoleBKT.Peeling.sum_pseudoforests_le`: (4.69),
  `∑_{F ∈ PF(V)} ∏_{ij ∈ F} g_ij ≤ ∏_{i ∈ V} (1 + ∑_{j ≠ i} g_ij)` for nonnegative weights;
* `MultipoleBKT.Peeling.isPseudoforest_fromEdgeSet`: edges oriented from pairwise distinct tails
  form a pseudoforest;
* `MultipoleBKT.Peeling.IsPseudoforest.mono`: a subgraph of a pseudoforest is a pseudoforest.
-/

@[expose] public section

namespace MultipoleBKT

namespace Peeling

open Finset SimpleGraph

variable {V : Type*}

/-- `F ∈ PF(V)` (Definition 4.48): `(V, F)` admits an orientation in which
every vertex has out-degree at most `1`. The orientation is a partial map `φ` sending a vertex to
the head of its out-edge; every arc `i → φ(i)` is an edge of `F` and every edge of `F` is the arc of
exactly one vertex. -/
def IsPseudoforest (F : SimpleGraph V) : Prop :=
  ∃ φ : V → Option V, (∀ i j, φ i = some j → F.Adj i j) ∧
    ∀ e ∈ F.edgeSet, ∃! i, ∃ j, φ i = some j ∧ s(i, j) = e

open scoped Classical in
/-- The finite set `PF(V)` of pseudoforests on `V`. -/
noncomputable def pseudoforests [Fintype V] : Finset (SimpleGraph V) :=
  (univ : Finset (SimpleGraph V)).filter IsPseudoforest

theorem mem_pseudoforests [Fintype V] {F : SimpleGraph V} :
    F ∈ pseudoforests ↔ IsPseudoforest F := by
  classical
  simp [pseudoforests]

/-- A subgraph of a pseudoforest is a pseudoforest. -/
theorem IsPseudoforest.mono {F F' : SimpleGraph V} (h : IsPseudoforest F) (hle : F' ≤ F) :
    IsPseudoforest F' := by
  classical
  obtain ⟨φ, h1, h2⟩ := h
  refine ⟨fun i => if ∃ j, φ i = some j ∧ F'.Adj i j then φ i else none, ?_, ?_⟩
  · intro i j hij
    dsimp only at hij
    split_ifs at hij with hc
    obtain ⟨j', hj', hadj⟩ := hc
    rw [hj'] at hij
    exact Option.some_injective _ hij ▸ hadj
  · intro e he
    obtain ⟨i, ⟨j, hij, rfl⟩, huniq⟩ := h2 e (edgeSet_mono hle he)
    refine ⟨i, ⟨j, by dsimp only; rw [ite_eq_left ⟨j, hij, he⟩, hij], rfl⟩, ?_⟩
    rintro i' ⟨j', hj', heq⟩
    dsimp only at hj'
    split_ifs at hj' with hc
    exact huniq i' ⟨j', hj', heq⟩

/-- An orientation determines the pseudoforest: `F.Adj u v ↔ φ u = some v ∨ φ v = some u`. -/
theorem adj_iff_of_orientation {F : SimpleGraph V} {φ : V → Option V}
    (h1 : ∀ i j, φ i = some j → F.Adj i j)
    (h2 : ∀ e ∈ F.edgeSet, ∃! i, ∃ j, φ i = some j ∧ s(i, j) = e) {u v : V} :
    F.Adj u v ↔ φ u = some v ∨ φ v = some u := by
  constructor
  · intro huv
    obtain ⟨i, ⟨j, hij, he⟩, -⟩ := h2 s(u, v) huv
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [Or.inl hij, Or.inr hij]
  · rintro (h | h)
    exacts [h1 _ _ h, (h1 _ _ h).symm]

/-- Edges oriented from pairwise distinct tails form a pseudoforest. -/
theorem isPseudoforest_fromEdgeSet {T : List (V × V)} (h1 : (T.map Prod.fst).Nodup)
    (h2 : (T.map edge).Nodup) (h3 : ∀ t ∈ T, t.1 ≠ t.2) :
    IsPseudoforest (fromEdgeSet {e | e ∈ T.map edge}) := by
  classical
  let φ : V → Option V := fun v =>
    if h : ∃ t ∈ T, t.1 = v then some (Classical.choose h).2 else none
  have key : ∀ v j, φ v = some j ↔ (v, j) ∈ T := by
    intro v j
    simp only [φ]
    split_ifs with h
    · obtain ⟨hmem, hfst⟩ := Classical.choose_spec h
      rw [Option.some_inj]
      constructor
      · rintro rfl
        convert hmem using 1
        exact Prod.ext hfst.symm rfl
      · intro hvj
        have := List.inj_on_of_nodup_map h1 hmem hvj hfst
        rw [this]
    · simp only [false_iff]
      exact fun hvj => h ⟨_, hvj, rfl⟩
  refine ⟨φ, fun i j hij => ?_, fun e he => ?_⟩
  · rw [key] at hij
    rw [fromEdgeSet_adj]
    exact ⟨List.mem_map_of_mem hij, h3 _ hij⟩
  · rw [edgeSet_fromEdgeSet, Set.mem_sdiff] at he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he.1
    refine ⟨t.1, ⟨t.2, (key _ _).mpr ht, rfl⟩, ?_⟩
    rintro i ⟨j, hij, heq⟩
    rw [key] at hij
    exact congrArg Prod.fst (List.inj_on_of_nodup_map h2 hij ht heq)

/-- The product of `g` over the edges of an oriented pseudoforest is the product over its tails. -/
theorem prod_edgeFinset_eq_prod_orientation [Fintype V] {F : SimpleGraph V}
    [Fintype F.edgeSet] {φ : V → Option V} (h1 : ∀ i j, φ i = some j → F.Adj i j)
    (h2 : ∀ e ∈ F.edgeSet, ∃! i, ∃ j, φ i = some j ∧ s(i, j) = e) (g : Sym2 V → ℝ) :
    ∏ e ∈ F.edgeFinset, g e = ∏ i, (φ i).elim 1 fun j => g s(i, j) := by
  classical
  rw [← prod_filter_of_ne (p := fun i => (φ i).isSome) (fun i _ hi => ?_)]
  · symm
    refine prod_bij (fun i hi => s(i, (φ i).get (mem_filter.mp hi).2)) (fun i hi => ?_)
      (fun i hi i' hi' heq => ?_) (fun e he => ?_) (fun i hi => ?_)
    · rw [mem_edgeFinset]
      exact h1 _ _ (Option.some_get _).symm
    · have he : s(i, (φ i).get (mem_filter.mp hi).2) ∈ F.edgeSet :=
        h1 _ _ (Option.some_get _).symm
      obtain ⟨k, -, huniq⟩ := h2 _ he
      exact (huniq i ⟨_, (Option.some_get _).symm, rfl⟩).trans
        (huniq i' ⟨_, (Option.some_get _).symm, heq.symm⟩).symm
    · rw [mem_edgeFinset] at he
      obtain ⟨i, ⟨j, hij, rfl⟩, -⟩ := h2 e he
      refine ⟨i, mem_filter.mpr ⟨mem_univ _, by rw [hij]; rfl⟩, ?_⟩
      simp [hij]
    · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (mem_filter.mp hi).2
      simp [hj]
  · cases hφ : φ i with
    | none => simp [hφ] at hi
    | some j => simp

open scoped Classical in
/-- Equation (4.69) of Lemma 4.49: for nonnegative weights,
`∑_{F ∈ PF(V)} ∏_{ij ∈ F} g_ij ≤ ∏_{i ∈ V} (1 + ∑_{j ≠ i} g_ij)`. -/
theorem sum_pseudoforests_le [Fintype V] [DecidableEq V] (g : Sym2 V → ℝ)
    (hg : ∀ e, 0 ≤ g e) :
    ∑ F ∈ pseudoforests, ∏ e ∈ F.edgeFinset, g e ≤
      ∏ i, (1 + ∑ j ∈ univ.erase i, g s(i, j)) := by
  classical
  -- the weight of a choice `o` of out-neighbour of `i`
  set w : V → Option V → ℝ := fun i o => o.elim 1 fun j => g s(i, j)
  have hw0 : ∀ i o, 0 ≤ w i o := fun i o => by
    cases o
    · exact zero_le_one
    · exact hg _
  set t : V → Finset (Option V) := fun i => insertNone (univ.erase i)
  have hrhs : ∏ i, (1 + ∑ j ∈ univ.erase i, g s(i, j)) =
      ∑ φ ∈ Fintype.piFinset t, ∏ i, w i (φ i) := by
    rw [← prod_univ_sum]
    refine prod_congr rfl fun i _ => ?_
    simp [t, w, sum_insertNone]
  rw [hrhs]
  -- choose an orientation of each pseudoforest
  have hor : ∀ F : SimpleGraph V, IsPseudoforest F → ∃ φ : V → Option V,
      (∀ i j, φ i = some j → F.Adj i j) ∧
        ∀ e ∈ F.edgeSet, ∃! i, ∃ j, φ i = some j ∧ s(i, j) = e := fun F h => h
  let ori : SimpleGraph V → V → Option V := fun F =>
    if h : IsPseudoforest F then Classical.choose (hor F h) else fun _ => none
  have hori : ∀ F ∈ (pseudoforests : Finset (SimpleGraph V)),
      (∀ i j, ori F i = some j → F.Adj i j) ∧
        ∀ e ∈ F.edgeSet, ∃! i, ∃ j, ori F i = some j ∧ s(i, j) = e := by
    intro F hF
    have h := mem_pseudoforests.mp hF
    simp only [ori, dite_eq_left h]
    exact Classical.choose_spec (hor F h)
  have hinj : Set.InjOn ori (pseudoforests : Finset (SimpleGraph V)) := by
    intro F hF F' hF' heq
    ext u v
    rw [adj_iff_of_orientation (hori F hF).1 (hori F hF).2,
      adj_iff_of_orientation (hori F' hF').1 (hori F' hF').2, heq]
  calc ∑ F ∈ pseudoforests, ∏ e ∈ F.edgeFinset, g e
      = ∑ F ∈ pseudoforests, ∏ i, w i (ori F i) := by
        refine sum_congr rfl fun F hF => ?_
        exact prod_edgeFinset_eq_prod_orientation (hori F hF).1 (hori F hF).2 g
    _ = ∑ φ ∈ (pseudoforests : Finset (SimpleGraph V)).image ori, ∏ i, w i (φ i) :=
        (sum_image (f := fun φ => ∏ i, w i (φ i)) hinj).symm
    _ ≤ ∑ φ ∈ Fintype.piFinset t, ∏ i, w i (φ i) := by
        refine sum_le_sum_of_subset_of_nonneg (fun φ hφ => ?_)
          (fun φ _ _ => prod_nonneg fun i _ => hw0 i (φ i))
        obtain ⟨F, hF, rfl⟩ := mem_image.mp hφ
        rw [Fintype.mem_piFinset]
        intro i
        cases hFi : ori F i with
        | none => simp [t]
        | some j =>
          simp only [t, mem_insertNone, Option.mem_def, Option.some.injEq, mem_erase, mem_univ,
            and_true]
          rintro a rfl
          exact ((hori F hF).1 i _ hFi).ne.symm

end Peeling

end MultipoleBKT

end
