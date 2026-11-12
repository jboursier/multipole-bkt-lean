/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Multipole.EdgeSets
public import MultipoleBKT.Frozen.MultipoleLinked

/-!
# Graphs on label sets as edge sets

The frozen activities (`dipoleActivity`, `multipolePartitionFunction`, `hierarchicalModel`,
`multipoleActivity`) sum over simple graphs on the subtype of a label set `U ⊆ ℕ` and multiply
pair factors `∏_{i, j} [i < j ∧ i ~ j] f(i, j)`. This file translates them into edge sets
`E ⊆ pairsOn U` (`MultipoleBKT.Multipole.EdgeSets`):

* `edgesOf G`, `graphOf U E`: the bijection between graphs on `U` and edge sets on `U`
  (`graphOf_edgesOf`, `edgesOf_graphOf`, `sum_graphs_eq_sum_edgeSets`);
* `prod_prod_ite_adj`: the pair product of a graph is the product over its edge set;
* `connected_iff_connOn`: connectivity of a graph on a type embedded in `ℕ` is `ConnOn` of its
  edge set, applied to the graphs of the frozen definitions (`connected_iff_connOn_edgesOf`,
  `connected_fromRel_iff`, `connected_induce_iff`, `connected_sup_iff`);
* `multipoleLinked_comm`: the multipole relation is symmetric, and `linkedPairs` is its edge set;
* `forall_adj_iff_edgesOf_subset_interPairs`: a graph has only inter-block edges iff its edge set
  is in `ℰ^inter(X)`; `card_le_one_of_connOn_intraPairs`: intra-block edges alone do not connect
  two blocks.
-/

@[expose] public section

namespace MultipoleBKT

open Finset

namespace Multipole

open SetPartition

/-! ### Graphs and edge sets -/

section GraphEdges

variable {U : Finset ℕ}

open scoped Classical in
/-- The edge set of a graph on the labels of `U`. -/
noncomputable def edgesOf (G : SimpleGraph U) : Finset (ℕ × ℕ) :=
  (pairsOn U).filter fun p => ∃ (h₁ : p.1 ∈ U) (h₂ : p.2 ∈ U), G.Adj ⟨p.1, h₁⟩ ⟨p.2, h₂⟩

/-- The graph on the labels of `U` with edge set `E`. -/
def graphOf (U : Finset ℕ) (E : Finset (ℕ × ℕ)) : SimpleGraph U :=
  SimpleGraph.fromRel fun i j => ((i : ℕ), (j : ℕ)) ∈ E

theorem mem_edgesOf {G : SimpleGraph U} {p : ℕ × ℕ} :
    p ∈ edgesOf G ↔ ∃ (h₁ : p.1 ∈ U) (h₂ : p.2 ∈ U), p.1 < p.2 ∧ G.Adj ⟨p.1, h₁⟩ ⟨p.2, h₂⟩ := by
  classical
  simp only [edgesOf, Finset.mem_filter, mem_pairsOn]
  constructor
  · rintro ⟨⟨-, -, h12⟩, h1', h2', hadj⟩
    exact ⟨h1', h2', h12, hadj⟩
  · rintro ⟨h1, h2, h12, hadj⟩
    exact ⟨⟨h1, h2, h12⟩, h1, h2, hadj⟩

theorem edgesOf_subset (G : SimpleGraph U) : edgesOf G ⊆ pairsOn U := by
  classical
  exact Finset.filter_subset _ _

theorem graphOf_adj {E : Finset (ℕ × ℕ)} {i j : U} :
    (graphOf U E).Adj i j ↔ (edgeGraph E).Adj i j := by
  rw [graphOf, SimpleGraph.fromRel_adj, edgeGraph_adj, Ne, Subtype.ext_iff]

theorem edgeGraph_edgesOf_adj (G : SimpleGraph U) (i j : U) :
    (edgeGraph (edgesOf G)).Adj i j ↔ G.Adj i j := by
  rw [edgeGraph_adj, mem_edgesOf, mem_edgesOf]
  constructor
  · rintro ⟨-, ⟨h1, h2, -, h⟩ | ⟨h1, h2, -, h⟩⟩
    · exact h
    · exact h.symm
  · intro h
    refine ⟨fun h' => h.ne (Subtype.ext h'), ?_⟩
    rcases lt_or_gt_of_ne (fun h' => h.ne (Subtype.ext h')) with h' | h'
    · exact Or.inl ⟨i.2, j.2, h', h⟩
    · exact Or.inr ⟨j.2, i.2, h', h.symm⟩

theorem graphOf_edgesOf (G : SimpleGraph U) : graphOf U (edgesOf G) = G := by
  ext i j
  rw [graphOf_adj, edgeGraph_edgesOf_adj]

theorem edgesOf_graphOf {E : Finset (ℕ × ℕ)} (hE : E ⊆ pairsOn U) : edgesOf (graphOf U E) = E := by
  ext p
  rw [mem_edgesOf]
  constructor
  · rintro ⟨h1, h2, h12, hadj⟩
    rw [graphOf_adj, edgeGraph_adj] at hadj
    rcases hadj.2 with h | h
    · exact h
    · exact absurd (mem_pairsOn.1 (hE h)).2.2 (not_lt.2 h12.le)
  · intro hp
    obtain ⟨h1, h2, h12⟩ := mem_pairsOn.1 (hE hp)
    exact ⟨h1, h2, h12, graphOf_adj.2 (edgeGraph_adj.2 ⟨h12.ne, Or.inl hp⟩)⟩

theorem edgesOf_injective : Function.Injective (edgesOf (U := U)) := by
  intro G G' h
  rw [← graphOf_edgesOf G, h, graphOf_edgesOf]

theorem edgesOf_eq_empty_iff {G : SimpleGraph U} : edgesOf G = ∅ ↔ G = ⊥ := by
  constructor
  · intro h
    rw [← graphOf_edgesOf G, h]
    ext i j
    rw [graphOf_adj, edgeGraph_adj]
    simp
  · rintro rfl
    ext p
    simp [mem_edgesOf]

theorem edgeSet_nonempty_iff {G : SimpleGraph U} : G.edgeSet.Nonempty ↔ edgesOf G ≠ ∅ := by
  rw [Ne, edgesOf_eq_empty_iff, ← SimpleGraph.edgeSet_eq_empty]
  exact Set.nonempty_iff_ne_empty

/-- Sums over graphs on `U` are sums over edge sets on `U`. -/
theorem sum_graphs_eq_sum_edgeSets {M : Type*} [AddCommMonoid M] (P : Finset (ℕ × ℕ) → Prop)
    [DecidablePred P] (F : Finset (ℕ × ℕ) → M) :
    ∑ G ∈ (Finset.univ : Finset (SimpleGraph U)).filter (fun G => P (edgesOf G)), F (edgesOf G) =
      ∑ E ∈ (pairsOn U).powerset.filter P, F E := by
  refine Finset.sum_nbij' edgesOf (graphOf U) ?_ ?_ ?_ ?_ ?_
  · intro G hG
    rw [Finset.mem_filter] at hG ⊢
    exact ⟨Finset.mem_powerset.2 (edgesOf_subset G), hG.2⟩
  · intro E hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE
    rw [Finset.mem_filter, edgesOf_graphOf hE.1]
    exact ⟨Finset.mem_univ _, hE.2⟩
  · intro G _
    exact graphOf_edgesOf G
  · intro E hE
    exact edgesOf_graphOf (Finset.mem_powerset.1 (Finset.mem_filter.1 hE).1)
  · intro _ _
    rfl

open scoped Classical in
/-- The pair product of a graph is the product over its edge set. -/
theorem prod_prod_ite_adj {M : Type*} [CommMonoid M] (G : SimpleGraph U) (f : ℕ → ℕ → M) :
    ∏ i : U, ∏ j : U, (if i < j ∧ G.Adj i j then f i j else 1) = ∏ p ∈ edgesOf G, f p.1 p.2 := by
  let e : U × U ↪ ℕ × ℕ :=
    (Function.Embedding.subtype (· ∈ U)).prodMap (Function.Embedding.subtype (· ∈ U))
  have hset : edgesOf G =
      ((Finset.univ : Finset (U × U)).filter fun q => q.1 < q.2 ∧ G.Adj q.1 q.2).map e := by
    ext p
    rw [mem_edgesOf, Finset.mem_map]
    constructor
    · rintro ⟨h1, h2, h12, hadj⟩
      exact ⟨(⟨p.1, h1⟩, ⟨p.2, h2⟩), Finset.mem_filter.2 ⟨Finset.mem_univ _, h12, hadj⟩, rfl⟩
    · rintro ⟨⟨i, j⟩, hq, rfl⟩
      rw [Finset.mem_filter] at hq
      exact ⟨i.2, j.2, hq.2.1, hq.2.2⟩
  rw [hset, Finset.prod_map, Finset.prod_filter, Fintype.prod_prod_type]
  rfl

end GraphEdges

/-! ### Connectivity -/

section Connectivity

/-- **Connectivity transport.** A graph `H` on a type `ι` embedded in `ℕ` by `e` with image `U`,
whose adjacency is that of `edgeGraph E` for an edge set `E` on `U`, is connected iff `E` connects
`U`. -/
theorem connected_iff_connOn {ι : Type*} (e : ι → ℕ) (he : Function.Injective e) (U : Finset ℕ)
    (hU : ∀ x, x ∈ U ↔ ∃ i, e i = x) (H : SimpleGraph ι) (E : Finset (ℕ × ℕ))
    (hE : E ⊆ pairsOn U) (hadj : ∀ i j, H.Adj i j ↔ (edgeGraph E).Adj (e i) (e j)) :
    H.Connected ↔ ConnOn U E := by
  constructor
  · intro hH
    obtain ⟨i₀⟩ := hH.nonempty
    refine ⟨⟨e i₀, (hU _).2 ⟨i₀, rfl⟩⟩, fun x hx y hy => ?_⟩
    obtain ⟨i, rfl⟩ := (hU x).1 hx
    obtain ⟨j, rfl⟩ := (hU y).1 hy
    let f : H →g edgeGraph E := ⟨e, fun h => (hadj _ _).1 h⟩
    exact (hH.preconnected i j).map f
  · rintro ⟨⟨x, hx⟩, hconn⟩
    obtain ⟨i₀, -⟩ := (hU x).1 hx
    have hlift : ∀ (u v : ℕ) (w : (edgeGraph E).Walk u v) (i j : ι), e i = u → e j = v →
        H.Reachable i j := by
      intro u v w
      induction w with
      | nil =>
        intro i j hi hj
        rw [he (hi.trans hj.symm)]
      | cons hadj' w' ih =>
        intro i j hi hj
        obtain ⟨k, hk⟩ := (hU _).1 (mem_of_edgeGraph_adj hE hadj').2
        refine SimpleGraph.Reachable.trans ?_ (ih k j hk hj)
        refine SimpleGraph.Adj.reachable ((hadj i k).2 ?_)
        rw [hi, hk]
        exact hadj'
    refine (SimpleGraph.connected_iff _).2 ⟨fun i j => ?_, ⟨i₀⟩⟩
    obtain ⟨w⟩ := hconn (e i) ((hU _).2 ⟨i, rfl⟩) (e j) ((hU _).2 ⟨j, rfl⟩)
    exact hlift _ _ w i j rfl rfl

end Connectivity

/-! ### Products over pairs of labels -/

section Products

variable {U : Finset ℕ}

/-- A pair product over the labels of `U` with a predicate on the labels is a product over the
pairs of labels satisfying it. -/
theorem prod_prod_ite_pred {M : Type*} [CommMonoid M] (P : ℕ → ℕ → Prop) [DecidableRel P]
    (f : ℕ → ℕ → M) :
    ∏ i : U, ∏ j : U, (if P i j then f i j else 1) =
      ∏ p ∈ (U ×ˢ U).filter (fun p => P p.1 p.2), f p.1 p.2 := by
  let e : U × U ↪ ℕ × ℕ :=
    (Function.Embedding.subtype (· ∈ U)).prodMap (Function.Embedding.subtype (· ∈ U))
  have hset : (U ×ˢ U).filter (fun p => P p.1 p.2) =
      ((Finset.univ : Finset (U × U)).filter fun q => P q.1 q.2).map e := by
    ext p
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_map]
    constructor
    · rintro ⟨⟨h1, h2⟩, hP⟩
      exact ⟨(⟨p.1, h1⟩, ⟨p.2, h2⟩), Finset.mem_filter.2 ⟨Finset.mem_univ _, hP⟩, rfl⟩
    · rintro ⟨⟨i, j⟩, hq, rfl⟩
      rw [Finset.mem_filter] at hq
      exact ⟨⟨i.2, j.2⟩, hq.2⟩
  rw [hset, Finset.prod_map, Finset.prod_filter, Fintype.prod_prod_type]
  rfl

open scoped Classical in
/-- The product over all pairs `i < j` of labels of `U`. -/
theorem prod_prod_ite_lt {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) :
    ∏ i : U, ∏ j : U, (if i < j then f i j else 1) = ∏ p ∈ pairsOn U, f p.1 p.2 := by
  exact prod_prod_ite_pred (fun i j => i < j) f

open scoped Classical in
/-- The product over the pairs `i < j` of labels of a block `B ⊆ V`, written over the labels
of `V`. -/
theorem prod_prod_ite_mem_lt {V B : Finset ℕ} (hBV : B ⊆ V) {M : Type*} [CommMonoid M]
    (f : ℕ → ℕ → M) :
    ∏ i : V, ∏ j : V, (if (i : ℕ) ∈ B ∧ (j : ℕ) ∈ B ∧ i < j then f i j else 1) =
      ∏ p ∈ pairsOn B, f p.1 p.2 := by
  refine (prod_prod_ite_pred (U := V) (fun i j => i ∈ B ∧ j ∈ B ∧ i < j) f).trans ?_
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, mem_pairsOn]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2, h12⟩
    exact ⟨⟨hBV h1, hBV h2⟩, h1, h2, h12⟩

end Products

/-! ### The multipole relation -/

section Linked

/-- The multipole relation is symmetric. -/
theorem multipoleLinked_comm {M lam : ℝ} {d e : ℂ × ℂ} :
    MultipoleLinked M lam d e ↔ MultipoleLinked M lam e d := by
  unfold MultipoleLinked
  rw [norm_sub_rev e.1 d.1, norm_sub_rev e.1 d.2, norm_sub_rev e.2 d.1, norm_sub_rev e.2 d.2,
    min_comm (max ‖e.1 - e.2‖ lam)]
  constructor <;> intro h <;> refine le_trans (le_of_eq ?_) h <;>
    simp only [min_assoc, min_left_comm]

open scoped Classical in
/-- The pairs `i < j` of labels of `U` whose dipoles are linked (`𝓑_ij`). -/
noncomputable def linkedPairs (M lam : ℝ) (c : ℕ → ℂ × ℂ) (U : Finset ℕ) : Finset (ℕ × ℕ) :=
  (pairsOn U).filter fun p => MultipoleLinked M lam (c p.1) (c p.2)

theorem mem_linkedPairs {M lam : ℝ} {c : ℕ → ℂ × ℂ} {U : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ linkedPairs M lam c U ↔ p ∈ pairsOn U ∧ MultipoleLinked M lam (c p.1) (c p.2) := by
  classical
  simp [linkedPairs]

theorem linkedPairs_subset {M lam : ℝ} {c : ℕ → ℂ × ℂ} {U : Finset ℕ} :
    linkedPairs M lam c U ⊆ pairsOn U := fun _ hp => (mem_linkedPairs.1 hp).1

theorem linkedPairs_inter_pairsOn {M lam : ℝ} {c : ℕ → ℂ × ℂ} {U B : Finset ℕ} (hB : B ⊆ U) :
    linkedPairs M lam c U ∩ pairsOn B = linkedPairs M lam c B := by
  ext p
  simp only [Finset.mem_inter, mem_linkedPairs]
  constructor
  · rintro ⟨⟨-, h⟩, hp⟩
    exact ⟨hp, h⟩
  · rintro ⟨hp, h⟩
    exact ⟨⟨pairsOn_mono hB hp, h⟩, hp⟩

/-- Adjacency in the near graph on the labels of `U` is adjacency in the graph of `linkedPairs`. -/
theorem edgeGraph_linkedPairs_adj {M lam : ℝ} {c : ℕ → ℂ × ℂ} {U : Finset ℕ} {i j : ℕ}
    (hi : i ∈ U) (hj : j ∈ U) :
    (edgeGraph (linkedPairs M lam c U)).Adj i j ↔ i ≠ j ∧
      (MultipoleLinked M lam (c i) (c j) ∨ MultipoleLinked M lam (c j) (c i)) := by
  rw [edgeGraph_adj, mem_linkedPairs, mem_linkedPairs, mem_pairsOn, mem_pairsOn]
  constructor
  · rintro ⟨hij, ⟨⟨-, -, -⟩, h⟩ | ⟨⟨-, -, -⟩, h⟩⟩
    · exact ⟨hij, Or.inl h⟩
    · exact ⟨hij, Or.inr h⟩
  · rintro ⟨hij, h⟩
    refine ⟨hij, ?_⟩
    have h' : MultipoleLinked M lam (c i) (c j) := h.elim id multipoleLinked_comm.1
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact Or.inl ⟨⟨hi, hj, hlt⟩, h'⟩
    · exact Or.inr ⟨⟨hj, hi, hlt⟩, multipoleLinked_comm.1 h'⟩

end Linked

/-! ### The graphs of the frozen definitions -/

section FrozenGraphs

/-- A graph on the labels of `U` is connected iff its edge set connects `U`. -/
theorem connected_iff_connOn_edgesOf {U : Finset ℕ} (G : SimpleGraph U) :
    G.Connected ↔ ConnOn U (edgesOf G) :=
  connected_iff_connOn (fun i : U => (i : ℕ)) Subtype.val_injective U
    (fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨i, hi⟩ => hi ▸ i.2⟩) G (edgesOf G)
    (edgesOf_subset G) (fun i j => (edgeGraph_edgesOf_adj G i j).symm)

/-- The near graph on the labels of `S` (the event `𝓑_S`). -/
theorem connected_fromRel_iff {M lam : ℝ} (c : ℕ → ℂ × ℂ) (S : Finset ℕ) :
    (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected ↔
      ConnOn S (linkedPairs M lam c S) := by
  refine connected_iff_connOn (fun i : S => (i : ℕ)) Subtype.val_injective S
    (fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨i, hi⟩ => hi ▸ i.2⟩) _ _ linkedPairs_subset
    (fun i j => ?_)
  rw [SimpleGraph.fromRel_adj, edgeGraph_linkedPairs_adj i.2 j.2, Ne, Ne, Subtype.ext_iff]

/-- The near graph on the labels of a block `B ⊆ V`, induced from the near graph on `V`. -/
theorem connected_induce_iff {M lam : ℝ} (c : ℕ → ℂ × ℂ) {V B : Finset ℕ} (hBV : B ⊆ V) :
    ((SimpleGraph.fromRel fun i j : V => MultipoleLinked M lam (c i) (c j)).induce
      {i : V | (i : ℕ) ∈ B}).Connected ↔ ConnOn B (linkedPairs M lam c B) := by
  refine connected_iff_connOn (fun i : {i : V | (i : ℕ) ∈ B} => ((i : V) : ℕ))
    (fun i j h => Subtype.ext (Subtype.ext h)) B
    (fun x => ⟨fun hx => ⟨⟨⟨x, hBV hx⟩, hx⟩, rfl⟩, fun ⟨i, hi⟩ => hi ▸ i.2⟩) _ _
    linkedPairs_subset (fun i j => ?_)
  rw [SimpleGraph.induce_adj, SimpleGraph.fromRel_adj, edgeGraph_linkedPairs_adj i.2 j.2, Ne, Ne,
    Subtype.ext_iff]

/-- The graph `E ∪ ℰ^intra(X)` of `𝖤^X`. -/
theorem connected_sup_iff {X : Finset (Finset ℕ)} (E : SimpleGraph (X.biUnion id)) :
    (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
        ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected ↔
      ConnOn (X.biUnion id) (edgesOf E ∪ intraPairs X) := by
  refine connected_iff_connOn (fun i : X.biUnion id => (i : ℕ)) Subtype.val_injective _
    (fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨i, hi⟩ => hi ▸ i.2⟩) _ _
    (Finset.union_subset (edgesOf_subset E) intraPairs_subset_pairsOn) (fun i j => ?_)
  rw [SimpleGraph.sup_adj, SimpleGraph.fromRel_adj, edgeGraph_adj, ← edgeGraph_edgesOf_adj E i j,
    edgeGraph_adj]
  simp only [Finset.mem_union, mem_intraPairs, mem_pairsOn, Ne, Subtype.ext_iff]
  constructor
  · rintro (⟨hij, h | h⟩ | ⟨hij, ⟨S, hS, hi, hj⟩ | ⟨S, hS, hj, hi⟩⟩)
    · exact ⟨hij, Or.inl (Or.inl h)⟩
    · exact ⟨hij, Or.inr (Or.inl h)⟩
    all_goals
      refine ⟨hij, ?_⟩
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact Or.inl (Or.inr ⟨S, hS, hi, hj, hlt⟩)
      · exact Or.inr (Or.inr ⟨S, hS, hj, hi, hlt⟩)
  · rintro ⟨hij, (h | ⟨S, hS, hi, hj, -⟩) | (h | ⟨S, hS, hj, hi, -⟩)⟩
    · exact Or.inl ⟨hij, Or.inl h⟩
    · exact Or.inr ⟨hij, Or.inl ⟨S, hS, hi, hj⟩⟩
    · exact Or.inl ⟨hij, Or.inr h⟩
    · exact Or.inr ⟨hij, Or.inl ⟨S, hS, hi, hj⟩⟩

/-- A graph on `V_X` has only edges between distinct blocks iff its edge set is in
`ℰ^inter(X)`. -/
theorem forall_adj_iff_edgesOf_subset_interPairs {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (E : SimpleGraph (X.biUnion id)) :
    (∀ i j : X.biUnion id, E.Adj i j → ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ↔
      edgesOf E ⊆ interPairs X := by
  constructor
  · intro h p hp
    obtain ⟨h1, h2, h12, hadj⟩ := mem_edgesOf.1 hp
    obtain ⟨S, hS, S', hS', hSS', hiS, hjS'⟩ := h _ _ hadj
    exact mem_interPairs_of hX hS hS' hSS' hiS hjS' h12
  · intro h i j hadj
    have hij : (i : ℕ) ≠ j := fun h' => hadj.ne (Subtype.ext h')
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hp : ((i : ℕ), (j : ℕ)) ∈ edgesOf E := mem_edgesOf.2 ⟨i.2, j.2, hlt, hadj⟩
      obtain ⟨S, hS, S', hS', hSS', h1, h2⟩ := exists_of_mem_interPairs (h hp)
      exact ⟨S, hS, S', hS', hSS', h1, h2⟩
    · have hp : ((j : ℕ), (i : ℕ)) ∈ edgesOf E := mem_edgesOf.2 ⟨j.2, i.2, hlt, hadj.symm⟩
      obtain ⟨S, hS, S', hS', hSS', h1, h2⟩ := exists_of_mem_interPairs (h hp)
      exact ⟨S', hS', S, hS, hSS'.symm, h2, h1⟩

/-- The intra-block pairs alone connect `V_X` only if `X` has at most one block. -/
theorem card_le_one_of_connOn_intraPairs {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (h : ConnOn (X.biUnion id) (intraPairs X)) : X.card ≤ 1 := by
  obtain ⟨⟨a, ha⟩, hconn⟩ := h
  obtain ⟨B₀, hB₀, haB₀⟩ := mem_biUnion_id.1 ha
  have hclosed : ∀ u v, (edgeGraph (intraPairs X)).Adj u v → u ∈ B₀ → v ∈ B₀ := by
    intro u v huv hu
    rcases exists_mem_of_edgeGraph_adj huv with hp | hp
    · obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
      have := mem_pairsOn.1 hpB
      rw [eq_of_isSubpartition hX hB hB₀ this.1 hu] at this
      exact this.2.1
    · obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
      have := mem_pairsOn.1 hpB
      rw [eq_of_isSubpartition hX hB hB₀ this.2.1 hu] at this
      exact this.1
  refine Finset.card_le_one.2 fun B hB B' hB' => ?_
  have hsub : ∀ C ∈ X, C = B₀ := by
    intro C hC
    obtain ⟨x, hx⟩ := hX.1 C hC
    have hxB₀ := mem_of_reachable_of_closed hclosed haB₀
      (hconn a ha x (subset_biUnion_of_mem hC hx))
    exact eq_of_isSubpartition hX hC hB₀ hx hxB₀
  rw [hsub B hB, hsub B' hB']

/-- The empty edge set connects only sets with at most one point. -/
theorem card_le_one_of_connOn_empty {D : Finset ℕ} (h : ConnOn D ∅) : D.card ≤ 1 := by
  have h' : ConnOn ((singletons D).biUnion id) (intraPairs (singletons D)) := by
    rwa [biUnion_singletons, intraPairs_singletons]
  have := card_le_one_of_connOn_intraPairs (isSubpartition_singletons D) h'
  rwa [singletons, Finset.card_image_of_injective _ Finset.singleton_injective] at this

/-- The complete edge set connects a nonempty set. -/
theorem connOn_pairsOn {D : Finset ℕ} (hD : D.Nonempty) : ConnOn D (pairsOn D) := by
  refine ⟨hD, fun i hi j hj => ?_⟩
  rcases lt_trichotomy i j with h | rfl | h
  · exact SimpleGraph.Adj.reachable (edgeGraph_adj.2 ⟨h.ne, Or.inl (mem_pairsOn.2 ⟨hi, hj, h⟩)⟩)
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (edgeGraph_adj.2 ⟨h.ne', Or.inr (mem_pairsOn.2 ⟨hj, hi, h⟩)⟩)

end FrozenGraphs

end Multipole

end MultipoleBKT

end
