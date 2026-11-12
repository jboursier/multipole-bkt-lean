/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.BoundedLowerEps.Reduction
public import MultipoleBKT.Appendix.SmallIntegral.TreeMajorant
public import MultipoleBKT.Limits.RouteBase.Activity

/-!
# From edge sets of labels to graphs on `V_X`

The activities of the hierarchical models (`MultipoleBKT.Hierarchical`) are written with edge sets
`E ⊆ pairsOn V_X` of pairs `(i, j)`, `i < j`, of labels. The retained near, odd and even trees
use unordered pairs of the type `V_X` and the blocks `blockOf X : V_X → X`.
proof of Lemma A.4. This file translates:

* `prod_pairs_eq_prod_edgeFinset`: `∏_{(i,j) ∈ E} f(c_i, c_j) = ∏_{e ∈ E(graphOf V E)} f_e` for a
  symmetric `f` and `c` read on `V_X`;
* `cutEven_of_mem_relEulerianPairs`: `E ∈ Eul^X` (every block has even degree) is cut-even on the
  blocks;
* `reachable_of_connOn`: `E ∪ ℰ^intra(X)` connects `V_X` iff the graph of `E` connects the blocks;
* `connected_induce_of_connOn`: the multipole event `𝓑_S` of a block, read on `V_X`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BoundedLowerEps

open Finset SimpleGraph
open Multipole SetPartition Limits SmallIntegral Hierarchical

variable {X : Finset (Finset ℕ)}

/-! ### Products over edge sets -/

section Products

open scoped Classical in
/-- `∏_{(i,j) ∈ E} f(i, j) = ∏_{e ∈ E(graphOf V E)} f_e` for `E ⊆ pairsOn V` and a symmetric
`f : V → V → ℝ`. -/
theorem prod_pairs_eq_prod_edgeFinset {V : Finset ℕ} {E : Finset (ℕ × ℕ)} (hE : E ⊆ pairsOn V)
    (f : V → V → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∏ p ∈ E, (if h : p.1 ∈ V ∧ p.2 ∈ V then f ⟨p.1, h.1⟩ ⟨p.2, h.2⟩ else 1) =
      ∏ e ∈ (graphOf V E).edgeFinset, symmLift f hf e := by
  rw [← prod_prod_ite_lt_adj (graphOf V E) f hf]
  set g : ℕ → ℕ → ℝ := fun a b => if h : a ∈ V ∧ b ∈ V then f ⟨a, h.1⟩ ⟨b, h.2⟩ else 1
  have h1 : ∏ p ∈ E, (if h : p.1 ∈ V ∧ p.2 ∈ V then f ⟨p.1, h.1⟩ ⟨p.2, h.2⟩ else 1) =
      ∏ p ∈ edgesOf (graphOf V E), g p.1 p.2 := by
    rw [edgesOf_graphOf hE]
  rw [h1, ← prod_prod_ite_adj (graphOf V E) g]
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  simp only [g, i.2, j.2, and_self, dite_true]

end Products

/-! ### Eulerian edge sets are cut-even -/

section CutEven

/-- The number of pairs of `E` with exactly one end in `U`. -/
theorem even_card_crossing {E : Finset (ℕ × ℕ)} {U : Finset ℕ}
    (h : Even ((E.filter fun p => p.1 ∈ U).card + (E.filter fun p => p.2 ∈ U).card)) :
    Even (E.filter fun p => (p.1 ∈ U ↔ p.2 ∉ U)).card := by
  classical
  have h1 : (E.filter fun p => p.1 ∈ U).card = (E.filter fun p => p.1 ∈ U ∧ p.2 ∈ U).card +
      (E.filter fun p => p.1 ∈ U ∧ p.2 ∉ U).card := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun p _ h1 h2 => h2.2 h1.2)]
    congr 1
    ext p
    simp only [mem_filter, mem_union]
    tauto
  have h2 : (E.filter fun p => p.2 ∈ U).card = (E.filter fun p => p.1 ∈ U ∧ p.2 ∈ U).card +
      (E.filter fun p => p.1 ∉ U ∧ p.2 ∈ U).card := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun p _ h1 h2 => h2.1 h1.1)]
    congr 1
    ext p
    simp only [mem_filter, mem_union]
    tauto
  have h3 : (E.filter fun p => (p.1 ∈ U ↔ p.2 ∉ U)).card =
      (E.filter fun p => p.1 ∈ U ∧ p.2 ∉ U).card + (E.filter fun p => p.1 ∉ U ∧ p.2 ∈ U).card := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun p _ h1 h2 => h2.1 h1.1)]
    congr 1
    ext p
    simp only [mem_filter, mem_union]
    tauto
  rw [h1, h2] at h
  rw [h3]
  have : (E.filter fun p => p.1 ∈ U ∧ p.2 ∉ U).card + (E.filter fun p => p.1 ∉ U ∧ p.2 ∈ U).card =
      ((E.filter fun p => p.1 ∈ U ∧ p.2 ∈ U).card + (E.filter fun p => p.1 ∈ U ∧ p.2 ∉ U).card +
        ((E.filter fun p => p.1 ∈ U ∧ p.2 ∈ U).card +
          (E.filter fun p => p.1 ∉ U ∧ p.2 ∈ U).card)) -
        2 * (E.filter fun p => p.1 ∈ U ∧ p.2 ∈ U).card := by omega
  rw [this, Nat.even_sub (by omega)]
  exact iff_of_true h (even_two_mul _)

/-- The degrees of the blocks of a set `A` of blocks add up to the number of ends in `⋃ A`. -/
theorem sum_blockDeg_eq (hX : IsSubpartition X) (E : Finset (ℕ × ℕ)) (A : Finset (Finset ℕ))
    (hA : A ⊆ X) :
    ∑ S ∈ A, blockDeg E S = (E.filter fun p => p.1 ∈ A.biUnion id).card +
      (E.filter fun p => p.2 ∈ A.biUnion id).card := by
  classical
  have hdisj : (A : Set (Finset ℕ)).PairwiseDisjoint id := fun S hS T hT hST =>
    hX.2 (hA hS) (hA hT) hST
  have key : ∀ g : ℕ × ℕ → ℕ, (E.filter fun p => g p ∈ A.biUnion id).card =
      ∑ S ∈ A, (E.filter fun p => g p ∈ S).card := by
    intro g
    rw [← card_biUnion]
    · congr 1
      ext p
      simp only [mem_filter, mem_biUnion, id]
      constructor
      · rintro ⟨hp, S, hS, h⟩; exact ⟨S, hS, hp, h⟩
      · rintro ⟨S, hS, hp, h⟩; exact ⟨hp, S, hS, h⟩
    · intro S hS T hT hST
      rw [Function.onFun, disjoint_filter]
      intro p _ h1 h2
      exact Finset.disjoint_left.1 (hdisj hS hT hST) h1 h2
  unfold blockDeg
  rw [sum_add_distrib, key Prod.fst, key Prod.snd]

/-- **Eulerian edge sets are cut-even**: if every block of `X` has even degree in `E`, then every
set of blocks is crossed by an even number of pairs of `E`. -/
theorem even_card_crossing_of_mem_relEulerianPairs (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ∈ relEulerianPairs X) (A : Finset (Finset ℕ)) (hA : A ⊆ X) :
    Even (E.filter fun p => (p.1 ∈ A.biUnion id ↔ p.2 ∉ A.biUnion id)).card := by
  refine even_card_crossing ?_
  rw [← sum_blockDeg_eq hX E A hA]
  exact Finset.even_sum _ fun S hS => (mem_relEulerianPairs.1 hE).2 S (hA hS)

end CutEven

/-! ### Graphs on `V_X` -/

section Graphs

theorem prod_ite_neg_one {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    ∏ x ∈ s, (if P x then (-1 : ℝ) else 1) = (-1) ^ (s.filter P).card := by
  rw [prod_ite, prod_const_one, mul_one, prod_const]

open scoped Classical in
/-- **Eulerian edge sets are cut-even on the blocks**, as graphs on `V_X`. -/
theorem cutEven_graphOf (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hEp : E ⊆ pairsOn (X.biUnion id)) (hE : E ∈ relEulerianPairs X) :
    CutEven (Sym2.map (Limits.blockOf X)) (graphOf (X.biUnion id) E).edgeFinset := by
  intro A
  set A₀ : Finset (Finset ℕ) := A.map (Function.Embedding.subtype _) with hA₀
  have hA₀X : A₀ ⊆ X := by
    intro S hS
    obtain ⟨T, -, rfl⟩ := mem_map.1 hS
    exact T.2
  set U := A₀.biUnion id with hU
  have hblk : ∀ i : X.biUnion id, Limits.blockOf X i ∈ A ↔ (i : ℕ) ∈ U := by
    intro i
    constructor
    · intro h
      exact mem_biUnion.2 ⟨_, mem_map_of_mem _ h, Limits.mem_blockOf i⟩
    · intro h
      obtain ⟨S, hS, hiS⟩ := mem_biUnion.1 h
      obtain ⟨T, hT, rfl⟩ := mem_map.1 hS
      rwa [Limits.blockOf_eq hX T.2 hiS]
  set f : X.biUnion id → X.biUnion id → ℝ := fun i j =>
    if Crosses A s(Limits.blockOf X i, Limits.blockOf X j) then -1 else 1 with hf
  have hfs : ∀ i j, f i j = f j i := fun i j => by
    simp only [hf]
    rw [Sym2.eq_swap]
  have key := prod_pairs_eq_prod_edgeFinset hEp f hfs
  have hlhs : ∏ p ∈ E, (if h : p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id then
      f ⟨p.1, h.1⟩ ⟨p.2, h.2⟩ else 1) =
      ∏ p ∈ E, (if (p.1 ∈ U ↔ p.2 ∉ U) then (-1 : ℝ) else 1) := by
    refine prod_congr rfl fun p hp => ?_
    have hpV := mem_pairsOn.1 (hEp hp)
    rw [dite_eq_left ⟨hpV.1, hpV.2.1⟩]
    simp only [hf, crosses_mk, hblk]
  have hrhs : ∏ e ∈ (graphOf (X.biUnion id) E).edgeFinset, symmLift f hfs e =
      ∏ e ∈ (graphOf (X.biUnion id) E).edgeFinset,
        (if Crosses A (Sym2.map (Limits.blockOf X) e) then (-1 : ℝ) else 1) := by
    refine prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | h i j =>
      simp only [symmLift_mk, hf, Sym2.map_mk]
      exact if_congr Iff.rfl rfl rfl
  rw [hlhs, hrhs, prod_ite_neg_one, prod_ite_neg_one] at key
  have hev := even_card_crossing_of_mem_relEulerianPairs hX hE A₀ hA₀X
  rw [← hU] at hev
  rw [← neg_one_pow_eq_one_iff_even (R := ℝ) (by norm_num), ← key]
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).2 hev

open scoped Classical in
/-- **Connectivity**: if `E ∪ ℰ^intra(X)` connects `V_X`, the graph of `E` together with the
blocks connects `V_X`. -/
theorem reachable_of_connOn (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hEp : E ⊆ pairsOn (X.biUnion id)) (hE : ConnOn (X.biUnion id) (E ∪ intraPairs X))
    (i j : X.biUnion id) :
    (sameBlockGraph (Limits.blockOf X) ⊔
      fromEdgeSet ((graphOf (X.biUnion id) E).edgeFinset : Set (Sym2 (X.biUnion id)))).Reachable
        i j := by
  have hconn := (connected_sup_iff (X := X) (graphOf (X.biUnion id) E)).2
    (by rw [edgesOf_graphOf hEp]; exact hE)
  refine (hconn.preconnected i j).mono ?_
  intro a b hab
  rw [sup_adj] at hab ⊢
  rcases hab with h | h
  · right
    rw [fromEdgeSet_adj, coe_edgeFinset, mem_edgeSet]
    exact ⟨h, h.ne⟩
  · left
    rw [fromRel_adj] at h
    rw [sameBlockGraph_adj]
    obtain ⟨hne, ⟨S, hS, ha, hb⟩ | ⟨S, hS, hb, ha⟩⟩ := h <;>
      exact ⟨hne, by rw [Limits.blockOf_eq hX hS ha, Limits.blockOf_eq hX hS hb]⟩

/-- **The multipole event of a block, on `V_X`**: `𝟙_{𝓑_S}` (`ConnOn S (linkedPairs …)`) for the
configuration `c` read on `V_X` is the connectivity of the near graph inside the block. -/
theorem connected_induce_of_connOn (hX : IsSubpartition X) {M lam : ℝ}
    (y : X.biUnion id → ℂ × ℂ) {S : Finset ℕ} (hS : S ∈ X)
    (h : ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S)) :
    ((nearGraph M lam y).induce {i | Limits.blockOf X i = ⟨S, hS⟩}).Connected := by
  have hSV : S ⊆ X.biUnion id := subset_biUnion_of_mem id hS
  have h1 := (connected_induce_iff (M := M) (lam := lam) (extendConfig (X.biUnion id) y) hSV).2 h
  have hgraph : (SimpleGraph.fromRel fun i j : X.biUnion id =>
      MultipoleLinked M lam (extendConfig (X.biUnion id) y i)
        (extendConfig (X.biUnion id) y j)) = nearGraph M lam y := by
    have hy : ∀ i : X.biUnion id, extendConfig (X.biUnion id) y i = y i := fun i => by
      simp [extendConfig, i.2]
    ext i j
    simp only [fromRel_adj, hy]
  have hset : {i : X.biUnion id | (i : ℕ) ∈ S} = {i | Limits.blockOf X i = ⟨S, hS⟩} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    exact (Limits.blockOf_eq_iff hX i ⟨S, hS⟩).symm
  rw [hgraph, hset] at h1
  exact h1

open scoped Classical in
/-- The graph of `E ∖ E₁`: `E(graphOf V (E ∖ E₁)) = E(graphOf V E) ∖ E(graphOf V E₁)` for
`E₁ ⊆ E ⊆ pairsOn V`. -/
theorem edgeFinset_graphOf_sdiff {V : Finset ℕ} {E E₁ : Finset (ℕ × ℕ)} (hE : E ⊆ pairsOn V)
    (hE₁ : E₁ ⊆ E) :
    (graphOf V (E \ E₁)).edgeFinset = (graphOf V E).edgeFinset \ (graphOf V E₁).edgeFinset := by
  ext e
  induction e using Sym2.ind with
  | h i j =>
    simp only [mem_sdiff, mem_edgeFinset, mem_edgeSet, graphOf_adj, edgeGraph_adj, ne_eq]
    have hlt : ∀ a b : ℕ, (a, b) ∈ E → a < b := fun a b h => (mem_pairsOn.1 (hE h)).2.2
    have h1 : ((i : ℕ), (j : ℕ)) ∈ E → ((j : ℕ), (i : ℕ)) ∉ E := fun h h' =>
      lt_asymm (hlt _ _ h) (hlt _ _ h')
    have h2 : ((i : ℕ), (j : ℕ)) ∈ E₁ → ((i : ℕ), (j : ℕ)) ∈ E := fun h => hE₁ h
    have h3 : ((j : ℕ), (i : ℕ)) ∈ E₁ → ((j : ℕ), (i : ℕ)) ∈ E := fun h => hE₁ h
    tauto

end Graphs

end BoundedLowerEps

end MultipoleBKT

end
