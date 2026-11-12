/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SourceCases

/-!
# Multiplying the separate odd-component bounds

See (A.55)–(A.58)
and the conclusion after (A.60). Each component keeps its
own subpartition. A marked component uses its prescribed strict-ear tree,
while all remaining components use their ordinary skeleton trees.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Peeling Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)}

/-- Restrict an edge function along the label inclusion of a subpartition. -/
def componentEdge {Y : Finset (Finset ℕ)} (f : Sym2 ℕ → ℝ) : Sym2 (Y.biUnion id) → ℝ :=
  f ∘ Sym2.map Subtype.val

/-- Restricting all three geometric data commutes with the absolute weight. -/
theorem absWeight_component (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    {Y : Finset (Finset ℕ)} (e : Sym2 (Y.biUnion id)) :
    absWeight (fun i : Y.biUnion id => r i) (componentEdge d) (componentEdge c) e =
      absWeight r d c (Sym2.map Subtype.val e) := by
  induction e using Sym2.ind with
  | h i j => rfl

open scoped Classical in
/-- Transport any symmetric edge product from ordered original pairs. -/
theorem component_product_function {Y : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}
    (hO : O ⊆ pairsOn (Y.biUnion id)) (f : Sym2 ℕ → ℝ) :
    (∏ p ∈ O, f s(p.1, p.2)) =
      ∏ e ∈ (pairGraph (Y.biUnion id) O).edgeFinset, componentEdge f e := by
  rw [prod_pairs_eq_prod_edgeFinset hO (fun i j => f s(i, j))
    (fun i j => congrArg f Sym2.eq_swap)]
  apply prod_congr rfl
  intro e _
  induction e using Sym2.ind with
  | h i j => rfl

open scoped Classical in
/-- The original ordered-pair product is the geometric product on the component
label subtype. This transport also applies after deleting a marked edge. -/
theorem component_product {Y : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}
    (hO : O ⊆ pairsOn (Y.biUnion id)) (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ) :
    (∏ p ∈ O, absWeight r d c s(p.1, p.2)) =
      ∏ e ∈ (pairGraph (Y.biUnion id) O).edgeFinset,
        absWeight (fun i : Y.biUnion id => r i) (componentEdge d) (componentEdge c) e := by
  rw [prod_pairs_eq_prod_edgeFinset hO (fun i j => absWeight r d c s(i, j))
    (fun i j => congrArg _ Sym2.eq_swap)]
  apply prod_congr rfl
  intro e _
  induction e using Sym2.ind with
  | h i j => rfl

open scoped Classical in
/-- The ordinary component estimate with its original ordered-pair product. -/
theorem source_ordinary_component (hX : IsSubpartition X) {O : Finset (ℕ × ℕ)}
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅)
    (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1, p.2))
    (Y : oddComponents X O) :
    ∃ (v : Y.val.biUnion id) (T : SimpleGraph (Y.val.biUnion id)),
      IsRelTree Y.val T ∧ T ≤ sourceOddSkeleton hX hOX hpar Y ∧
        (∀ i : Y.val.biUnion id, r i ≤ r v) ∧
      (∏ p ∈ O ∩ interPairs Y.val, absWeight r d c s(p.1, p.2)) ≤
        (∏ S ∈ univ.erase (MultipoleBKT.blockOf
            (source_odd_component_eulerian hX hOX hpar Y.property).1 v),
          blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
            (fun i : Y.val.biUnion id => r i) S ^ 2) *
          ∏ e ∈ T.edgeFinset, keptWeight (componentEdge d) (componentEdge c) e := by
  obtain ⟨hY, hE⟩ := source_odd_component_eulerian hX hOX hpar Y.property
  have hfar' : ∀ i j : Y.val.biUnion id,
      (pairGraph _ (O ∩ interPairs Y.val)).Adj i j →
        min (r i) (r j) ≤ componentEdge d s(i, j) := by
    intro i j hij
    rcases (pairGraph_adj.1 hij).2 with hij | hji
    · exact hfar _ (mem_inter.1 hij).1
    · simpa only [componentEdge, Function.comp_apply, Sym2.map_mk, min_comm, Sym2.eq_swap] using hfar _ (mem_inter.1 hji).1
  obtain ⟨v, T, hT, hTK, hmax, hb⟩ := standard_odd_component hY hE
    (fun i : Y.val.biUnion id => r i) (componentEdge d) (componentEdge c)
    (fun i => hr i) (fun e => hd _) (fun e => hc _) (fun e => hc1 _) hfar'
  refine ⟨v, T, hT, hTK, hmax, ?_⟩
  rw [component_product (inter_subset_right.trans interPairs_subset_pairsOn) r d c]
  exact hb

open scoped Classical in
/-- The full case-D odd family. The marked component uses the prescribed
strict-ear deletion. Every other component keeps its ordinary radius product
and tree. The left side deletes only the marked original edge. -/
theorem source_marked_family (hX : IsSubpartition X) {O : Finset (ℕ × ℕ)}
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅)
    (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1, p.2))
    (Y₀ : oddComponents X O) {x y : Y₀.val.biUnion id}
    (hxy : (sourceOddSkeleton hX hOX hpar Y₀).Adj x y) :
    ∃ (T₀ : SimpleGraph (Y₀.val.biUnion id))
      (v : (Y : oddComponents X O) → Y.val.biUnion id)
      (T : (Y : oddComponents X O) → SimpleGraph (Y.val.biUnion id)),
      (IsRelTree Y₀.val T₀ ∧ T₀ ≤ sourceOddSkeleton hX hOX hpar Y₀ ∧ s(x, y) ∉ T₀.edgeSet) ∧
      (∀ Y, IsRelTree Y.val (T Y) ∧ T Y ≤ sourceOddSkeleton hX hOX hpar Y ∧
        ∀ i : Y.val.biUnion id, r i ≤ r (v Y)) ∧
      r x * r y * (∏ p ∈ O, if s(p.1, p.2) = s(x.val, y.val) then 1 else
          absWeight r d c s(p.1, p.2)) ≤
        ((∏ S : Y₀.val, blockRadius
            (source_odd_component_eulerian hX hOX hpar Y₀.property).1
            (fun i : Y₀.val.biUnion id => r i) S ^ 2) *
          ∏ e ∈ T₀.edgeFinset, keptWeight (componentEdge d) (componentEdge c) e) *
        ∏ Y ∈ univ.erase Y₀,
          (∏ S ∈ univ.erase (MultipoleBKT.blockOf
              (source_odd_component_eulerian hX hOX hpar Y.property).1 (v Y)),
            blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
              (fun i : Y.val.biUnion id => r i) S ^ 2) *
            ∏ e ∈ (T Y).edgeFinset, keptWeight (componentEdge d) (componentEdge c) e := by
  have hall := source_ordinary_component hX hOX hpar r d c hr hd hc hc1 hfar
  choose v T hT hTK hmax hb using hall
  have hfar₀ : ∀ i j : Y₀.val.biUnion id,
      (pairGraph _ (O ∩ interPairs Y₀.val)).Adj i j →
        min (r i) (r j) ≤ componentEdge d s(i, j) := by
    intro i j hij
    rcases (pairGraph_adj.1 hij).2 with hij | hji
    · exact hfar _ (mem_inter.1 hij).1
    · simpa only [componentEdge, Function.comp_apply, Sym2.map_mk, min_comm, Sym2.eq_swap]
        using hfar _ (mem_inter.1 hji).1
  obtain ⟨T₀, hT₀, hTK₀, hmark, hb₀⟩ := source_caseD_pointwise hX hOX hpar Y₀ hxy
    (fun i : Y₀.val.biUnion id => r i) (componentEdge d) (componentEdge c)
    (fun i => hr i) (fun e => hd _) (fun e => hc _) (fun e => hc1 _) hfar₀
  let f : Sym2 ℕ → ℝ := fun e => if e = s(x.val, y.val) then 1 else absWeight r d c e
  have hf0 : ∀ e, 0 ≤ f e := by
    intro e
    dsimp [f]
    split_ifs
    · exact zero_le_one
    · exact absWeight_nonneg hr hd hc e
  have hbase : (∏ p ∈ O ∩ interPairs Y₀.val, f s(p.1, p.2)) =
      ∏ e ∈ (pairGraph _ (O ∩ interPairs Y₀.val)).edgeFinset.erase s(x, y),
        absWeight (fun i : Y₀.val.biUnion id => r i) (componentEdge d) (componentEdge c) e := by
    rw [component_product_function (inter_subset_right.trans interPairs_subset_pairsOn)]
    have hmap : ∀ e : Sym2 (Y₀.val.biUnion id), componentEdge f e =
        if e = s(x, y) then 1 else
          absWeight (fun i : Y₀.val.biUnion id => r i) (componentEdge d) (componentEdge c) e := by
      intro e
      rw [absWeight_component]
      change (if Sym2.map Subtype.val e = Sym2.map Subtype.val s(x, y) then 1 else _) = _
      simp only [(Sym2.map.injective Subtype.val_injective).eq_iff]
    simp_rw [hmap]
    rw [prod_ite]
    simp only [prod_const_one, one_mul]
    congr 1
    ext e
    simp only [mem_filter, mem_erase, and_comm]
  have hother : ∀ Y : oddComponents X O, Y ≠ Y₀ →
      (∏ p ∈ O ∩ interPairs Y.val, f s(p.1, p.2)) =
        ∏ p ∈ O ∩ interPairs Y.val, absWeight r d c s(p.1, p.2) := by
    intro Y hne
    have hdis := UpperBound.BoundedUpper.disjoint_biUnion_of_disjoint hX
      (subset_of_mem_relComponents (oddComponents_subset O Y.property))
      (subset_of_mem_relComponents (oddComponents_subset O Y₀.property))
      (disjoint_of_mem_relComponents hX (oddComponents_subset O Y.property)
        (oddComponents_subset O Y₀.property) (fun h => hne (Subtype.ext h)))
    apply prod_congr rfl
    intro p hp
    dsimp [f]
    apply ite_eq_right
    intro heq
    have hpY := (mem_pairsOn.1 (interPairs_subset_pairsOn (mem_inter.1 hp).2)).1
    rcases Sym2.eq_iff.1 heq with ⟨hx, -⟩ | ⟨hy, -⟩
    · exact disjoint_left.1 hdis hpY (hx.symm ▸ x.property)
    · exact disjoint_left.1 hdis hpY (hy.symm ▸ y.property)
  refine ⟨T₀, v, T, ⟨hT₀, hTK₀, hmark⟩, fun Y => ⟨hT Y, hTK Y, hmax Y⟩, ?_⟩
  change r x * r y * (∏ p ∈ O, f s(p.1, p.2)) ≤ _
  rw [prod_eq_prod_oddComponents hX hOX, ← prod_coe_sort,
    ← mul_prod_erase univ (fun Y : oddComponents X O =>
      ∏ p ∈ O ∩ interPairs Y.val, f s(p.1, p.2)) (mem_univ Y₀), hbase]
  rw [← mul_assoc]
  apply mul_le_mul hb₀
  · apply prod_le_prod₀ (fun Y _ => prod_nonneg fun p _ => hf0 _)
    intro Y hY
    rw [hother Y (mem_erase.1 hY).1]
    exact hb Y
  · exact prod_nonneg fun Y _ => prod_nonneg fun p _ => hf0 _
  · exact mul_nonneg (prod_nonneg fun S _ => sq_nonneg _)
      (prod_nonneg fun e _ => keptWeight_nonneg (fun e => hc _) e)

end MultipoleBKT.ExpansionK.RouteCases

end
