/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SourceMarked

/-!
# A single global tail for the odd family

See Lemma A.7, omitted-long-edge
argument. Each selected minimal skeleton is peeled in its
own component. The quadratic cutoff gain and all component tails are then
combined into one global tail on the union of the retained odd trees.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Limits Peeling Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

open scoped Classical in
/-- The ordinary peelings of the fixed original skeletons. -/
structure SourcePeeling (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d : Sym2 ℕ → ℝ) where
  root : (Y : oddComponents X O) → Y.val.biUnion id
  longest : (Y : oddComponents X O) → Sym2 (Y.val.biUnion id)
  ears : (Y : oddComponents X O) → List (Ear (Y.val.biUnion id) × (Y.val.biUnion id × Y.val.biUnion id))
  peeling : ∀ Y, IsPeeling (source_odd_component_eulerian hX hOX hpar Y.property).1
    (sourceOddSkeleton hX hOX hpar Y) (fun i : Y.val.biUnion id => r i) (componentEdge d)
    (root Y) (longest Y) (ears Y)

open scoped Classical in
/-- The component peelings exist before choosing any omitted edge. -/
theorem exists_source_peeling (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d : Sym2 ℕ → ℝ) :
    Nonempty (SourcePeeling hX hOX hpar r d) := by
  have hh := fun Y : oddComponents X O => exists_isPeeling
    (hX := (source_odd_component_eulerian hX hOX hpar Y.property).1)
    (oddSkeleton_spec (source_odd_component_eulerian hX hOX hpar Y.property).1
      (source_odd_component_eulerian hX hOX hpar Y.property).2).2
    (fun i : Y.val.biUnion id => r i) (componentEdge d)
  choose v e Q hQ using hh
  exact ⟨⟨v,e,Q,hQ⟩⟩

open scoped Classical in
/-- The tree family produced by those component peelings. -/
noncomputable def SourcePeeling.family {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} {d : Sym2 ℕ → ℝ}
    (P : SourcePeeling hX hOX hpar r d) : OddFamily hX hOX hpar r where
  root := P.root
  tree Y := keptGraph (sourceOddSkeleton hX hOX hpar Y) (P.ears Y)
  tree_spec Y := ⟨(P.peeling Y).isRelTree
    ((isRelMinTwoEdgeConnected_iff_on
      (source_odd_component_eulerian hX hOX hpar Y.property).1).1
      (oddSkeleton_spec (source_odd_component_eulerian hX hOX hpar Y.property).1
        (source_odd_component_eulerian hX hOX hpar Y.property).2).2).1,
    deleteEdges_le _⟩
  root_max Y := (P.peeling Y).le_radius

open scoped Classical in
/-- The retained odd edges, on the original natural labels. -/
noncomputable def OddFamily.edges {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} (F : OddFamily hX hOX hpar r) : Finset (Sym2 ℕ) :=
  univ.biUnion fun Y : oddComponents X O => (F.tree Y).edgeFinset.image (Sym2.map Subtype.val)

open scoped Classical in
/-- One component factor of the ordinary tree family. -/
noncomputable def OddFamily.componentWeight {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} (F : OddFamily hX hOX hpar r)
    (d c : Sym2 ℕ → ℝ) (Y : oddComponents X O) : ℝ :=
  (∏ S ∈ univ.erase (MultipoleBKT.blockOf
    (source_odd_component_eulerian hX hOX hpar Y.property).1 (F.root Y)),
    blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
      (fun i : Y.val.biUnion id => r i) S ^ 2) *
    ∏ e ∈ (F.tree Y).edgeFinset, keptWeight (componentEdge d) (componentEdge c) e

/-- Each component factor is nonnegative. -/
theorem OddFamily.componentWeight_nonneg {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} (F : OddFamily hX hOX hpar r)
    (d c : Sym2 ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) (Y : oddComponents X O) :
    0 ≤ F.componentWeight d c Y := by
  classical
  exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
    (prod_nonneg fun _ _ => keptWeight_nonneg (fun e => hc _) _)

section Bounds

variable (hX : IsSubpartition X) (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅)
variable (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
variable (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
variable (hpos : ∀ p ∈ O, 0 < d s(p.1,p.2))
variable (P : SourcePeeling hX hOX hpar r d)

include hpos

private theorem kept_pos (Y : oddComponents X O) {e : Sym2 (Y.val.biUnion id)}
    (he : e ∈ (P.family.tree Y).edgeSet) : 0 < componentEdge d e := by
  have hsub := (P.family.tree_spec Y).2.trans
    (oddSkeleton_spec (source_odd_component_eulerian hX hOX hpar Y.property).1
      (source_odd_component_eulerian hX hOX hpar Y.property).2).1
  induction e using Sym2.ind with
  | h i j =>
    rcases (pairGraph_adj.1 (hsub he)).2 with h | h
    · exact hpos _ (mem_inter.1 h).1
    · simpa only [componentEdge,Function.comp_apply,Sym2.map_mk,Sym2.eq_swap] using hpos _ (mem_inter.1 h).1

include hr hd hc hc1 hpos

open scoped Classical in
/-- Component estimates retain their tails until the family is multiplied. -/
theorem SourcePeeling.component_tail (Y : oddComponents X O) :
    (∏ e ∈ (sourceOddSkeleton hX hOX hpar Y).edgeFinset,
      absWeight (fun i : Y.val.biUnion id => r i) (componentEdge d) (componentEdge c) e) ≤
      ((∏ S ∈ univ.erase (MultipoleBKT.blockOf
        (source_odd_component_eulerian hX hOX hpar Y.property).1 (P.root Y)),
        blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
          (fun i : Y.val.biUnion id => r i) S ^ 2) *
        ∏ e ∈ (P.family.tree Y).edgeFinset, keptWeight (componentEdge d) (componentEdge c) e) *
      globalTail (r (P.root Y)) d ((P.family.tree Y).edgeFinset.image (Sym2.map Subtype.val)) := by
  have hb := quadratic_estimate (c := componentEdge c) (P.peeling Y) (fun i => hr i) (fun e => hd _) (fun e => hc _)
  have ht := deleted_weights_single_tail (c := componentEdge c) (P.peeling Y) (fun i => hr i) (fun e => hd _)
    (fun e => hc _) (fun e => hc1 _) (fun e he => kept_pos hX hOX hpar r d hpos P Y (e := e) he)
  rw [globalTail_image]
  exact hb.trans (mul_le_mul_of_nonneg_left ht
    (mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
      (prod_nonneg fun _ _ => keptWeight_nonneg (fun e => hc _) _)))

open scoped Classical in
/-- One long skeleton edge gives the literal minimum before family assembly. -/
theorem SourcePeeling.component_long (Y : oddComponents X O)
    {em : Sym2 (Y.val.biUnion id)} (hem : em ∈ (sourceOddSkeleton hX hOX hpar Y).edgeSet)
    {H : ℝ} (hH : 0 < H) (hRH : r (P.root Y) ≤ H) (hm : H ≤ componentEdge d em) :
    (∏ e ∈ (sourceOddSkeleton hX hOX hpar Y).edgeFinset,
      absWeight (fun i : Y.val.biUnion id => r i) (componentEdge d) (componentEdge c) e) ≤
      ((∏ S ∈ univ.erase (MultipoleBKT.blockOf
        (source_odd_component_eulerian hX hOX hpar Y.property).1 (P.root Y)),
        blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
          (fun i : Y.val.biUnion id => r i) S ^ 2) *
        ∏ e ∈ (P.family.tree Y).edgeFinset, keptWeight (componentEdge d) (componentEdge c) e) *
      min (r (P.root Y) ^ 2 / H ^ 2)
        (globalTail (r (P.root Y)) d ((P.family.tree Y).edgeFinset.image (Sym2.map Subtype.val))) := by
  rw [globalTail_image]
  exact long_odd_skeleton_product (P.peeling Y) (fun i => hr i) (fun e => hd _)
    (fun e => hc _) (fun e => hc1 _)
    (blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1 (fun i : Y.val.biUnion id => r i))
    (le_blockRadius _) (fun e he => kept_pos hX hOX hpar r d hpos P Y (e := e) he) hem hH hRH hm

open scoped Classical in
/-- Multiplying the component estimates leaves a single global tail. -/
theorem SourcePeeling.family_tail {R : ℝ} (hR : ∀ i ∈ X.biUnion id, r i ≤ R) :
    (∏ p ∈ sourceSkeletonEdges hX hOX hpar, absWeight r d c s(p.1,p.2)) ≤
      P.family.weight d c * globalTail R d P.family.edges := by
  let tail := fun Y : oddComponents X O => globalTail (r (P.root Y)) d
    ((P.family.tree Y).edgeFinset.image (Sym2.map Subtype.val))
  have hbound : (∏ p ∈ sourceSkeletonEdges hX hOX hpar, absWeight r d c s(p.1,p.2)) ≤
      ∏ Y : oddComponents X O, P.family.componentWeight d c Y * tail Y := by
    rw [source_skeleton_product hX hOX hpar]
    apply prod_le_prod₀ (fun _ _ => prod_nonneg fun _ _ => absWeight_nonneg hr hd hc _)
    intro Y _
    simpa only [OddFamily.componentWeight,SourcePeeling.family,tail,componentEdge,Function.comp_apply,← absWeight_component] using
      SourcePeeling.component_tail hX hOX hpar r d c hr hd hc hc1 hpos P Y
  have ht : (∏ Y : oddComponents X O, tail Y) ≤ globalTail R d P.family.edges := by
    apply prod_globalTail_le_biUnion univ (fun Y => r (P.root Y)) R d
      (fun Y => (P.family.tree Y).edgeFinset.image (Sym2.map Subtype.val))
      (fun Y _ => hr _) (fun Y _ => ?_)
    exact hR _ (biUnion_subset_biUnion_of_subset_left id
      (subset_of_mem_relComponents (oddComponents_subset O Y.property)) (P.root Y).property)
  rw [prod_mul_distrib] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left ht (by
    exact prod_nonneg fun Y _ => P.family.componentWeight_nonneg d c hc Y))

open scoped Classical in
/-- A long edge in any selected skeleton gives the quadratic gain with exactly
one global tail for the full component family. -/
theorem SourcePeeling.family_long {R H : ℝ} (hR : ∀ i ∈ X.biUnion id, r i ≤ R)
    (hH : 0 < H) (hRH : R ≤ H) {p : ℕ × ℕ}
    (hp : p ∈ sourceSkeletonEdges hX hOX hpar) (hm : H ≤ d s(p.1,p.2)) :
    (∏ p ∈ sourceSkeletonEdges hX hOX hpar, absWeight r d c s(p.1,p.2)) ≤
      P.family.weight d c * min (R ^ 2 / H ^ 2) (globalTail R d P.family.edges) := by
  obtain ⟨Y₀,-,hpY⟩ := mem_biUnion.1 hp
  obtain ⟨hi,hj,-,hij⟩ := mem_graphPairs.1 hpY
  let tail := fun Y : oddComponents X O => globalTail (r (P.root Y)) d
    ((P.family.tree Y).edgeFinset.image (Sym2.map Subtype.val))
  let q := min (r (P.root Y₀) ^ 2 / H ^ 2) (tail Y₀)
  have hRY : ∀ Y : oddComponents X O, r (P.root Y) ≤ R := fun Y => hR _
    (biUnion_subset_biUnion_of_subset_left id
      (subset_of_mem_relComponents (oddComponents_subset O Y.property)) (P.root Y).property)
  have hbound : (∏ p ∈ sourceSkeletonEdges hX hOX hpar, absWeight r d c s(p.1,p.2)) ≤
      ∏ Y : oddComponents X O, P.family.componentWeight d c Y * (if Y = Y₀ then q else tail Y) := by
    rw [source_skeleton_product hX hOX hpar]
    apply prod_le_prod₀ (fun _ _ => prod_nonneg fun _ _ => absWeight_nonneg hr hd hc _)
    intro Y _
    by_cases hY : Y = Y₀
    · subst Y
      simp only [ite_true]
      simpa only [q,OddFamily.componentWeight,SourcePeeling.family,tail,componentEdge,Function.comp_apply,← absWeight_component] using
        SourcePeeling.component_long hX hOX hpar r d c hr hd hc hc1 hpos P Y₀ (em := s((⟨p.1,hi⟩ : Y₀.val.biUnion id), (⟨p.2,hj⟩ : Y₀.val.biUnion id)))
          hij hH ((hRY Y₀).trans hRH) hm
    · rw [ite_eq_right hY]
      simpa only [q,OddFamily.componentWeight,SourcePeeling.family,tail,componentEdge,Function.comp_apply,← absWeight_component] using
        SourcePeeling.component_tail hX hOX hpar r d c hr hd hc hc1 hpos P Y
  rw [prod_mul_distrib,internal_selected_product univ tail (mem_univ Y₀) q] at hbound
  have ht := long_odd_forest_tail univ
    (fun Y : oddComponents X O => (P.family.tree Y).edgeFinset.image (Sym2.map Subtype.val))
    d (fun Y : oddComponents X O => r (P.root Y))
    (R := R) (H := H) (fun Y _ => hr _) (fun Y _ => hRY Y) (mem_univ Y₀)
  exact hbound.trans (mul_le_mul_of_nonneg_left ht (P.family.weight_nonneg d c hc))

end Bounds

end MultipoleBKT.ExpansionK.RouteCases

end
