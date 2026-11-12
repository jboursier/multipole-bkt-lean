/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ForestLifting
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.SourceRadius
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.CoreMajorant

/-!
# Component radii on the original label carrier

See Step 3 of
the proof of Lemma A.7. Component block maxima and
maximal component roots are transported to the ambient subpartition before
the two applications of tree ordering. All radii may already be regularized.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ UpperBound.BoundedUpper
open scoped Classical

variable {X Y : Finset (Finset ℕ)}

/-- The inclusion of the labels of a subcollection of multipoles. -/
def componentLabel (hYX : Y ⊆ X) (i : Y.biUnion id) : X.biUnion id :=
  ⟨i, biUnion_subset_biUnion_of_subset_left id hYX i.property⟩

/-- The inclusion of a component's blocks in the ambient subpartition. -/
def componentBlock (hYX : Y ⊆ X) (S : Y) : X := ⟨S, hYX S.property⟩

/-- The block maximum is bounded exactly when every radius in the block is. -/
theorem blockRadius_le_iff (hX : IsSubpartition X) (r : X.biUnion id → ℝ)
    (S : X) (a : ℝ) :
    blockRadius hX r S ≤ a ↔ ∀ i : X.biUnion id, i.val ∈ S.val → r i ≤ a := by
  unfold blockRadius
  rw [sup'_le_iff]
  constructor
  · intro h i hi
    exact h i (mem_filter.2 ⟨mem_univ _, (MultipoleBKT.blockOf_eq_iff hX).2 hi⟩)
  · intro h i hi
    exact h i ((MultipoleBKT.blockOf_eq_iff hX).1 (mem_filter.1 hi).2)

/-- Restriction to a component does not change a block's maximum. -/
theorem component_blockRadius (hX : IsSubpartition X) (hY : IsSubpartition Y)
    (hYX : Y ⊆ X) (r : X.biUnion id → ℝ) (S : Y) :
    blockRadius hY (r ∘ componentLabel hYX) S =
      blockRadius hX r (componentBlock hYX S) := by
  apply le_antisymm
  · rw [blockRadius_le_iff]
    intro i hi
    exact (blockRadius_le_iff hX r (componentBlock hYX S) _).1 le_rfl
      (componentLabel hYX i) hi
  · rw [blockRadius_le_iff]
    intro i hi
    let j : Y.biUnion id := ⟨i, mem_biUnion.2 ⟨S, S.property, hi⟩⟩
    exact (blockRadius_le_iff hY (r ∘ componentLabel hYX) S _).1 le_rfl j hi

/-- A maximal component label supplies the largest ambient block in its component. -/
theorem component_root_max (hX : IsSubpartition X) (hY : IsSubpartition Y)
    (hYX : Y ⊆ X) (r : X.biUnion id → ℝ) (v : Y.biUnion id)
    (hv : ∀ i, r (componentLabel hYX i) ≤ r (componentLabel hYX v)) :
    ∀ S : Y, blockRadius hX r (componentBlock hYX S) ≤
      blockRadius hX r (componentBlock hYX (MultipoleBKT.blockOf hY v)) := by
  intro S
  rw [← component_blockRadius hX hY hYX, ← component_blockRadius hX hY hYX]
  refine ((blockRadius_le_iff hY _ S _).2 (fun i _ => hv i)).trans ?_
  exact le_blockRadius (r ∘ componentLabel hYX) v

/-- Reindex the omitted-root block product onto the ambient component blocks.
The radii are unchanged, including their regularized cores. -/
theorem component_prefactor (hX : IsSubpartition X) (hY : IsSubpartition Y)
    (hYX : Y ⊆ X) (r : X.biUnion id → ℝ) (v : Y.biUnion id) :
    (∏ S ∈ univ.erase (MultipoleBKT.blockOf hY v),
      blockRadius hY (r ∘ componentLabel hYX) S ^ 2) =
    ∏ S ∈ (Y.subtype (· ∈ X)).erase
      (componentBlock hYX (MultipoleBKT.blockOf hY v)), blockRadius hX r S ^ 2 := by
  apply prod_bij (fun S _ => componentBlock hYX S)
  · intro S hS
    exact mem_erase.2 ⟨fun he => (mem_erase.1 hS).1
      (Subtype.ext (congrArg (fun S : X => S.val) he)), by
        simp only [mem_subtype]
        exact S.property⟩
  · intro S _ T _ he
    exact Subtype.ext (congrArg (fun S : X => S.val) he)
  · intro S hS
    have hSY : S.val ∈ Y := by simpa only [mem_subtype] using (mem_erase.1 hS).2
    refine ⟨⟨S.val, hSY⟩, mem_erase.2 ⟨?_, mem_univ _⟩, Subtype.ext rfl⟩
    intro he
    exact (mem_erase.1 hS).1 (Subtype.ext (congrArg (fun S : Y => S.val) he))
  · intro S _
    rw [component_blockRadius hX hY hYX]

/-- The odd prefactor on the dependent component carriers. This is precisely
its radius part in the `OddFamily.weight`. -/
noncomputable def oddPrefactor {O : Finset (ℕ × ℕ)} {hX : IsSubpartition X}
    {hOX : O ⊆ interPairs X} {hpar : IsParityPair X O ∅} {r : ℕ → ℝ}
    (F : RouteCases.OddFamily hX hOX hpar r) : ℝ :=
  ∏ Y : oddComponents X O,
    ∏ S ∈ univ.erase (MultipoleBKT.blockOf
      (RouteCases.source_odd_component_eulerian hX hOX hpar Y.property).1 (F.root Y)),
      blockRadius (RouteCases.source_odd_component_eulerian hX hOX hpar Y.property).1
        (fun i : Y.val.biUnion id => r i) S ^ 2

/-- The radius budget for the entire separate odd family, its actual coarse
even tree and an arbitrary near-tree family. The omitted label is a global
maximum. No change of exponent or radius is made. -/
theorem source_family_radius_allocation {O : Finset (ℕ × ℕ)} (hX : IsSubpartition X)
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)]
    (r : ℕ → ℝ) (hr : ∀ i ∈ X.biUnion id, 0 ≤ r i)
    (F : RouteCases.OddFamily hX hOX hpar r)
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (Q : NearTreeFamily (Limits.blockOf X)) {lam : ℝ} (hlam : 0 < lam) :
    ∃ i₀ : X.biUnion id, (∀ i : X.biUnion id, r i ≤ r i₀) ∧
      oddPrefactor F *
        (∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset,
          edgeMin (fun a => max a lam ^ 2) (fun i : X.biUnion id => r i) e) *
        (∏ e ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val),
          edgeMin (fun a => max a lam ^ 2) (fun i : X.biUnion id => r i) e) ≤
        ∏ i ∈ univ.erase i₀, max (r i) lam ^ 2 := by
  let e := (Fintype.equivFin (oddComponents X O)).symm
  let Xs := fun l => (e l).val
  let Ta := fun l => edgesOf (F.tree (e l))
  have hXs : univ.image Xs = oddComponents X O := by
    ext Y
    constructor
    · intro hY
      obtain ⟨l,-,rfl⟩ := mem_image.1 hY
      exact (e l).property
    · intro hY
      obtain ⟨l,hl⟩ := e.surjective ⟨Y,hY⟩
      exact mem_image.2 ⟨l,mem_univ _,congrArg Subtype.val hl⟩
  have hXsX : ∀ l, Xs l ⊆ X := fun l =>
    subset_of_mem_relComponents (oddComponents_subset O (e l).property)
  have hdis : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l') := by
    intro l l' hne
    exact disjoint_of_mem_relComponents hX (oddComponents_subset O (e l).property)
      (oddComponents_subset O (e l').property) (fun h => hne (e.injective (Subtype.ext h)))
  have hTa : ∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf := fun l =>
    mem_image.2 ⟨F.tree (e l),mem_relTrees.2 (F.tree_spec (e l)).1,rfl⟩
  have hTb' : edgesOf Tb ∈ (relTrees₀ (coarsen X (univ.image Xs))).image edgesOf := by
    rw [hXs]
    exact mem_image.2 ⟨Tb,mem_relTrees₀.2 hTb,rfl⟩
  let hY := fun l => (RouteCases.source_odd_component_eulerian hX hOX hpar (e l).property).1
  let hat := fun l => componentBlock (hXsX l) (MultipoleBKT.blockOf (hY l) (F.root (e l)))
  have hhat : ∀ l, hat l ∈ (Xs l).subtype (· ∈ X) ∧
      ∀ S ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i : X.biUnion id => r i) S ≤
          blockRadius hX (fun i : X.biUnion id => r i) (hat l) := by
    intro l
    refine ⟨by simp only [hat, componentBlock, mem_subtype]; exact
      (MultipoleBKT.blockOf (hY l) (F.root (e l))).property, ?_⟩
    intro S hS
    have hSY : S.val ∈ Xs l := by simpa only [mem_subtype] using hS
    exact component_root_max hX (hY l) (hXsX l) (fun i : X.biUnion id => r i)
      (F.root (e l)) (F.root_max (e l)) ⟨S, hSY⟩
  have hp : oddPrefactor F =
      ∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hat l),
        blockRadius hX (fun i : X.biUnion id => r i) S ^ 2 := by
    unfold oddPrefactor
    symm
    apply Fintype.prod_equiv e
    intro l
    exact (component_prefactor hX (hY l) (hXsX l) (fun i : X.biUnion id => r i) (F.root (e l))).symm
  rw [hp]
  exact source_radius_allocation hX Xs hXsX hdis Ta hTa (edgesOf Tb) hTb'
    (fun i : X.biUnion id => r i) (fun i => hr i i.property) hat hhat
    (fun S => (Q S).val) (fun S => (Q S).property) lam hlam

/-- The regularized radius allocation cancels the extracted largest-radius
square exactly. It includes the cores below lambda on every component. -/
theorem regularized_family_radius_allocation {O : Finset (ℕ × ℕ)}
    (hX : IsSubpartition X) (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅)
    [Nonempty (X.biUnion id)] {lam : ℝ} (hlam : 0 < lam)
    (c : ℕ → ℂ × ℂ)
    (F : RouteCases.OddFamily hX hOX hpar (fun i => rhoD lam (c i)))
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (Q : NearTreeFamily (Limits.blockOf X)) :
    maxRad lam (fun i : X.biUnion id => c i) ^ 2 * oddPrefactor F *
        (∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset,
          minSq lam (fun i : X.biUnion id => c i) e) *
        (∏ e ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val),
          minSq lam (fun i : X.biUnion id => c i) e) ≤
      ∏ i : X.biUnion id, rhoD lam (c i) ^ 2 := by
  obtain ⟨i₀,hmax,halloc⟩ := source_family_radius_allocation hX hOX hpar
    (fun i => rhoD lam (c i)) (fun i _ => (rhoD_pos hlam (c i)).le) F Tb hTb Q hlam
  have hR : maxRad lam (fun i : X.biUnion id => c i) = rhoD lam (c i₀) := by
    apply le_antisymm
    · exact (fold_max_le _).2 ⟨le_max_right _ _,fun i _ => hmax i⟩
    · exact rhoD_le_maxRad lam (fun i : X.biUnion id => c i) i₀
  have he (e : Sym2 (X.biUnion id)) :
      edgeMin (fun a => max a lam ^ 2) (fun i : X.biUnion id => rhoD lam (c i)) e =
      minSq lam (fun i : X.biUnion id => c i) e := by
    induction e using Sym2.ind with
    | h i j =>
      rw [edgeMin_mk,minSq_mk,max_eq_left
        (show lam ≤ min (rhoD lam (c i)) (rhoD lam (c j)) from
          le_min (le_max_right _ _) (le_max_right _ _))]
  have hreg (i : X.biUnion id) : max (rhoD lam (c i)) lam = rhoD lam (c i) :=
    max_eq_left (le_max_right _ _)
  simp_rw [he,hreg] at halloc
  have hm := mul_le_mul_of_nonneg_left halloc (sq_nonneg (rhoD lam (c i₀)))
  rw [mul_prod_erase univ (fun i : X.biUnion id => rhoD lam (c i) ^ 2) (mem_univ i₀)] at hm
  rw [hR]
  convert hm using 1
  ring

end MultipoleBKT.ExpansionK.RouteSpatial

end
