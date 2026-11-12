/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.SourceRadii
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.MarkedAllocation

/-!
# The marked-even radius budget on the dependent component family

See (A.62) and Step 3 of the proof of Lemma A.7. Apply the two-sided
ordering on the coarse tree to the actual component prefactor.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ UpperBound.BoundedUpper
open scoped Classical

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- The actual marked-even original budget. Both endpoint squares remain
until the marked coarse edge has been deleted and its two sides ordered. -/
theorem source_family_marked_radius_allocation (hX : IsSubpartition X)
    (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)]
    (r : ℕ → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hreg : ∀ i ∈ X.biUnion id, lam ≤ r i)
    (F : RouteCases.OddFamily hX hOX hpar r)
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (Q : NearTreeFamily (Limits.blockOf X)) {i j : X.biUnion id}
    (hmark : s(i,j) ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset) :
    oddPrefactor F * (r i ^ 2 * r j ^ 2) *
      (∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset.erase s(i,j),
        edgeMin (fun a => max a lam ^ 2) (fun i : X.biUnion id => r i) e) *
      (∏ e ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val),
        edgeMin (fun a => max a lam ^ 2) (fun i : X.biUnion id => r i) e) ≤
      ∏ v : X.biUnion id, r v ^ 2 := by
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
  obtain ⟨hG,hAG,hAc,-,hconn,hcard⟩ := trees_structure hX hXsX hdis hTa hTb'
  obtain ⟨root,hroot,hradius,hmax⟩ := exists_block_radius_roots hX (fun i : X.biUnion id => r i)
  have hhatmax : ∀ l S, S ∈ (Xs l).subtype (· ∈ X) →
      r (root S) ≤ r (root (hat l)) := by
    intro l S hS
    rw [hradius,hradius]
    exact (hhat l).2 S hS
  have halloc := grouped_marked_radius_allocation (Limits.blockOf X) root hroot
    (fun l => (Xs l).subtype (· ∈ X)) hG
    (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset)
    (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset hAG hAc hconn hcard hat
    (fun l => (hhat l).1) (fun i : X.biUnion id => r i) hmax hhatmax
    (fun S => (Q S).val) (fun S => (Q S).property) hlam hmark
  have hrootreg (S : X) : max (r (root S)) lam = r (root S) :=
    max_eq_left (hreg _ (root S).property)
  simp_rw [hrootreg,hradius] at halloc
  have hmaxreg (v : X.biUnion id) : max (r v) lam = r v := max_eq_left (hreg _ v.property)
  simp_rw [hmaxreg] at halloc
  rw [hp]
  exact halloc

end MultipoleBKT.ExpansionK.RouteSpatial

end
