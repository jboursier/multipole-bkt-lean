/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.FamilyAssembly

/-!
# The case-D family with its screening gain

See the conclusion after
(A.60). The prescribed marked component is multiplied
with every ordinary component. Its maximal block radius is bounded by the
global radius only after this multiplication.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Peeling Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

open scoped Classical in
/-- Case D on the full odd family with the marked maximal radius extracted.
The marked tree still omits the prescribed base-cycle edge. -/
theorem source_marked_family_reduced (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2))
    (Y₀ : oddComponents X O) {x y : Y₀.val.biUnion id}
    (hxy : (sourceOddSkeleton hX hOX hpar Y₀).Adj x y)
    {R : ℝ} (hR : ∀ i ∈ X.biUnion id, r i ≤ R) :
    ∃ F : OddFamily hX hOX hpar r,
      s(x,y) ∉ (F.tree Y₀).edgeSet ∧
      r x * r y * (∏ p ∈ O, if s(p.1,p.2) = s(x.val,y.val) then 1 else
        absWeight r d c s(p.1,p.2)) ≤ R ^ 2 * F.weight d c := by
  obtain ⟨T₀,v,T,⟨hT₀,hTK₀,hm⟩,hs,hb⟩ :=
    source_marked_family hX hOX hpar r d c hr hd hc hc1 hfar Y₀ hxy
  let T' := Function.update T Y₀ T₀
  let F : OddFamily hX hOX hpar r :=
    { root := v
      tree := T'
      tree_spec := by
        intro Y
        by_cases h : Y = Y₀
        · subst Y
          simpa only [T', Function.update_self] using And.intro hT₀ hTK₀
        · simpa only [T', Function.update_of_ne h] using And.intro (hs Y).1 (hs Y).2.1
      root_max := fun Y => (hs Y).2.2 }
  let hY := (source_odd_component_eulerian hX hOX hpar Y₀.property).1
  let S₀ := MultipoleBKT.blockOf hY (v Y₀)
  let ρ := blockRadius hY (fun i : Y₀.val.biUnion id => r i)
  have hρR : ρ S₀ ≤ R := by
    apply sup'_le
    intro i _
    exact hR i (biUnion_subset_biUnion_of_subset_left id
      (subset_of_mem_relComponents (oddComponents_subset O Y₀.property)) i.property)
  have hρ0 : 0 ≤ ρ S₀ := (hr (v Y₀)).trans (le_blockRadius (fun i : Y₀.val.biUnion id => r i) (v Y₀))
  have hF0 : 0 ≤ F.weight d c := by
    apply prod_nonneg
    intro Y _
    exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
      (prod_nonneg fun _ _ => keptWeight_nonneg (fun e => hc _) _)
  have heq :
      ((∏ S : Y₀.val, ρ S ^ 2) * ∏ e ∈ T₀.edgeFinset, keptWeight (componentEdge d) (componentEdge c) e) *
      (∏ Y ∈ univ.erase Y₀,
        (∏ S ∈ univ.erase (MultipoleBKT.blockOf
          (source_odd_component_eulerian hX hOX hpar Y.property).1 (v Y)),
          blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
            (fun i : Y.val.biUnion id => r i) S ^ 2) *
          ∏ e ∈ (T Y).edgeFinset, keptWeight (componentEdge d) (componentEdge c) e) =
      ρ S₀ ^ 2 * F.weight d c := by
    unfold OddFamily.weight
    rw [← mul_prod_erase univ _ (mem_univ Y₀)]
    have hothers : (∏ Y ∈ univ.erase Y₀,
        (∏ S ∈ univ.erase (MultipoleBKT.blockOf
          (source_odd_component_eulerian hX hOX hpar Y.property).1 (F.root Y)),
          blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
            (fun i : Y.val.biUnion id => r i) S ^ 2) *
          ∏ e ∈ (F.tree Y).edgeFinset, keptWeight (componentEdge d) (componentEdge c) e) =
      (∏ Y ∈ univ.erase Y₀,
        (∏ S ∈ univ.erase (MultipoleBKT.blockOf
          (source_odd_component_eulerian hX hOX hpar Y.property).1 (v Y)),
          blockRadius (source_odd_component_eulerian hX hOX hpar Y.property).1
            (fun i : Y.val.biUnion id => r i) S ^ 2) *
          ∏ e ∈ (T Y).edgeFinset, keptWeight (componentEdge d) (componentEdge c) e) := by
      apply prod_congr rfl
      intro Y hY'
      change _ * (∏ e ∈ (Function.update T Y₀ T₀ Y).edgeFinset, _) = _
      rw [Function.update_of_ne (mem_erase.1 hY').1]
    rw [hothers]
    dsimp only [F, T']
    have he0 : (Function.update T Y₀ T₀ Y₀).edgeFinset = T₀.edgeFinset := by
      ext e
      simp only [mem_edgeFinset, Function.update_self]
    rw [he0]
    rw [← mul_prod_erase univ (fun S : Y₀.val => ρ S ^ 2) (mem_univ S₀)]
    dsimp only [S₀,ρ,hY]
    ring
  refine ⟨F, by simpa only [F,T',Function.update_self] using hm, hb.trans ?_⟩
  rw [heq]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ0 hρR 2) hF0

end MultipoleBKT.ExpansionK.RouteCases

end
