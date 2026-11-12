/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.MarkedFamilyAssembly
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.GeometryAssembly

/-!
# Joining cases B and D after the selected-factor bound

See (A.57) and the
conclusion after (A.60). The split is made against the
fixed minimal skeletons. The retained case uses the prescribed strict ear.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Peeling Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

open scoped Classical in
/-- A mark on any original odd edge has the complete family bound. The proof
splits into the surplus-edge case B and the prescribed strict-ear case D. -/
theorem source_odd_marked_family (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2))
    {p : ℕ × ℕ} (hp : p ∈ O) {R : ℝ} (hR : ∀ i ∈ X.biUnion id, r i ≤ R) :
    ∃ F : OddFamily hX hOX hpar r,
      r p.1 * r p.2 * (∏ q ∈ O, if s(q.1,q.2) = s(p.1,p.2) then 1 else
        absWeight r d c s(q.1,q.2)) ≤ R ^ 2 * F.weight d c := by
  by_cases hK : p ∈ sourceSkeletonEdges hX hOX hpar
  · obtain ⟨Y,-,hpY⟩ := mem_biUnion.1 hK
    obtain ⟨hi,hj,-,hij⟩ := mem_graphPairs.1 hpY
    obtain ⟨F,-,hb⟩ := source_marked_family_reduced hX hOX hpar r d c hr hd hc hc1 hfar Y hij hR
    exact ⟨F,hb⟩
  · obtain ⟨F,hF⟩ := source_skeleton_family hX hOX hpar r d c hr hd hc hc1
    have hdrop := source_surplus_skeleton hX hOX hpar r d c hr hd hc hc1 hfar hK
    have hEq : (∏ q ∈ O, if s(q.1,q.2) = s(p.1,p.2) then 1 else absWeight r d c s(q.1,q.2)) =
        ∏ q ∈ O.erase p, absWeight r d c s(q.1,q.2) := by
      rw [← mul_prod_erase O _ hp]
      simp only [ite_true, one_mul]
      apply prod_congr rfl
      intro q hq
      apply ite_eq_right
      intro heq
      have hqord := (mem_pairsOn.1 (interPairs_subset_pairsOn (hOX (mem_of_mem_erase hq)))).2.2
      have hpord := (mem_pairsOn.1 (interPairs_subset_pairsOn (hOX hp))).2.2
      rcases Sym2.eq_iff.1 heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact (mem_erase.1 hq).1 (Prod.ext h1 h2)
      · omega
    have hpV := mem_pairsOn.1 (interPairs_subset_pairsOn (hOX hp))
    have hrad : r p.1 * r p.2 ≤ R ^ 2 := by
      rw [sq]
      exact mul_le_mul (hR p.1 hpV.1) (hR p.2 hpV.2.1) (hr _) ((hr _).trans (hR p.1 hpV.1))
    refine ⟨F,?_⟩
    rw [hEq]
    exact mul_le_mul hrad (hdrop.trans hF)
      (prod_nonneg fun _ _ => absWeight_nonneg hr hd hc _) (sq_nonneg R)

/-- Nonnegativity of a complete ordinary component family. -/
theorem OddFamily.weight_nonneg {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} (F : OddFamily hX hOX hpar r)
    (d c : Sym2 ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) : 0 ≤ F.weight d c := by
  classical
  apply prod_nonneg
  intro Y _
  exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
    (prod_nonneg fun _ _ => keptWeight_nonneg (fun e => hc _) _)

end MultipoleBKT.ExpansionK.RouteCases

end
