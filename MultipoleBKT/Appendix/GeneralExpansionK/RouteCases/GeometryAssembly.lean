/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.FamilyAssembly
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SelectedTerms
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.BondError
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.LongEdge

/-!
# Geometric products for the complete five-case assembly

See Lemma A.7, Step 2 of the proof of Lemma A.7. The connecting even tree may use near bonds. Those edges
have weight one on the retained near support and are included before dropping
surplus factors. Odd weights are enlarged to the cutoff endpoint radii.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Peeling SimpleGraph Multipole Hierarchical UpperBound.BoundedUpper

variable {ι : Type*} [LinearOrder ι]

omit [LinearOrder ι] in
/-- Enlarging the endpoint radii gives the geometric odd weight used by the
original skeletons, with the far indicator retained. -/
theorem mixedOdd_le_absWeight {lam M : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    mixedOddWeight M lam c e ≤
      absWeight (fun i => rhoD lam (c i)) (paperDistE c) (farInd M lam c) e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    have hf : farInd M lam c s(i,j) = if MultipoleLinked M lam (c i) (c j) then 0 else 1 := rfl
    by_cases hn : MultipoleLinked M lam (c i) (c j)
    · simp only [mixedOddWeight, absWeight, hf, ite_eq_left hn, mul_zero, le_refl]
    · have hd := hlam.trans (far_facts hlam hM hn).1
      have hp := div_mul_max_le (norm_nonneg ((c i).1 - (c i).2)) (norm_nonneg ((c j).1 - (c j).2))
        (le_max_left ‖(c i).1 - (c i).2‖ lam) (le_max_left ‖(c j).1 - (c j).2‖ lam) hd
      simpa only [mixedOddWeight, absWeight, hf, ite_eq_right hn, mul_one, radProd, radMax,
        symmLift_mk, paperDistE, Sym2.lift_mk, rhoD, max_comm, ahatE, ahat] using hp

omit [LinearOrder ι] in
/-- The even weight is enlarged only by adding the near branch of weight one. -/
theorem mixedEven_le_paperEven {lam M : ℝ} (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    mixedEvenWeight M lam c e ≤ paperEvenE M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    change ahat (c i) (c j) ^ 2 * (if MultipoleLinked M lam (c i) (c j) then 0 else 1) ≤
      if MultipoleLinked M lam (c i) (c j) then 1 else ahat (c i) (c j) ^ 2
    split_ifs <;> simp only [mul_zero, mul_one] <;> norm_num

/-- Products of natural original functions transport to the actual subtype
integrand without extending a configuration by default values. -/
theorem source_product {U : Finset ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ pairsOn U)
    (f : Sym2 ℕ → ℝ) :
    (∏ e ∈ symOf U S, f (Sym2.map Subtype.val e)) = ∏ p ∈ S, f s(p.1,p.2) := by
  symm
  exact prod_symOf hS (fun p => f s(p.1,p.2)) (fun e => f (Sym2.map Subtype.val e)) (fun _ _ _ => rfl)

/-- Deleting a marked unordered edge commutes with the original product. -/
theorem source_product_erase {U : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ pairsOn U) (f : Sym2 ℕ → ℝ) (i j : U) :
    (∏ e ∈ (symOf U S).erase s(i,j), f (Sym2.map Subtype.val e)) =
      ∏ p ∈ S, if s(p.1,p.2) = s(i.val,j.val) then 1 else f s(p.1,p.2) := by
  classical
  rw [← source_product hS (fun e => if e = s(i.val,j.val) then 1 else f e)]
  have heq : ∀ e : Sym2 U, Sym2.map Subtype.val e = s(i.val,j.val) ↔ e = s(i,j) := by
    intro e
    change Sym2.map Subtype.val e = Sym2.map Subtype.val s(i,j) ↔ _
    exact (Sym2.map.injective Subtype.val_injective).eq_iff
  simp_rw [heq]
  rw [prod_ite, prod_const_one, one_mul]
  apply prod_congr
  · ext e
    simp only [mem_erase, mem_filter, and_comm]
  · intro _ _
    rfl

/-- Internal deletion of surplus even edges, with all near edges supplied by
the common support. No disjointness of the original near/far sets is required. -/
theorem internal_even_drop_near {ε : Type*} [DecidableEq ε]
    (S N T : Finset ε) (hT : T ⊆ N ∪ S) (b : ε → ℝ)
    (hb0 : ∀ e, 0 ≤ b e) (hb1 : ∀ e, b e ≤ 1) (hN : ∀ e ∈ N, b e = 1) :
    (∏ e ∈ S, b e) ≤ ∏ e ∈ T, b e := by
  have hi : T ∩ S ⊆ S := inter_subset_right
  have heq : (∏ e ∈ T, b e) = ∏ e ∈ T ∩ S, b e := by
    symm
    apply prod_subset inter_subset_left
    intro e he hn
    have hnot : e ∉ S := fun hs => hn (mem_inter.2 ⟨he,hs⟩)
    exact hN e ((mem_union.1 (hT he)).resolve_right hnot)
  rw [heq, ← prod_sdiff hi]
  exact mul_le_of_le_one_left (prod_nonneg fun _ _ => hb0 _)
    (prod_le_one₀ (fun _ _ => hb0 _) (fun _ _ => hb1 _))

/-- Every odd factor is at most one on far support. -/
theorem source_odd_le_one {O : Finset (ℕ × ℕ)} (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2)) :
    ∀ p ∈ O, absWeight r d c s(p.1,p.2) ≤ 1 :=
  fun p hp => absWeight_le_one_of_far hr hd hc hc1 (hfar p hp)

open scoped Classical in
/-- The ordinary full odd product is first reduced to the selected skeletons. -/
theorem source_odd_skeleton_drop {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {O : Finset (ℕ × ℕ)} (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅)
    (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2)) :
    (∏ p ∈ O, absWeight r d c s(p.1,p.2)) ≤
      ∏ p ∈ sourceSkeletonEdges hX hOX hpar, absWeight r d c s(p.1,p.2) := by
  rw [← prod_sdiff (sourceSkeletonEdges_subset hX hOX hpar)]
  exact mul_le_of_le_one_left (prod_nonneg fun _ _ => absWeight_nonneg hr hd hc _)
    (prod_le_one₀ (fun _ _ => absWeight_nonneg hr hd hc _) (fun p hp =>
      source_odd_le_one r d c hr hd hc hc1 hfar p (mem_sdiff.1 hp).1))

end MultipoleBKT.ExpansionK.RouteCases

end
