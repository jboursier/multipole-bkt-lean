/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.Component
public import MultipoleBKT.UpperBound.BoundedUpper.Pointwise

/-!
# Separate odd and even trees for the bounded lower reduction

The proof of Proposition 4.23, (4.74). The odd components determine the groups.
Apply the endpoint half-sum ear argument to each hatted component and retain
a separate even tree on their coarsening. The hatted step is in the proof of Proposition 4.23.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open SetPartition Finset SimpleGraph Hierarchical Multipole Parity Peeling Limits SmallIntegral
open UpperBound.BoundedUpper
open scoped Classical NNReal

/-- The hatted even weight of the written reduction. -/
noncomputable def hatEven (M lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  if MultipoleLinked M lam d e then 1 else ahat d e ^ 2

/-- The spatial and radius factors in the hatted displayed reduction. -/
noncomputable def hatTreeCore (M lam : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id)) (c : ℕ → ℂ × ℂ) : ℝ :=
  jTail c X Xs Ta * (∏ l, radialExceptMax c (Xs l)) *
    (∏ l, ∏ e ∈ (Ta l).edgeFinset, keptE M lam (fun i : (Xs l).biUnion id => c i) e) *
      ∏ e ∈ Tb.edgeFinset, symmLift (fun (i j : (coarsen X (univ.image Xs)).biUnion id) => hatEven M lam (c i) (c j))
        (fun i j => by unfold hatEven; rw [ahat_comm]; exact if_congr Limits.multipoleLinked_comm rfl rfl) e

/-- The hatted tree expression is nonnegative. -/
theorem hatTreeCore_nonneg (M lam : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id)) (c : ℕ → ℂ × ℂ) :
    0 ≤ hatTreeCore M lam X Xs Ta Tb c := by
  unfold hatTreeCore
  refine mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
    (prod_nonneg fun l _ => radialExceptMax_nonneg c _))
    (prod_nonneg fun l _ => prod_nonneg fun e _ => keptE_nonneg _ e))
    (prod_nonneg fun e _ => ?_)
  induction e using Sym2.ind with
  | h i j => simp only [symmLift_mk, hatEven]; split_ifs <;> positivity

/-- The half-sum ear argument on an odd component gives its relative tree.
proof of Proposition 4.23,
using (A.30) in the proof of Lemma A.5, with the actual radii. -/
theorem odd_component_tree {χ : ℂ → ℝ} (hχ : IsMollifier χ) {M lam : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {A : Finset (ℕ × ℕ)} (hA : A ∈ relEulerianPairs X)
    {Y : Finset (Finset ℕ)} (hY : Y ∈ oddComponents X A)
    (c : ℕ → ℂ × ℂ) (hc : ∀ i ∈ Y.biUnion id, 0 < ‖(c i).1 - (c i).2‖) :
    ∃ T : SimpleGraph (Y.biUnion id), IsRelTree Y T ∧
      ∏ p ∈ A ∩ interPairs Y, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2) ≤
        radialExceptMax c Y * ((∏ e ∈ T.edgeFinset, keptE M lam (fun i : Y.biUnion id => c i) e) * compTail c Y T) := by
  have hYX := subset_of_mem_relComponents (oddComponents_subset A hY)
  have hYs := isSubpartition_mono hX hYX
  let G := pairGraph (Y.biUnion id) (A ∩ interPairs Y)
  have hconn := isRelConnected_pairGraph hX (mem_relEulerianPairs.1 hA).1 hY
  have heul : IsRelEulerianConnected Y G := by
    refine ⟨hconn, hconn.1, fun S hS => ?_⟩
    dsimp only [G]
    rw [blockDegree_pairGraph (E := A ∩ interPairs Y) (inter_subset_right.trans interPairs_subset_pairsOn)
      (show S ⊆ Y.biUnion id from subset_biUnion_of_mem id hS), blockDeg_inter_interPairs hX
      (mem_relEulerianPairs.1 hA).1 (oddComponents_subset A hY) hS]
    exact (mem_relEulerianPairs.1 hA).2 S (hYX hS)
  have hcut : CutEven (Sym2.map (Limits.blockOf Y)) G.edgeFinset := by
    have hAY : A ∩ interPairs Y ∈ relEulerianPairs Y := by
      refine mem_relEulerianPairs.2 ⟨inter_subset_right, fun S hS => ?_⟩
      rw [blockDeg_inter_interPairs hX (mem_relEulerianPairs.1 hA).1
        (oddComponents_subset A hY) hS]
      exact (mem_relEulerianPairs.1 hA).2 S (hYX hS)
    exact BoundedLowerEps.cutEven_graphOf hYs
      (inter_subset_right.trans interPairs_subset_pairsOn) hAY
  have hYne : (univ : Finset Y).Nonempty := by
    obtain ⟨S, hS⟩ := nonempty_of_mem_relComponents (oddComponents_subset A hY)
    exact ⟨⟨S, hS⟩, mem_univ _⟩
  obtain ⟨Ŝ, _, hmax⟩ := exists_max_image (univ : Finset Y)
    (fun S => blockRadius hYs (fun i : Y.biUnion id => dipoleLength (c i)) S) hYne
  have hmax' := fun S => hmax S (mem_univ S)
  have hmax'' : ∀ S : Y, blockRad c S ≤ blockRad c Ŝ := by
    intro S
    simpa only [dipoleLength, blockRadius_eq_blockRad] using hmax' S
  have hpos : 0 < blockRad c Ŝ := by
    obtain ⟨i, hi⟩ := hYs.1 Ŝ Ŝ.2
    exact (hc i (subset_biUnion_of_mem id Ŝ.2 hi)).trans_le (le_blockRad c hi)
  let z : Y.biUnion id → ℂ × ℂ := fun i => c i
  obtain ⟨T, hT, ht⟩ := component_bound_of_pair_bounds hχ hlam hM hYs heul hcut z (fun i => hc i i.2)
    (A := oddMaj M lam z) (oddMaj_nonneg z) (C := 1) le_rfl
    (fun i j _ => by
      change (if MultipoleLinked M lam (c i) (c j) then 0 else min 1 (ahat (c i) (c j))) ≤
        1 * hatOdd M lam (c i) (c j)
      unfold hatOdd
      split_ifs <;> simp) hmax'
  simp only [one_pow, one_mul] at ht
  have hp := prod_pairs_eq_prod_edgeFinset (W := Y.biUnion id)
    (inter_subset_right.trans interPairs_subset_pairsOn : A ∩ interPairs Y ⊆ _)
    (fun i j => BoundedLowerEps.oddMajP M lam (c i) (c j))
    (fun i j => BoundedLowerEps.oddMajP_comm M lam (c i) (c j))
  have hprod : ∏ p ∈ A ∩ interPairs Y, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2) =
      ∏ e ∈ G.edgeFinset, oddMaj M lam z e := hp
  dsimp only [z, dipoleLength] at ht
  rw [prod_erase_blockRadius_eq hYs c hmax'' hpos,
    blockRadius_eq_blockRad hYs c Ŝ, blockRad_biUnion_eq c hmax''] at ht
  exact ⟨T, hT, hprod.trans_le ht⟩

/-- The pointwise hatted reduction with separate odd trees and one even
coarse tree. No even edge is doubled. (4.74), proof of Proposition 4.23. -/
theorem majorants_le_hatTree {χ : ℂ → ℝ} (hχ : IsMollifier χ) {M lam : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {E A : Finset (ℕ × ℕ)} (hE : E ∈ relEdgeSets₀ X) (hAE : A ⊆ E)
    (hA : A ∈ relEulerianPairs X) :
    ∃ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), n ≤ (X.biUnion id).card ∧
      (∀ l, Xs l ⊆ X) ∧ (∀ l m, l ≠ m → Disjoint (Xs l) (Xs m)) ∧
      ∃ Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id),
        IsRelTree₀ (coarsen X (univ.image Xs)) Tb ∧
        ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖) →
          ∃ Ta : ∀ l, SimpleGraph ((Xs l).biUnion id), (∀ l, IsRelTree (Xs l) (Ta l)) ∧
            (∏ p ∈ A, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2)) *
                (∏ p ∈ E \ A, BoundedLowerEps.evenMajP M lam (c p.1) (c p.2)) ≤
              hatTreeCore M lam X Xs Ta Tb c := by
  let odd := oddComponents X A
  let e := odd.equivFin
  let Xs : Fin odd.card → Finset (Finset ℕ) := fun l => (e.symm l).1
  have hmem : ∀ l, Xs l ∈ odd := fun l => (e.symm l).2
  have himg : univ.image Xs = odd := by
    ext Y
    simp only [mem_image, mem_univ, true_and]
    exact ⟨by rintro ⟨l, rfl⟩; exact hmem l,
      fun hY => ⟨e ⟨Y, hY⟩, by simp [Xs]⟩⟩
  have hXs : ∀ l, Xs l ⊆ X := fun l =>
    subset_of_mem_relComponents (oddComponents_subset A (hmem l))
  have hdisj : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m) := by
    intro l m hne
    apply disjoint_of_mem_relComponents hX (oddComponents_subset A (hmem l))
      (oddComponents_subset A (hmem m))
    intro heq
    exact hne (e.symm.injective (Subtype.ext heq))
  obtain ⟨Tb, hTb, hTbE⟩ := exists_isRelTree₀_even hX hE hAE himg
  have hn : odd.card ≤ (X.biUnion id).card := by
    apply (card_le_card_biUnion (pairwiseDisjoint_oddComponents hX A)
      (fun Y hY => nonempty_of_mem_relComponents (oddComponents_subset A hY))).trans
    apply (card_le_card (biUnion_subset.2 fun Y hY =>
      subset_of_mem_relComponents (oddComponents_subset A hY))).trans
    exact card_le_card_biUnion hX.2 hX.1
  refine ⟨odd.card, Xs, hn, hXs, hdisj, Tb, hTb, fun c hc => ?_⟩
  have hcomp := fun l => odd_component_tree hχ hlam hM hX hA (hmem l) c
    (fun i hi => hc i (biUnion_subset_biUnion_of_subset_left id (hXs l) hi))
  choose Ta hTa ht using hcomp
  refine ⟨Ta, hTa, ?_⟩
  have hreindex (f : Finset (Finset ℕ) → ℝ) : ∏ Y ∈ odd, f Y = ∏ l, f (Xs l) := by
    rw [← prod_coe_sort odd f]
    exact (Equiv.prod_comp e.symm (fun Y : odd => f Y)).symm
  have hoddprod : ∏ p ∈ A, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2) =
      ∏ l, ∏ p ∈ A ∩ interPairs (Xs l), BoundedLowerEps.oddMajP M lam (c p.1) (c p.2) := by
    rw [prod_eq_prod_oddComponents hX (mem_relEulerianPairs.1 hA).1]
    exact hreindex _
  have hodd : ∏ p ∈ A, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2) ≤
      (∏ l, radialExceptMax c (Xs l)) *
        (∏ l, ∏ e ∈ (Ta l).edgeFinset, keptE M lam (fun i : (Xs l).biUnion id => c i) e) * jTail c X Xs Ta := by
    rw [hoddprod]
    apply (prod_le_prod₀ (fun l _ => prod_nonneg fun p _ =>
      BoundedLowerEps.oddMajP_nonneg _ _ _ _) (fun l _ => ht l)).trans
    simp_rw [prod_mul_distrib]
    have hpos : 0 < blockRad c (X.biUnion id) := by
      obtain ⟨i, hi⟩ := (mem_relEdgeSets₀.1 hE).2.1
      exact (hc i hi).trans_le (le_blockRad c hi)
    have htail := prod_compTail_le_jTail c X Xs hXs Ta hpos
    change (∏ l, radialExceptMax c (Xs l)) *
      ((∏ l, ∏ e ∈ (Ta l).edgeFinset, keptE M lam (fun i : (Xs l).biUnion id => c i) e) *
        ∏ l, compTail c (Xs l) (Ta l)) ≤ _
    have hrad0 : 0 ≤ ∏ l, radialExceptMax c (Xs l) :=
      prod_nonneg fun l _ => radialExceptMax_nonneg c _
    have hkept0 : 0 ≤ ∏ l, ∏ e ∈ (Ta l).edgeFinset,
        keptE M lam (fun i : (Xs l).biUnion id => c i) e :=
      prod_nonneg fun l _ => prod_nonneg fun e _ => keptE_nonneg _ e
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail (mul_nonneg hrad0 hkept0)

  have heven : ∏ p ∈ E \ A, BoundedLowerEps.evenMajP M lam (c p.1) (c p.2) ≤
      ∏ e ∈ Tb.edgeFinset, symmLift (fun (i j : (coarsen X (univ.image Xs)).biUnion id) => hatEven M lam (c i) (c j))
        (fun i j => by unfold hatEven; rw [ahat_comm]; exact if_congr Limits.multipoleLinked_comm rfl rfl) e := by
    have hdrop : ∏ p ∈ E \ A, BoundedLowerEps.evenMajP M lam (c p.1) (c p.2) ≤
        ∏ p ∈ graphPairs Tb, BoundedLowerEps.evenMajP M lam (c p.1) (c p.2) := by
      rw [← prod_sdiff hTbE]
      apply mul_le_of_le_one_left (prod_nonneg fun p _ => BoundedLowerEps.evenMajP_nonneg _ _ _ _)
      apply prod_le_one₀ (fun p _ => BoundedLowerEps.evenMajP_nonneg _ _ _ _)
      intro p _
      unfold BoundedLowerEps.evenMajP
      split_ifs
      · exact le_rfl
      · exact pow_le_one₀ (le_min zero_le_one (ahat_nonneg _ _)) (min_le_left _ _)
    apply hdrop.trans
    rw [prod_graphPairs Tb (fun i j => BoundedLowerEps.evenMajP M lam (c i) (c j))
      (fun i j => BoundedLowerEps.evenMajP_comm M lam (c i) (c j))]
    apply prod_le_prod₀
    · intro a _
      induction a using Sym2.ind with
      | h i j => exact BoundedLowerEps.evenMajP_nonneg _ _ _ _
    · intro a _
      induction a using Sym2.ind with
      | h i j =>
        change BoundedLowerEps.evenMajP M lam (c i) (c j) ≤ hatEven M lam (c i) (c j)
        unfold BoundedLowerEps.evenMajP hatEven
        split_ifs
        · exact le_rfl
        · exact pow_le_pow_left₀ (le_min zero_le_one (ahat_nonneg _ _)) (min_le_right _ _) 2
  have heven0 : 0 ≤ ∏ p ∈ E \ A, BoundedLowerEps.evenMajP M lam (c p.1) (c p.2) :=
    prod_nonneg fun p _ => BoundedLowerEps.evenMajP_nonneg _ _ _ _
  have hodd0 : 0 ≤ (∏ l, radialExceptMax c (Xs l)) *
      (∏ l, ∏ e ∈ (Ta l).edgeFinset, keptE M lam (fun i : (Xs l).biUnion id => c i) e) * jTail c X Xs Ta := by
    exact mul_nonneg (mul_nonneg (prod_nonneg fun l _ => radialExceptMax_nonneg c _)
      (prod_nonneg fun l _ => prod_nonneg fun e _ => keptE_nonneg _ e)) (sq_nonneg _)
  exact (mul_le_mul hodd heven heven0 hodd0).trans_eq (by unfold hatTreeCore; ring)

end MultipoleBKT.LowerBound.RouteBounded

end
