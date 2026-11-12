/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.Component
public import MultipoleBKT.UpperBound.BoundedUpper.Pointwise

/-!
# Spatially truncated odd and even trees for the lower reduction

The proof of Proposition 4.23, (4.74). The odd components determine the groups.
Peel each component and retain a separate even tree on their coarsening.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open SetPartition Finset SimpleGraph Hierarchical Multipole Parity Peeling Limits SmallIntegral
open UpperBound.BoundedUpper
open scoped Classical NNReal

/-- The absolute even weight is bounded by one. -/
theorem absEvenWeight_le_one {M lam : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (ε₀ R : ℝ) (d e : ℂ × ℂ) : absEvenWeight M lam ε₀ R d e ≤ 1 := by
  have ha := absOddWeight_le_one' (ε₀ := ε₀) (R := R) hM hlam d e
  have ha0 := absOddWeight_nonneg M lam ε₀ R d e
  unfold absEvenWeight
  by_cases hl : MultipoleLinked M lam d e
  · have hz : absOddWeight M lam ε₀ R d e = 0 := by
      unfold absOddWeight
      rw [ite_eq_left hl, mul_zero, zero_mul]
    rw [hz, ite_eq_left hl]
    norm_num
  · rw [ite_eq_right hl, add_zero]
    exact pow_le_one₀ ha0 ha

/-- Peeling an odd component of the majorant gives its relative tree.
proof of Proposition 4.23. -/
theorem screen_component_tree {M lam ε₀ R : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {A : Finset (ℕ × ℕ)} (hA : A ∈ relEulerianPairs X)
    {Y : Finset (Finset ℕ)} (hY : Y ∈ oddComponents X A)
    (c : ℕ → ℂ × ℂ) (hc : ∀ i ∈ Y.biUnion id, 0 < ‖(c i).1 - (c i).2‖) :
    ∃ T : SimpleGraph (Y.biUnion id), IsRelTree Y T ∧
      ∏ p ∈ A ∩ interPairs Y, absOddWeight M lam ε₀ R (c p.1) (c p.2) ≤
        radialExceptMax c Y * ((∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * compTail c Y T) := by
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
  let aw := absWeight (fun i => dipoleLength (z i)) (dipoleDistOn z) (absIndicator M lam ε₀ R z)
  have ha0 : ∀ e, 0 ≤ aw e := absWeight_nonneg (fun i => norm_nonneg _)
    (dipoleDistOn_nonneg z) (absIndicator_nonneg M lam ε₀ R z)
  have ha1 : ∀ e ∈ G.edgeSet, aw e ≤ 1 := by
    intro e _
    induction e using Sym2.ind with
    | h i j =>
      rw [show aw s(i, j) = absOddWeight M lam ε₀ R (c i) (c j) from absWeight_dipole M lam ε₀ R z i j]
      exact absOddWeight_le_one' hM hlam _ _
  obtain ⟨T, hT, ht⟩ := euler_component_bound hYs heul (fun i => norm_nonneg _)
    (dipoleDistOn_nonneg z) (absIndicator_nonneg M lam ε₀ R z)
    (absIndicator_le_one M lam ε₀ R z) ha0 (C₁ := 1) le_rfl
    (fun e _ => by change aw e ≤ 1 * aw e; rw [one_mul]) ha1 hmax'
  simp only [one_pow, one_mul] at ht
  have hp := prod_pairs_eq_prod_edgeFinset (W := Y.biUnion id)
    (inter_subset_right.trans interPairs_subset_pairsOn : A ∩ interPairs Y ⊆ _)
    (fun i j => absOddWeight M lam ε₀ R (c i) (c j))
    (fun i j => absOddWeight_comm M lam ε₀ R (c i) (c j))
  have hprod : ∏ p ∈ A ∩ interPairs Y, absOddWeight M lam ε₀ R (c p.1) (c p.2) =
      ∏ e ∈ G.edgeFinset, aw e := by
    apply hp.trans
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with
    | h i j => exact (absWeight_dipole M lam ε₀ R z i j).symm
  dsimp only [z, dipoleLength] at ht
  rw [prod_erase_blockRadius_eq hYs c hmax'' hpos,
    blockRadius_eq_blockRad hYs c Ŝ, blockRad_biUnion_eq c hmax''] at ht
  exact ⟨T, hT, hprod.trans_le ht⟩

/-- The pointwise screened reduction with separate odd trees and one even
coarse tree. No even edge is doubled. (4.74), proof of Proposition 4.23. -/
theorem majorants_le_screenTree {M lam ε₀ R : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {E A : Finset (ℕ × ℕ)} (hE : E ∈ relEdgeSets₀ X) (hAE : A ⊆ E)
    (hA : A ∈ relEulerianPairs X) :
    ∃ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), n ≤ (X.biUnion id).card ∧
      (∀ l, Xs l ⊆ X) ∧ (∀ l m, l ≠ m → Disjoint (Xs l) (Xs m)) ∧
      ∃ Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id),
        IsRelTree₀ (coarsen X (univ.image Xs)) Tb ∧
        ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖) →
          ∃ Ta : ∀ l, SimpleGraph ((Xs l).biUnion id), (∀ l, IsRelTree (Xs l) (Ta l)) ∧
            (∏ p ∈ A, absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
                (∏ p ∈ E \ A, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) ≤
              jIntegrand M lam ε₀ R X Xs Ta Tb c := by
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
  have hcomp := fun l => screen_component_tree (ε₀ := ε₀) (R := R) hlam hM hX hA (hmem l) c
    (fun i hi => hc i (biUnion_subset_biUnion_of_subset_left id (hXs l) hi))
  choose Ta hTa ht using hcomp
  refine ⟨Ta, hTa, ?_⟩
  have hreindex (f : Finset (Finset ℕ) → ℝ) : ∏ Y ∈ odd, f Y = ∏ l, f (Xs l) := by
    rw [← prod_coe_sort odd f]
    exact (Equiv.prod_comp e.symm (fun Y : odd => f Y)).symm
  have hoddprod : ∏ p ∈ A, absOddWeight M lam ε₀ R (c p.1) (c p.2) =
      ∏ l, ∏ p ∈ A ∩ interPairs (Xs l), absOddWeight M lam ε₀ R (c p.1) (c p.2) := by
    rw [prod_eq_prod_oddComponents hX (mem_relEulerianPairs.1 hA).1]
    exact hreindex _
  have hodd : ∏ p ∈ A, absOddWeight M lam ε₀ R (c p.1) (c p.2) ≤
      (∏ l, radialExceptMax c (Xs l)) *
        (∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e) * jTail c X Xs Ta := by
    rw [hoddprod]
    apply (prod_le_prod₀ (fun l _ => prod_nonneg fun p _ =>
      absOddWeight_nonneg _ _ _ _ _ _) (fun l _ => ht l)).trans
    simp_rw [prod_mul_distrib]
    have hpos : 0 < blockRad c (X.biUnion id) := by
      obtain ⟨i, hi⟩ := (mem_relEdgeSets₀.1 hE).2.1
      exact (hc i hi).trans_le (le_blockRad c hi)
    have htail := prod_compTail_le_jTail c X Xs hXs Ta hpos
    change (∏ l, radialExceptMax c (Xs l)) *
      ((∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e) *
        ∏ l, compTail c (Xs l) (Ta l)) ≤ _
    have hrad0 : 0 ≤ ∏ l, radialExceptMax c (Xs l) :=
      prod_nonneg fun l _ => radialExceptMax_nonneg c _
    have hkept0 : 0 ≤ ∏ l, ∏ e ∈ (Ta l).edgeFinset,
        keptLift M lam ε₀ R c e :=
      prod_nonneg fun l _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail (mul_nonneg hrad0 hkept0)

  have heven : ∏ p ∈ E \ A, absEvenWeight M lam ε₀ R (c p.1) (c p.2) ≤
      ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e := by
    have hdrop : ∏ p ∈ E \ A, absEvenWeight M lam ε₀ R (c p.1) (c p.2) ≤
        ∏ p ∈ graphPairs Tb, absEvenWeight M lam ε₀ R (c p.1) (c p.2) := by
      rw [← prod_sdiff hTbE]
      apply mul_le_of_le_one_left (prod_nonneg fun p _ => absEvenWeight_nonneg _ _ _ _ _ _)
      apply prod_le_one₀ (fun p _ => absEvenWeight_nonneg _ _ _ _ _ _)
      intro p _
      exact absEvenWeight_le_one hlam hM ε₀ R _ _
    exact hdrop.trans_eq (prod_graphPairs Tb (fun i j => absEvenWeight M lam ε₀ R (c i) (c j))
      (fun i j => absEvenWeight_comm M lam ε₀ R (c i) (c j)))
  have heven0 : 0 ≤ ∏ p ∈ E \ A, absEvenWeight M lam ε₀ R (c p.1) (c p.2) :=
    prod_nonneg fun p _ => absEvenWeight_nonneg _ _ _ _ _ _
  have hodd0 : 0 ≤ (∏ l, radialExceptMax c (Xs l)) *
      (∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e) * jTail c X Xs Ta := by
    exact mul_nonneg (mul_nonneg (prod_nonneg fun l _ => radialExceptMax_nonneg c _)
      (prod_nonneg fun l _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e)) (sq_nonneg _)
  exact (mul_le_mul hodd heven heven0 hodd0).trans_eq (by unfold jIntegrand; ring)

end MultipoleBKT.LowerBound.RouteBounded

end
