/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.GroupedParity
public import MultipoleBKT.LowerBound.RouteBounded.HatTrees
public import MultipoleBKT.UpperBound.NonEmptyMarks.Compare

/-!
# Pair majorants for a retained grouped term

Proposition 4.23,
(4.73). Keep the original separation indicators through parity,
then compare odd bonds and even bonds separately with their absolute weights.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical Multipole Parity SetPartition
open UpperBound.BoundedUpper UpperBound.NonEmptyMarks
open scoped Classical

/-- An even unlinked bond and the linked indicator are both controlled by
the even compact bond. This is only an algebraic comparison of one term. -/
theorem even_pair_comparison (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (d e : ℂ × ℂ) :
    |evenBondUnlinked β w M lam d e| ≤ |evenBondMult β w M lam d e| ∧
      (if MultipoleLinked M lam d e then (1 : ℝ) else 0) ≤ |evenBondMult β w M lam d e| := by
  unfold evenBondMult
  by_cases h : MultipoleLinked M lam d e
  · rw [evenBondUnlinked_of_linked h, ite_eq_left h]
    norm_num
  · rw [ite_eq_right h, sub_zero]
    exact ⟨le_rfl, abs_nonneg _⟩

/-- Internal pair comparison for a grouped Eulerian term. The separation
factors are used to put the odd and even bonds on `𝓑ᶜ`, before the
separate odd-component and even-tree estimates are applied. -/
theorem abs_eulerTerm_le_bonds {β M lam : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} {Es : Fin n → Finset (ℕ × ℕ)}
    (hEs : ∀ l, Es l ⊆ interPairs (Xs l)) {F A : Finset (ℕ × ℕ)}
    (hF : F ⊆ interPairs (coarsen X (univ.image Xs))) (hA : A ⊆ univ.biUnion Es)
    (c : ℕ → ℂ × ℂ) :
    |eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F c| ≤
      (∏ p ∈ A, |oddBondUnlinked β w M lam (c p.1) (c p.2)|) *
        ∏ p ∈ (univ.biUnion Es ∪ F) \ A, |evenBondMult β w M lam (c p.1) (c p.2)| := by
  let I := univ.biUnion fun l => interPairs (Xs l)
  have hEI : univ.biUnion Es ⊆ I := biUnion_mono fun l _ => hEs l
  have hd := disjoint_biUnion_F hEs hF
  have hsplit : (univ.biUnion Es ∪ F) \ A = (univ.biUnion Es \ A) ∪ F := by
    rw [union_sdiff_distrib, sdiff_eq_left.2 (disjoint_of_subset_left hA hd).symm]
  have hidem := prod_odd_even_mul_eq_eulerTerm (β := β) (w := w) (M := M) (lam := lam) (E₂ := univ.biUnion Es \ A)
    (hA.trans hEI) (sdiff_subset.trans hEI) F c
  rw [← hidem, abs_mul, abs_mul, abs_prod, abs_prod, abs_mul, abs_prod, abs_prod]
  have hsep : ∏ p ∈ I, |if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1| ≤ 1 :=
    prod_le_one₀ (fun p _ => abs_nonneg _) (fun p _ => by split_ifs <;> norm_num)
  have hnear : ∏ p ∈ F, |-(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0)| ≤
      ∏ p ∈ F, |evenBondMult β w M lam (c p.1) (c p.2)| := by
    apply prod_le_prod₀ (fun p _ => abs_nonneg _)
    intro p _
    have heq : |-(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0)| =
        if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0 := by split_ifs <;> norm_num
    rw [heq]
    exact (even_pair_comparison β w M lam _ _).2
  have heven : ∏ p ∈ univ.biUnion Es \ A, |evenBondUnlinked β w M lam (c p.1) (c p.2)| ≤
      ∏ p ∈ univ.biUnion Es \ A, |evenBondMult β w M lam (c p.1) (c p.2)| :=
    prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p _ => (even_pair_comparison β w M lam _ _).1)
  rw [hsplit, prod_union (disjoint_of_subset_left sdiff_subset hd)]
  have hodd0 : 0 ≤ ∏ p ∈ A, |oddBondUnlinked β w M lam (c p.1) (c p.2)| :=
    prod_nonneg fun p _ => abs_nonneg _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hodd0
  have h1 := mul_le_mul heven
    (mul_le_mul hsep hnear (prod_nonneg fun p _ => abs_nonneg _ ) zero_le_one)
    (mul_nonneg (prod_nonneg fun p _ => abs_nonneg _) (prod_nonneg fun p _ => abs_nonneg _))
    (prod_nonneg fun p _ => abs_nonneg _)
  simpa only [one_mul, mul_assoc] using h1

/-- A grouped term is bounded by the product of odd and even majorants,
with a coefficient depending only on the total number of pairs. -/
theorem abs_eulerTerm_le_majorants {β M lam : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l))
    {F A : Finset (ℕ × ℕ)} (hF : F ⊆ interPairs (coarsen X (univ.image Xs)))
    (hA : A ⊆ univ.biUnion Es) {C : ℝ} (hC : 1 ≤ C) {k : ℕ}
    (hEk : (univ.biUnion Es ∪ F).card ≤ k * k) (c : ℕ → ℂ × ℂ)
    (hb : ∀ p ∈ univ.biUnion Es ∪ F,
      |oddBondUnlinked β w M lam (c p.1) (c p.2)| ≤ C * BoundedLowerEps.oddMajP M lam (c p.1) (c p.2) ∧
      |evenBondMult β w M lam (c p.1) (c p.2)| ≤ C * BoundedLowerEps.evenMajP M lam (c p.1) (c p.2)) :
    |eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F c| ≤
      C ^ (k * k) * ((∏ p ∈ A, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2)) *
        ∏ p ∈ (univ.biUnion Es ∪ F) \ A, BoundedLowerEps.evenMajP M lam (c p.1) (c p.2)) := by
  have hAE : A ⊆ univ.biUnion Es ∪ F := hA.trans subset_union_left
  have ho : ∏ p ∈ A, |oddBondUnlinked β w M lam (c p.1) (c p.2)| ≤
      C ^ A.card * ∏ p ∈ A, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2) := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p hp => (hb p (hAE hp)).1)
  have he : ∏ p ∈ (univ.biUnion Es ∪ F) \ A, |evenBondMult β w M lam (c p.1) (c p.2)| ≤
      C ^ ((univ.biUnion Es ∪ F) \ A).card *
        ∏ p ∈ (univ.biUnion Es ∪ F) \ A, BoundedLowerEps.evenMajP M lam (c p.1) (c p.2) := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p hp => (hb p (sdiff_subset hp)).2)
  have hpow : C ^ A.card * C ^ ((univ.biUnion Es ∪ F) \ A).card ≤ C ^ (k * k) := by
    rw [← pow_add, Nat.add_comm, card_sdiff_add_card_eq_card hAE]
    exact pow_le_pow_right₀ hC hEk
  apply (abs_eulerTerm_le_bonds hEs hF hA c).trans
  have hright0 : 0 ≤ C ^ A.card * ∏ p ∈ A, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2) :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hC) _)
      (prod_nonneg fun p _ => BoundedLowerEps.oddMajP_nonneg _ _ _ _)
  apply (mul_le_mul ho he (prod_nonneg fun p _ => abs_nonneg _) hright0).trans
  have hprod0 : 0 ≤ (∏ p ∈ A, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2)) *
      ∏ p ∈ (univ.biUnion Es ∪ F) \ A, BoundedLowerEps.evenMajP M lam (c p.1) (c p.2) :=
    mul_nonneg (prod_nonneg fun p _ => BoundedLowerEps.oddMajP_nonneg _ _ _ _)
      (prod_nonneg fun p _ => BoundedLowerEps.evenMajP_nonneg _ _ _ _)
  have h := mul_le_mul_of_nonneg_right hpow hprod0
  calc _ = (C ^ A.card * C ^ ((univ.biUnion Es ∪ F) \ A).card) *
      ((∏ p ∈ A, BoundedLowerEps.oddMajP M lam (c p.1) (c p.2)) *
        ∏ p ∈ (univ.biUnion Es ∪ F) \ A, BoundedLowerEps.evenMajP M lam (c p.1) (c p.2)) := by ring
    _ ≤ _ := h

end MultipoleBKT.LowerBound.RouteBounded

end
