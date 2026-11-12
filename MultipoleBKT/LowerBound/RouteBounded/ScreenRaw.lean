/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.GroupedParity
public import MultipoleBKT.LowerBound.RouteBounded.RawBounds
public import MultipoleBKT.LowerBound.RouteBounded.ScreenTrees

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

/-- Remark 4.30 bounds the even bond together with its linked part. -/
theorem evenMult_le_absEven {β M lam ε₀ R C : ℝ}
    {w : ℂ × ℂ → ℂ × ℂ → ℝ} {d e : ℂ × ℂ}
    (h : |evenBondUnlinked β w M lam d e| +
      (if MultipoleLinked M lam d e then 1 else 0) ≤ C * absEvenWeight M lam ε₀ R d e) :
    |evenBondMult β w M lam d e| ≤ C * absEvenWeight M lam ε₀ R d e := by
  unfold evenBondMult
  apply (abs_sub _ _).trans
  have hi : |if MultipoleLinked M lam d e then (1 : ℝ) else 0| =
      if MultipoleLinked M lam d e then 1 else 0 := by split_ifs <;> norm_num
  rwa [hi]

/-- A grouped term is bounded by the product of odd and even majorants,
with a coefficient depending only on the total number of pairs. -/
theorem abs_eulerTerm_le_screenMajorants {β M lam ε₀ R : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l))
    {F A : Finset (ℕ × ℕ)} (hF : F ⊆ interPairs (coarsen X (univ.image Xs)))
    (hA : A ⊆ univ.biUnion Es) {C : ℝ} (hC : 1 ≤ C) {k : ℕ}
    (hEk : (univ.biUnion Es ∪ F).card ≤ k * k) (c : ℕ → ℂ × ℂ)
    (hb : ∀ p ∈ univ.biUnion Es ∪ F,
      |oddBondUnlinked β w M lam (c p.1) (c p.2)| ≤ C * absOddWeight M lam ε₀ R (c p.1) (c p.2) ∧
      |evenBondMult β w M lam (c p.1) (c p.2)| ≤ C * absEvenWeight M lam ε₀ R (c p.1) (c p.2)) :
    |eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F c| ≤
      C ^ (k * k) * ((∏ p ∈ A, absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
        ∏ p ∈ (univ.biUnion Es ∪ F) \ A, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) := by
  have hAE : A ⊆ univ.biUnion Es ∪ F := hA.trans subset_union_left
  have ho : ∏ p ∈ A, |oddBondUnlinked β w M lam (c p.1) (c p.2)| ≤
      C ^ A.card * ∏ p ∈ A, absOddWeight M lam ε₀ R (c p.1) (c p.2) := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p hp => (hb p (hAE hp)).1)
  have he : ∏ p ∈ (univ.biUnion Es ∪ F) \ A, |evenBondMult β w M lam (c p.1) (c p.2)| ≤
      C ^ ((univ.biUnion Es ∪ F) \ A).card *
        ∏ p ∈ (univ.biUnion Es ∪ F) \ A, absEvenWeight M lam ε₀ R (c p.1) (c p.2) := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p hp => (hb p (sdiff_subset hp)).2)
  have hpow : C ^ A.card * C ^ ((univ.biUnion Es ∪ F) \ A).card ≤ C ^ (k * k) := by
    rw [← pow_add, Nat.add_comm, card_sdiff_add_card_eq_card hAE]
    exact pow_le_pow_right₀ hC hEk
  apply (abs_eulerTerm_le_bonds hEs hF hA c).trans
  have hright0 : 0 ≤ C ^ A.card * ∏ p ∈ A, absOddWeight M lam ε₀ R (c p.1) (c p.2) :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hC) _)
      (prod_nonneg fun p _ => absOddWeight_nonneg _ _ _ _ _ _)
  apply (mul_le_mul ho he (prod_nonneg fun p _ => abs_nonneg _) hright0).trans
  have hprod0 : 0 ≤ (∏ p ∈ A, absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
      ∏ p ∈ (univ.biUnion Es ∪ F) \ A, absEvenWeight M lam ε₀ R (c p.1) (c p.2) :=
    mul_nonneg (prod_nonneg fun p _ => absOddWeight_nonneg _ _ _ _ _ _)
      (prod_nonneg fun p _ => absEvenWeight_nonneg _ _ _ _ _ _)
  have h := mul_le_mul_of_nonneg_right hpow hprod0
  calc _ = (C ^ A.card * C ^ ((univ.biUnion Es ∪ F) \ A).card) *
      ((∏ p ∈ A, absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
        ∏ p ∈ (univ.biUnion Es ∪ F) \ A, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) := by ring
    _ ≤ _ := h

end MultipoleBKT.LowerBound.RouteBounded

end
