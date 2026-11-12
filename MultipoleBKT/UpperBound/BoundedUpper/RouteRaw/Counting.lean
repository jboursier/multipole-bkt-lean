/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.NonEmptyMarks.Compare

/-!
# Finite budgets for the nested marked expansion

The paper: Proposition 5.18. For bounded `|V_X|`, all the displayed sums can be
bounded by a constant times their largest term. The constants here count
the finite choices explicitly.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open Finset Multipole Hierarchical Parity
open scoped Classical

/-- A finite sum of absolute values with an explicit cardinal budget. -/
theorem abs_sum_le_budget {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {C Q : ℝ} (hcard : (s.card : ℝ) ≤ C) (hQ : 0 ≤ Q)
    (hf : ∀ i ∈ s, |f i| ≤ Q) : |∑ i ∈ s, f i| ≤ C * Q := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_card_nsmul _ _ _ hf).trans
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard hQ

/-- Edge families are subsets of the available inter-block pairs. -/
theorem card_relEdgeSets_le {X : Finset (Finset ℕ)} {k : ℕ}
    (hk : (X.biUnion id).card ≤ k) : (relEdgeSets X).card ≤ 2 ^ (k * k) := by
  have hp : (interPairs X).card ≤ k * k :=
    (card_le_card interPairs_subset_pairsOn).trans
      ((card_pairsOn_le _).trans (Nat.mul_le_mul hk hk))
  apply (card_le_card (s := relEdgeSets X) (t := (interPairs X).powerset) _).trans
    ((card_powerset _).le.trans (Nat.pow_le_pow_right (by norm_num) hp))
  intro E hE
  exact mem_powerset.2 (mem_relEdgeSets.1 hE).1

/-- The connected separation edge families obey the same budget. -/
theorem card_relEdgeSets₀_le {X : Finset (Finset ℕ)} {k : ℕ}
    (hk : (X.biUnion id).card ≤ k) : (relEdgeSets₀ X).card ≤ 2 ^ (k * k) := by
  have hp : (interPairs X).card ≤ k * k :=
    (card_le_card interPairs_subset_pairsOn).trans
      ((card_pairsOn_le _).trans (Nat.mul_le_mul hk hk))
  apply (card_le_card (s := relEdgeSets₀ X) (t := (interPairs X).powerset) _).trans
    ((card_powerset _).le.trans (Nat.pow_le_pow_right (by norm_num) hp))
  intro E hE
  exact mem_powerset.2 (mem_relEdgeSets₀.1 hE).1

/-- The tuple of Mayer groups has at most `2^(k*k)` choices. -/
theorem card_group_tuples_le {X : Finset (Finset ℕ)} {n k : ℕ}
    (hX : X.card ≤ k) (hn : n ≤ k) :
    ((Fintype.piFinset fun _ : Fin n => X.powerset).filter
      (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j))).card ≤ 2 ^ (k * k) := by
  apply (card_filter_le _ _).trans
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, card_powerset, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hX hn)

/-- One connected Mayer edge family is chosen in every group. -/
theorem card_edge_tuples_le {X : Finset (Finset ℕ)} {n k : ℕ}
    (hk : (X.biUnion id).card ≤ k) (hn : n ≤ k)
    (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X) :
    (Fintype.piFinset fun l => relEdgeSets (Xs l)).card ≤ 2 ^ (k * k * k) := by
  rw [Fintype.card_piFinset]
  calc ∏ l, (relEdgeSets (Xs l)).card ≤ ∏ _l : Fin n, 2 ^ (k * k) := by
        apply prod_le_prod
        intro l _
        exact card_relEdgeSets_le ((card_le_card
          (biUnion_subset_biUnion_of_subset_left _ (hXs l))).trans hk)
    _ = 2 ^ (k * k * n) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hn)

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
