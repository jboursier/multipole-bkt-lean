/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RoutePrufer.Equiv

/-!
# Counting words with prescribed multiplicities

The elementary multinomial count of Prüfer words used in Lemma A.9. This calculation counts words,
independently of trees, by splitting off the first letter.
-/

@[expose] public section

namespace MultipoleBKT.Cayley

universe u

open Finset
open scoped Classical

/-! ### The multinomial recursion -/

section Multinomial

/-- Pascal-type recursion for multinomial coefficients:
`(∑ κ)! / ∏ (κ i)! = ∑_p (∑ κ - 1)! / ∏ ((κ - e_p) i)!`, the sum over `p` with `κ p ≥ 1`. -/
theorem multinomial_eq_sum {W : Type u} [Fintype W] [DecidableEq W] (κ : W → ℕ) (hκ : 1 ≤ ∑ i, κ i) :
    Nat.multinomial univ κ = ∑ p : W, if 1 ≤ κ p then
      Nat.multinomial univ (fun j => κ j - if j = p then 1 else 0) else 0 := by
  set M := ∑ i, κ i with hM
  set P := ∏ i, (κ i).factorial with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => Nat.factorial_pos _
  have key : ∀ p : W, P * (if 1 ≤ κ p then
      Nat.multinomial univ (fun j => κ j - if j = p then 1 else 0) else 0) =
      κ p * (M - 1).factorial := by
    intro p
    by_cases hp : 1 ≤ κ p
    · rw [ite_eq_left hp]
      set κ' : W → ℕ := fun j => κ j - if j = p then 1 else 0 with hκ'
      have hsum : ∑ j, κ' j = M - 1 := by
        have : ∑ j, κ' j = ∑ j, κ j - ∑ j : W, (if j = p then 1 else 0) := by
          refine Finset.sum_tsub_distrib _ fun j _ => ?_
          by_cases h : j = p
          · simp [h, hp]
          · simp [h]
        rw [this]
        simp [hM]
      have hprod : P = κ p * ∏ j, (κ' j).factorial := by
        have h1 : P = (κ p).factorial * ∏ j ∈ univ.erase p, (κ j).factorial :=
          (Finset.mul_prod_erase univ (fun j => (κ j).factorial) (mem_univ p)).symm
        have h2 : ∏ j, (κ' j).factorial =
            (κ' p).factorial * ∏ j ∈ univ.erase p, (κ' j).factorial :=
          (Finset.mul_prod_erase univ (fun j => (κ' j).factorial) (mem_univ p)).symm
        have h3 : ∏ j ∈ univ.erase p, (κ' j).factorial = ∏ j ∈ univ.erase p, (κ j).factorial := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have : j ≠ p := (mem_erase.mp hj).1
          simp [hκ', this]
        have h4 : κ' p = κ p - 1 := by simp [hκ']
        rw [h1, h2, h3, h4, ← mul_assoc, Nat.mul_factorial_pred (by omega)]
      have hspec := Nat.multinomial_spec (univ : Finset W) κ'
      rw [hsum] at hspec
      rw [hprod, mul_assoc, hspec]
    · rw [ite_eq_right hp]
      have : κ p = 0 := by omega
      simp [this]
  have hsumkey : P * (∑ p : W, if 1 ≤ κ p then
      Nat.multinomial univ (fun j => κ j - if j = p then 1 else 0) else 0) = P * Nat.multinomial univ κ := by
    rw [Finset.mul_sum]
    simp_rw [key]
    rw [← Finset.sum_mul]
    have hspec := Nat.multinomial_spec (univ : Finset W) κ
    rw [← hP] at hspec
    rw [hspec, ← hM, Nat.mul_factorial_pred (by omega)]
  exact (Nat.eq_of_mul_eq_mul_left hPpos hsumkey).symm

/-- A zero entry does not change a multinomial coefficient. -/
theorem multinomial_subtype_ne {W : Type u} [Fintype W] (κ : W → ℕ) (v : W) (hκ : κ v = 0) :
    Nat.multinomial (univ : Finset {i // i ≠ v}) (fun j => κ j.1) = Nat.multinomial univ κ := by
  have hP : ∏ i, (κ i).factorial = ∏ j : {i // i ≠ v}, (κ j.1).factorial := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ v, hκ]
    simp
  have hS : ∑ i, κ i = ∑ j : {i // i ≠ v}, κ j.1 := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ v, hκ]
    simp
  have h1 := Nat.multinomial_spec (univ : Finset W) κ
  have h2 := Nat.multinomial_spec (univ : Finset {i // i ≠ v}) (fun j => κ j.1)
  rw [← hP, ← hS] at h2
  have hPpos : 0 < ∏ i, (κ i).factorial := Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact Nat.eq_of_mul_eq_mul_left hPpos (h2.trans h1.symm)

end Multinomial

/-- There are `n! / ∏ i, (k i)!` words with multiplicities `k`. -/
theorem card_words :
    ∀ (n : ℕ) (V : Type u) [Fintype V], Fintype.card V = n + 2 →
      ∀ k : V → ℕ, ∑ i, k i = n →
        Fintype.card (Words n k) = Nat.multinomial univ k := by
  intro n
  induction n with
  | zero =>
    intro V _ hV k hk
    have hk0 : k = 0 := funext fun i => (Finset.sum_eq_zero_iff.mp hk) i (mem_univ i)
    have hcard : Fintype.card (Words 0 k) = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨Fin.elim0, fun i => by simp [occurrences, hk0]⟩, fun c => ?_⟩
      apply Subtype.ext
      exact (funext fun i => Fin.elim0 i)
    rw [hcard, hk0]
    simp [Nat.multinomial]
  | succ n ih =>
    intro V _ hV k hk
    obtain ⟨v, hv⟩ := exists_zero_entry k (by omega)
    have hcard : Fintype.card {i // i ≠ v} = n + 2 := by
      have := card_subtype_ne_add_one v
      omega
    have hsum : ∑ j : {i // i ≠ v}, k j.1 = n + 1 := by
      have := Fintype.sum_eq_add_sum_subtype_ne k v
      omega
    rw [Fintype.card_congr (wordStep (n := n) hv), Fintype.card_sigma]
    have hterm : ∀ p : Parents k v,
        Fintype.card (Words n (decAt k v p.1)) = Nat.multinomial univ (decAt k v p.1) := by
      intro p
      exact ih _ hcard _ (by rw [sum_decAt hv p, hk]; omega)
    simp_rw [hterm]
    calc ∑ p : Parents k v, Nat.multinomial univ (decAt k v p.1)
        = ∑ p : {i // i ≠ v}, if 1 ≤ k p.1 then
            Nat.multinomial univ (decAt k v p) else 0 := by
          simpa only [Finset.sum_filter] using
            (Finset.sum_subtype (univ.filter fun p : {i // i ≠ v} => 1 ≤ k p.1)
              (by simp) (fun p => Nat.multinomial univ (decAt k v p))).symm
      _ = Nat.multinomial univ k :=
        (multinomial_eq_sum (fun j : {i // i ≠ v} => k j.1) (by omega)).symm.trans
          (multinomial_subtype_ne k v hv)

end MultipoleBKT.Cayley

end
