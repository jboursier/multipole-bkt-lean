/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Count
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Group enumeration by sizes

(4.124) and
(4.125) in the proof of Lemma 4.59. Choose the union of the groups, then
partition it into ordered groups with prescribed sizes. Positive size
profiles are counted by stars and bars.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open Finset
open scoped Classical

/-- Ordered disjoint subsets with prescribed sizes. -/
noncomputable def orderedGroups {α : Type*} (U : Finset α) {n : ℕ} (m : Fin n → ℕ) :
    Finset (Fin n → Finset α) :=
  (Fintype.piFinset fun _ : Fin n => U.powerset).filter fun G =>
    (∀ i, (G i).card = m i) ∧ ∀ i j, i ≠ j → Disjoint (G i) (G j)

theorem mem_orderedGroups {α : Type*} {U : Finset α} {n : ℕ}
    {m : Fin n → ℕ} {G : Fin n → Finset α} : G ∈ orderedGroups U m ↔
      (∀ i, G i ⊆ U) ∧ (∀ i, (G i).card = m i) ∧ ∀ i j, i ≠ j → Disjoint (G i) (G j) := by
  simp only [orderedGroups, mem_filter, Fintype.mem_piFinset, mem_powerset]

/-- Split off the first group. This is the multinomial counting recursion. -/
theorem card_orderedGroups_succ {α : Type*} (U : Finset α) {n : ℕ} (m : Fin (n + 1) → ℕ) :
    (orderedGroups U m).card =
      ∑ A ∈ U.powersetCard (m 0), (orderedGroups (U \ A) (Fin.tail m)).card := by
  rw [← card_sigma]
  apply card_bij (fun G _ => (⟨G 0, Fin.tail G⟩ : Σ _A : Finset α, Fin n → Finset α))
  · intro G hG
    obtain ⟨hGU, hGc, hGd⟩ := mem_orderedGroups.mp hG
    rw [mem_sigma]
    refine ⟨mem_powersetCard.mpr ⟨hGU 0, hGc 0⟩, mem_orderedGroups.mpr ⟨?_, ?_, ?_⟩⟩
    · intro i x hx
      exact mem_sdiff.mpr ⟨hGU i.succ hx,
        fun h0 => (disjoint_left.mp (hGd i.succ 0 (Fin.succ_ne_zero i))) hx h0⟩
    · exact fun i => hGc i.succ
    · exact fun i j hij => hGd i.succ j.succ (fun h => hij (Fin.succ_injective _ h))
  · intro G _ H _ h
    have h0 : G 0 = H 0 := congrArg Sigma.fst h
    have ht : Fin.tail G = Fin.tail H := congrArg
      (fun p : Σ _A : Finset α, Fin n → Finset α => p.2) h
    exact funext fun i => Fin.cases h0 (congrFun ht) i
  · rintro ⟨A, G⟩ h
    obtain ⟨hA, hG⟩ := mem_sigma.mp h
    obtain ⟨hAU, hAc⟩ := mem_powersetCard.mp hA
    obtain ⟨hGU, hGc, hGd⟩ := mem_orderedGroups.mp hG
    refine ⟨Fin.cons A G, mem_orderedGroups.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i
      refine Fin.cases hAU (fun j => (hGU j).trans sdiff_subset) i
    · intro i
      exact Fin.cases hAc hGc i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          apply disjoint_left.mpr
          intro x hx hxG
          exact (mem_sdiff.mp (hGU j hxG)).2 hx
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          apply disjoint_left.mpr
          intro x hxG hx
          exact (mem_sdiff.mp (hGU i hxG)).2 hx
        | succ j => exact hGd i j (fun h => hij (congrArg Fin.succ h))
    · simp only [Fin.cons_zero, Fin.tail_cons]

/-- The exact factorial count before division. Unused elements form the final class. -/
theorem card_orderedGroups_mul_factorials {α : Type*} :
    ∀ (n : ℕ) (U : Finset α) (m : Fin n → ℕ), (∑ i, m i) ≤ U.card →
      (orderedGroups U m).card * (U.card - ∑ i, m i).factorial *
        (∏ i, (m i).factorial) = U.card.factorial := by
  intro n
  induction n with
  | zero =>
    intro U m _
    have hG : orderedGroups U m = {Fin.elim0} := by
      ext G
      simp only [mem_orderedGroups, mem_singleton]
      constructor
      · intro _
        exact funext fun i => Fin.elim0 i
      · intro _
        exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    simp [hG]
  | succ n ih =>
    intro U m hm
    rw [card_orderedGroups_succ]
    have hm0 : m 0 ≤ U.card := by rw [Fin.sum_univ_succ] at hm; omega
    have htail : ∑ i, Fin.tail m i ≤ U.card - m 0 := by
      rw [Fin.sum_univ_succ] at hm
      exact Nat.le_sub_of_add_le' hm
    have hterm (A : Finset α) (hA : A ∈ U.powersetCard (m 0)) :
        (orderedGroups (U \ A) (Fin.tail m)).card * (U.card - ∑ i, m i).factorial *
          (∏ i, (Fin.tail m i).factorial) = (U.card - m 0).factorial := by
      obtain ⟨hAU, hAc⟩ := mem_powersetCard.mp hA
      have hc : (U \ A).card = U.card - m 0 := by rw [card_sdiff_of_subset hAU, hAc]
      have hi := ih (U \ A) (Fin.tail m) (hc ▸ htail)
      rw [hc] at hi
      rw [show U.card - ∑ i, m i = U.card - m 0 - ∑ i, Fin.tail m i by
        rw [Fin.sum_univ_succ]
        simp only [Fin.tail]
        omega]
      exact hi
    rw [Fin.prod_univ_succ]
    have heq : (∑ A ∈ U.powersetCard (m 0), (orderedGroups (U \ A) (Fin.tail m)).card) *
        (U.card - ∑ i, m i).factorial * ((m 0).factorial * ∏ i, (Fin.tail m i).factorial) =
        (m 0).factorial * ∑ A ∈ U.powersetCard (m 0),
          (orderedGroups (U \ A) (Fin.tail m)).card * (U.card - ∑ i, m i).factorial *
            (∏ i, (Fin.tail m i).factorial) := by
      simp only [mul_sum, sum_mul]
      apply sum_congr rfl
      intro A _
      ring
    change _ * _ * ((m 0).factorial * ∏ i, (Fin.tail m i).factorial) = _
    rw [heq, sum_congr rfl hterm, sum_const, card_powersetCard, nsmul_eq_mul]
    have h := Nat.choose_mul_factorial_mul_factorial hm0
    nlinarith

/-- Choose the union in `binom(q,s)` ways and split it by a multinomial.
This is the displayed counting coefficient in (4.124). -/
theorem card_orderedGroups {α : Type*} {n : ℕ} (U : Finset α) (m : Fin n → ℕ)
    (hm : ∑ i, m i ≤ U.card) :
    (orderedGroups U m).card = U.card.choose (∑ i, m i) * Nat.multinomial univ m := by
  have hc := card_orderedGroups_mul_factorials n U m hm
  have hchoose := Nat.choose_mul_factorial_mul_factorial hm
  have hmult := Nat.multinomial_spec univ m
  have hpos : 0 < (U.card - ∑ i, m i).factorial * ∏ i, (m i).factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    _ = U.card.factorial := by nlinarith [hc]
    _ = _ := by rw [← hchoose, ← hmult]; ring

/-- Positive ordered size profiles with total size `s`. -/
noncomputable def positiveProfiles (n s : ℕ) : Finset (Fin n → ℕ) :=
  (piAntidiag univ s).filter fun m => ∀ i, 0 < m i

theorem mem_positiveProfiles {n s : ℕ} {m : Fin n → ℕ} :
    m ∈ positiveProfiles n s ↔ (∑ i, m i = s) ∧ ∀ i, 0 < m i := by
  simp only [positiveProfiles, mem_filter, mem_piAntidiag, mem_univ, implies_true, and_true]

/-- Stars and bars in exactly the form used in Step 2 of the written proof. -/
theorem card_positiveProfiles {n s : ℕ} (hn : 1 ≤ n) (hns : n ≤ s) :
    (positiveProfiles n s).card = (s - 1).choose (n - 1) := by
  have hcard : (positiveProfiles n s).card =
      ((univ : Finset (Fin n)).finsuppAntidiag (s - n)).card := by
    apply card_bij (fun m _ => Finsupp.equivFunOnFinite.symm (fun i => m i - 1))
    · intro m hm
      obtain ⟨hm, hpos⟩ := mem_positiveProfiles.mp hm
      rw [mem_finsuppAntidiag']
      refine ⟨?_, subset_univ _⟩
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      change ∑ i, (m i - 1) = s - n
      rw [sum_tsub_distrib _ (fun i _ => hpos i), hm]
      simp
    · intro m hm m' hm' he
      have hmpos := (mem_positiveProfiles.mp hm).2
      have hm'pos := (mem_positiveProfiles.mp hm').2
      apply funext
      intro i
      have h := congrArg (fun f : Fin n →₀ ℕ => f i) he
      change m i - 1 = m' i - 1 at h
      have := hmpos i
      have := hm'pos i
      omega
    · intro f hf
      have hs := (mem_finsuppAntidiag'.mp hf).1
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hs
      refine ⟨fun i => f i + 1, mem_positiveProfiles.mpr ⟨?_, fun _ => by omega⟩, ?_⟩
      · rw [sum_add_distrib, hs]
        simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        omega
      · apply Finsupp.ext
        intro i
        change f i + 1 - 1 = f i
        omega
  rw [hcard, card_finsuppAntidiag_nat_eq_choose, card_univ, Fintype.card_fin,
    show n + (s - n) - 1 = s - 1 by omega]
  have he : s - n = (s - 1) - (n - 1) := by omega
  rw [he, Nat.choose_symm (by omega : n - 1 ≤ s - 1)]

/-- The zero-group term has exactly one empty profile. -/
theorem positiveProfiles_zero (s : ℕ) :
    positiveProfiles 0 s = if s = 0 then {Fin.elim0} else ∅ := by
  ext m
  simp only [mem_positiveProfiles]
  by_cases hs : s = 0
  · simp only [hs, ite_true, mem_singleton]
    exact ⟨fun _ => funext fun i => Fin.elim0 i, fun _ => ⟨rfl, fun i => Fin.elim0 i⟩⟩
  · simp only [hs, ite_false, notMem_empty, iff_false, not_and]
    exact fun h => (hs h.symm).elim

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
