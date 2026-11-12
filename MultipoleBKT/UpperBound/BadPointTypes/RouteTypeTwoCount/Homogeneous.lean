/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Profiles

/-!
# Equal-size partitions and the divisibility split

The paper: Lemma 5.42. The empty ground set has one partition. A partition into
`k`-element blocks forces divisibility before any factorial is cancelled.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeTwoCount

open Finset SetPartition PropFiveFortyFive

variable {α : Type*} [DecidableEq α]

/-- Partitions with every block of cardinality `k`. -/
noncomputable def homogeneous (U : Finset α) (k : ℕ) : Finset (Finset (Finset α)) := by
  classical
  exact (partitions U).filter fun π => ∀ S ∈ π, S.card = k

theorem mem_homogeneous {U : Finset α} {k : ℕ} {π : Finset (Finset α)} :
    π ∈ homogeneous U k ↔ π ∈ partitions U ∧ ∀ S ∈ π, S.card = k := by
  classical
  simp only [homogeneous, mem_filter]

/-- An equal-size partition has exactly `|U|/k` blocks. -/
theorem homogeneous_size {U : Finset α} {k : ℕ} {π : Finset (Finset α)}
    (hπ : π ∈ homogeneous U k) : k * π.card = U.card := by
  classical
  obtain ⟨hπ, hk⟩ := mem_filter.1 hπ
  rw [← sum_sizes hπ, sum_congr rfl hk, sum_const, smul_eq_mul, mul_comm]

/-- The nondivisible case is empty. -/
theorem homogeneous_eq_empty_of_not_dvd (U : Finset α) (k : ℕ) (h : ¬ k ∣ U.card) :
    homogeneous U k = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.2
  intro π hπ
  exact h ⟨π.card, (homogeneous_size hπ).symm⟩

/-- The empty family contributes one, for every block size. -/
theorem homogeneous_empty (k : ℕ) : homogeneous (∅ : Finset α) k = {∅} := by
  classical
  simp [homogeneous, partitions_empty]

/-- The literal equal-size count, stated before division: when `|U| = kq`. -/
theorem card_homogeneous_mul (U : Finset α) {k q : ℕ} (hk : 1 ≤ k)
    (hsize : k * q = U.card) :
    (homogeneous U k).card * (k.factorial ^ q * q.factorial) = U.card.factorial := by
  classical
  let j : Fin k := ⟨k - 1, by omega⟩
  let m : Fin k → ℕ := Pi.single j q
  have hj : (j : ℕ) + 1 = k := by dsimp [j]; omega
  have hm (i : Fin k) : m i = if i = j then q else 0 := by
    simp [m, Pi.single_apply]
  have hmass : ∑ i : Fin k, ((i : ℕ) + 1) * m i = U.card := by
    simp_rw [hm]
    simp [mul_ite, hj, hsize]
  have he : homogeneous U k = (partitions U).filter
      (fun π => (∀ S ∈ π, S.card ≤ k) ∧ blockCount k π = m) := by
    ext π
    simp only [homogeneous, mem_filter]
    constructor
    · rintro ⟨hπ, hblocks⟩
      refine ⟨hπ, fun S hS => (hblocks S hS).le, ?_⟩
      have hcard : π.card = q := Nat.eq_of_mul_eq_mul_left hk (by
        rw [homogeneous_size (show π ∈ homogeneous U k from mem_filter.2 ⟨hπ, hblocks⟩), hsize])
      funext i
      rw [blockCount, hm]
      by_cases hi : i = j
      · subst i
        simp only [hj, ite_true]
        rw [filter_true_of_mem hblocks, hcard]
      · have hne : k ≠ (i : ℕ) + 1 := by
          intro h
          exact hi (Fin.ext (by omega))
        rw [ite_eq_right hi, filter_eq_empty_iff.2 (fun S hS => by rw [hblocks S hS]; exact hne), card_empty]
    · rintro ⟨hπ, hle, hcount⟩
      refine ⟨hπ, fun S hS => ?_⟩
      have hs := (block_sizes hπ S hS).1
      let i : Fin k := ⟨S.card - 1, by have := hle S hS; omega⟩
      have hi : (i : ℕ) + 1 = S.card := by dsimp [i]; omega
      by_contra hne
      have hij : i ≠ j := by intro h; rw [h, hj] at hi; exact hne hi.symm
      have hz : (π.filter fun T => T.card = (i : ℕ) + 1).card = 0 := by
        change blockCount k π i = 0
        rw [hcount, hm, ite_eq_right hij]
      exact (card_eq_zero.1 hz ▸ mem_filter.2 ⟨hS, hi.symm⟩ : S ∈ (∅ : Finset (Finset α)))
        |> notMem_empty S
  have hw : profileWeight m = k.factorial ^ q * q.factorial := by
    unfold profileWeight
    rw [prod_eq_single j]
    · rw [hm, ite_eq_left rfl, hj]
    · intro i _ hi
      rw [hm, ite_eq_right hi]
      simp
    · simp
  rw [he, ← hw]
  exact card_partitions_filter_mul k U m hmass

/-- Equal-size partitions have the written factorial quotient. -/
theorem card_homogeneous (U : Finset α) {k q : ℕ} (hk : 1 ≤ k)
    (hsize : k * q = U.card) :
    ((homogeneous U k).card : ℝ) = U.card.factorial / (k.factorial ^ q * q.factorial) := by
  rw [eq_div_iff (by positivity)]
  exact_mod_cast card_homogeneous_mul U hk hsize

/-- A constant block integral contributes one power for each of the `|U|/k` blocks. -/
theorem sum_homogeneous (U : Finset α) {k q : ℕ} (hk : 1 ≤ k)
    (hsize : k * q = U.card) (B : ℝ) :
    ∑ π ∈ homogeneous U k, ∏ _S ∈ π, B =
      U.card.factorial / (k.factorial ^ q * q.factorial) * B ^ q := by
  classical
  have hc : ∀ π ∈ homogeneous U k, π.card = q := fun π hπ =>
    Nat.eq_of_mul_eq_mul_left hk (by rw [homogeneous_size hπ, hsize])
  simp_rw [prod_const]
  rw [sum_congr rfl (fun π hπ => congrArg (B ^ ·) (hc π hπ)), sum_const, nsmul_eq_mul,
    card_homogeneous U hk hsize]

end MultipoleBKT.BadPointTypes.RouteTypeTwoCount

end
