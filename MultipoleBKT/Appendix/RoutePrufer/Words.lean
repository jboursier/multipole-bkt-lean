/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RoutePrufer.TreeStep
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Prüfer words with prescribed multiplicities

The word side of Prüfer's bijection in Lemma A.9.
The multiplicity of a label is its degree minus one. Deleting the first letter
lowers exactly that multiplicity and leaves the selected absent label absent.
-/

@[expose] public section

namespace MultipoleBKT.Cayley

universe u

open Finset
open scoped Classical

variable {V : Type u} {n : ℕ}

/-- The number of occurrences of a label in a word. -/
noncomputable def occurrences (c : Fin n → V) (i : V) : ℕ :=
  ∑ j, if c j = i then 1 else 0

theorem occurrences_map {W : Type*} (g : V → W) (hg : Function.Injective g)
    (c : Fin n → V) (i : V) :
    occurrences (fun j => g (c j)) (g i) = occurrences c i := by
  simp only [occurrences, hg.eq_iff]

theorem occurrences_zero_iff (c : Fin n → V) (i : V) :
    occurrences c i = 0 ↔ ∀ j, c j ≠ i := by
  simp [occurrences]

theorem occurrences_self_pos (c : Fin n → V) (j : Fin n) : 1 ≤ occurrences c (c j) := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
    Nat.zero_le (if c i = c j then 1 else 0)) (mem_univ j)
  simpa only [occurrences, ite_true] using h

theorem sum_occurrences [Fintype V] (c : Fin n → V) : ∑ i, occurrences c i = n := by
  unfold occurrences
  rw [Finset.sum_comm]
  simp

theorem occurrences_succ (c : Fin (n + 1) → V) (i : V) :
    occurrences c i = (if c 0 = i then 1 else 0) + occurrences (fun j => c j.succ) i := by
  exact Fin.sum_univ_succ _

/-- Words in which label `i` occurs `k i` times. -/
abbrev Words (n : ℕ) (k : V → ℕ) := {c : Fin n → V // ∀ i, occurrences c i = k i}

variable [Fintype V] {k : V → ℕ} {v : V}

/-- The first letter is an allowed neighbour of any absent label. -/
noncomputable def wordHead (hk : k v = 0) (c : Words (n + 1) k) : Parents k v :=
  ⟨⟨c.1 0, (occurrences_zero_iff c.1 v).mp ((c.2 v).trans hk) 0⟩,
    (occurrences_self_pos c.1 0).trans_eq (c.2 _)⟩

/-- The tail, now viewed on the vertex set without the absent label. -/
noncomputable def wordTail (hk : k v = 0) (c : Words (n + 1) k) :
    Words n (decAt k v (wordHead hk c).1) := by
  refine ⟨fun j => ⟨c.1 j.succ,
    (occurrences_zero_iff c.1 v).mp ((c.2 v).trans hk) j.succ⟩, fun i => ?_⟩
  have h := c.2 i.1
  rw [occurrences_succ] at h
  have hm := occurrences_map (Subtype.val : {i // i ≠ v} → V) Subtype.val_injective
    (fun j : Fin n => (⟨c.1 j.succ,
      (occurrences_zero_iff c.1 v).mp ((c.2 v).trans hk) j.succ⟩ : {i // i ≠ v})) i
  rw [hm] at h
  unfold decAt
  have heq : c.1 0 = i.1 ↔ i = (wordHead hk c).1 := by
    constructor
    · intro h
      exact Subtype.ext h.symm
    · intro h
      exact (congrArg Subtype.val h).symm
  split_ifs with hi
  · rw [ite_eq_left (heq.mpr hi)] at h
    omega
  · rw [ite_eq_right (heq.not.mpr hi)] at h
    omega

/-- Prepending the recorded neighbour is inverse to taking the tail. -/
noncomputable def wordCons (hk : k v = 0) (p : Parents k v)
    (c : Words n (decAt k v p.1)) : Words (n + 1) k := by
  refine ⟨Fin.cons p.1.1 (fun j => (c.1 j).1), fun i => ?_⟩
  rw [occurrences_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases hi : i = v
  · subst i
    rw [ite_eq_right p.1.2, hk]
    simp only [zero_add, occurrences_zero_iff]
    exact fun j => (c.1 j).2
  · let i' : {i // i ≠ v} := ⟨i, hi⟩
    have h := c.2 i'
    rw [← occurrences_map Subtype.val Subtype.val_injective c.1 i'] at h
    change occurrences (fun j => (c.1 j).1) i = k i - if i' = p.1 then 1 else 0 at h
    rw [h]
    have heq : p.1.1 = i ↔ i' = p.1 := by
      constructor
      · intro h
        exact Subtype.ext h.symm
      · intro h
        exact (congrArg Subtype.val h).symm
    by_cases hp : i' = p.1
    · rw [ite_eq_left hp, ite_eq_left (heq.mpr hp)]
      have hpos : 1 ≤ k i := by simpa only [← congrArg Subtype.val hp] using p.2
      omega
    · rw [ite_eq_right hp, ite_eq_right (heq.not.mpr hp), Nat.sub_zero, zero_add]

/-- Splitting a Prüfer word into its first letter and its tail. -/
noncomputable def wordStep (hk : k v = 0) :
    Words (n + 1) k ≃ (Σ p : Parents k v, Words n (decAt k v p.1)) where
  toFun c := ⟨wordHead hk c, wordTail hk c⟩
  invFun Q := wordCons hk Q.1 Q.2
  left_inv c := by
    apply Subtype.ext
    exact Fin.cons_self_tail c.1
  right_inv Q := by
    obtain ⟨p, c⟩ := Q
    have hp : wordHead hk (wordCons hk p c) = p := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    apply Sigma.ext hp
    apply heq_of_eq
    apply Subtype.ext
    rfl

end MultipoleBKT.Cayley

end
