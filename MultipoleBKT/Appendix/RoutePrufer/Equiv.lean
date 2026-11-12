/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RoutePrufer.Words
public import Mathlib.Data.Finset.Max

/-!
# Prüfer encoding and decoding with prescribed degrees

The bijection used in Lemma A.9.
At each step remove the least leaf and record its neighbour. Decode by taking the least
label absent from the word, decoding its tail, and attaching that label to the first letter.
Two remaining labels form the last edge and have empty code.
-/

@[expose] public section

namespace MultipoleBKT.Cayley

universe u

open SimpleGraph Finset
open scoped Classical

variable {V : Type u} [Fintype V]

/-- A multiplicity sequence whose sum is smaller than the number of labels has a zero. -/
theorem exists_zero_entry (k : V → ℕ) (h : ∑ i, k i < Fintype.card V) : ∃ v, k v = 0 := by
  by_contra! hn
  have hle : ∑ _i : V, 1 ≤ ∑ i, k i :=
    Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (hn i)
  simpa using (not_le_of_gt h) (by simpa using hle)

/-- The least absent label, which is the least leaf on the tree side. -/
noncomputable def firstLeaf [LinearOrder V] (k : V → ℕ)
    (h : ∑ i, k i < Fintype.card V) : V :=
  (univ.filter fun i => k i = 0).min' (by
    obtain ⟨v, hv⟩ := exists_zero_entry k h
    exact ⟨v, by simp [hv]⟩)

theorem firstLeaf_zero [LinearOrder V] (k : V → ℕ)
    (h : ∑ i, k i < Fintype.card V) : k (firstLeaf k h) = 0 := by
  unfold firstLeaf
  exact (Finset.mem_filter.mp (Finset.min'_mem (univ.filter (fun i : V => k i = 0)) _)).2

/-- Deleting the first letter lowers the total multiplicity by one. -/
theorem sum_decAt {k : V → ℕ} {v : V} (hk : k v = 0) (p : Parents k v) :
    ∑ j, decAt k v p.1 j = (∑ i, k i) - 1 := by
  have hsum : ∑ j : {i // i ≠ v}, k j.1 = ∑ i, k i := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ v, hk, zero_add]
  unfold decAt
  rw [Finset.sum_tsub_distrib]
  · simp only [Finset.sum_ite_eq', mem_univ, ite_true, hsum]
  · intro j _
    split_ifs with hj
    · subst j
      exact p.2
    · exact Nat.zero_le _

/-- The two-vertex tree encodes as the empty word. -/
noncomputable def emptyPruferEquiv (hV : Fintype.card V = 2) (k : V → ℕ)
    (hk : ∑ i, k i = 0) : {T // T ∈ degTrees k} ≃ Words 0 k := by
  have hk0 : k = 0 := funext fun i => (Finset.sum_eq_zero_iff.mp hk) i (mem_univ i)
  refine {
    toFun := fun _ => ⟨Fin.elim0, fun i => by simp [occurrences, hk0]⟩
    invFun := fun _ => ⟨⊤, by rw [hk0, degTrees_zero_of_card_two hV]; simp⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro T
    apply Subtype.ext
    have h : T.1 = ⊤ := by simpa [hk0, degTrees_zero_of_card_two hV] using T.2
    exact h.symm
  · intro c
    apply Subtype.ext
    exact funext fun i => Fin.elim0 i

/-- Combine the invertible tree step and word step with the equivalences for the tails. -/
noncomputable def pruferStep {n : ℕ} {k : V → ℕ} {v : V} (hk : k v = 0)
    (hV : 3 ≤ Fintype.card V)
    (e : ∀ p : Parents k v,
      {T // T ∈ degTrees (decAt k v p.1)} ≃ Words n (decAt k v p.1)) :
    {T // T ∈ degTrees k} ≃ Words (n + 1) k :=
  (treeStep hk hV).trans ((Equiv.sigmaCongrRight e).trans (wordStep hk).symm)

/-- **Prüfer's bijection with degree multiplicities.** The code has length `n`, and
label `i` occurs exactly `k i = deg T i - 1` times. The inverse is recursive leaf attachment.
The recursion stops at the single edge on two labels. -/
noncomputable def degreePruferEquiv :
    ∀ (n : ℕ) (V : Type u) [Fintype V] [LinearOrder V],
      Fintype.card V = n + 2 → ∀ k : V → ℕ, ∑ i, k i = n →
        {T // T ∈ degTrees k} ≃ Words n k := by
  intro n
  induction n with
  | zero =>
    intro V _ _ hV k hk
    exact emptyPruferEquiv hV k hk
  | succ n ih =>
    intro V _ _ hV k hk
    letI : DecidableEq V := Classical.decEq V
    have hlt : ∑ i, k i < Fintype.card V := by omega
    let v := firstLeaf k hlt
    have hv : k v = 0 := firstLeaf_zero k hlt
    have hcard : Fintype.card {i // i ≠ v} = n + 2 := by
      have hs : Fintype.card {i // i ≠ v} + 1 = Fintype.card V := by
        convert card_subtype_ne_add_one v
      omega
    refine pruferStep (V := V) (n := n) (k := k) (v := v) hv (by omega) ?_
    intro p
    have hsum : ∑ j, decAt k v p.1 j = n := by
      rw [sum_decAt hv p, hk]
      omega
    exact @ih {i // i ≠ v} inferInstance inferInstance hcard (decAt k v p.1) hsum

/-- The degree of each label is one plus its multiplicity in the Prüfer code. -/
theorem degreePruferEquiv_degree [LinearOrder V] (n : ℕ) (hV : Fintype.card V = n + 2)
    (k : V → ℕ) (hk : ∑ i, k i = n) (T : {T // T ∈ degTrees k}) (i : V) :
    deg T.1 i = occurrences (degreePruferEquiv n V hV k hk T).1 i + 1 := by
  rw [(degreePruferEquiv n V hV k hk T).2 i, (mem_degTrees.mp T.2).2 i]

end MultipoleBKT.Cayley

end
