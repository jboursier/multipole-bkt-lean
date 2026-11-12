/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RoutePrufer.Equiv

/-!
# Prüfer's bijection

The bijection cited in Lemma A.9.
The degree-prescribed construction gives a bijection from all labelled trees on `n + 2`
vertices to all words of length `n`. The inverse reads the multiplicities from the word.
-/

@[expose] public section

namespace MultipoleBKT.Cayley

universe u

open SimpleGraph Finset
open scoped Classical

variable {V : Type u} [Fintype V] {n : ℕ}

/-- The degree sequence shifted down by one has total `|V| - 2`. -/
theorem sum_degree_sub_one (hV : Fintype.card V = n + 2)
    {T : SimpleGraph V} (hT : T.IsTree) : ∑ i, (deg T i - 1) = n := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hsum := sum_deg_of_isTree hT
  have hsub : ∑ i, (deg T i - 1) = ∑ i, deg T i - ∑ _i : V, 1 :=
    Finset.sum_tsub_distrib _ fun i _ => one_le_deg_of_isTree hT i
  simp only [sum_const, card_univ, smul_eq_mul, mul_one] at hsub
  omega

/-- Separate all trees into their shifted degree fibres. -/
noncomputable def treeDegreesEquiv (hV : Fintype.card V = n + 2) :
    {T : SimpleGraph V // T.IsTree} ≃
      (Σ k : {k : V → ℕ // ∑ i, k i = n}, {T // T ∈ degTrees k.1}) where
  toFun T := ⟨⟨fun i => deg T.1 i - 1, sum_degree_sub_one hV T.2⟩,
    ⟨T.1, mem_degTrees.mpr ⟨T.2, fun i => by
      have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have := one_le_deg_of_isTree T.2 i
      change deg T.1 i = (deg T.1 i - 1) + 1
      omega⟩⟩⟩
  invFun Q := ⟨Q.2.1, (mem_degTrees.mp Q.2.2).1⟩
  left_inv T := Subtype.ext rfl
  right_inv Q := by
    obtain ⟨k, T⟩ := Q
    have hk : (fun i => deg T.1 i - 1) = k.1 := by
      funext i
      rw [(mem_degTrees.mp T.2).2 i]
      omega
    apply Sigma.ext (Subtype.ext hk)
    dsimp only
    apply (Subtype.heq_iff_coe_eq (fun G => by rw [hk])).mpr
    rfl

/-- Separate all words into their multiplicity fibres. -/
noncomputable def wordDegreesEquiv :
    (Fin n → V) ≃
      (Σ k : {k : V → ℕ // ∑ i, k i = n}, Words n k.1) where
  toFun c := ⟨⟨occurrences c, sum_occurrences c⟩, ⟨c, fun _ => rfl⟩⟩
  invFun Q := Q.2.1
  left_inv c := rfl
  right_inv Q := by
    obtain ⟨k, c⟩ := Q
    have hk : occurrences c.1 = k.1 := funext c.2
    apply Sigma.ext (Subtype.ext hk)
    dsimp only
    apply (Subtype.heq_iff_coe_eq (fun w => by rw [hk])).mpr
    rfl

/-- **Prüfer's bijection.** Encoding repeatedly deletes the least leaf and records its
neighbour. Decoding repeatedly attaches the least absent label to the first letter.
Both algorithms stop at the single edge on the last two labels. -/
noncomputable def pruferEquiv [LinearOrder V] (hV : Fintype.card V = n + 2) :
    {T : SimpleGraph V // T.IsTree} ≃ (Fin n → V) :=
  (treeDegreesEquiv hV).trans
    ((Equiv.sigmaCongrRight fun k : {k : V → ℕ // ∑ i, k i = n} =>
      degreePruferEquiv n V hV k.1 k.2).trans wordDegreesEquiv.symm)

/-- Each vertex occurs in the code exactly its degree minus one times. -/
theorem prufer_degree [LinearOrder V] (hV : Fintype.card V = n + 2)
    (T : {T : SimpleGraph V // T.IsTree}) (i : V) :
    deg T.1 i = occurrences (pruferEquiv hV T) i + 1 := by
  let Q := treeDegreesEquiv hV T
  have h := degreePruferEquiv_degree n hV Q.1.1 Q.1.2 Q.2 i
  change deg T.1 i = occurrences (pruferEquiv hV T) i + 1 at h
  exact h

/-- Decoding an encoded tree returns the original tree. -/
theorem prufer_decode_encode [LinearOrder V] (hV : Fintype.card V = n + 2)
    (T : {T : SimpleGraph V // T.IsTree}) :
    (pruferEquiv hV).symm (pruferEquiv hV T) = T :=
  (pruferEquiv hV).symm_apply_apply T

/-- Encoding a decoded word returns every letter of the original word. -/
theorem prufer_encode_decode [LinearOrder V] (hV : Fintype.card V = n + 2)
    (c : Fin n → V) : pruferEquiv hV ((pruferEquiv hV).symm c) = c :=
  (pruferEquiv hV).apply_symm_apply c

end MultipoleBKT.Cayley

end
