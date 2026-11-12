/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.RouteChromatic.Rooting

/-!
# Coloring along a rooted incidence tree

A coloring consists of a root color and, independently at each element, an
injection from its children into the colors other than its parent's color.
The injections enforce distinct child colors, as required in
(4.150).
-/

@[expose] public section

namespace MultipoleBKT.RouteChromatic

open Finset

variable {V A : Type*} [DecidableEq V] {C : A → Finset V} {r : V}

namespace Rooting

/-- The children of an element of the rooted incidence tree. -/
def children (R : Rooting C r) (a : A) : Finset V := (C a).erase (R.parent a)

/-- A nonroot index, as a child of its parent element. -/
def asChild (R : Rooting C r) (i : {i : V // i ≠ r}) : R.children (R.branch i) :=
  ⟨i.val, mem_erase.mpr ⟨R.branch_ne i, R.branch_mem i⟩⟩

/-- All independent choices in a rooted coloring: a root color and an injection
of each set of children into the remaining colors. -/
abbrev ColorChoices (R : Rooting C r) (t : ℕ) :=
  Fin (t + 1) × (∀ a, R.children a ↪ Fin t)

/-- Reconstruct the color at an index by following its parent toward the root.
`succAbove` skips exactly the parent's color. -/
def decode (R : Rooting C r) {t : ℕ} (q : R.ColorChoices t) (i : V) : Fin (t + 1) :=
  if hi : i = r then q.1 else
    (R.decode q (R.parent (R.branch ⟨i, hi⟩))).succAbove
      (q.2 (R.branch ⟨i, hi⟩) (R.asChild ⟨i, hi⟩))
termination_by R.depth i
decreasing_by exact R.parent_lt _ _ (R.branch_mem ⟨i, hi⟩) (R.branch_ne ⟨i, hi⟩)

private theorem decode_root (R : Rooting C r) {t : ℕ} (q : R.ColorChoices t) :
    R.decode q r = q.1 := by
  rw [decode, dite_eq_left rfl]

private theorem decode_child (R : Rooting C r) {t : ℕ} (q : R.ColorChoices t)
    (a : A) (i : R.children a) :
    R.decode q i.val = (R.decode q (R.parent a)).succAbove (q.2 a i) := by
  rcases i with ⟨i, hi⟩
  have hi' := mem_erase.mp hi
  have hir := R.child_ne_root a i hi'.2 hi'.1
  have hba := R.branch_eq a i hi'.2 hi'.1
  rw [decode, dite_eq_right hir]
  have hchoice : ∀ (j : {i : V // i ≠ r}) (b : A) (hb : R.branch j = b)
      (k : R.children b), j.val = k.val →
        (q.2 (R.branch j)) (R.asChild j) = (q.2 b) k := by
    intro j b hb k hk
    subst b
    exact congrArg (q.2 (R.branch j)) (Subtype.ext hk)
  rw [hchoice ⟨i, hir⟩ a hba ⟨i, hi⟩ rfl, hba]

/-- The reconstructed coloring is injective on every incidence set. -/
theorem decode_injOn (R : Rooting C r) {t : ℕ} (q : R.ColorChoices t) :
    ∀ a, Set.InjOn (R.decode q) (C a) := by
  intro a u hu v hv heq
  by_cases hup : u = R.parent a
  · subst u
    by_cases hvp : v = R.parent a
    · exact hvp.symm
    · have h := R.decode_child q a ⟨v, mem_erase.mpr ⟨hvp, hv⟩⟩
      rw [h] at heq
      exact False.elim ((Fin.succAbove_ne _ _) heq.symm)
  · by_cases hvp : v = R.parent a
    · subst v
      have h := R.decode_child q a ⟨u, mem_erase.mpr ⟨hup, hu⟩⟩
      rw [h] at heq
      exact False.elim ((Fin.succAbove_ne _ _) heq)
    · rw [R.decode_child q a ⟨u, mem_erase.mpr ⟨hup, hu⟩⟩,
        R.decode_child q a ⟨v, mem_erase.mpr ⟨hvp, hv⟩⟩] at heq
      exact congrArg Subtype.val ((q.2 a).injective (Fin.succAbove_right_injective heq))

/-- Record the root color and the distinct child colors, renumbered by deleting
the parent's color. -/
def encode (R : Rooting C r) {t : ℕ}
    (f : {f : V → Fin (t + 1) // ∀ a, Set.InjOn f (C a)}) : R.ColorChoices t :=
  (f.val r, fun a =>
    { toFun := fun i => (finSuccAboveEquiv (f.val (R.parent a))).symm
        ⟨f.val i.val, fun h => (mem_erase.mp i.prop).1
          (f.prop a (mem_erase.mp i.prop).2 (R.parent_mem a) h)⟩
      inj' := by
        intro i j h
        have h' := congrArg (fun c => ((finSuccAboveEquiv (f.val (R.parent a))) c).val) h
        simp only [Equiv.apply_symm_apply] at h'
        exact Subtype.ext (f.prop a (mem_erase.mp i.prop).2 (mem_erase.mp j.prop).2 h') })

private theorem decode_encode (R : Rooting C r) {t : ℕ}
    (f : {f : V → Fin (t + 1) // ∀ a, Set.InjOn f (C a)}) :
    ∀ i, R.decode (R.encode f) i = f.val i := by
  intro i
  induction hi : R.depth i using Nat.strong_induction_on generalizing i with
  | h d ih =>
    by_cases hir : i = r
    · subst i
      exact R.decode_root _
    · rw [decode, dite_eq_right hir]
      rw [ih _ (hi ▸ R.parent_lt _ _ (R.branch_mem ⟨i, hir⟩) (R.branch_ne ⟨i, hir⟩)) _ rfl]
      exact congrArg Subtype.val ((finSuccAboveEquiv _).apply_symm_apply _)

private theorem encode_decode (R : Rooting C r) {t : ℕ} (q : R.ColorChoices t) :
    R.encode ⟨R.decode q, R.decode_injOn q⟩ = q := by
  apply Prod.ext
  · exact R.decode_root q
  · funext a
    apply Function.Embedding.ext
    intro i
    change (finSuccAboveEquiv (R.decode q (R.parent a))).symm _ = _
    apply (Equiv.symm_apply_eq _).mpr
    apply Subtype.ext
    exact R.decode_child q a i

/-- Proper colorings of the entire incidence family are in bijection with a
root color and independent injective child-color choices. -/
def coloringEquiv (R : Rooting C r) (t : ℕ) :
    {f : V → Fin (t + 1) // ∀ a, Set.InjOn f (C a)} ≃ R.ColorChoices t where
  toFun := R.encode
  invFun q := ⟨R.decode q, R.decode_injOn q⟩
  left_inv := by
    intro f
    exact Subtype.ext (funext (decode_encode R f))
  right_inv := by
    intro q
    exact encode_decode R q

/-- Rooting counts colorings as `t+1` choices at the root, and a falling factorial
for each incidence vertex. The children must have distinct colors. -/
theorem card_colorings [Fintype V] [Fintype A] (R : Rooting C r) (t : ℕ) :
    Nat.card {f : V → Fin (t + 1) // ∀ a, Set.InjOn f (C a)} =
      (t + 1) * ∏ a, t.descFactorial ((C a).card - 1) := by
  classical
  rw [Nat.card_congr (R.coloringEquiv t)]
  change Nat.card (Fin (t + 1) × (∀ a, R.children a ↪ Fin t)) = _
  rw [Nat.card_prod, Nat.card_pi, Nat.card_eq_fintype_card, Fintype.card_fin]
  congr 1
  apply prod_congr rfl
  intro a _
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe, children, card_erase_of_mem (R.parent_mem a)]

end Rooting

end MultipoleBKT.RouteChromatic

end
