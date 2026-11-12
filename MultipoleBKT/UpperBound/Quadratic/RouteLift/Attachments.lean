/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.CoreForest.HeavyLight
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Attachment fibers of lifted heavy-light paths

The paper: proof of Corollary 5.34,
Step 2, and Step 4.

The terminal child of a heavy-light path determines its attachment inside its terminal
block. Counting paths at a block alone does not count paths at each attachment.
`card_attachmentFiber` refines the block count to the individual parts. The bridge
endpoints are indexed by nonroot blocks, so no endpoint is assigned to a nonexistent
parent bridge of the root.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic.RouteLift

open CoreForest

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
  {τ : SimpleGraph Λ} [DecidableRel τ.Adj] {a : Λ} {h : Λ → Λ}

/-- The nonroot leaves index the set `X*` in Step 2. -/
abbrev Leaf (τ : SimpleGraph Λ) [DecidableRel τ.Adj] (a : Λ) :=
  {l : Λ // l ∈ (leaves τ).erase a}

/-- The blocks carrying a parent bridge. -/
abbrev Nonroot (a : Λ) := {l : Λ // l ≠ a}

noncomputable instance : Fintype (Leaf τ a) := inferInstanceAs (Fintype {l // l ∈ (leaves τ).erase a})
instance : Fintype (Nonroot a) := inferInstanceAs (Fintype {l // l ≠ a})

variable (hτ : τ.IsTree)

/-- The child on the final bridge of the path starting at a nonroot leaf. It is
uniquely determined by `IsLocWitness`. -/
noncomputable def terminalChild (l : Leaf τ a) : Nonroot a :=
  ⟨(exists_locWitness hτ (h := h) (Finset.mem_erase.1 l.property).1).choose,
    fun hc => not_isParent_root _ (hc ▸
      (exists_locWitness hτ (h := h) (Finset.mem_erase.1 l.property).1).choose_spec.1)⟩

theorem terminalChild_spec (l : Leaf τ a) :
    IsLocWitness τ a h l (CoreForest.loc hτ a h l) (terminalChild (h := h) hτ l) :=
  (exists_locWitness hτ (h := h) (Finset.mem_erase.1 l.property).1).choose_spec

/-- An attachment of the path is the parent endpoint of its last bridge. -/
noncomputable def loc {V : Type*} (p : Nonroot a → V) (l : Leaf τ a) : V :=
  p (terminalChild (h := h) hτ l)

/-- The child bridges of `u` at which a heavy-light path stops. At the root every
child bridge stops a path. Elsewhere the heavy child is excluded. -/
noncomputable def stoppingChildren (u : Λ) : Finset (Nonroot a) :=
  univ.filter fun c => IsParent τ a u c ∧ (u = a ∨ h u ≠ c.val)

/-- The leaf-to-last-bridge correspondence is a bijection, including at individual
attachments. This is the counting step behind (5.96) and (5.98). -/
theorem terminalChild_bij (hh : IsChildChoice τ a h) (u : Λ) :
    Set.BijOn (terminalChild (h := h) hτ)
      {l : Leaf τ a | CoreForest.loc hτ a h l = u}
      (stoppingChildren (τ := τ) (a := a) (h := h) u : Set (Nonroot a)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    have hs := terminalChild_spec (h := h) hτ l
    change CoreForest.loc hτ a h l = u at hl
    rw [← hl]
    exact mem_filter.2 ⟨mem_univ _, hs.1, hs.2.2⟩
  · intro l hl l' hl' heq
    apply Subtype.ext
    have hs := terminalChild_spec (h := h) hτ l
    have hs' := terminalChild_spec (h := h) hτ l'
    rw [heq] at hs
    exact hs.2.1.eq_of_leaf hs'.2.1
      ((mem_leaves_iff_of_ne hτ (mem_erase.1 l.property).1).1 (mem_erase.1 l.property).2)
      ((mem_leaves_iff_of_ne hτ (mem_erase.1 l'.property).1).1 (mem_erase.1 l'.property).2)
  · intro c hc
    obtain ⟨huc, hstop⟩ := (mem_filter.1 hc).2
    obtain ⟨l, hcl, hleaf⟩ := existsUnique_heavyLeaf hτ hh c.property
    let L : Leaf τ a := ⟨l, hcl.1⟩
    have hw : IsLocWitness τ a h L u c := ⟨huc, hcl.2, hstop⟩
    have hloc : CoreForest.loc hτ a h L = u := loc_eq_of_locWitness hτ hw
    refine ⟨L, hloc, ?_⟩
    apply Subtype.ext
    exact (locWitness_unique hτ (terminalChild_spec (h := h) hτ L) hw).2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The leaves whose lifted paths stop at a given part. -/
noncomputable def attachmentFiber (p : Nonroot a → V) (S : V) : Finset (Leaf τ a) :=
  univ.filter fun l => loc (h := h) hτ p l = S

/-- The child bridges of block `u` incident to its part `S`. -/
noncomputable def childBridges (p : Nonroot a → V) (u : Λ) (S : V) : Finset (Nonroot a) :=
  univ.filter fun c => IsParent τ a u c ∧ p c = S

omit [Fintype V] in
/-- Attachment-level counting: the fiber at `S` is precisely the child bridges
incident to `S`, with the heavy child removed except at the root. -/
theorem card_attachmentFiber (hh : IsChildChoice τ a h) (b : V → Λ)
    (p : Nonroot a → V)
    (hp : ∀ c, IsParent τ a (b (p c)) c) (S : V) :
    (attachmentFiber (h := h) hτ p S).card =
      ((childBridges (τ := τ) p (b S) S).filter fun c => b S = a ∨ h (b S) ≠ c.val).card := by
  classical
  refine Finset.card_bij (fun l _ => terminalChild (h := h) hτ l) ?_ ?_ ?_
  · intro l hl
    have hlS : p (terminalChild (h := h) hτ l) = S := (mem_filter.1 hl).2
    have hs := terminalChild_spec (h := h) hτ l
    have hloc : CoreForest.loc hτ a h l = b S := by
      have hp' := hp (terminalChild (h := h) hτ l)
      rw [hlS] at hp'
      exact hs.1.unique hτ hp'
    rw [hloc] at hs
    exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hs.1, hlS⟩, hs.2.2⟩
  · intro l _ l' _ heq
    have hs := terminalChild_spec (h := h) hτ l
    have hs' := terminalChild_spec (h := h) hτ l'
    apply Subtype.ext
    rw [heq] at hs
    exact hs.2.1.eq_of_leaf hs'.2.1
      ((mem_leaves_iff_of_ne hτ (mem_erase.1 l.property).1).1 (mem_erase.1 l.property).2)
      ((mem_leaves_iff_of_ne hτ (mem_erase.1 l'.property).1).1 (mem_erase.1 l'.property).2)
  · intro c hc
    obtain ⟨hc', hstop⟩ := mem_filter.1 hc
    obtain ⟨-, hparent, hpS⟩ := mem_filter.1 hc'
    have hcstop : c ∈ stoppingChildren (τ := τ) (a := a) (h := h) (b S) :=
      mem_filter.2 ⟨mem_univ _, hparent, hstop⟩
    obtain ⟨l, -, hlc⟩ := (terminalChild_bij hτ hh (b S)).surjOn hcstop
    refine ⟨l, mem_filter.2 ⟨mem_univ _, ?_⟩, hlc⟩
    change p (terminalChild (h := h) hτ l) = S
    rw [hlc, hpS]

omit [Fintype V] in
/-- At the root every incident child bridge stops one path, including when several
bridges meet the same part. This is (5.98). -/
theorem card_attachmentFiber_root (hh : IsChildChoice τ a h) (b : V → Λ)
    (p : Nonroot a → V) (hp : ∀ c, IsParent τ a (b (p c)) c)
    {S : V} (hS : b S = a) :
    (attachmentFiber (h := h) hτ p S).card = (childBridges (τ := τ) p a S).card := by
  rw [card_attachmentFiber hτ hh b p hp, hS]
  congr 1
  exact Finset.filter_true_of_mem fun _ _ => Or.inl rfl

omit [Fintype V] in
/-- At a nonroot block the heavy bridge removes exactly one path at its own
attachment and removes none at all other attachments. -/
theorem card_attachmentFiber_nonroot (hh : IsChildChoice τ a h) (b : V → Λ)
    (p : Nonroot a → V) (hp : ∀ c, IsParent τ a (b (p c)) c)
    {u : Λ} (hu : u ≠ a) (huChild : IsParent τ a u (h u))
    {S : V} (hS : b S = u) :
    (attachmentFiber (h := h) hτ p S).card +
        (if p ⟨h u, fun he => not_isParent_root _ (he ▸ huChild)⟩ = S then 1 else 0) =
      (childBridges (τ := τ) p u S).card := by
  classical
  rw [card_attachmentFiber hτ hh b p hp, hS]
  let H : Nonroot a := ⟨h u, fun he => not_isParent_root _ (he ▸ huChild)⟩
  have heq : ((childBridges (τ := τ) p u S).filter fun c => u = a ∨ h u ≠ c.val) =
      (childBridges (τ := τ) p u S).erase H := by
    ext c
    simp only [mem_filter, mem_erase, hu, false_or]
    constructor
    · rintro ⟨hc, hn⟩
      exact ⟨fun he => hn (congrArg Subtype.val he).symm, hc⟩
    · rintro ⟨hn, hc⟩
      exact ⟨hc, fun he => hn (Subtype.ext he.symm)⟩
  rw [heq]
  by_cases hpS : p H = S
  · have hmem : H ∈ childBridges (τ := τ) p u S :=
      mem_filter.2 ⟨mem_univ _, huChild, hpS⟩
    rw [ite_eq_left hpS, Finset.card_erase_of_mem hmem]
    have := Finset.card_pos.2 ⟨H, hmem⟩
    omega
  · have hnot : H ∉ childBridges (τ := τ) p u S := fun hc => hpS (mem_filter.1 hc).2.2
    rw [ite_eq_right hpS, Finset.erase_eq_of_notMem hnot, add_zero]

/-- Regrouping the leaf factors by the actual lifted attachment, as in Step 4
before (5.94). -/
theorem prod_attachmentFiber {M : Type*} [CommMonoid M] (p : Nonroot a → V) (f : V → M) :
    ∏ l : Leaf τ a, f (loc (h := h) hτ p l) =
      ∏ S, f S ^ (attachmentFiber (h := h) hτ p S).card := by
  classical
  have heq := Finset.prod_fiberwise_of_maps_to
    (s := (univ : Finset (Leaf τ a))) (t := (univ : Finset V))
    (g := loc (h := h) hτ p) (fun _ _ => mem_univ _) (fun l => f (loc (h := h) hτ p l))
  rw [← heq]
  refine Finset.prod_congr rfl fun S _ => ?_
  calc (∏ l ∈ univ.filter (fun l => loc (h := h) hτ p l = S),
        f (loc (h := h) hτ p l)) = ∏ _l ∈ attachmentFiber (h := h) hτ p S, f S := by
          exact Finset.prod_congr rfl fun l hl => congrArg f (mem_filter.1 hl).2
    _ = _ := Finset.prod_const _

end MultipoleBKT.UpperBound.Quadratic.RouteLift

end
