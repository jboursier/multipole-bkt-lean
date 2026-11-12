/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.RadiusAllocation

/-!
# The coarse blocks with their original group labels

See Lemma A.4. A coarse block is either one of
the disjoint groups or an ungrouped fine block. This representation preserves
the selected largest block in each group.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open Finset
open scoped Classical

variable {B : Type*} [Fintype B] [DecidableEq B] {n : ℕ}

/-- The coarse partition, represented by group indices and the remaining blocks. -/
abbrev GroupedBlock (G : Fin n → Finset B) :=
  Fin n ⊕ {b : B // ∀ l, b ∉ G l}

/-- Map a fine block to its unique group, or to its own singleton coarse block.
Disjointness makes the group index unique. -/
noncomputable def groupedOf (G : Fin n → Finset B)
    (_hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l')) (b : B) : GroupedBlock G :=
  if h : ∃ l, b ∈ G l then Sum.inl h.choose else Sum.inr ⟨b, not_exists.mp h⟩

omit [Fintype B] in
theorem groupedOf_eq_inl (G : Fin n → Finset B)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l')) (b : B) (l : Fin n) :
    groupedOf G hdisj b = Sum.inl l ↔ b ∈ G l := by
  unfold groupedOf
  split_ifs with h
  · rw [Sum.inl.injEq]
    constructor
    · intro heq
      exact heq ▸ h.choose_spec
    · intro hb
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj _ _ hne) h.choose_spec hb
  · exact ⟨fun heq => heq.elim, fun hb => (h ⟨l, hb⟩).elim⟩

omit [Fintype B] in
theorem groupedOf_eq_inr (G : Fin n → Finset B)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l')) (b : B)
    (c : {b : B // ∀ l, b ∉ G l}) :
    groupedOf G hdisj b = Sum.inr c ↔ b = c.val := by
  unfold groupedOf
  split_ifs with h
  · refine ⟨fun heq => heq.elim, fun heq => ?_⟩
    exact (c.property h.choose (heq ▸ h.choose_spec)).elim
  · simp only [Sum.inr.injEq, Subtype.ext_iff]

/-- A selected representative for each coarse block. -/
def groupedHat (G : Fin n → Finset B) (hat : Fin n → B) : GroupedBlock G → B :=
  Sum.elim hat Subtype.val

omit [Fintype B] in
theorem groupedHat_right_inverse (G : Fin n → Finset B)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l'))
    (hat : Fin n → B) (hhat : ∀ l, hat l ∈ G l) (c : GroupedBlock G) :
    groupedOf G hdisj (groupedHat G hat c) = c := by
  cases c with
  | inl l => exact (groupedOf_eq_inl G hdisj _ l).mpr (hhat l)
  | inr b => exact (groupedOf_eq_inr G hdisj _ b).mpr rfl

/-- The omitted representatives in the odd prefactor are precisely
the omitted representatives in the coarse fibres. Singleton fibres contribute one. -/
theorem grouped_prefactor (G : Fin n → Finset B)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l'))
    (hat : Fin n → B) (f : B → ℝ) :
    (∏ c : GroupedBlock G,
      ∏ b ∈ (univ.filter fun b => groupedOf G hdisj b = c).erase (groupedHat G hat c), f b) =
        ∏ l, ∏ b ∈ (G l).erase (hat l), f b := by
  rw [Fintype.prod_sum_type]
  have hleft (l : Fin n) : (univ.filter fun b => groupedOf G hdisj b = Sum.inl l) = G l := by
    ext b
    simp only [mem_filter, mem_univ, true_and, groupedOf_eq_inl]
  have hright (c : {b : B // ∀ l, b ∉ G l}) :
      (univ.filter fun b => groupedOf G hdisj b = Sum.inr c) = {c.val} := by
    ext b
    simp only [mem_filter, mem_univ, true_and, groupedOf_eq_inr, mem_singleton]
  simp only [hleft, hright, groupedHat, Sum.elim_inl, Sum.elim_inr, erase_singleton,
    prod_empty, prod_const_one, mul_one]

/-- Counting the tagged coarse blocks removes exactly `|G_l|-1` blocks per
group. This is the cardinality of `Coarse_X(X_1,...,X_n)`. -/
theorem card_groupedBlock (G : Fin n → Finset B)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l'))
    (a : Fin n → ℕ) (ha : ∀ l, a l + 1 = (G l).card) :
    Fintype.card (GroupedBlock G) + ∑ l, a l = Fintype.card B := by
  have hdis : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint G :=
    fun l _ l' _ h => hdisj l l' h
  have hgroup : (univ.biUnion G).card = ∑ l, (G l).card := card_biUnion hdis
  have hrem : Fintype.card {b : B // ∀ l, b ∉ G l} =
      (univ \ univ.biUnion G).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_biUnion, not_exists]
  have hsum : ∑ l, (G l).card = (∑ l, a l) + n := by
    simp only [← ha, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  rw [Fintype.card_sum, Fintype.card_fin, hrem, card_sdiff_of_subset (subset_univ _), card_univ]
  have hle := card_le_univ (univ.biUnion G)
  omega

end MultipoleBKT.SmallIntegral.RouteJ

end
