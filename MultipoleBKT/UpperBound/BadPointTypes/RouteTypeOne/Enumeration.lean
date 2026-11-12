/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeOne.Skeleton

/-!
# Successive finite choices for type 1

The paper: Lemma 5.40,
(5.125)–(5.127) and Step 6.
The enumeration retains both bad-charge sets, both injective partner maps and both
same-sign partitions as separate choices.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeOne

open Finset

variable {n : ℕ}

open scoped Classical in
/-- All charges of a specified sign. -/
noncomputable def charges (s : Bool) : Finset (Charge n) := univ.filter fun v => positive v = s

theorem card_charges (s : Bool) : (charges (n := n) s).card = n := by
  classical
  cases s
  · have he : charges (n := n) false = univ.map Function.Embedding.inr := by
      apply Finset.ext
      intro v
      rw [charges, Finset.mem_filter, Finset.mem_map]
      cases v <;> simp [positive]
    rw [he, card_map, card_univ, Fintype.card_fin]
  · have he : charges (n := n) true = univ.map Function.Embedding.inl := by
      apply Finset.ext
      intro v
      rw [charges, Finset.mem_filter, Finset.mem_map]
      cases v <;> simp [positive]
    rw [he, card_map, card_univ, Fintype.card_fin]

theorem badSet_subset (D : TOData n) (s : Bool) : badSet D s ⊆ charges s := by
  classical
  intro v hv
  exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hv).2.1⟩

/-- The number of bad-charge set choices in (5.125). -/
theorem card_badSet_choices (s : Bool) (a : ℕ) :
    ((charges (n := n) s).powersetCard a).card = n.choose a := by
  rw [card_powersetCard, card_charges]

/-- Splitting first by the number of bad charges and then choosing their set.
The cardinality of the inner set choices is the paper's binomial coefficient. -/
theorem sum_badSets_by_counts {R : Type*} [AddCommMonoid R] (s : Bool)
    (F : Finset (Charge n) → R) :
    ∑ A ∈ (charges s).powerset, F A =
      ∑ m ∈ range (n + 1), ∑ A ∈ (charges s).powersetCard m, F A := by
  classical
  have hm : ∀ A ∈ (charges (n := n) s).powerset, A.card ∈ range (n + 1) := by
    intro A hA
    exact mem_range.2 (Nat.lt_succ_of_le ((card_le_card (mem_powerset.1 hA)).trans_eq
      (card_charges s)))
  rw [← sum_fiberwise_of_maps_to hm]
  apply sum_congr rfl
  intro m _
  apply sum_congr
  · ext A
    simp [mem_powersetCard]
  · intro _ _
    rfl

open scoped Classical in
/-- Injective partner assignments from a good-charge set `G` into the opposite bad set `A`.
The identity extension has no additional choices. -/
noncomputable def injections (G A : Finset (Charge n)) : Finset (Charge n → Charge n) :=
  (Fintype.piFinset fun v => if v ∈ G then A else {v}).filter fun f => Set.InjOn f G

/-- There are at most `|A|^{|G|}` injective partner assignments. -/
theorem card_injections_le (G A : Finset (Charge n)) :
    (injections G A).card ≤ A.card ^ G.card := by
  classical
  refine (card_filter_le _ _).trans_eq ?_
  rw [Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_singleton]
  rw [prod_ite, prod_const, prod_const_one, mul_one, filter_mem_eq_inter, univ_inter]

/-- The stable matching restricted to good charges is one of the enumerated injections. -/
theorem partner_mem_injections {q : ℕ} {D : TOData n} (hD : TypeOneValid q D)
    (hC : Compatible D) (s : Bool) :
    partner D s ∈ injections (charges s \ badSet D s) (badSet D (!s)) := by
  classical
  have hgood : ∀ v, v ∈ charges s \ badSet D s ↔ positive v = s ∧ D.1 v = 3 := by
    intro v
    by_cases hs : positive v = s <;> simp [charges, badSet, mem_sdiff, hs]
  refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun v => ?_, ?_⟩
  · by_cases hv : positive v = s ∧ D.1 v = 3
    · rw [ite_eq_left ((hgood v).2 hv), partner, ite_eq_left hv]
      refine mem_filter.2 ⟨mem_univ _, (hC.2.1 v hv.2).trans (congrArg Bool.not hv.1), ?_⟩
      rcases hD.2.1 v hv.2 with h | h <;> rw [h] <;> norm_num
    · rw [ite_eq_right (fun h => hv ((hgood v).1 h)), partner, ite_eq_right hv, mem_singleton]
  · intro v hv w hw he
    obtain ⟨hvs, hvk⟩ := (hgood v).1 hv
    obtain ⟨hws, hwk⟩ := (hgood w).1 hw
    rw [partner, ite_eq_left ⟨hvs, hvk⟩, partner, ite_eq_left ⟨hws, hwk⟩] at he
    exact hC.2.2 hvk hwk he

/-- Once the injection `f` is fixed, the good partners attached to a block are its
intersection with `im f` (Lemma 5.40, Step 3). -/
theorem goodPartners_eq_inter_image (S G : Finset (Charge n)) (f : Charge n → Charge n) :
    (S.filter fun i => ∃ j ∈ G, f j = i) = S ∩ G.image f := by
  classical
  apply Finset.ext
  intro i
  simp only [mem_filter, mem_inter, mem_image]

/-- For `q ≥ 1`, a root is overcrowded precisely when it has a distinct bad child.
This recovers the charge kinds from the successive partition choices. -/
theorem crowded_iff_child {q : ℕ} (hq : 1 ≤ q) {D : TOData n} (hD : TypeOneValid q D)
    {r : Charge n} (_hr : D.1 r = 0 ∨ D.1 r = 1) :
    D.1 r = 0 ↔ ∃ v, D.1 v ≠ 3 ∧ v ≠ r ∧ D.2.1 v = r := by
  classical
  constructor
  · intro hr0
    have hp := hD.2.2.1 r hr0
    have hn : (univ.filter fun v => D.1 v = 2 ∧ D.2.1 v = r).Nonempty :=
      card_pos.1 (by rw [hp]; omega)
    obtain ⟨v, hv⟩ := hn
    obtain ⟨hk, he⟩ := (mem_filter.1 hv).2
    exact ⟨v, by rw [hk]; norm_num, fun h => by rw [h, hr0] at hk; norm_num at hk, he⟩
  · rintro ⟨v, hv, hvr, hp⟩
    have hk2 : D.1 v = 2 := by
      rcases kind_cases (D.1 v) with h | h | h | h
      · exact (hvr ((hD.2.2.2.2.1 v (Or.inl h)).symm.trans hp)).elim
      · exact (hvr ((hD.2.2.2.2.1 v (Or.inr h)).symm.trans hp)).elim
      · exact h
      · exact (hv h).elim
    have he := hD.1 v hk2
    rwa [hp] at he

/-- Once the bad-charge sets and the parent map are fixed, no charge-kind choices remain. -/
theorem kinds_unique {q : ℕ} (hq : 1 ≤ q) {D E : TOData n}
    (hD : TypeOneValid q D) (hE : TypeOneValid q E)
    (hgood : ∀ v, D.1 v = 3 ↔ E.1 v = 3) (hpar : D.2.1 = E.2.1) : D.1 = E.1 := by
  funext v
  by_cases hv : D.1 v = 3
  · exact hv.trans ((hgood v).1 hv).symm
  have he : E.1 v ≠ 3 := fun h => hv ((hgood v).2 h)
  have htwo (F : TOData n) (hF : TypeOneValid q F) (hf : F.1 v ≠ 3) :
      F.1 v = 2 ↔ F.2.1 v ≠ v := by
    constructor
    · intro h hp
      have := hF.1 v h
      rw [hp, h] at this
      norm_num at this
    · intro hp
      rcases kind_cases (F.1 v) with h | h | h | h
      · exact (hp (hF.2.2.2.2.1 v (Or.inl h))).elim
      · exact (hp (hF.2.2.2.2.1 v (Or.inr h))).elim
      · exact h
      · exact (hf h).elim
  by_cases h2 : D.1 v = 2
  · have he2 : E.1 v = 2 := (htwo E hE he).2 (by rw [← hpar]; exact (htwo D hD hv).1 h2)
    exact h2.trans he2.symm
  have he2 : E.1 v ≠ 2 := fun h => h2 ((htwo D hD hv).2 (by
    rw [hpar]; exact (htwo E hE he).1 h))
  have hd01 : D.1 v = 0 ∨ D.1 v = 1 := by
    rcases kind_cases (D.1 v) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (h2 h).elim
    · exact (hv h).elim
  have he01 : E.1 v = 0 ∨ E.1 v = 1 := by
    rcases kind_cases (E.1 v) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (he2 h).elim
    · exact (he h).elim
  have hzero : D.1 v = 0 ↔ E.1 v = 0 := by
    rw [crowded_iff_child hq hD hd01, crowded_iff_child hq hE he01]
    simp_rw [hpar, not_congr (hgood _)]
  rcases hd01 with hd | hd <;> rcases he01 with he | he
  · exact hd.trans he.symm
  · have hz := hzero.1 hd
    rw [he] at hz
    norm_num at hz
  · have hz := hzero.2 he
    rw [hd] at hz
    norm_num at hz
  · exact hd.trans he.symm

end MultipoleBKT.BadPointTypes.RouteTypeOne

end
