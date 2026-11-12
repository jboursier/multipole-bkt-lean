/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ConnectedTransport

/-!
# Transport of the five correction subsets

See (A.51) and Step 2 of the proof of Lemma A.7. Every unordered subset is transported, rather than only the
original edge family. Products and the nonempty condition are preserved.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Multipole SimpleGraph Hierarchical UpperBound.BoundedUpper

/-- The ordered representative of an unordered pair of original labels. -/
def sourcePair {U : Finset ℕ} : Sym2 U → ℕ × ℕ :=
  Sym2.lift ⟨fun i j => (min i.val j.val, max i.val j.val), fun i j => by
    simp only [min_comm, max_comm]⟩

/-- Transport an arbitrary unordered subset to ordered original pairs. -/
def sourcePairs {U : Finset ℕ} (D : Finset (Sym2 U)) : Finset (ℕ × ℕ) :=
  D.image sourcePair

/-- The canonical representative map is injective, including on diagonal pairs. -/
theorem sourcePair_injective {U : Finset ℕ} : Function.Injective (@sourcePair U) := by
  intro e f
  induction e using Sym2.ind with
  | h i j =>
    induction f using Sym2.ind with
    | h k l =>
      intro h
      change (min i.val j.val, max i.val j.val) = (min k.val l.val, max k.val l.val) at h
      have hm := congrArg Prod.fst h
      have hM := congrArg Prod.snd h
      apply Sym2.eq_iff.2
      rcases le_total i.val j.val with hij | hij <;>
        rcases le_total k.val l.val with hkl | hkl
      · simp only [min_eq_left hij, max_eq_right hij, min_eq_left hkl, max_eq_right hkl] at hm hM
        exact Or.inl ⟨Subtype.ext hm, Subtype.ext hM⟩
      · simp only [min_eq_left hij, max_eq_right hij, min_eq_right hkl, max_eq_left hkl] at hm hM
        exact Or.inr ⟨Subtype.ext hm, Subtype.ext hM⟩
      · simp only [min_eq_right hij, max_eq_left hij, min_eq_left hkl, max_eq_right hkl] at hm hM
        exact Or.inr ⟨Subtype.ext hM, Subtype.ext hm⟩
      · simp only [min_eq_right hij, max_eq_left hij, min_eq_right hkl, max_eq_left hkl] at hm hM
        exact Or.inl ⟨Subtype.ext hM, Subtype.ext hm⟩

/-- Transport back recovers every loopless unordered subset. -/
theorem symOf_sourcePairs {U : Finset ℕ} {D : Finset (Sym2 U)}
    (hD : ∀ e ∈ D, ¬ e.IsDiag) : symOf U (sourcePairs D) = D := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨i, j, hij, hp, rfl⟩ := mem_symOf.1 he
    obtain ⟨f, hf, heq⟩ := mem_image.1 hp
    have hs : sourcePair s(i, j) = ((i : ℕ), (j : ℕ)) := by
      change (min i.val j.val, max i.val j.val) = _
      rw [min_eq_left (show i.val ≤ j.val from hij.le), max_eq_right (show i.val ≤ j.val from hij.le)]
    exact sourcePair_injective (heq.trans hs.symm) ▸ hf
  · intro he
    induction e using Sym2.ind with
    | h i j =>
      have hne : i ≠ j := Sym2.mk_isDiag_iff.not.1 (hD _ he)
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact mem_symOf.2 ⟨i, j, hij, mem_image.2 ⟨_, he, by
          change (min i.val j.val, max i.val j.val) = _
          rw [min_eq_left (show i.val ≤ j.val from hij.le), max_eq_right (show i.val ≤ j.val from hij.le)]⟩, rfl⟩
      · exact mem_symOf.2 ⟨j, i, hji, mem_image.2 ⟨_, he, by
          change (min i.val j.val, max i.val j.val) = _
          rw [min_eq_right (show j.val ≤ i.val from hji.le), max_eq_left (show j.val ≤ i.val from hji.le)]⟩, Sym2.eq_swap⟩

/-- Ordered products recover arbitrary symmetric functions of original edges. -/
theorem prod_sourcePairs {U : Finset ℕ} (D : Finset (Sym2 U)) (f : ℕ × ℕ → ℝ) :
    (∏ p ∈ sourcePairs D, f p) = ∏ e ∈ D, f (sourcePair e) := by
  classical
  exact prod_image (fun _ _ _ _ h => sourcePair_injective h)

/-- Valid ordered original families are recovered in the other direction too. -/
theorem sourcePairs_symOf {U : Finset ℕ} {P : Finset (ℕ × ℕ)}
    (hP : P ⊆ pairsOn U) : sourcePairs (symOf U P) = P := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨e, he, rfl⟩ := mem_image.1 hp
    obtain ⟨i, j, hij, hpair, rfl⟩ := mem_symOf.1 he
    simpa only [sourcePair, Sym2.lift_mk, min_eq_left (show i.val ≤ j.val from hij.le),
      max_eq_right (show i.val ≤ j.val from hij.le)] using hpair
  · intro hp
    obtain ⟨hi, hj, hij⟩ := mem_pairsOn.1 (hP hp)
    refine mem_image.2 ⟨s((⟨p.1, hi⟩ : U), (⟨p.2, hj⟩ : U)),
      mem_symOf.2 ⟨_, _, hij, hp, rfl⟩, ?_⟩
    change (min p.1 p.2, max p.1 p.2) = p
    rw [min_eq_left hij.le, max_eq_right hij.le]

/-- Transport commutes with deletion and therefore with both bond remainders. -/
theorem sourcePairs_sdiff {U : Finset ℕ} (D F : Finset (Sym2 U)) :
    sourcePairs (D \ F) = sourcePairs D \ sourcePairs F := by
  classical
  exact image_sdiff D F sourcePair_injective

/-- Cut-even unordered subsets have the paper's even degree at every block.
The singleton cut counts each inter-block edge once, with its multiplicity. -/
theorem source_cutEven_parity {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {O : Finset (ℕ × ℕ)} (hO : O ⊆ interPairs X)
    (hcut : CutEven (Sym2.map (Limits.blockOf X)) (symOf (X.biUnion id) O)) :
    IsParityPair X O ∅ := by
  classical
  intro S hS
  have hmem : ∀ i : X.biUnion id, Limits.blockOf X i = (⟨S, hS⟩ : X) ↔ i.val ∈ S :=
    fun i => Limits.blockOf_eq_iff hX i ⟨S, hS⟩
  let A := O.filter fun p => p.1 ∈ S
  let B := O.filter fun p => p.2 ∈ S
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.2
    intro p ha hb
    have hp := hO (mem_filter.1 ha).1
    have hi := (mem_filter.1 ha).2
    have hj := (mem_filter.1 hb).2
    exact (mem_interPairs.1 hp).2 ⟨S,hS, mem_pairsOn.2 ⟨hi,hj,(mem_pairsOn.1 (interPairs_subset_pairsOn hp)).2.2⟩⟩
  have hcross : (symOf (X.biUnion id) O).filter
      (fun e => Crosses ({⟨S, hS⟩} : Finset X) (Sym2.map (Limits.blockOf X) e)) =
      symOf (X.biUnion id) (A ∪ B) := by
    ext e
    constructor
    · intro he
      obtain ⟨i, j, hij, hp, rfl⟩ := mem_symOf.1 (mem_filter.1 he).1
      have hc := (mem_filter.1 he).2
      simp only [Sym2.map_mk, crosses_mk, mem_singleton, hmem] at hc
      exact mem_symOf.2 ⟨i, j, hij, mem_union.2 (by
        by_cases hi : i.val ∈ S
        · exact Or.inl (mem_filter.2 ⟨hp, hi⟩)
        · exact Or.inr (mem_filter.2 ⟨hp, Classical.byContradiction (fun hj => hi (hc.mpr hj))⟩)), rfl⟩
    · intro he
      obtain ⟨i, j, hij, hp, rfl⟩ := mem_symOf.1 he
      have hpO : (i.val,j.val) ∈ O := by
        rcases mem_union.1 hp with h | h <;> exact (mem_filter.1 h).1
      refine mem_filter.2 ⟨mem_symOf.2 ⟨i,j,hij,hpO,rfl⟩, ?_⟩
      simp only [Sym2.map_mk, crosses_mk, mem_singleton, hmem]
      have hboth : ¬ (i.val ∈ S ∧ j.val ∈ S) := fun h =>
        (mem_interPairs.1 (hO hpO)).2 ⟨S,hS,mem_pairsOn.2 ⟨h.1,h.2,hij⟩⟩
      rcases mem_union.1 hp with h | h
      · have hi := (mem_filter.1 h).2
        exact ⟨fun _ hj => hboth ⟨hi,hj⟩, fun _ => hi⟩
      · have hj := (mem_filter.1 h).2
        exact ⟨fun hi => False.elim (hboth ⟨hi,hj⟩), fun hn => False.elim (hn hj)⟩
  have heven := hcut {⟨S, hS⟩}
  rw [hcross] at heven
  have hAB : A ∪ B ⊆ pairsOn (X.biUnion id) :=
    (union_subset (filter_subset _ _) (filter_subset _ _)).trans (hO.trans interPairs_subset_pairsOn)
  have hcard : (symOf (X.biUnion id) (A ∪ B)).card = (A ∪ B).card := by
    calc _ = (sourcePairs (symOf (X.biUnion id) (A ∪ B))).card :=
           (card_image_of_injective _ sourcePair_injective).symm
         _ = _ := congrArg Finset.card (sourcePairs_symOf hAB)
  rw [hcard, card_union_of_disjoint hdis] at heven
  simpa only [blockDeg, inter_empty, card_empty, add_zero] using heven

/-- Actual cut-even subsets, rather than only prescribed original subsets,
transport to valid odd graphs with exactly the same edges. -/
theorem actual_source_odd {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ interPairs X)
    {D : Finset (Sym2 (X.biUnion id))} (hD : D ⊆ symOf (X.biUnion id) S)
    (hcut : CutEven (Sym2.map (Limits.blockOf X)) D) :
    sourcePairs D ⊆ S ∧ symOf (X.biUnion id) (sourcePairs D) = D ∧
      IsParityPair X (sourcePairs D) ∅ := by
  have hs : sourcePairs D ⊆ S := by
    have hi := image_subset_image (f := @sourcePair (X.biUnion id)) hD
    change sourcePairs D ⊆ sourcePairs (symOf (X.biUnion id) S) at hi
    rwa [sourcePairs_symOf (hS.trans interPairs_subset_pairsOn)] at hi
  have hlo : ∀ e ∈ D, ¬ e.IsDiag := by
    intro e he
    obtain ⟨i,j,hij,-,rfl⟩ := mem_symOf.1 (hD he)
    exact Sym2.mk_isDiag_iff.not.2 hij.ne
  have heq := symOf_sourcePairs hlo
  exact ⟨hs,heq,source_cutEven_parity hX (hs.trans hS) (heq.symm ▸ hcut)⟩

/-- Products of symmetric original edge functions are unchanged by transport. -/
theorem prod_source_symmetric {U : Finset ℕ} (D : Finset (Sym2 U)) (f : Sym2 ℕ → ℝ) :
    (∏ p ∈ sourcePairs D, f s(p.1,p.2)) = ∏ e ∈ D, f (Sym2.map Subtype.val e) := by
  rw [prod_sourcePairs]
  apply prod_congr rfl
  intro e _
  induction e using Sym2.ind with
  | h i j =>
    change f s(min i.val j.val,max i.val j.val) = f s(i.val,j.val)
    rcases le_total i.val j.val with h | h
    · rw [min_eq_left h,max_eq_right h]
    · rw [min_eq_right h,max_eq_left h,Sym2.eq_swap]

end MultipoleBKT.ExpansionK.RouteCases

end
