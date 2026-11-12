/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeOne.Partitions

/-!
# Bad sets, partner injections and same-sign partitions

The paper: Lemma 5.40,
(5.125), (5.126) and (5.127).
The charge data remain the interface to fixed-data integration. Here they are projected
onto the successive combinatorial choices made in the written proof.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeOne

open Finset

variable {n : ℕ}

/-- The sign of a charge, positive for `true`. -/
def positive : Charge n → Bool := Sum.elim (fun _ => true) (fun _ => false)

open scoped Classical in
/-- The positive or negative bad-charge set, in the charge carrier. -/
noncomputable def badSet (D : TOData n) (s : Bool) : Finset (Charge n) :=
  univ.filter fun v => positive v = s ∧ D.1 v ≠ 3

/-- The positive bad set is exactly the long or overcrowded positive charges
(Lemma 5.40, Step 2). -/
theorem mem_badSet_typeOneData_inl (p₀ : ℕ) (β lam ε₀ : ℝ)
    (c : Fin n → ℂ × ℂ) (i : Fin n) :
    Sum.inl i ∈ badSet (typeOneData p₀ β lam ε₀ c) true ↔
      longD p₀ β lam ε₀ c i ∨ crowdedP p₀ β lam ε₀ c i := by
  classical
  rw [badSet, Finset.mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩
    simp only [ne_eq, kind_inl_eq_three_iff] at h
    tauto
  · intro h
    refine ⟨rfl, ?_⟩
    simp only [ne_eq, kind_inl_eq_three_iff]
    tauto

/-- The negative bad set uses the inverse stable matching for its length cutoff
(Lemma 5.40, Step 1). -/
theorem mem_badSet_typeOneData_inr (p₀ : ℕ) (β lam ε₀ : ℝ)
    (c : Fin n → ℂ × ℂ) (j : Fin n) :
    Sum.inr j ∈ badSet (typeOneData p₀ β lam ε₀ c) false ↔
      longD p₀ β lam ε₀ c ((stableMatching c).symm j) ∨
        crowdedM p₀ β lam ε₀ c ((stableMatching c).symm j) := by
  classical
  rw [badSet, Finset.mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩
    simp only [ne_eq, kind_inr_eq_three_iff] at h
    tauto
  · intro h
    refine ⟨rfl, ?_⟩
    simp only [ne_eq, kind_inr_eq_three_iff]
    tauto

/-- The extra combinatorial constraints used in the successive enumeration.
They retain the sign of same-sign blocks and the injectivity of the matching on good charges. -/
def Compatible (D : TOData n) : Prop :=
  (∀ v, D.1 v ≠ 3 → positive (D.2.1 v) = positive v) ∧
  (∀ v, D.1 v = 3 → positive (D.2.1 v) = !positive v) ∧
  Set.InjOn D.2.1 {v | D.1 v = 3}

open scoped Classical in
/-- The partner map on the good charges of one sign, extended by the identity elsewhere. -/
noncomputable def partner (D : TOData n) (s : Bool) : Charge n → Charge n :=
  fun v => if positive v = s ∧ D.1 v = 3 then D.2.1 v else v

open scoped Classical in
/-- The retraction encoding the partition of one bad-charge set. -/
noncomputable def partition (D : TOData n) (s : Bool) : Charge n → Charge n :=
  fun v => if v ∈ badSet D s then D.2.1 v else v

theorem kind_cases (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  fin_cases k <;> simp

/-- Bad parents stay in the same bad set. -/
theorem parent_mem_badSet {q : ℕ} {D : TOData n} (hD : TypeOneValid q D)
    (hC : Compatible D) {s : Bool} {v : Charge n} (hv : v ∈ badSet D s) :
    D.2.1 v ∈ badSet D s := by
  classical
  obtain ⟨hs, hk⟩ := (mem_filter.1 hv).2
  refine mem_filter.2 ⟨mem_univ _, (hC.1 v hk).trans hs, ?_⟩
  rcases kind_cases (D.1 v) with h | h | h | h
  · rw [hD.2.2.2.2.1 v (Or.inl h), h]
    norm_num
  · rw [hD.2.2.2.2.1 v (Or.inr h), h]
    norm_num
  · rw [hD.1 v h]
    norm_num
  · exact (hk h).elim

/-- The same-sign parent map is a retraction on its bad set. -/
theorem partition_retract {q : ℕ} {D : TOData n} (hD : TypeOneValid q D)
    (hC : Compatible D) (s : Bool) :
    (∀ v ∉ badSet D s, partition D s v = v) ∧
      ∀ v ∈ badSet D s, partition D s v ∈ badSet D s ∧
        partition D s (partition D s v) = partition D s v := by
  classical
  refine ⟨fun v hv => ite_eq_right hv, fun v hv => ?_⟩
  have hp := parent_mem_badSet hD hC hv
  rw [partition, ite_eq_left hv]
  refine ⟨hp, ?_⟩
  rw [partition, ite_eq_left hp]
  have hk := (mem_filter.1 hv).2.2
  rcases kind_cases (D.1 v) with h | h | h | h
  · rw [hD.2.2.2.2.1 v (Or.inl h)]
    exact hD.2.2.2.2.1 v (Or.inl h)
  · rw [hD.2.2.2.2.1 v (Or.inr h)]
    exact hD.2.2.2.2.1 v (Or.inr h)
  · exact hD.2.2.2.2.1 _ (Or.inl (hD.1 v h))
  · exact (hk h).elim

/-- Representatives are precisely the overcrowded roots and the long singletons. -/
theorem mem_roots_partition {q : ℕ} {D : TOData n} (hD : TypeOneValid q D)
    (s : Bool) (v : Charge n) :
    v ∈ roots (badSet D s) (partition D s) ↔
      positive v = s ∧ (D.1 v = 0 ∨ D.1 v = 1) := by
  classical
  simp only [roots, badSet, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hs, hk⟩, hp⟩
    have hv : v ∈ badSet D s := mem_filter.2 ⟨mem_univ _, hs, hk⟩
    rw [partition, ite_eq_left hv] at hp
    refine ⟨hs, ?_⟩
    rcases kind_cases (D.1 v) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := hD.1 v h
      rw [hp, h] at this
      norm_num at this
    · exact (hk h).elim
  · rintro ⟨hs, hk⟩
    have hn : D.1 v ≠ 3 := by rcases hk with h | h <;> rw [h] <;> norm_num
    refine ⟨⟨hs, hn⟩, ?_⟩
    have hv : v ∈ badSet D s := mem_filter.2 ⟨mem_univ _, hs, hn⟩
    rw [partition, ite_eq_left hv]
    exact hD.2.2.2.2.1 v hk

/-- Each block has the size specified in `Πᵏ`: one or `q + 1`. -/
theorem partition_isPartition {q : ℕ} {D : TOData n} (hD : TypeOneValid q D)
    (hC : Compatible D) (s : Bool) :
    IsPartition q (badSet D s) (partition D s) := by
  classical
  refine ⟨(partition_retract hD hC s).1, (partition_retract hD hC s).2, ?_⟩
  intro r hr
  obtain ⟨hrs, hrk⟩ := (mem_roots_partition hD s r).1 hr
  have hrA : r ∈ badSet D s := (mem_filter.1 hr).1
  have hroot := hD.2.2.2.2.1 r hrk
  have hfiber : (badSet D s).filter (fun v => partition D s v = r) =
      insert r (univ.filter fun v => D.1 v = 2 ∧ D.2.1 v = r) := by
    ext v
    simp only [mem_filter, mem_insert, mem_univ, true_and]
    constructor
    · rintro ⟨hv, hp⟩
      rw [partition, ite_eq_left hv] at hp
      by_cases hvr : v = r
      · exact Or.inl hvr
      · right
        refine ⟨?_, hp⟩
        rcases kind_cases (D.1 v) with h | h | h | h
        · exact (hvr ((hD.2.2.2.2.1 v (Or.inl h)).symm.trans hp)).elim
        · exact (hvr ((hD.2.2.2.2.1 v (Or.inr h)).symm.trans hp)).elim
        · exact h
        · exact ((mem_filter.1 hv).2.2 h).elim
    · rintro (rfl | ⟨hk, hp⟩)
      · exact ⟨hrA, by rw [partition, ite_eq_left hrA, hroot]⟩
      · have hv : v ∈ badSet D s := by
          refine mem_filter.2 ⟨mem_univ _, ?_, by rw [hk]; norm_num⟩
          have he := hC.1 v (by rw [hk]; norm_num)
          rw [hp] at he
          exact he.symm.trans hrs
        exact ⟨hv, by rw [partition, ite_eq_left hv, hp]⟩
  have hnot : r ∉ (univ.filter fun v => D.1 v = 2 ∧ D.2.1 v = r) := by
    simp only [mem_filter, mem_univ, true_and, not_and]
    intro hk
    rcases hrk with h | h <;> rw [h] at hk <;> norm_num at hk
  rw [hfiber, card_insert_of_notMem hnot]
  rcases hrk with hk | hk
  · right
    rw [hD.2.2.1 r hk]
  · left
    have he : (univ.filter fun v => D.1 v = 2 ∧ D.2.1 v = r) = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro v hv
      obtain ⟨hv, hp⟩ := (mem_filter.1 hv).2
      have he := hD.1 v hv
      rw [hp, hk] at he
      norm_num at he
    rw [he, card_empty]

/-- The paper's matching gives injective partners of opposite sign. -/
theorem typeOneData_compatible (p₀ : ℕ) (β lam ε₀ : ℝ) (c : Fin n → ℂ × ℂ) :
    Compatible (typeOneData p₀ β lam ε₀ c) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro (i | j) hv
    · rw [typeOneData_par_inl]
      split_ifs with hc hl
      · rfl
      · rfl
      · exact (hv ((kind_inl_eq_three_iff i).2 ⟨hc, hl⟩)).elim
    · rw [typeOneData_par_inr]
      split_ifs with hc hl
      · rfl
      · rfl
      · exact (hv ((kind_inr_eq_three_iff j).2 ⟨hc, hl⟩)).elim
  · rintro (i | j) hv
    · obtain ⟨hc, hl⟩ := (kind_inl_eq_three_iff i).1 hv
      rw [typeOneData_par_inl, ite_eq_right hc, ite_eq_right hl]
      rfl
    · obtain ⟨hc, hl⟩ := (kind_inr_eq_three_iff j).1 hv
      rw [typeOneData_par_inr, ite_eq_right hc, ite_eq_right hl]
      rfl
  · intro v hv w hw he
    rcases v with i | j <;> rcases w with i' | j'
    · obtain ⟨hc, hl⟩ := (kind_inl_eq_three_iff i).1 hv
      obtain ⟨hc', hl'⟩ := (kind_inl_eq_three_iff i').1 hw
      rw [typeOneData_par_inl, ite_eq_right hc, ite_eq_right hl,
        typeOneData_par_inl, ite_eq_right hc', ite_eq_right hl', Sum.inr.injEq] at he
      exact congrArg Sum.inl ((stableMatching c).injective he)
    · obtain ⟨hc, hl⟩ := (kind_inl_eq_three_iff i).1 hv
      obtain ⟨hc', hl'⟩ := (kind_inr_eq_three_iff j').1 hw
      rw [typeOneData_par_inl, ite_eq_right hc, ite_eq_right hl,
        typeOneData_par_inr, ite_eq_right hc', ite_eq_right hl'] at he
      cases he
    · obtain ⟨hc, hl⟩ := (kind_inr_eq_three_iff j).1 hv
      obtain ⟨hc', hl'⟩ := (kind_inl_eq_three_iff i').1 hw
      rw [typeOneData_par_inr, ite_eq_right hc, ite_eq_right hl,
        typeOneData_par_inl, ite_eq_right hc', ite_eq_right hl'] at he
      cases he
    · obtain ⟨hc, hl⟩ := (kind_inr_eq_three_iff j).1 hv
      obtain ⟨hc', hl'⟩ := (kind_inr_eq_three_iff j').1 hw
      rw [typeOneData_par_inr, ite_eq_right hc, ite_eq_right hl,
        typeOneData_par_inr, ite_eq_right hc', ite_eq_right hl', Sum.inl.injEq] at he
      exact congrArg Sum.inr ((stableMatching c).symm.injective he)

end MultipoleBKT.BadPointTypes.RouteTypeOne

end
