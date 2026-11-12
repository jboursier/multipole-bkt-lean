/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Fold
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# One maximal-distance tail

See (A.30).
The empty odd tree has tail one. On a nonempty tree the finite minimum below equals
`min(1, R² / max_e d_e²)`. Multiplying component tails retains a single global tail.
-/

@[expose] public section

namespace MultipoleBKT.Limits

open Finset

/-- The maximal-distance tail, with value one for an empty edge set. -/
noncomputable def globalTail {ε : Type*} (R : ℝ) (d : ε → ℝ) (T : Finset ε) : ℝ :=
  T.fold min 1 fun e => min 1 (R ^ 2 / d e ^ 2)

theorem globalTail_nonneg {ε : Type*} (R : ℝ) (d : ε → ℝ) (T : Finset ε) :
    0 ≤ globalTail R d T :=
  (le_fold_min _).2 ⟨zero_le_one, fun _ _ => le_min zero_le_one (div_nonneg (sq_nonneg _) (sq_nonneg _))⟩

theorem globalTail_le_one {ε : Type*} (R : ℝ) (d : ε → ℝ) (T : Finset ε) :
    globalTail R d T ≤ 1 := (fold_min_le _).2 (Or.inl le_rfl)

theorem globalTail_le {ε : Type*} {R : ℝ} {d : ε → ℝ} {T : Finset ε} {e : ε} (he : e ∈ T) :
    globalTail R d T ≤ min 1 (R ^ 2 / d e ^ 2) := (fold_min_le _).2 (Or.inr ⟨e, he, le_rfl⟩)

/-- Tail factors multiply to at most the tail on the union. -/
theorem globalTail_mul_le_union {ε : Type*} [DecidableEq ε] (R : ℝ) (d : ε → ℝ)
    (S T : Finset ε) : globalTail R d S * globalTail R d T ≤ globalTail R d (S ∪ T) := by
  refine (le_fold_min _).2 ⟨?_, ?_⟩
  · exact (mul_le_of_le_one_right (globalTail_nonneg R d S) (globalTail_le_one R d T)).trans
      (globalTail_le_one R d S)
  · intro e he
    rcases mem_union.1 he with he | he
    · exact (mul_le_of_le_one_right (globalTail_nonneg R d S) (globalTail_le_one R d T)).trans
        (globalTail_le he)
    · exact (mul_le_of_le_one_left (globalTail_nonneg R d T) (globalTail_le_one R d S)).trans
        (globalTail_le he)

/-- Enlarging a component radius enlarges its maximal-distance tail. -/
theorem globalTail_mono_radius {ε : Type*} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (d : ε → ℝ) (T : Finset ε) : globalTail r d T ≤ globalTail R d T := by
  refine (le_fold_min _).2 ⟨globalTail_le_one _ _ _, fun e he => ?_⟩
  exact (globalTail_le he).trans (min_le_min_left _
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hr hrR 2) (sq_nonneg _)))

/-- The component tails give the single global tail displayed after (A.30).
-/
theorem prod_globalTail_le_biUnion {α ε : Type*} [DecidableEq ε]
    (C : Finset α) (r : α → ℝ) (R : ℝ) (d : ε → ℝ) (T : α → Finset ε)
    (hr : ∀ i ∈ C, 0 ≤ r i) (hR : ∀ i ∈ C, r i ≤ R) :
    ∏ i ∈ C, globalTail (r i) d (T i) ≤ globalTail R d (C.biUnion T) := by
  classical
  revert hr hR
  induction C using Finset.induction_on with
  | empty => simp [globalTail]
  | @insert i C hi ih =>
    intro hr hR
    rw [prod_insert hi, biUnion_insert]
    calc globalTail (r i) d (T i) * ∏ j ∈ C, globalTail (r j) d (T j)
        ≤ globalTail R d (T i) * globalTail R d (C.biUnion T) :=
          mul_le_mul (globalTail_mono_radius (hr i (mem_insert_self _ _)) (hR i (mem_insert_self _ _)) d (T i))
            (ih (fun j hj => hr j (mem_insert_of_mem hj)) (fun j hj => hR j (mem_insert_of_mem hj)))
            (prod_nonneg fun j _ => globalTail_nonneg _ _ _) (globalTail_nonneg _ _ _)
      _ ≤ _ := globalTail_mul_le_union _ _ _ _

/-- Reindexing the tail by an edge map does not introduce multiplicities. -/
theorem globalTail_image {ε η : Type*} [DecidableEq ε] (R : ℝ) (d : ε → ℝ)
    (f : η → ε) (T : Finset η) : globalTail R d (T.image f) = globalTail R (d ∘ f) T := by
  exact fold_image_idem

/-- Identification with the displayed maximal-distance tail. -/
theorem globalTail_eq_of_max {ε : Type*} {R : ℝ} {d : ε → ℝ} {T : Finset ε} {e : ε}
    (he : e ∈ T) (hd : ∀ f ∈ T, 0 < d f) (hm : ∀ f ∈ T, d f ≤ d e) :
    globalTail R d T = min 1 (R ^ 2 / d e ^ 2) := by
  refine le_antisymm (globalTail_le he) ((le_fold_min _).2 ⟨min_le_left _ _, ?_⟩)
  intro f hf
  exact min_le_min_left _ (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos (hd f hf))
    (pow_le_pow_left₀ (hd f hf).le (hm f hf) 2))

/-- The longest edge of the whole ear family controls the tail of every
retained tree. See the proof of Lemma A.5. -/
theorem tail_le_globalTail_image {ε : Type*} {R D : ℝ} (d : ε → ℝ)
    (T : Finset ε) (hd : ∀ e ∈ T, 0 < d e) (hm : ∀ e ∈ T, d e ≤ D) :
    min 1 (R ^ 2 / D ^ 2) ≤ globalTail R d T := by
  classical
  by_cases hT : T.Nonempty
  · obtain ⟨e, he, hmax⟩ := exists_max_image T d hT
    rw [globalTail_eq_of_max he hd hmax]
    exact min_le_min_left _ (div_le_div_of_nonneg_left (sq_nonneg _)
      (sq_pos_of_pos (hd e he)) (pow_le_pow_left₀ (hd e he).le (hm e he) 2))
  · have hT : T = ∅ := not_nonempty_iff_eq_empty.1 hT
    simpa only [hT, globalTail, fold_empty] using min_le_left 1 (R ^ 2 / D ^ 2)

end MultipoleBKT.Limits

end
