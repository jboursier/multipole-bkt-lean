/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Core

/-!
# Cayley count and maximum over the near trees

The proof of Lemma 4.58. Count actual spanning trees
in each block, including the unique tree of a singleton block. The product
of Cayley counts is kept explicit until the spatial bound is assembled.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RoutePosition

open Finset SimpleGraph SmallIntegral.RouteJ
open scoped Classical ENNReal

/-- Cayley's count for every nonempty fibre, including singleton fibres.
proof of Lemma 4.58. -/
theorem card_fibre_trees {W : Type*} [Fintype W] (hW : 0 < Fintype.card W) :
    Fintype.card {T : SimpleGraph W // T.IsTree} =
      Fintype.card W ^ (Fintype.card W - 2) := by
  by_cases h2 : 2 ≤ Fintype.card W
  · rw [Fintype.card_subtype]
    exact card_isTree_eq_pow h2
  · have hc : Fintype.card W = 1 := by omega
    let : Nonempty W := Fintype.card_pos_iff.mp hW
    let : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    simp only [Fintype.card_subtype, IsTree.of_subsingleton, filter_true]
    rw [card_univ, Fintype.card_unique, hc]
    rfl

private theorem nat_card_fibre_trees {W : Type*} [Fintype W]
    (hW : 0 < Fintype.card W) :
    Nat.card {T : SimpleGraph W // T.IsTree} =
      Fintype.card W ^ (Fintype.card W - 2) := by
  rw [Nat.card_eq_fintype_card]
  exact card_fibre_trees hW

/-- The literal product of Cayley counts for the near-tree family.
proof of Lemma 4.58. -/
theorem card_nearTreeFamily_eq {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
    (blk : V → B) (hblk : Function.Surjective blk) :
    Fintype.card (NearTreeFamily blk) =
      ∏ b, Fintype.card {i // blk i = b} ^ (Fintype.card {i // blk i = b} - 2) := by
  rw [Fintype.card_pi]
  apply prod_congr rfl
  intro b _
  obtain ⟨i, hi⟩ := hblk b
  let : Nonempty {i // blk i = b} := ⟨⟨i, hi⟩⟩
  rw [← Nat.card_eq_fintype_card]
  exact nat_card_fibre_trees Fintype.card_pos

/-- The finite supremum over near-tree families is attained.
the maximum in the proof of Lemma 4.58. -/
theorem exists_nearTreeFamily_max {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] [DecidableEq B] (blk : V → B) (hblk : Function.Surjective blk)
    (J₁ : NearTreeFamily blk → ℝ≥0∞) : ∃ R, J₁ R = ⨆ Q, J₁ Q := by
  have hp : 0 < Fintype.card (NearTreeFamily blk) := by
    rw [card_nearTreeFamily_eq blk hblk]
    apply prod_pos
    intro b _
    obtain ⟨i, hi⟩ := hblk b
    have : Nonempty {i // blk i = b} := ⟨⟨i, hi⟩⟩
    exact Nat.pow_pos Fintype.card_pos
  have : Nonempty (NearTreeFamily blk) := Fintype.card_pos_iff.mp hp
  exact exists_eq_ciSup_of_finite

/-- A finite tree sum is bounded by the exact Cayley count times its maximum.
The supremum is a maximum whenever the family is nonempty.
proof of Lemma 4.58. -/
theorem sum_nearTreeFamily_le_count_mul_max {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
    (blk : V → B) (hblk : Function.Surjective blk) (J₁ : NearTreeFamily blk → ℝ≥0∞) :
    (∑ R, J₁ R) ≤
      (∏ b, Fintype.card {i // blk i = b} ^ (Fintype.card {i // blk i = b} - 2) : ℕ) *
        ⨆ R, J₁ R := by
  obtain ⟨Rmax, hmax⟩ := exists_nearTreeFamily_max blk hblk J₁
  have hle (R : NearTreeFamily blk) : J₁ R ≤ J₁ Rmax := by
    rw [hmax]
    exact le_iSup J₁ R
  calc
    _ ≤ ∑ _R : NearTreeFamily blk, ⨆ R, J₁ R := by
      rw [← hmax]
      exact sum_le_sum fun R _ => hle R
    _ = (Fintype.card (NearTreeFamily blk) : ℝ≥0∞) * ⨆ R, J₁ R := by
      rw [sum_const, card_univ, nsmul_eq_mul]
    _ = _ := by rw [card_nearTreeFamily_eq blk hblk]

/-- Only at the end do bounded block sizes absorb the Cayley product into `C^k`.
proof of Lemma 4.58. -/
theorem cayley_product_le {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
    (blk : V → B) {p : ℕ} (hp : ∀ b, Fintype.card {i // blk i = b} ≤ p) :
    (∏ b, Fintype.card {i // blk i = b} ^ (Fintype.card {i // blk i = b} - 2)) ≤
      2 ^ (p * Fintype.card V) := by
  have hfib : ∑ b, Fintype.card {i // blk i = b} = Fintype.card V := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv blk)
  calc
    _ ≤ ∏ b, (2 ^ p) ^ Fintype.card {i // blk i = b} := by
      apply prod_le_prod
      intro b _
      exact (Nat.pow_le_pow_left ((hp b).trans (Nat.le_of_lt p.lt_two_pow_self)) _).trans
        (Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) (by omega))
    _ = 2 ^ (p * Fintype.card V) := by
      rw [prod_pow_eq_pow_sum, hfib, ← pow_mul]

end MultipoleBKT.AbsoluteLower.RoutePosition

end
