/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Symmetrize

/-!
# The specified reversal averages and their subgroups

See (4.48), (4.50), and Lemma 4.26.
Averaging over the original parts absorbs averaging over any merged parts.
This is a pointwise identity, before integration or absolute values.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open Finset MeasureTheory
open scoped Classical

variable {ι B C : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- The operator `Sym` for the parts specified by `blk`. -/
noncomputable def reversalAverage (blk : ι → B) (F : (ι → ℂ × ℂ) → ℝ)
    (c : ι → ℂ × ℂ) : ℝ :=
  (∑ A : Finset B, F (flipCfg (blockLabels blk A) c)) / 2 ^ Fintype.card B

omit [Fintype ι] in
/-- Reversals form the symmetric-difference group of label sets. -/
theorem flipCfg_symmDiff (A D : Finset ι) (c : ι → ℂ × ℂ) :
    flipCfg A (flipCfg D c) = flipCfg (symmDiff A D) c := by
  funext i
  by_cases ha : i ∈ A <;> by_cases hd : i ∈ D <;>
    simp [flipCfg, Finset.mem_symmDiff, ha, hd]

omit [Fintype B] in
/-- Pulling back block sets commutes with symmetric difference. -/
theorem blockLabels_symmDiff (blk : ι → B) (A D : Finset B) :
    blockLabels blk (symmDiff A D) = symmDiff (blockLabels blk A) (blockLabels blk D) := by
  ext i
  simp only [mem_blockLabels, Finset.mem_symmDiff]

omit [DecidableEq ι] [Fintype C] in
/-- Pullback through a merger of the original parts. -/
theorem blockLabels_comp (blk : ι → B) (q : B → C) (A : Finset C) :
    blockLabels (q ∘ blk) A = blockLabels blk (blockLabels q A) := by
  ext i
  simp only [mem_blockLabels, Function.comp_apply]

/-- A shift in the reversal group leaves its average unchanged. -/
theorem reversalAverage_comp_flip (blk : ι → B) (D : Finset B)
    (F : (ι → ℂ × ℂ) → ℝ) (c : ι → ℂ × ℂ) :
    reversalAverage blk (fun c => F (flipCfg (blockLabels blk D) c)) c =
      reversalAverage blk F c := by
  unfold reversalAverage
  congr 1
  simp_rw [flipCfg_symmDiff, ← blockLabels_symmDiff]
  have hinv : Function.Involutive (fun A : Finset B => symmDiff D A) :=
    fun A => symmDiff_symmDiff_cancel_left D A
  exact Fintype.sum_equiv (hinv.toPerm _) _ _ (fun A => rfl)

/-- The subgroup averaging identity used for both `G'` and `G''`.
The original parts are indexed by `B`, and `q` merges them into `C`. -/
theorem reversalAverage_subgroup (blk : ι → B) (q : B → C)
    (F : (ι → ℂ × ℂ) → ℝ) (c : ι → ℂ × ℂ) :
    reversalAverage blk (reversalAverage (q ∘ blk) F) c = reversalAverage blk F c := by
  unfold reversalAverage
  simp_rw [← Finset.sum_div]
  rw [Finset.sum_comm]
  have hshift (D : Finset C) :
      (∑ A : Finset B, F (flipCfg (blockLabels (q ∘ blk) D)
        (flipCfg (blockLabels blk A) c))) =
      ∑ A : Finset B, F (flipCfg (blockLabels blk A) c) := by
    have h := reversalAverage_comp_flip blk (blockLabels q D) F c
    rw [blockLabels_comp] at *
    exact (div_left_inj' (by positivity : (2 : ℝ) ^ Fintype.card B ≠ 0)).mp h
  simp_rw [hshift]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- Measurability of a finite reversal average. -/
theorem measurable_reversalAverage (blk : ι → B) {F : (ι → ℂ × ℂ) → ℝ}
    (hF : Measurable F) : Measurable (reversalAverage blk F) :=
  (Finset.measurable_sum _ fun _ _ => hF.comp (measurable_flipCfg _)).div_const _

end MultipoleBKT.Limits.RouteDirect

end
