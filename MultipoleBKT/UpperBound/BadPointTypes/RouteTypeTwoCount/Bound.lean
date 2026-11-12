/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Integral
public import MultipoleBKT.UpperBound.BadPointTypes.Exponential
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Homogeneous

/-!
# Integrated partition sums and their exponential bound

The paper: (5.141).
First integrate each fixed partition, then enumerate its size profile, then sum
the factorial denominators as an exponential series.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open MeasureTheory Finset SetPartition RouteTypeTwoCount
open scoped ENNReal Classical

variable {n : ℕ} {M lam : ℝ}

/-- The integrated partition sum with real, nonnegative block bounds. -/
theorem lintegral_classWeight_le_partitionSum (A : ℕ → Prop) {w : ℂ × ℂ → ℝ≥0∞}
    (hw : Measurable w) (b : ℕ → ℝ) (hb0 : ∀ m, 0 ≤ b m)
    (hb : ∀ T : Finset (Fin n), A T.card →
      ∫⁻ y : T → ℂ × ℂ, blockWeight M lam w y ≤ ENNReal.ofReal (b T.card)) :
    ∫⁻ c : Fin n → ℂ × ℂ, classWeight M lam A w univ c ≤
      ENNReal.ofReal (∑ π ∈ partitions (univ : Finset (Fin n)),
        ∏ T ∈ π, if A T.card then b T.card else 0) := by
  refine (lintegral_classWeight_le_partitions A hw (fun m => ENNReal.ofReal (b m)) hb).trans
    (le_of_eq ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun π _ => prod_nonneg fun T _ => by split_ifs <;> simp [hb0])]
  apply sum_congr rfl
  intro π _
  rw [ENNReal.ofReal_prod_of_nonneg (fun T _ => by split_ifs <;> simp [hb0])]
  apply prod_congr rfl
  intro T _
  split_ifs <;> simp

/-- The exponential estimate obtained by explicit partition enumeration. -/
theorem lintegral_classWeight_le_exp (A : ℕ → Prop) {w : ℂ × ℂ → ℝ≥0∞}
    (hw : Measurable w) (b : ℕ → ℝ) (hb0 : ∀ m, 0 ≤ b m)
    (hb : ∀ T : Finset (Fin n), A T.card →
      ∫⁻ y : T → ℂ × ℂ, blockWeight M lam w y ≤ ENNReal.ofReal (b T.card))
    {y : ℝ} (hy : 0 < y) :
    ∫⁻ c : Fin n → ℂ × ℂ, classWeight M lam A w univ c ≤
      ENNReal.ofReal (n.factorial / y ^ n * Real.exp (∑ m ∈ range n,
        (if A (m + 1) then b (m + 1) else 0) / (m + 1).factorial * y ^ (m + 1))) := by
  refine (lintegral_classWeight_le_partitionSum A hw b hb0 hb).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := sum_partitions_le_exp (univ : Finset (Fin n))
    (b := fun m => if A m then b m else 0) (fun m => by split_ifs <;> simp [hb0]) hy
  simpa only [card_univ, Fintype.card_fin] using h

/-- Fixed-size blocks: the count and the integrated contribution are explicit. -/
theorem lintegral_classWeight_homogeneous_le {w : ℂ × ℂ → ℝ≥0∞}
    (hw : Measurable w) {k q : ℕ} (hk : 1 ≤ k) (hn : k * q = n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ T : Finset (Fin n), T.card = k →
      ∫⁻ y : T → ℂ × ℂ, blockWeight M lam w y ≤ ENNReal.ofReal B) :
    ∫⁻ c : Fin n → ℂ × ℂ, classWeight M lam (· = k) w univ c ≤
      ENNReal.ofReal (n.factorial / (k.factorial ^ q * q.factorial) * B ^ q) := by
  refine (lintegral_classWeight_le_partitionSum (· = k) hw (fun _ => B) (fun _ => hB) hb).trans
    (le_of_eq ?_)
  congr 1
  rw [← sum_filter_of_ne (s := partitions (univ : Finset (Fin n)))
    (p := fun π => ∀ S ∈ π, S.card = k) (fun π _ hne => ?_)]
  · have he : ((partitions (univ : Finset (Fin n))).filter
        (fun π => ∀ S ∈ π, S.card = k)) = homogeneous univ k := by
      ext π
      simp only [homogeneous, mem_filter]
    rw [he]
    have hs := sum_homogeneous (univ : Finset (Fin n)) hk (by simpa using hn) B
    refine Eq.trans ?_ (by simpa only [card_univ, Fintype.card_fin] using hs)
    apply sum_congr rfl
    intro π hπ
    apply prod_congr rfl
    intro T hT
    simp only [(mem_homogeneous.1 hπ).2 T hT, ite_true]
  · intro T hT
    by_contra h
    exact hne (prod_eq_zero hT (ite_eq_right h))

end MultipoleBKT.BadPointTypes

end
