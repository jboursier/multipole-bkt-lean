/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Euler
public import MultipoleBKT.UpperBound.SimplifiedUpper.Series

/-!
# The lower inner series and the common merger

The proof of Lemma 4.57. The factorials remove the
orderings of the disjoint groups. The lower inner series is the finite
family sum used by the upper merger. The paper sets this series to zero
on outer groups of at most one block.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower

open Finset Multipole Hierarchical SetPartition Parity
open scoped Classical

/-- The literal `𝓛'` in proof of Lemma 4.57,
including its specified value on groups of at most one block. -/
noncomputable def sourceInnerSeries (M lam ε₀ R : ℝ) (Y : Finset (Finset ℕ))
    (c : ℕ → ℂ × ℂ) : ℝ :=
  if 2 ≤ Y.card then innerSeries M lam ε₀ R Y c else 0

theorem sourceInnerSeries_nonneg (M lam ε₀ R : ℝ) (Y : Finset (Finset ℕ))
    (c : ℕ → ℂ × ℂ) : 0 ≤ sourceInnerSeries M lam ε₀ R Y c := by
  unfold sourceInnerSeries
  split_ifs
  · exact innerSeries_nonneg _ _
  · exact le_rfl

/-- The factorial-weighted lower series equals the family sum of the
proved merger. Small inner groups have no odd relative tree. -/
theorem innerSeries_eq_family {M lam ε₀ R : ℝ} {Y : Finset (Finset ℕ)}
    (hY : IsSubpartition Y) (c : ℕ → ℂ × ℂ) :
    innerSeries M lam ε₀ R Y c =
      UpperBound.SimplifiedUpper.innerSeries M lam ε₀ R c Y := by
  let A := UpperBound.SimplifiedUpper.treeWeightA M lam ε₀ R c
  let B := UpperBound.SimplifiedUpper.treeWeightB M lam ε₀ R c Y
  have hterm (n : ℕ) :
      (∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesD Y n,
        (∏ l, A (Xs l)) * B (univ.image Xs)) =
      ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesT Y n,
        (∏ l, A (Xs l)) * B (univ.image Xs) := by
    symm
    apply sum_subset (UpperBound.SimplifiedUpper.tuplesT_subset_tuplesD Y n)
    intro Xs hD hT
    obtain ⟨hsub, hd⟩ := mem_filter.mp hD
    have hs : ∀ l, Xs l ⊆ Y := fun l => mem_powerset.mp (Fintype.mem_piFinset.mp hsub l)
    have hsmall : ∃ l, (Xs l).card ≤ 1 := by
      by_contra h
      push Not at h
      exact hT (UpperBound.SimplifiedUpper.mem_tuplesT.mpr ⟨hs, hd, fun l => by
        have := h l
        omega⟩)
    obtain ⟨l, hl⟩ := hsmall
    have hzero : A (Xs l) = 0 := by
      dsimp only [A, UpperBound.SimplifiedUpper.treeWeightA]
      rw [relTreePairs_eq_empty_of_card_le_one (isSubpartition_mono hY (hs l)) hl,
        sum_empty, mul_zero]
    rw [prod_eq_zero (mem_univ l) hzero, zero_mul]
  have heq : innerSeries M lam ε₀ R Y c =
      ∑ n ∈ range (Y.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesT Y n,
          (∏ l, A (Xs l)) * B (univ.image Xs) := by
    unfold innerSeries
    change (∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesD Y n,
        (∏ l, A (Xs l)) * B (univ.image Xs)) = _
    simp_rw [hterm]
    apply tsum_eq_sum
    intro n hn
    rw [UpperBound.SimplifiedUpper.tuplesT_eq_empty (by
      have := not_lt.mp (fun h => hn (mem_range.mpr h))
      omega), sum_empty, mul_zero]
  rw [heq]
  have hprod {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
      (hXs : Xs ∈ UpperBound.SimplifiedUpper.tuplesT Y n) :
      (∏ l, A (Xs l)) = ∏ G ∈ univ.image Xs, A G := by
    obtain ⟨_, hd, h2⟩ := UpperBound.SimplifiedUpper.mem_tuplesT.mp hXs
    have hinj := injective_of_disjoint hd
      (fun i => card_pos.mp (by have := h2 i; omega))
    rw [prod_image (fun i _ j _ h => hinj h)]
  simp_rw [sum_congr rfl (fun Xs hXs => congrArg (· * B (univ.image Xs)) (hprod Xs hXs))]
  exact UpperBound.SimplifiedUpper.sum_tuplesT_eq
    (fun G => (∏ Z ∈ G, A Z) * B G)

/-- Merging the two even-tree levels records the former groups by marked
outer edges, proof of Lemma 4.57. The factor is the
marking bound supplied by `MergeSum.merge_le`. -/
theorem source_inner_merge {M lam ε₀ R : ℝ} {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (c : ℕ → ℂ × ℂ) :
    (∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesT X n,
        (∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
          ∏ q ∈ Tb, absEvenWeight M lam ε₀ R (c q.1) (c q.2)) *
        ∏ l, sourceInnerSeries M lam ε₀ R (Xs l) c) ≤
      2 ^ X.card *
        ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
          ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesD X n,
            ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
              ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
                UpperBound.SimplifiedUpper.treeProd M lam ε₀ R Xs Ta Tb c := by
  have heq {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
      (hXs : Xs ∈ UpperBound.SimplifiedUpper.tuplesT X n) :
      (∏ l, sourceInnerSeries M lam ε₀ R (Xs l) c) =
        ∏ l, UpperBound.SimplifiedUpper.innerSeries M lam ε₀ R c (Xs l) := by
    obtain ⟨hs, _, h2⟩ := UpperBound.SimplifiedUpper.mem_tuplesT.mp hXs
    apply prod_congr rfl
    intro l _
    rw [sourceInnerSeries, ite_eq_left (h2 l)]
    exact innerSeries_eq_family (isSubpartition_mono hX (hs l)) c
  simp_rw [sum_congr rfl (fun Xs hXs => congrArg
    ((∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
      ∏ q ∈ Tb, absEvenWeight M lam ε₀ R (c q.1) (c q.2)) * ·) (heq Xs hXs))]
  exact (UpperBound.SimplifiedUpper.sum_tuples_inner_le hX c).trans
    (mul_le_mul_of_nonneg_left (UpperBound.SimplifiedUpper.innerSeries_le_tuples c)
      (by positivity))

end MultipoleBKT.AbsoluteLower

end
