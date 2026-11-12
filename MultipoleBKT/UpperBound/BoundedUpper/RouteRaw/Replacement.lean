/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.ComponentBound

/-!
# Lengths and quadratic tails of all replacement trees

The paper: proof of
Proposition 5.18. An edge changed in `B(·, T)`
is shorter than the larger endpoint radius. Unchanged edges retain the
comparison with the distance of a maximal-radius dipole to the bad points.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open Finset SimpleGraph Peeling CoreForest Quadratic
open scoped Classical NNReal

variable {X : Finset (Finset ℕ)} {r : X.biUnion id → ℝ}
  {d : Sym2 (X.biUnion id) → ℝ} {T U : SimpleGraph (X.biUnion id)}

/-- Every new edge in the replacement family is short. This is the
replacement-edge assertion in Proposition 5.18. -/
theorem replacement_edge_short (hU : U ∈ longAgreeingTrees X r d T)
    {e : Sym2 (X.biUnion id)} (he : e ∈ U.edgeSet) (heT : e ∉ T.edgeSet) :
    d e < radMax r e := by
  have hagree := (mem_filter.1 hU).2 e
  by_contra h
  exact heT (hagree.1 ⟨he, le_of_not_gt h⟩).1

/-- For every replacement tree, the edges shared with the original tree retain their length bound
and each new edge is bounded by the largest radius. -/
theorem replacement_edge_le (hU : U ∈ longAgreeingTrees X r d T)
    {R D : ℝ} (hr : ∀ i, r i ≤ R) (hRD : R ≤ D)
    (hT : ∀ e ∈ T.edgeSet, d e ≤ D) {e : Sym2 (X.biUnion id)}
    (he : e ∈ U.edgeSet) : d e ≤ D := by
  by_cases heT : e ∈ T.edgeSet
  · exact hT e heT
  · refine (replacement_edge_short hU he heT).le.trans ((show radMax r e ≤ R from ?_).trans hRD)
    induction e using Sym2.ind with
    | h i j => exact max_le (hr i) (hr j)

/-- The maximum is bounded uniformly over the whole replacement family. -/
theorem replacement_max_le (hU : U ∈ longAgreeingTrees X r d T)
    {R D : ℝ} (hr : ∀ i, r i ≤ R) (hRD : R ≤ D) (hD : 0 ≤ D)
    (hT : ∀ e ∈ T.edgeSet, d e ≤ D) :
    ((U.edgeFinset.sup fun e => (d e).toNNReal : ℝ≥0) : ℝ) ≤ D := by
  have h : (U.edgeFinset.sup fun e => (d e).toNNReal) ≤ ⟨D, hD⟩ := by
    refine Finset.sup_le fun e he => Real.toNNReal_le_iff_le_coe.2 ?_
    exact replacement_edge_le hU hr hRD hT (mem_edgeFinset.1 he)
  exact_mod_cast h

/-- The unmarked tail of the retained tree also bounds the tail needed
for each replacement tree. New edges have length at most `R`. -/
theorem treeTail_le_replacement (hU : U ∈ longAgreeingTrees X r d T)
    {R : ℝ} (hR : 0 < R) (hr : ∀ i, r i ≤ R) (hd : ∀ e, 0 ≤ d e) :
    treeTail d T R ≤ treeTail d U R := by
  let m : ℝ := ((T.edgeFinset.sup fun e => (d e).toNNReal : ℝ≥0) : ℝ)
  have hm : ∀ e ∈ T.edgeSet, d e ≤ max m R := by
    intro e he
    have h := Finset.le_sup (f := fun e => (d e).toNNReal) (mem_edgeFinset.2 he)
    have h' : d e ≤ m := by
      dsimp [m]
      rw [← Real.coe_toNNReal (d e) (hd e)]
      exact_mod_cast h
    exact h'.trans (le_max_left _ _)
  have hmax := replacement_max_le hU hr (le_max_right m R)
    (hR.le.trans (le_max_right m R)) hm
  unfold treeTail
  apply pow_le_pow_left₀ (div_nonneg hR.le (hR.le.trans (le_max_right _ _))) _ 2
  apply div_le_div_of_nonneg_left hR.le (hR.trans_le (le_max_right _ _))
  exact max_le hmax (le_max_right _ _)

/-- The marked bad-distance gain supplies the required quadratic tail
for every member of `B(·, T)`, including all changed edges. -/
theorem sq_div_le_replacement_tail (hU : U ∈ longAgreeingTrees X r d T)
    {R δ K : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hRδ : R ≤ δ)
    (hr : ∀ i, r i ≤ R) (hK : 1 ≤ K)
    (hT : ∀ e ∈ T.edgeSet, d e ≤ 2 * K * δ) :
    R ^ 2 / δ ^ 2 ≤ 4 * K ^ 2 * treeTail d U R := by
  have hRD : R ≤ 2 * K * δ := by nlinarith
  exact sq_div_le_tail hR hδ hRδ (NNReal.coe_nonneg _)
    (replacement_max_le hU hr hRD (hR.trans hRD) hT) hK

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
