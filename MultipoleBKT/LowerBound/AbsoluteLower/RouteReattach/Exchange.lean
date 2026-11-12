/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.TreeCount

/-!
# Exchanging the original and reattached tree sums

(4.102), (4.101).
The fibers record all original trees that can produce a fixed reattached tree.
Their cardinalities are bounded by the determinant forest estimate (4.71).
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteReattach

open Finset Peeling
open scoped Classical

variable {X : Finset (Finset ℕ)}

/-- Original trees that can reattach to `T`, the fiber in (4.102). -/
noncomputable def predecessors (r : X.biUnion id → ℝ) (d : Sym2 (X.biUnion id) → ℝ)
    (T : SimpleGraph (X.biUnion id)) : Finset (SimpleGraph (X.biUnion id)) :=
  (relTrees X).filter fun T₀ => T ∈ longAgreeingTrees X r d T₀

/-- Exchange the two tree sums and evaluate the inner sum as a fiber cardinality.
This is the first line of (4.102) in the proof of Lemma 4.55. -/
theorem exchange (r : X.biUnion id → ℝ) (d : Sym2 (X.biUnion id) → ℝ)
    (w : SimpleGraph (X.biUnion id) → ℝ) :
    ∑ T₀ ∈ relTrees X, ∑ T ∈ longAgreeingTrees X r d T₀, w T =
      ∑ T ∈ relTrees X, (predecessors r d T).card * w T := by
  simp only [longAgreeingTrees, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun T hT => ?_
  simp only [predecessors, longAgreeingTrees, mem_filter, hT, true_and]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]

/-- The multiplicity estimate after the exchange, obtained from the determinant
forest count, equation (4.71) and (4.102). -/
theorem exchange_le (p : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {X : Finset (Finset ℕ)}, IsSubpartition X → (∀ S ∈ X, S.card ≤ p) →
      ∀ {M lam R : ℝ} (z : X.biUnion id → ℂ × ℂ), 9 ≤ M →
      (∀ i, 0 < dipoleLength (z i) ∧ dipoleLength (z i) ≤ R) →
      (∀ i j, (interEdges X).Adj i j → ¬ MultipoleLinked M lam (z i) (z j)) →
      ∀ w : SimpleGraph (X.biUnion id) → ℝ, (∀ T ∈ relTrees X, 0 ≤ w T) →
        (∑ T₀ ∈ relTrees X,
          ∑ T ∈ longAgreeingTrees X (fun i => dipoleLength (z i)) (dipoleDistOn z) T₀, w T) ≤
          C ^ (X.biUnion id).card *
            (∏ i, (1 + Real.logb M (17 * R / dipoleLength (z i))) ^ 2) *
            ∑ T ∈ relTrees X, w T := by
  obtain ⟨C, hC, hcount⟩ := lemma_4_49_three p
  refine ⟨C, hC, fun {X} hX hp {M lam R} z hM hr hB w hw => ?_⟩
  rw [exchange, mul_sum]
  exact sum_le_sum fun T hT =>
    mul_le_mul_of_nonneg_right (hcount hX hp z hM hr hB T hT) (hw T hT)

end MultipoleBKT.AbsoluteLower.RouteReattach

end
