/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.EulerGroup

/-!
# The logarithmic predecessor product

The paper: (4.97),
and (4.102). The factor is retained until the
absorption preceding integration in Lemma 5.37.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.SimplifiedUpper

open Finset Parity Peeling AbsoluteLower Hierarchical Multipole
open scoped Classical

/-- The factor `Λ(Y)` in (4.97), the paper. -/
noncomputable def logProduct (M ε₀ R : ℝ) (c : ℕ → ℂ × ℂ)
    (Y : Finset (Finset ℕ)) : ℝ :=
  ∏ i ∈ Y.biUnion id, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2

theorem logProduct_nonneg (M ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (Y : Finset (Finset ℕ)) :
    0 ≤ logProduct M ε₀ R c Y := prod_nonneg fun _ _ => sq_nonneg _

theorem one_le_logFactor {M ε₀ R : ℝ} (hM : 1 < M) {r : ℝ}
    (hr : 0 < r) (hle : r ≤ ε₀ * R) :
    1 ≤ (1 + Real.logb M (17 * ε₀ * R / r)) ^ 2 := by
  have hx : 1 ≤ 17 * ε₀ * R / r := by
    rw [le_div_iff₀ hr]
    nlinarith
  have hlog := Real.logb_nonneg hM hx
  nlinarith [sq_nonneg (Real.logb M (17 * ε₀ * R / r))]

/-- Exchange the original and replacement trees after their bridge records have
been counted. This is (4.102), in pair notation. -/
theorem replacement_sum_le (p : ℕ) : ∃ D : ℝ, 0 < D ∧
    ∀ {Y : Finset (Finset ℕ)}, IsSubpartition Y → (∀ S ∈ Y, S.card ≤ p) →
    ∀ {M lam ε₀ R : ℝ} (c : ℕ → ℂ × ℂ), 9 ≤ M →
    (∀ i ∈ Y.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
    (∀ i j : Y.biUnion id, (interEdges Y).Adj i j → ¬ MultipoleLinked M lam (c i) (c j)) →
    (∑ T₀ ∈ relTrees Y, ∑ T ∈ longAgreeingTrees Y
      (fun i : Y.biUnion id => dipoleLength (c i))
      (dipoleDistOn fun i : Y.biUnion id => c i) T₀,
      ∏ e ∈ T.edgeFinset, keptWeight (dipoleDistOn fun i : Y.biUnion id => c i)
        (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) e) ≤
      D ^ (Y.biUnion id).card * logProduct M ε₀ R c Y *
        ∑ T ∈ relTreePairs Y, ∏ q ∈ T, keptPair M lam ε₀ R c q := by
  obtain ⟨D, hD, hcount⟩ := RouteReattach.exchange_le p
  refine ⟨D, hD, fun {Y} hY hp {M lam ε₀ R} c hM hr hB => ?_⟩
  let z : Y.biUnion id → ℂ × ℂ := fun i => c i
  let w : SimpleGraph (Y.biUnion id) → ℝ := fun T =>
    ∏ e ∈ T.edgeFinset, keptWeight (dipoleDistOn z) (absIndicator M lam ε₀ R z) e
  have hchange := hcount hY hp (R := ε₀ * R) z hM (fun i => hr i i.2) hB w
    (fun T _ => prod_nonneg fun e _ => keptWeight_nonneg (absIndicator_nonneg M lam ε₀ R z) e)
  have hinj : Set.InjOn (edgesOf (U := Y.biUnion id)) (relTrees Y) := by
    intro T hT T' hT' h
    simpa only [graphOf_edgesOf] using congrArg (graphOf (Y.biUnion id)) h
  have hsum : (∑ T ∈ relTrees Y, w T) =
      ∑ T ∈ relTreePairs Y, ∏ q ∈ T, keptPair M lam ε₀ R c q := by
    rw [relTreePairs, sum_image hinj]
    exact sum_congr rfl fun T _ => (prod_edgesOf_eq_of T _ _ (fun i j => rfl)).symm
  have hlog : (∏ i : Y.biUnion id, (1 + Real.logb M
      (17 * (ε₀ * R) / dipoleLength (z i))) ^ 2) = logProduct M ε₀ R c Y := by
    rw [logProduct, ← prod_coe_sort (Y.biUnion id)]
    simp only [z, dipoleLength, mul_assoc]
  simpa only [hsum, hlog] using hchange

end MultipoleBKT.UpperBound.SimplifiedUpper

end
