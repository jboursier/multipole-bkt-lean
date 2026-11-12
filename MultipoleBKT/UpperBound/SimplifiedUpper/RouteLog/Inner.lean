/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.MarkedGroup
public import MultipoleBKT.UpperBound.SimplifiedUpper.RouteLog.Factors

/-!
# The logarithmic inner Euler group bound

The paper: Lemma 5.36. Marked components use the summed quadratic estimate.
Their bridge and exception records refer to the original tree. The two tree
sums are exchanged only after the records have been summed. Unmarked components
use `eulerGroupSum_route_le`, with the same logarithmic predecessor factor.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.SimplifiedUpper

open Finset SimpleGraph Multipole Hierarchical SetPartition AbsoluteLower Parity Peeling Quadratic
open scoped Classical

theorem markEulerConnPairs_inter {Y : Finset (Finset ℕ)} (U : Finset ℕ) :
    markEulerConnPairs Y U = markEulerConnPairs Y (U ∩ Y.biUnion id) := by
  ext E
  simp only [mem_markEulerConnPairs, mem_markEulerPairs]
  have h : ∀ S ∈ Y, S ∩ (U ∩ Y.biUnion id) = S ∩ U := fun S hS => by
    rw [← inter_assoc, inter_comm S U, inter_assoc, inter_eq_left.2 (subset_biUnion_of_mem hS),
      inter_comm]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun S hS => by rw [h S hS]; exact h3 S hS⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun S hS => by rw [← h S hS]; exact h3 S hS⟩


/-- The inner estimate of Lemma 5.36, including `Λ(Y)`.
The constant `Q` is uniform in the configuration and all cutoffs. -/
theorem groupSum_route_le (p : ℕ) {C₁ : ℝ} (hC₁ : 1 ≤ C₁) :
    ∃ Q : ℝ, 1 ≤ Q ∧
    ∀ {Y : Finset (Finset ℕ)} (_hY : IsSubpartition Y) (U : Finset ℕ)
  (c : ℕ → ℂ × ℂ) {M lam ε₀ R C₂ K : ℝ} (_hM : 9 ≤ M) (_hlam : 0 < lam)
  (_hC₂ : 1 ≤ C₂) (_hK : 1 ≤ K)
  (a : ℕ → ℕ → ℝ) (_ha0 : ∀ i j, 0 ≤ a i j) (_hasymm : ∀ i j, a i j = a j i)
  (_ha : ∀ i ∈ Y.biUnion id, ∀ j ∈ Y.biUnion id,
    a i j ≤ C₁ * absOddWeight M lam ε₀ R (c i) (c j))
  (m δ : ℕ → ℝ) (_hm0 : ∀ i, 0 ≤ m i)
  (_hm : ∀ i ∈ U ∩ Y.biUnion id, m i ≤ C₂ * (‖(c i).1 - (c i).2‖ / δ i))
  (_hδ : ∀ i ∈ Y.biUnion id, 0 < δ i) (_hrδ : ∀ i ∈ Y.biUnion id, ‖(c i).1 - (c i).2‖ ≤ δ i)
  (_hKE : ∀ i ∈ Y.biUnion id, ∀ j ∈ Y.biUnion id, a i j ≠ 0 → δ j ≤ K * δ i)
  (_hKS : ∀ S ∈ Y, ∀ i ∈ S, ∀ j ∈ S, δ j ≤ K * δ i)
  (_hp : ∀ S ∈ Y, S.card ≤ p)
  (_hr : ∀ i ∈ Y.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R)
  (_hB : ∀ i j : Y.biUnion id, (interEdges Y).Adj i j → ¬ MultipoleLinked M lam (c i) (c j)),
    ∑ E ∈ markEulerConnPairs Y U, (∏ p ∈ E, a p.1 p.2) * ∏ i ∈ U ∩ Y.biUnion id, m i ≤
      (Q * (8 * (C₁ ^ 3 * C₂ * K ^ 6) + 1)) ^ (Y.biUnion id).card * prodExceptMax c Y *
        (∑ T ∈ relTreePairs Y, ∏ p ∈ T, keptPair M lam ε₀ R c p) *
        (∏ p ∈ interPairs Y, Real.exp (C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2))) *
        (∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j)) * logProduct M ε₀ R c Y := by
  obtain ⟨D, hD, hchange⟩ := replacement_sum_le p
  obtain ⟨Ku, hKu, hunmarked⟩ := eulerGroupSum_route_le p hC₁
  let Q := max (max D Ku) 1
  have hQ1 : 1 ≤ Q := le_max_right _ _
  have hDQ : D ≤ Q := (le_max_left _ _).trans (le_max_left _ _)
  have hKuQ : Ku ≤ Q := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨Q, hQ1, ?_⟩
  intro Y hY U c M lam ε₀ R C₂ K hM hlam hC₂ hK a ha0 hasymm ha m δ hm0 hm hδ hrδ hKE hKS hp hr hB
  let V := Y.biUnion id
  let k := V.card
  let P := prodExceptMax c Y
  let Tw := ∑ T ∈ relTreePairs Y, ∏ q ∈ T, keptPair M lam ε₀ R c q
  let Ex := ∏ q ∈ interPairs Y, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))
  let G := ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j)
  let Λ := logProduct M ε₀ R c Y
  let Kh := Q * (8 * (C₁ ^ 3 * C₂ * K ^ 6) + 1)
  have hC₁0 : 0 ≤ C₁ := by linarith
  have hC₂0 : 0 ≤ C₂ := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hP0 : 0 ≤ P := prodExceptMax_nonneg Y
  have hTw0 : 0 ≤ Tw := sum_nonneg fun T _ => prod_nonneg fun q _ => keptPair_nonneg q
  have hEx0 : 0 ≤ Ex := prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hG0 : 0 ≤ G := prod_nonneg fun i _ => add_nonneg zero_le_one
    (sum_nonneg fun j _ => gbar_nonneg _ _)
  have hΛ0 : 0 ≤ Λ := logProduct_nonneg _ _ _ _ _
  have hrest0 : 0 ≤ P * Tw * Ex * G * Λ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hP0 hTw0) hEx0) hG0) hΛ0
  have hKh : ∀ x : ℝ, 0 ≤ x → x ≤ Kh →
      x ^ k * P * Tw * Ex * G * Λ ≤ Kh ^ k * P * Tw * Ex * G * Λ := by
    intro x hx hxK
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hx hxK k) hrest0
  rw [markEulerConnPairs_inter U]
  by_cases hW : (U ∩ V).Nonempty
  · have hraw := markedGroupSum_reattach hY c (by linarith) hlam hC₁ hC₂ hK a ha0 hasymm ha
      m δ hm0 hm hδ hrδ hKE hKS inter_subset_right hW
    have hc := hchange hY hp (M := M) (lam := lam) c hM hr hB
    have hwt : (∑ E ∈ markEulerConnPairs Y (U ∩ V),
        (∏ q ∈ E, a q.1 q.2) * ∏ i ∈ U ∩ V, m i) ≤ (4 * (C₁ ^ 3 * C₂ * K ^ 6) * D) ^ k * P * Tw * Ex * G * Λ := by
      refine hraw.trans ?_
      calc _ ≤ (4 * (C₁ ^ 3 * C₂ * K ^ 6)) ^ k * P * (D ^ k * Λ * Tw) * Ex * G := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc (mul_nonneg (pow_nonneg (by positivity) _) hP0)) hEx0) hG0
        _ = _ := by rw [mul_pow]; ring
    exact hwt.trans (hKh _ (by positivity) (by
      dsimp [Kh]
      have h0 : 0 ≤ 4 * (C₁ ^ 3 * C₂ * K ^ 6) := by positivity
      nlinarith))
  · rw [not_nonempty_iff_eq_empty] at hW
    rw [hW, markEulerConnPairs_empty, prod_empty]
    simp only [mul_one]
    have hu := hunmarked M lam ε₀ R hM hlam hY hp c hr hB
    refine (sum_le_sum fun E hE => ?_).trans (hu.trans (hKh Ku hKu.le ?_))
    · have hEp : E ⊆ pairsOn V :=
        (mem_relEdgeSets.1 (mem_relEulerianConnectedPairs.1 hE).1).1.trans interPairs_subset_pairsOn
      refine prod_le_prod₀ (fun q _ => ha0 _ _) fun q hq => ?_
      have hqV := mem_pairsOn.1 (hEp hq)
      exact ha q.1 hqV.1 q.2 hqV.2.1
    · dsimp [Kh]
      have h0 : 0 ≤ 8 * (C₁ ^ 3 * C₂ * K ^ 6) := by positivity
      nlinarith

end MultipoleBKT.UpperBound.SimplifiedUpper

end
