/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.Corollary

/-!
# Dropping the maximal-radius quotient in the summed quadratic estimate

The paper: Corollary 5.34. The replacement-tree family is retained when the quotient
of the omitted block radius and the bad distance is bounded by one.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.SimplifiedUpper

open Finset SimpleGraph CoreForest Peeling Quadratic

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)

open scoped Classical in
/-- **The summed form of (5.90)** (internal): the factor
`r_Ŝ² / δ_{i₀}²` is dropped (choose `i₀ ∈ Ŝ` of radius `r_Ŝ` and use `r_{i₀} ≤ δ_{i₀}`). The paper
takes `Ŝ` of maximal radius. The bound holds for every part `Ŝ`. -/
theorem mainducorollaire_sum_of_bounds {V₁ : Finset (X.biUnion id)} {E₀ E : SimpleGraph (X.biUnion id)}
    (hE₀ : IsRelEulerianOffConnected X V₁ E₀) (hV₁ : V₁.Nonempty)
    (hE : IsMinimalSkeleton (blockOf hX) E₀ E) {r : X.biUnion id → ℝ}
    {dist c : Sym2 (X.biUnion id) → ℝ}
    {v₁ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      X.biUnion id}
    {e₀ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      Sym2 (X.biUnion id)}
    {Ts Fs : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      SimpleGraph (X.biUnion id)}
    (hP : IsPlusPeeling (blockOf hX) E (blockInnerEdges (blockOf hX) E) r dist v₁ e₀ Ts Fs)
    (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ dist e) (hc : ∀ e, 0 ≤ c e)
    {A : Sym2 (X.biUnion id) → ℝ} {Ainf δ : X.biUnion id → ℝ} {C₁ C₂ K : ℝ}
    (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hK : 1 ≤ K)
    (hA0 : ∀ e, 0 ≤ A e) (hA : ∀ e ∈ E.edgeSet, A e ≤ C₁ * absWeight r dist c e)
    (hAi0 : ∀ i, 0 ≤ Ainf i) (hAi : ∀ i ∈ V₁, Ainf i ≤ C₂ * (r i / δ i))
    (hδ : ∀ i, 0 < δ i) (hrδ : ∀ i, r i ≤ δ i)
    (hKE : ∀ i j, E.Adj i j → A s(i, j) ≠ 0 → δ j ≤ K * δ i)
    (hKS : ∀ i j, blockOf hX i = blockOf hX j → δ j ≤ K * δ i) (Ŝ : X) :
    (∏ e ∈ E.edgeFinset, A e) * ∏ i ∈ V₁, Ainf i ≤
      (C₁ ^ 3 * C₂ * K ^ 6) ^ (X.biUnion id).card *
        (∏ S ∈ univ.erase Ŝ, blockRadius hX r S ^ 2) *
        (∑ T ∈ longAgreeingTrees X r dist (plusTree (blockOf hX) E Ts),
          ∏ e ∈ T.edgeFinset, keptWeight dist c e) *
        (∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e) := by
  -- a vertex of `Ŝ` of maximal radius
  obtain ⟨i₀, hi₀, hri₀⟩ := Finset.exists_mem_eq_sup'
    (s := univ.filter fun i => blockOf hX i = Ŝ)
    (by
      obtain ⟨i, hi⟩ := blockOf_surjective hX Ŝ
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩) r
  have hŜi₀ : blockRadius hX r Ŝ = r i₀ := hri₀
  have key := squares_of_bounds_sum hX hE₀ hV₁ hE hP hr hd hc hC₁ hC₂ hK hA0 hA hAi0 hAi hδ hrδ hKE
    hKS i₀
  refine key.trans ?_
  rw [← Finset.mul_prod_erase univ (fun S => blockRadius hX r S ^ 2) (mem_univ Ŝ), hŜi₀]
  have hq : r i₀ ^ 2 / δ i₀ ^ 2 ≤ 1 := by
    rw [div_le_one (pow_pos (hδ i₀) 2)]
    exact pow_le_pow_left₀ (hr i₀) (hrδ i₀) 2
  have h0 : 0 ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ (X.biUnion id).card *
      (∏ S ∈ univ.erase Ŝ, blockRadius hX r S ^ 2) *
      (∑ T ∈ longAgreeingTrees X r dist (plusTree (blockOf hX) E Ts),
          ∏ e ∈ T.edgeFinset, keptWeight dist c e) *
      (∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by
      have := zero_le_one.trans hC₁; have := zero_le_one.trans hC₂
      have := zero_le_one.trans hK; positivity) _)
      (prod_nonneg fun S _ => sq_nonneg _)) (sum_nonneg fun T _ => prod_nonneg fun e _ => keptWeight_nonneg hc e))
      (prod_nonneg fun l _ => prod_nonneg fun e _ => peelWeight_nonneg hc _ _)
  calc (C₁ ^ 3 * C₂ * K ^ 6) ^ (X.biUnion id).card *
        (r i₀ ^ 2 * ∏ S ∈ univ.erase Ŝ, blockRadius hX r S ^ 2) *
        (∑ T ∈ longAgreeingTrees X r dist (plusTree (blockOf hX) E Ts),
          ∏ e ∈ T.edgeFinset, keptWeight dist c e) *
        (∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e) / δ i₀ ^ 2
      = ((C₁ ^ 3 * C₂ * K ^ 6) ^ (X.biUnion id).card *
        (∏ S ∈ univ.erase Ŝ, blockRadius hX r S ^ 2) *
        (∑ T ∈ longAgreeingTrees X r dist (plusTree (blockOf hX) E Ts),
          ∏ e ∈ T.edgeFinset, keptWeight dist c e) *
        (∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e)) *
          (r i₀ ^ 2 / δ i₀ ^ 2) := by ring
    _ ≤ _ := mul_le_of_le_one_right h0 hq


end MultipoleBKT.UpperBound.SimplifiedUpper

end
