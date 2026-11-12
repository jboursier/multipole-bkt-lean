/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.RouteLift.Family

/-!
# Local block estimates with their tree-family sums

The paper: Corollary 5.34. Apply Corollary 4.47 on each nontrivial block. On a singleton
block the graph and extracted edge sets are empty.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic.RouteLift
open CoreForest Peeling

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
  {b : V → β} {E : SimpleGraph V} {r : V → ℝ} {dist c : Sym2 V → ℝ}
  {v₁ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → V}
  {e₀ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → Sym2 V}
  {Ts Fs : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V}

/-- Internal blockwise application of Corollary 4.47, followed by its local
family sum. The chosen maximal part is recorded by `hŜv`. -/
theorem block_weight_family_le
    (hcross : E ≤ crossBlockGraph b) (hEE : IsMinimalSkeleton b E E)
    (hP : IsPlusPeeling b E (blockInnerEdges b E) r dist v₁ e₀ Ts Fs)
    (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ dist e) (hc : ∀ e, 0 ≤ c e)
    (ρ : β → ℝ) (hρ : ∀ v, r v ≤ ρ (b v))
    (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent)
    (Ŝ : β) (hŜmem : Ŝ ∈ blockParts b E l)
    (hŜv : (blockParts b E l).card ≠ 1 → Ŝ = b (v₁ l))
    {A : Sym2 V → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (hA0 : ∀ e, 0 ≤ A e) (hA : ∀ e ∈ E.edgeSet, A e ≤ C * absWeight r dist c e) :
    (∏ e ∈ (blockInnerEdges b E l).edgeFinset, A e) ≤
      C ^ (2 * (univ.filter fun v => bridgeBlock b (coreEdges b E) v = l).card) *
        ((∏ S ∈ (blockParts b E l).erase Ŝ, ρ S ^ 2) *
          (∑ U ∈ blockAgreeingTrees r dist l (Ts l), ∏ e ∈ U.edgeFinset, keptWeight dist c e) *
          ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e) := by
  have hAW : ∏ e ∈ (blockInnerEdges b E l).edgeFinset, A e ≤
      C ^ (2 * (univ.filter fun v => bridgeBlock b (coreEdges b E) v = l).card) * ∏ e ∈ (blockInnerEdges b E l).edgeFinset,
        absWeight r dist c e := by
    calc ∏ e ∈ (blockInnerEdges b E l).edgeFinset, A e
        ≤ ∏ e ∈ (blockInnerEdges b E l).edgeFinset, (C * absWeight r dist c e) :=
          Finset.prod_le_prod₀ (fun e _ => hA0 e) fun e he =>
            hA e (edgeSet_mono (blockInnerEdges_le l) (mem_edgeFinset.1 he))
      _ = C ^ (blockInnerEdges b E l).edgeFinset.card *
            ∏ e ∈ (blockInnerEdges b E l).edgeFinset, absWeight r dist c e := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ C ^ (2 * (univ.filter fun v => bridgeBlock b (coreEdges b E) v = l).card) *
            ∏ e ∈ (blockInnerEdges b E l).edgeFinset, absWeight r dist c e := by
          refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC ?_)
            (prod_nonneg fun e _ => absWeight_nonneg hr hd hc e)
          have := natCard_edgeSet_blockInnerEdges_le hcross hEE hP l
          rwa [edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hraw : (∏ e ∈ (blockInnerEdges b E l).edgeFinset, absWeight r dist c e) ≤
      (∏ S ∈ (blockParts b E l).erase (Ŝ), ρ S ^ 2) *
        (∏ e ∈ (Ts l).edgeFinset, keptWeight dist c e) *
        ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e := by
    by_cases h1 : (blockParts b E l).card = 1
    · obtain ⟨hT, hF⟩ := (hP l).2 h1
      obtain ⟨S, hS⟩ := Finset.card_eq_one.1 h1
      have hŜS : Ŝ = S := by
        have := hŜmem
        rwa [hS, mem_singleton] at this
      rw [blockInnerEdges_eq_bot_of_card_eq_one hcross h1, hT, hF, hS, hŜS, Finset.erase_singleton]
      rw [prod_edgeFinset_bot, prod_edgeFinset_bot, prod_edgeFinset_bot]
      norm_num
    · have hK := (isMinimalSkeleton_self_iff.1 hEE) l
      rw [hŜv h1]
      exact ((hP l).1 h1).prod_absWeight_le hK hr hd hc ρ hρ
  have hsumT := Finset.single_le_sum
    (f := fun U : SimpleGraph V => ∏ e ∈ U.edgeFinset, keptWeight dist c e)
    (fun U _ => prod_nonneg fun e _ => keptWeight_nonneg hc e)
    (self_mem_blockAgreeingTrees (r := r) (d := dist) (localTree_of_peeling hcross hEE hP l))
  refine hAW.trans (mul_le_mul_of_nonneg_left (hraw.trans ?_) (pow_nonneg (zero_le_one.trans hC) _))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsumT (prod_nonneg fun S _ => sq_nonneg _))
    (prod_nonneg fun e _ => peelWeight_nonneg hc _ _)

/-- Internal scalar bookkeeping. The local sums are assembled first, then
the remaining bridge radii and marked ratios are compensated. -/
theorem assembly_compensation_le {I B M P Tl Fl Bk Br Mk Rprod Rall Tsum δ C₁ C₂ K : ℝ}
    {n : ℕ} (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    (hP0 : 0 ≤ P) (hTl0 : 0 ≤ Tl) (hFl0 : 0 ≤ Fl) (hBk0 : 0 ≤ Bk)
    (hBr0 : 0 ≤ Br) (hMk0 : 0 ≤ Mk) (hT0 : 0 ≤ Tsum)
    (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (hI : I ≤ C₁ ^ (2 * n) * (P * Tl * Fl))
    (hB : B ≤ C₁ ^ n * (Br * Bk)) (hM : M ≤ C₂ ^ n * Mk)
    (hT : Tl * Bk ≤ Tsum)
    (hBM : Br * Mk ≤ K ^ (6 * n) * Rprod / δ ^ 2)
    (hR : P * Rprod = Rall) :
    I * B * M ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ n * Rall * Tsum * Fl / δ ^ 2 := by
  have hC₁0 := zero_le_one.trans hC₁
  have hC₂0 := zero_le_one.trans hC₂
  have h1 : 0 ≤ C₁ ^ (2 * n) * (P * Tl * Fl) := by positivity
  have h2 : 0 ≤ C₁ ^ n * (Br * Bk) := by positivity
  have h3 : 0 ≤ C₁ ^ (2 * n) * C₁ ^ n * C₂ ^ n := by positivity
  have hconst : C₁ ^ (2 * n) * C₁ ^ n * C₂ ^ n * K ^ (6 * n) =
      (C₁ ^ 3 * C₂ * K ^ 6) ^ n := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_add,
      show 2 * n + n = 3 * n by ring, mul_comm 3 n, mul_comm 6 n]
  calc I * B * M ≤ (C₁ ^ (2 * n) * (P * Tl * Fl)) *
        (C₁ ^ n * (Br * Bk)) * (C₂ ^ n * Mk) :=
      mul_le_mul (mul_le_mul hI hB hB0 h1) hM hM0 (mul_nonneg h1 h2)
    _ = C₁ ^ (2 * n) * C₁ ^ n * C₂ ^ n * (P * (Tl * Bk) * Fl) * (Br * Mk) := by ring
    _ ≤ C₁ ^ (2 * n) * C₁ ^ n * C₂ ^ n * (P * Tsum * Fl) * (Br * Mk) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hP0) hFl0) h3)
        (mul_nonneg hBr0 hMk0)
    _ ≤ C₁ ^ (2 * n) * C₁ ^ n * C₂ ^ n * (P * Tsum * Fl) *
        (K ^ (6 * n) * Rprod / δ ^ 2) :=
      mul_le_mul_of_nonneg_left hBM (by positivity)
    _ = (C₁ ^ (2 * n) * C₁ ^ n * C₂ ^ n * K ^ (6 * n)) *
        (P * Rprod) * Tsum * Fl / δ ^ 2 := by ring
    _ = _ := by rw [hconst, hR]

end MultipoleBKT.UpperBound.Quadratic.RouteLift

end
