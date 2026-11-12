/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Replacement

/-!
# Unmarked odd components with all replacement-tree tails

The paper: Proposition 5.18. Corollary 4.47 gives the tree family.
The removed-edge estimate (4.70) bounds its quadratic tail, which
also bounds the tail required on every replacement tree.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open Finset SimpleGraph Peeling CoreForest Quadratic
open scoped Classical NNReal

variable {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)

/-- The unmarked family estimate with the tail on every summand.
The strictly positive maximal radius holds almost everywhere in the model. -/
theorem euler_component_family_bound {G : SimpleGraph (Y.biUnion id)} (hG : Parity.IsRelEulerianConnected Y G)
    {r : Y.biUnion id → ℝ} (hr : ∀ v, 0 ≤ r v) {d c : Sym2 (Y.biUnion id) → ℝ}
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    {A : Sym2 (Y.biUnion id) → ℝ} (hA0 : ∀ e, 0 ≤ A e) {C₁ : ℝ} (hC₁ : 1 ≤ C₁)
    (hA : ∀ e ∈ G.edgeSet, A e ≤ C₁ * absWeight r d c e)
    (ha1 : ∀ e ∈ G.edgeSet, absWeight r d c e ≤ 1) {Ŝ : Y}
    (hŜ : ∀ S, blockRadius hY r S ≤ blockRadius hY r Ŝ)
    (hRpos : 0 < blockRadius hY r Ŝ) :
    ∃ T : SimpleGraph (Y.biUnion id), IsRelTree Y T ∧
      ∏ e ∈ G.edgeFinset, A e ≤ C₁ ^ G.edgeFinset.card *
        (∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2) *
        (∑ U ∈ longAgreeingTrees Y r d T,
          (∏ e ∈ U.edgeFinset, keptWeight d c e) * treeTail d U (blockRadius hY r Ŝ)) := by
  obtain ⟨E', v₁, e₀, Qs, hP⟩ := exists_isEulerPeeling_of_eulerian (hX := hY) hG r d
  have hstr := hP.structure hG.1.1
  set T := keptGraph E' Qs
  refine ⟨T, (isRelTree₀_iff hY).1 (Or.inl hstr.1) |> fun _ => hstr.1, ?_⟩
  -- the maximal radius is that of `v₁`
  have hle := hP.2.le_radius
  have hv₁ : blockRadius hY r (blockOf hY v₁) = blockRadius hY r Ŝ := by
    refine le_antisymm (hŜ _) ?_
    have h1 : blockRadius hY r Ŝ ≤ r v₁ := by
      unfold blockRadius
      exact Finset.sup'_le _ _ fun i _ => hle i
    exact h1.trans (le_blockRadius r v₁)
  have hRv : blockRadius hY r Ŝ = r v₁ := by
    rw [← hv₁]
    refine le_antisymm ?_ (le_blockRadius r v₁)
    unfold blockRadius
    exact Finset.sup'_le _ _ fun i _ => hle i
  -- Corollary 4.47 through the skeleton
  have hq := hP.prod_absWeight_le hr hd hc ha1
  rw [prod_erase_eq_of_eq (fun S => blockRadius hY r S ^ 2) (a := blockOf hY v₁) (b := Ŝ)
    (congrArg (· ^ 2) hv₁)] at hq
  have hAle : ∏ e ∈ G.edgeFinset, A e ≤ C₁ ^ G.edgeFinset.card *
      ∏ e ∈ G.edgeFinset, absWeight r d c e := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun e _ => hA0 e) fun e he => hA e (mem_edgeFinset.1 he)
  have hP0 : 0 ≤ ∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2 :=
    prod_nonneg fun _ _ => sq_nonneg _
  have hK0 : 0 ≤ ∏ e ∈ T.edgeFinset, keptWeight d c e :=
    prod_nonneg fun e _ => keptWeight_nonneg' hc e
  have hF0 : 0 ≤ ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e :=
    prod_nonneg fun e _ => peelWeight_nonneg' hc _ _ _
  -- Corollary 4.47 supplies the family before the tail is inserted.
  let fam := longAgreeingTrees Y r d T
  let w := fun U : SimpleGraph (Y.biUnion id) => ∏ e ∈ U.edgeFinset, keptWeight d c e
  have hw : ∀ U, 0 ≤ w U := fun U => prod_nonneg fun e _ => keptWeight_nonneg' hc e
  have hfamily : w T ≤ ∑ U ∈ fam, w U :=
    single_le_sum (fun U _ => hw U) (self_mem_longAgreeingTrees hstr.1)
  have hqfamily : ∏ e ∈ G.edgeFinset, absWeight r d c e ≤
      (∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2) *
        (∑ U ∈ fam, w U) *
          ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e :=
    hq.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfamily hP0) hF0)
  have htail : ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e ≤
      treeTail d T (blockRadius hY r Ŝ) := by
    have hTne : T.edgeFinset.Nonempty := by
      obtain ⟨e, he⟩ := hstr.1.1.2.1
      exact ⟨e, mem_edgeFinset.2 he⟩
    obtain ⟨e, he, hemax⟩ := Finset.exists_mem_eq_sup T.edgeFinset hTne
      (fun e => (d e).toNNReal)
    by_cases he0 : d e = 0
    · have hF1 := (hP.lemma_4_49 hr hd hc hc1).2.1
      have ht : treeTail d T (blockRadius hY r Ŝ) = 1 := by
        unfold treeTail
        rw [hemax, he0, Real.toNNReal_zero, NNReal.coe_zero,
          max_eq_right hRpos.le, div_self hRpos.ne', one_pow]
      rwa [ht]
    · have hepos := lt_of_le_of_ne (hd e) (Ne.symm he0)
      have h1 := hP.prod_peelWeight_le_min_sq (c := c) hr hd hc hc1 (mem_edgeFinset.1 he) hepos
      refine h1.trans ?_
      rw [← hRv]
      exact min_sq_le_treeTail hd hRpos.le hemax hepos
  have htailU : ∀ U ∈ fam,
      (∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e) ≤
        treeTail d U (blockRadius hY r Ŝ) := by
    intro U hU
    apply htail.trans (treeTail_le_replacement hU hRpos _ hd)
    intro i
    exact (hle i).trans_eq hRv.symm
  have hsum : (∑ U ∈ fam, w U) *
      (∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e) ≤
        ∑ U ∈ fam, w U * treeTail d U (blockRadius hY r Ŝ) := by
    rw [sum_mul]
    exact sum_le_sum fun U hU => mul_le_mul_of_nonneg_left (htailU U hU) (hw U)
  calc ∏ e ∈ G.edgeFinset, A e
      ≤ C₁ ^ G.edgeFinset.card * ∏ e ∈ G.edgeFinset, absWeight r d c e := hAle
    _ ≤ C₁ ^ G.edgeFinset.card * ((∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2) *
        (∑ U ∈ fam, w U) *
          ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e) :=
      mul_le_mul_of_nonneg_left hqfamily (pow_nonneg (zero_le_one.trans hC₁) _)
    _ = C₁ ^ G.edgeFinset.card * (∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2) *
        ((∑ U ∈ fam, w U) *
          ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (pow_nonneg (zero_le_one.trans hC₁) _) hP0)

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
