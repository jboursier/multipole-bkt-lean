/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Replacement

/-!
# Marked odd components with the whole replacement family

The paper: Proposition 5.18. Apply the tree-family form of (5.89), remove the
peeled factors bounded by one, and use the length comparison for every
replacement tree before summing. The single-tree estimate is also available.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open Finset SimpleGraph Peeling CoreForest Quadratic
open scoped Classical NNReal

variable {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)

/-- The marked component bound with a quadratic tail on every replacement tree.
The geometric bounds are internal hypotheses, instantiated by the frozen model. -/
theorem marked_component_family_bound {G : SimpleGraph (Y.biUnion id)} {W : Finset (Y.biUnion id)}
    (hG : IsRelEulerianOffConnected Y W G) (hW : W.Nonempty)
    {r : Y.biUnion id → ℝ} (hr : ∀ v, 0 ≤ r v) {d c : Sym2 (Y.biUnion id) → ℝ}
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    {A : Sym2 (Y.biUnion id) → ℝ} {Ainf δ : Y.biUnion id → ℝ} {C₁ C₂ K : ℝ}
    (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hK : 1 ≤ K) (hA0 : ∀ e, 0 ≤ A e)
    (hA : ∀ e ∈ G.edgeSet, A e ≤ C₁ * absWeight r d c e)
    (ha1 : ∀ e ∈ G.edgeSet, absWeight r d c e ≤ 1)
    (hAi0 : ∀ i, 0 ≤ Ainf i) (hAi : ∀ i ∈ W, Ainf i ≤ C₂ * (r i / δ i))
    (hδ : ∀ i, 0 < δ i) (hrδ : ∀ i, r i ≤ δ i)
    (hKE : ∀ i j, G.Adj i j → A s(i, j) ≠ 0 → δ j ≤ K * δ i)
    (hKS : ∀ i j, blockOf hY i = blockOf hY j → δ j ≤ K * δ i)
    (hsupp : ∀ i j, G.Adj i j → A s(i, j) ≠ 0 → d s(i, j) ≤ δ i + δ j)
    {Ŝ : Y} (hŜ : ∀ S, blockRadius hY r S ≤ blockRadius hY r Ŝ) :
    ∃ T : SimpleGraph (Y.biUnion id), IsRelTree Y T ∧
      (∏ e ∈ G.edgeFinset, A e) * ∏ i ∈ W, Ainf i ≤
        C₁ ^ G.edgeFinset.card * ((C₁ ^ 3 * C₂ * K ^ 6) ^ (Y.biUnion id).card *
          (4 * (K ^ (Y.biUnion id).card) ^ 2)) *
        (∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2) *
        (∑ U ∈ longAgreeingTrees Y r d T,
          (∏ e ∈ U.edgeFinset, keptWeight d c e) * treeTail d U (blockRadius hY r Ŝ)) := by
  set n := (Y.biUnion id).card
  set b := blockOf hY
  have hcross : G ≤ crossBlockGraph b := interEdges_eq hY ▸ hG.1.1
  obtain ⟨E, hE⟩ := exists_isMinimalSkeleton (b := b) (E := G)
  have hEE := isMinimalSkeleton_self_of_isMinimalSkeleton hcross hE
  have hKs := isMinimalSkeleton_self_iff.1 hEE
  have hcrossE : E ≤ crossBlockGraph b := hE.le.trans hcross
  obtain ⟨v₁, e₀, Ts, Fs, hP⟩ := exists_isPlusPeeling hcrossE hKs r d
  set T := plusTree b E Ts
  have hT : IsRelTree Y T := isRelTree_plusTree_of_peeled hY hG hE hP
  refine ⟨T, hT, ?_⟩
  -- a vertex of maximal radius
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (univ : Finset (Y.biUnion id)) r
    (by
      obtain ⟨i, -⟩ := hW
      exact ⟨i, mem_univ i⟩)
  have hRi₀ : blockRadius hY r Ŝ = r i₀ := by
    refine le_antisymm ?_ ((le_blockRadius r i₀).trans (hŜ _))
    unfold blockRadius
    exact Finset.sup'_le _ _ fun i _ => hi₀ i (mem_univ i)
  have hŜi₀ : blockRadius hY r (b i₀) = blockRadius hY r Ŝ :=
    le_antisymm (hŜ _) (hRi₀ ▸ le_blockRadius r i₀)
  have hmain := squares_of_bounds_sum hY hG hW hE hP hr hd hc (A := A) (Ainf := Ainf) (δ := δ) hC₁ hC₂
    hK hA0 (fun e he => hA e (edgeSet_mono hE.le he)) hAi0 hAi hδ hrδ
    (fun i j hadj hAij => hKE i j (hE.le hadj) hAij) hKS i₀
  -- the nonnegativity of the factors
  have hP0 : 0 ≤ ∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2 := prod_nonneg fun _ _ => sq_nonneg _
  let fam := longAgreeingTrees Y r d T
  let w := fun U : SimpleGraph (Y.biUnion id) => ∏ e ∈ U.edgeFinset, keptWeight d c e
  have hw : ∀ U, 0 ≤ w U := fun U => prod_nonneg fun e _ => keptWeight_nonneg' hc e
  have hsum0 : 0 ≤ ∑ U ∈ fam, w U * treeTail d U (blockRadius hY r Ŝ) :=
    sum_nonneg fun U _ => mul_nonneg (hw U) (treeTail_nonneg _ _ _)
  have hF0 : 0 ≤ ∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r d c (r (v₁ l)) (e₀ l) e :=
    prod_nonneg fun l _ => prod_nonneg fun e _ => peelWeight_nonneg' hc _ _ _
  have hF1 : ∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r d c (r (v₁ l)) (e₀ l) e ≤ 1 :=
    prod_le_one₀ (fun l _ => prod_nonneg fun e _ => peelWeight_nonneg' hc _ _ _) fun l _ =>
      prod_le_one₀ (fun e _ => peelWeight_nonneg' hc _ _ _) fun e _ =>
        peelWeight_le_one hr hd hc hc1 (hr _) _ _
  have hAinf0 : 0 ≤ ∏ i ∈ W, Ainf i := prod_nonneg fun i _ => hAi0 i
  have hAE0 : 0 ≤ ∏ e ∈ E.edgeFinset, A e := prod_nonneg fun e _ => hA0 e
  have hC0 : 0 ≤ C₁ ^ 3 * C₂ * K ^ 6 := by positivity
  -- `∏_G A ≤ C₁^{|G|} ∏_E A`
  have hGE : ∏ e ∈ G.edgeFinset, A e ≤ C₁ ^ G.edgeFinset.card * ∏ e ∈ E.edgeFinset, A e := by
    have hsub : E.edgeFinset ⊆ G.edgeFinset := edgeFinset_mono hE.le
    rw [← Finset.prod_sdiff hsub]
    have h1 : ∏ e ∈ G.edgeFinset \ E.edgeFinset, A e ≤ C₁ ^ G.edgeFinset.card := by
      calc ∏ e ∈ G.edgeFinset \ E.edgeFinset, A e ≤ ∏ _e ∈ G.edgeFinset \ E.edgeFinset, C₁ :=
            Finset.prod_le_prod₀ (fun e _ => hA0 e) fun e he => by
              have he' := mem_edgeFinset.1 (Finset.mem_sdiff.1 he).1
              calc A e ≤ C₁ * absWeight r d c e := hA e he'
                _ ≤ C₁ * 1 := mul_le_mul_of_nonneg_left (ha1 e he') (by linarith)
                _ = C₁ := mul_one C₁
        _ = C₁ ^ (G.edgeFinset \ E.edgeFinset).card := Finset.prod_const _
        _ ≤ C₁ ^ G.edgeFinset.card := pow_le_pow_right₀ hC₁ (Finset.card_le_card sdiff_subset)
    exact mul_le_mul_of_nonneg_right h1 hAE0
  by_cases hzero : ∏ e ∈ E.edgeFinset, A e = 0
  · have hlhs : (∏ e ∈ G.edgeFinset, A e) * ∏ i ∈ W, Ainf i ≤ 0 := by
      have := mul_le_mul_of_nonneg_right hGE hAinf0
      rw [hzero, mul_zero, zero_mul] at this
      exact this
    refine hlhs.trans ?_
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hC₁) _)
      (mul_nonneg (pow_nonneg hC0 _) (by positivity))) hP0) hsum0
  · -- the comparison of the bad distances along the component
    have hAne : ∀ i j, E.Adj i j → A s(i, j) ≠ 0 := fun i j hij h0 =>
      hzero (Finset.prod_eq_zero (mem_edgeFinset.2 hij) h0)
    have hconn₀ : (G ⊔ sameBlockGraph b).Connected := intraEdges_eq hY ▸ hG.2.2.2
    have hconn := connected_sup_of_isMinimalSkeleton hE hconn₀
    have hcmp : ∀ y, δ y ≤ K ^ n * δ i₀ := by
      intro y
      have h := le_pow_card_mul (G := E ⊔ sameBlockGraph b) (δ := δ) hK
        (fun u w huw => by
          rcases huw with huw | huw
          · exact hKE u w (hE.le huw) (hAne u w huw)
          · exact hKS u w (sameBlockGraph_adj.1 huw).2)
        (fun v => (hδ v).le) (S := univ) (hconn.preconnected i₀ y) (fun v _ => mem_univ v)
      rwa [Finset.card_univ, Fintype.card_coe] at h
    have hmax : ∀ e ∈ T.edgeSet, d e ≤ 2 * K ^ n * δ i₀ := by
      intro e he
      induction e using Sym2.ind with
      | h i j =>
          have hTE : T ≤ E := by
            have h1 : T ≤ plusTree b E Ts ⊔ (⨆ l, Fs l) := le_sup_left
            rw [IsPlusPeeling.plusTree_sup hcrossE hKs hP] at h1
            refine h1.trans (sup_le (sup_le (iSup_le fun l => ?_) pendantEdges_le)
              (relBridges_le.trans coreEdges_le))
            intro u v huv
            exact coreEdges_le (blockInnerEdges_adj.1 huv).1
          have hij : E.Adj i j := hTE he
          have hd' := hsupp i j (hE.le hij) (hAne i j hij)
          linarith [hcmp i, hcmp j]
    have htail : ∀ U ∈ fam, r i₀ ^ 2 / δ i₀ ^ 2 ≤
        4 * (K ^ n) ^ 2 * treeTail d U (r i₀) := by
      intro U hU
      exact sq_div_le_replacement_tail hU (hr i₀) (hδ i₀) (hrδ i₀)
        (fun i => hi₀ i (mem_univ i)) (one_le_pow₀ hK) hmax
    rw [← Finset.mul_prod_erase univ (fun S => blockRadius hY r S ^ 2) (mem_univ Ŝ)] at hmain
    have hδ2 : 0 < δ i₀ ^ 2 := pow_pos (hδ i₀) 2
    set P := ∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2
    set R := blockRadius hY r Ŝ
    have hgain : (∑ U ∈ fam, w U) *
        (∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r d c (r (v₁ l)) (e₀ l) e) *
        (R ^ 2 / δ i₀ ^ 2) ≤
        (4 * (K ^ n) ^ 2) * ∑ U ∈ fam, w U * treeTail d U R := by
      have hq0 : 0 ≤ R ^ 2 / δ i₀ ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
      calc (∑ U ∈ fam, w U) * _ * (R ^ 2 / δ i₀ ^ 2)
          ≤ (∑ U ∈ fam, w U) * (R ^ 2 / δ i₀ ^ 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_of_le_one_right (sum_nonneg fun U _ => hw U) hF1) hq0
        _ = ∑ U ∈ fam, w U * (R ^ 2 / δ i₀ ^ 2) := by rw [sum_mul]
        _ ≤ ∑ U ∈ fam, w U * (4 * (K ^ n) ^ 2 * treeTail d U R) := by
            apply sum_le_sum
            intro U hU
            apply mul_le_mul_of_nonneg_left _ (hw U)
            rw [hRi₀]
            exact htail U hU
        _ = _ := by rw [Finset.mul_sum]; apply sum_congr rfl; intro U _; ring
    have hbase0 : 0 ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ n * P :=
      mul_nonneg (pow_nonneg hC0 _) hP0
    have hmain' : (∏ e ∈ E.edgeFinset, A e) * ∏ i ∈ W, Ainf i ≤
        (C₁ ^ 3 * C₂ * K ^ 6) ^ n * P *
          ((4 * (K ^ n) ^ 2) * ∑ U ∈ fam, w U * treeTail d U R) := by
      refine hmain.trans ?_
      calc _ = ((C₁ ^ 3 * C₂ * K ^ 6) ^ n * P) *
          ((∑ U ∈ fam, w U) *
            (∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r d c (r (v₁ l)) (e₀ l) e) *
              (R ^ 2 / δ i₀ ^ 2)) := by dsimp [R, P, fam, w, T, b]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hgain hbase0
    calc (∏ e ∈ G.edgeFinset, A e) * ∏ i ∈ W, Ainf i
        ≤ (C₁ ^ G.edgeFinset.card * ∏ e ∈ E.edgeFinset, A e) * ∏ i ∈ W, Ainf i :=
          mul_le_mul_of_nonneg_right hGE hAinf0
      _ = C₁ ^ G.edgeFinset.card * ((∏ e ∈ E.edgeFinset, A e) * ∏ i ∈ W, Ainf i) := by ring
      _ ≤ C₁ ^ G.edgeFinset.card *
          ((C₁ ^ 3 * C₂ * K ^ 6) ^ n * P *
            ((4 * (K ^ n) ^ 2) * ∑ U ∈ fam, w U * treeTail d U R)) :=
          mul_le_mul_of_nonneg_left hmain' (pow_nonneg (zero_le_one.trans hC₁) _)
      _ = _ := by ring

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
