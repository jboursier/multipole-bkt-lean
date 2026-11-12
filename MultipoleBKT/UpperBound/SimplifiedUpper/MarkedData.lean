/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.Grouping
public import MultipoleBKT.UpperBound.SimplifiedUpper.Exceptional
public import MultipoleBKT.UpperBound.Quadratic.Instance
public import MultipoleBKT.UpperBound.SimplifiedUpper.RouteLog.Quadratic
public import MultipoleBKT.UpperBound.Quadratic.RelTree
public import MultipoleBKT.UpperBound.BoundedUpper.ComponentZ

/-!
# Peeling data with the replacement-tree family retained

The paper: Lemma 5.36, using Corollary 5.34.

`exists_markedData_sum` chooses a minimal marked skeleton and peels its bridge-blocks.
It retains the original tree `T`, its bridge-cut forest `Hs`, the pseudoforest `F`
after exceptional-edge deletion, and the exception record `D`. These records
reconstruct the original skeleton. The weight bound uses `squares_of_bounds_sum`
through its maximal-radius specialization. The sum over `B(·,T)` stays inside the
bound. In particular, the bridge and exception records are relative to `T`, before
any replacement tree is selected. The nonexceptional removed edges have weights `ḡ`.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Finset SimpleGraph Multipole Hierarchical SetPartition AbsoluteLower Parity Peeling
  CoreForest Quadratic

/-! ### Edge sets of pairs and graphs -/

section Pairs

variable {Y : Finset (Finset ℕ)}

/-- The graph of `E ∈ Eulc^Y(W)` is in `Eulc^Y(W)` (Definition 5.23 in graph form). -/
theorem isRelEulerianOffConnected_pairGraph {W : Finset ℕ}
    {E : Finset (ℕ × ℕ)} (hE : E ∈ markEulerConnPairs Y W) :
    IsRelEulerianOffConnected Y (BoundedUpper.marksOn Y W)
      (BoundedUpper.pairGraph (Y.biUnion id) E) := by
  classical
  obtain ⟨hEc, hEp⟩ := mem_markEulerConnPairs.1 hE
  obtain ⟨hEI, hEne, hEconn⟩ := mem_relEdgeSets.1 hEc
  refine ⟨⟨BoundedUpper.pairGraph_le_interEdges hEI, fun S hS => ?_⟩,
    BoundedUpper.pairGraph_le_interEdges hEI, ?_,
    BoundedUpper.connected_sup_intraEdges_of_connOn hEI hEconn⟩
  · have hSY : S ⊆ Y.biUnion id := subset_biUnion_of_mem hS
    rw [BoundedUpper.blockDegree_pairGraph (hEI.trans interPairs_subset_pairsOn) hSY,
      BoundedUpper.card_blockSet_inter_marksOn hSY]
    exact (mem_markEulerPairs.1 hEp).2 S hS
  · obtain ⟨p, hp⟩ := hEne
    obtain ⟨h1, h2, h12⟩ := mem_pairsOn.1 (interPairs_subset_pairsOn (hEI hp))
    refine ⟨s(⟨p.1, h1⟩, ⟨p.2, h2⟩), ?_⟩
    rw [mem_edgeSet, BoundedUpper.pairGraph_adj]
    exact ⟨fun h => h12.ne (congrArg Subtype.val h), Or.inl hp⟩

end Pairs

/-! ### Graph facts -/

section GraphFacts

variable {V : Type*}

/-- The endpoints of an edge of a graph whose edges stay in a fiber of `f` lie in that fiber. -/
theorem eq_of_mem_of_mem_edgeSet {α : Type*} {G : SimpleGraph V} {f : V → α} {k : α}
    (hG : ∀ u v, G.Adj u v → f u = k ∧ f v = k) {e : Sym2 V} (he : e ∈ G.edgeSet) {x : V}
    (hx : x ∈ e) : f x = k := by
  induction e using Sym2.ind with
  | h u v =>
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact (hG _ _ he).1
    · exact (hG _ _ he).2

theorem isPseudoforest_bot : IsPseudoforest (⊥ : SimpleGraph V) :=
  ⟨fun _ => none, fun _ _ h => by simp at h, fun e he => by simp at he⟩

open scoped Classical in
/-- `⋃_l F_l = ⋃_l (F_l ∖ {e₀ l}) ∪ D` with `D` the set of the `e₀ l ∈ F_l`. -/
theorem iSup_eq_sup_fromEdgeSet [DecidableEq V] {ι : Type*} [Fintype ι] (Fs : ι → SimpleGraph V)
    (e₀ : ι → Sym2 V) :
    (⨆ l, Fs l) = (⨆ l, (Fs l).deleteEdges {e₀ l}) ⊔
      fromEdgeSet (((univ.filter fun l => e₀ l ∈ (Fs l).edgeSet).image e₀ : Finset (Sym2 V)) :
        Set (Sym2 V)) := by
  classical
  ext u v
  simp only [iSup_adj, sup_adj, deleteEdges_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
    coe_image, coe_filter, mem_univ, true_and, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨l, hl⟩
    by_cases h : s(u, v) = e₀ l
    · exact Or.inr ⟨⟨l, h ▸ hl, h.symm⟩, hl.ne⟩
    · exact Or.inl ⟨l, hl, h⟩
  · rintro (⟨l, hl, -⟩ | ⟨⟨l, hl, heq⟩, -⟩)
    · exact ⟨l, hl⟩
    · refine ⟨l, ?_⟩
      rw [← mem_edgeSet, ← heq]
      exact hl

end GraphFacts

/-! ### The data of one edge set -/

section Data

variable {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y) {W : Finset ℕ}

/-- The weight `A_ij = a i j` on the unordered pairs of `V_Y`, for a symmetric `a`. -/
noncomputable def symLift (U : Finset ℕ) (a : ℕ → ℕ → ℝ) (ha : ∀ i j, a i j = a j i) :
    Sym2 U → ℝ :=
  Sym2.lift ⟨fun i j => a i j, fun i j => ha i j⟩

/-- The weight `ḡ_ij` on the unordered pairs of `V_Y`. -/
noncomputable def gbarLift (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (U : Finset ℕ) : Sym2 U → ℝ :=
  Sym2.lift ⟨fun i j => gbar M lam ε₀ R c i j, fun i j => gbar_comm i j⟩

theorem gbarLift_nonneg (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (U : Finset ℕ) (e : Sym2 U) :
    0 ≤ gbarLift M lam ε₀ R c U e := by
  induction e using Sym2.ind with
  | h i j => exact gbar_nonneg _ _

theorem symLift_nonneg {U : Finset ℕ} {a : ℕ → ℕ → ℝ} (ha0 : ∀ i j, 0 ≤ a i j)
    (ha : ∀ i j, a i j = a j i) (e : Sym2 U) : 0 ≤ symLift U a ha e := by
  induction e using Sym2.ind with
  | h i j => exact ha0 _ _

variable (c : ℕ → ℂ × ℂ) {M lam ε₀ R C₁ C₂ K : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam)
  (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hK : 1 ≤ K)
  (a : ℕ → ℕ → ℝ) (ha0 : ∀ i j, 0 ≤ a i j) (hasymm : ∀ i j, a i j = a j i)
  (ha : ∀ i ∈ Y.biUnion id, ∀ j ∈ Y.biUnion id,
    a i j ≤ C₁ * absOddWeight M lam ε₀ R (c i) (c j))
  (m δ : ℕ → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hm : ∀ i ∈ W, m i ≤ C₂ * (‖(c i).1 - (c i).2‖ / δ i))
  (hδ : ∀ i ∈ Y.biUnion id, 0 < δ i) (hrδ : ∀ i ∈ Y.biUnion id, ‖(c i).1 - (c i).2‖ ≤ δ i)
  (hKE : ∀ i ∈ Y.biUnion id, ∀ j ∈ Y.biUnion id, a i j ≠ 0 → δ j ≤ K * δ i)
  (hKS : ∀ S ∈ Y, ∀ i ∈ S, ∀ j ∈ S, δ j ≤ K * δ i)
include hY hM hlam hC₁ hC₂ hK ha0 ha hm0 hm hδ hrδ hKE hKS

open scoped Classical in
/-- **The peeling data of one `E ∈ Eulc^Y(W)`** (proof of Lemma 5.36): see the module docstring. -/
theorem exists_markedData_sum (hW : W ⊆ Y.biUnion id) (hWne : W.Nonempty) {E : Finset (ℕ × ℕ)}
    (hE : E ∈ markEulerConnPairs Y W) :
    ∃ (T Hs F : SimpleGraph (Y.biUnion id)) (D : Finset (Sym2 (Y.biUnion id)))
      (E' : SimpleGraph (Y.biUnion id)),
      IsRelTree Y T ∧ Hs ≤ T ∧ IsPseudoforest F ∧
        ValidExc (Hs ⊔ sameBlockGraph (blockOf hY)) D ∧
        E' = T ⊔ F ⊔ fromEdgeSet (D : Set (Sym2 (Y.biUnion id))) ∧
        E' ≤ BoundedUpper.pairGraph (Y.biUnion id) E ∧
        (∏ e ∈ E'.edgeFinset, symLift (Y.biUnion id) a hasymm e) * ∏ i ∈ W, m i ≤
          (C₁ ^ 3 * C₂ * K ^ 6) ^ (Y.biUnion id).card * prodExceptMax c Y *
            (∑ T' ∈ longAgreeingTrees Y (fun i : Y.biUnion id => dipoleLength (c i))
              (dipoleDistOn fun i : Y.biUnion id => c i) T,
              ∏ e ∈ T'.edgeFinset, keptWeight (dipoleDistOn fun i : Y.biUnion id => c i)
                (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) e) *
            ∏ e ∈ F.edgeFinset, gbarLift M lam ε₀ R c (Y.biUnion id) e := by
  set V := Y.biUnion id with hVdef
  set n := V.card with hn
  set z : V → ℂ × ℂ := fun i => c i with hz
  set r : V → ℝ := fun i => dipoleLength (z i) with hr_def
  set d : Sym2 V → ℝ := dipoleDistOn z with hd_def
  set cc : Sym2 V → ℝ := absIndicator M lam ε₀ R z with hcc_def
  set g : Sym2 V → ℝ := gbarLift M lam ε₀ R c V with hg_def
  set A : Sym2 V → ℝ := symLift V a hasymm with hA_def
  set b := blockOf hY with hb
  set W' := BoundedUpper.marksOn Y W with hW'
  set G := BoundedUpper.pairGraph V E with hGdef
  have hG : IsRelEulerianOffConnected Y W' G := isRelEulerianOffConnected_pairGraph hE
  have hWne' : W'.Nonempty := by
    obtain ⟨w, hw⟩ := hWne
    exact ⟨⟨w, hW hw⟩, mem_filter.2 ⟨mem_univ _, hw⟩⟩
  have hr : ∀ v, 0 ≤ r v := fun v => norm_nonneg _
  have hd : ∀ e, 0 ≤ d e := dipoleDistOn_nonneg z
  have hcc : ∀ e, 0 ≤ cc e := absIndicator_nonneg M lam ε₀ R z
  have hcross : G ≤ crossBlockGraph b := interEdges_eq hY ▸ hG.1.1
  -- the minimal skeleton and its peeling
  obtain ⟨E', hE'⟩ := exists_isMinimalSkeleton (b := b) (E := G)
  have hEE := isMinimalSkeleton_self_of_isMinimalSkeleton hcross hE'
  have hKs := isMinimalSkeleton_self_iff.1 hEE
  have hcrossE : E' ≤ crossBlockGraph b := hE'.le.trans hcross
  obtain ⟨v₁, e₀, Ts, Fs, hP⟩ := exists_isPlusPeeling hcrossE hKs r d
  set T := plusTree b E' Ts with hT_def
  have hT : IsRelTree Y T := isRelTree_plusTree_of_peeled hY hG hE' hP
  set Hs := ⨆ l, Ts l with hHs
  set F := ⨆ l, (Fs l).deleteEdges {e₀ l} with hF
  set D : Finset (Sym2 V) := (univ.filter fun l => e₀ l ∈ (Fs l).edgeSet).image e₀ with hD
  -- the blocks of the peeling
  have hFle : ∀ l, Fs l ≤ blockInnerEdges b E' l := fun l =>
    (tree_sup_removed hcrossE hEE hP l).1 ▸ le_sup_right
  have hTle : ∀ l, Ts l ≤ blockInnerEdges b E' l := fun l =>
    (tree_sup_removed hcrossE hEE hP l).1 ▸ le_sup_left
  have hFin : ∀ l u v, (Fs l).Adj u v →
      bridgeBlock b (coreEdges b E') u = l ∧ bridgeBlock b (coreEdges b E') v = l :=
    fun l u v huv => blockInnerEdges_adj_inBlock (hFle l huv)
  have hTin : ∀ l u v, (Ts l).Adj u v →
      bridgeBlock b (coreEdges b E') u = l ∧ bridgeBlock b (coreEdges b E') v = l :=
    fun l u v huv => blockInnerEdges_adj_inBlock (hTle l huv)
  -- `Fs l` is a pseudoforest
  have hFpf : ∀ l, IsPseudoforest (Fs l) := by
    intro l
    by_cases h1 : (blockParts b E' l).card = 1
    · rw [((hP l).2 h1).2]
      exact isPseudoforest_bot
    · obtain ⟨w₁, e₀', Qs, hp, -, -, -, hFs⟩ := (hP l).1 h1
      rw [hFs]
      exact IsPseudoforest.map _ hp.isPseudoforest
  refine ⟨T, Hs, F, D, E', hT, ?_, ?_, ⟨?_, ?_⟩, ?_, hE'.le, ?_⟩
  · -- `Hs ≤ T`
    show Hs ≤ plusTree b E' Ts
    rw [plusTree_eq hcrossE]
    exact le_sup_left
  · -- `F` is a pseudoforest
    refine isPseudoforest_iSup _ (fun l => (hFpf l).mono (deleteEdges_le _)) ?_
    intro l l' v w w' hvw hvw'
    exact (hFin l v w (deleteEdges_le _ hvw)).1.symm.trans (hFin l' v w' (deleteEdges_le _ hvw')).1
  · -- the endpoints of an exceptional edge are joined in `Hs ∪ ℰ^intra`
    intro e he x hx y hy
    obtain ⟨l, hl, rfl⟩ := mem_image.1 he
    have hl' := (mem_filter.1 hl).2
    have hxl := eq_of_mem_of_mem_edgeSet (hFin l) hl' hx
    have hyl := eq_of_mem_of_mem_edgeSet (hFin l) hl' hy
    exact (reachable_tree_of_inBlock hP l hxl hyl).mono (sup_le_sup_right (le_iSup Ts l) _)
  · -- at most one exceptional edge per component
    intro e he e' he' x hx y hy hxy
    obtain ⟨l, hl, rfl⟩ := mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := mem_image.1 he'
    have hxl := eq_of_mem_of_mem_edgeSet (hFin l) (mem_filter.1 hl).2 hx
    have hyl := eq_of_mem_of_mem_edgeSet (hFin l') (mem_filter.1 hl').2 hy
    have hbb := eq_of_reachable_of_forall_adj (f := bridgeBlock b (coreEdges b E'))
      (fun u v huv => by
        rcases huv with huv | huv
        · obtain ⟨k, hk⟩ := iSup_adj.1 huv
          exact (hTin k u v hk).1.trans (hTin k u v hk).2.symm
        · exact bridgeBlock_eq_of_eq (sameBlockGraph_adj.1 huv).2) hxy
    rw [← hxl, ← hyl, hbb]
  · -- `E' = T ∪ F ∪ D`
    have h1 := IsPlusPeeling.plusTree_sup hcrossE hKs hP
    have h2 := eq_iSup_sup_relBridges hcrossE hEE
    rw [relBridges_eq_sup hcrossE] at h2
    rw [sup_assoc, ← iSup_eq_sup_fromEdgeSet Fs e₀, h1, sup_assoc]
    exact h2
  · -- the weight bound
    obtain ⟨v₀, -, hv₀⟩ := Finset.exists_max_image (univ : Finset V) r
      (by
        obtain ⟨w, hw⟩ := hWne'
        exact ⟨w, mem_univ _⟩)
    have hA0 : ∀ e, 0 ≤ A e := symLift_nonneg ha0 hasymm
    have hA : ∀ e ∈ E'.edgeSet, A e ≤ C₁ * absWeight r d cc e := by
      intro e _
      induction e using Sym2.ind with
      | h i j =>
        rw [absWeight_dipole M lam ε₀ R z i j]
        exact ha i i.2 j j.2
    have hAi0 : ∀ i : V, 0 ≤ m i := fun i => hm0 i
    have hAi : ∀ i ∈ W', m i ≤ C₂ * (r i / δ i) := fun i hi =>
      hm i (mem_filter.1 hi).2
    have hKE' : ∀ i j : V, E'.Adj i j → A s(i, j) ≠ 0 → δ j ≤ K * δ i :=
      fun i j _ hne => hKE i i.2 j j.2 hne
    have hKS' : ∀ i j : V, b i = b j → δ j ≤ K * δ i := by
      intro i j hij
      have hi := mem_blockOf hY i
      have hj := mem_blockOf hY j
      rw [← hb, ← hij] at hj
      exact hKS _ (b i).2 i (by rw [← hb] at hi; exact hi) j hj
    have hmain := mainducorollaire_sum_of_bounds hY hG hWne' hE' hP hr hd hcc (A := A)
      (Ainf := fun i : V => m i) (δ := fun i : V => δ i) hC₁ hC₂ hK hA0 hA hAi0 hAi
      (fun i => hδ i i.2) (fun i => hrδ i i.2) hKE' hKS' (b v₀)
    have hrad : ∏ S ∈ univ.erase (b v₀), blockRadius hY r S ^ 2 = prodExceptMax c Y :=
      prod_blockRadius_erase_eq hY c (v := v₀) fun i => hv₀ i (mem_univ i)
    rw [hrad] at hmain
    have hmk : ∏ i ∈ W', m i = ∏ i ∈ W, m i := BoundedUpper.prod_marksOn hW m
    rw [hmk] at hmain
    -- the removed edges
    have hFdisj : ∀ l l', l ≠ l' →
        Disjoint ((Fs l).deleteEdges {e₀ l}) ((Fs l').deleteEdges {e₀ l'}) := fun l l' hll' =>
      (disjoint_blockInnerEdges hll').mono ((deleteEdges_le _).trans (hFle l))
        ((deleteEdges_le _).trans (hFle l'))
    have hFprod : ∏ e ∈ F.edgeFinset, g e =
        ∏ l, ∏ e ∈ (Fs l).edgeFinset.erase (e₀ l), g e := by
      have hset : F.edgeFinset = univ.biUnion fun l => (Fs l).edgeFinset.erase (e₀ l) := by
        ext e
        simp only [hF, mem_edgeFinset, edgeSet_iSup, Set.mem_iUnion, mem_biUnion, mem_univ,
          true_and, mem_erase, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨l, h1, h2⟩
          exact ⟨l, h2, h1⟩
        · rintro ⟨l, h1, h2⟩
          exact ⟨l, h2, h1⟩
      rw [hset, prod_biUnion]
      intro l _ l' _ hll'
      rw [Function.onFun, Finset.disjoint_left]
      intro e he he'
      have h1 := (mem_erase.1 he).2
      have h2 := (mem_erase.1 he').2
      rw [mem_edgeFinset] at h1 h2
      induction e using Sym2.ind with
      | h u v => exact hll' ((hFin l u v h1).1.symm.trans (hFin l' u v h2).1)
    have hpeel : ∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r d cc (r (v₁ l)) (e₀ l) e ≤
        ∏ e ∈ F.edgeFinset, g e := by
      rw [hFprod]
      exact prod_le_prod₀ (fun l _ => prod_nonneg fun e _ =>
        peelWeight_nonneg hcc _ _) fun l _ =>
        prod_peelWeight_le_prod_gbar (ε₀ := ε₀) (R := R) hM hlam c (hr _) (Fs l) (e₀ l)
    have hK0 : 0 ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ n * prodExceptMax c Y *
        ∑ T' ∈ longAgreeingTrees Y r d T, ∏ e ∈ T'.edgeFinset, keptWeight d cc e := by
      have : 0 ≤ C₁ ^ 3 * C₂ * K ^ 6 := by
        have := zero_le_one.trans hC₁
        have := zero_le_one.trans hC₂
        have := zero_le_one.trans hK
        positivity
      exact mul_nonneg (mul_nonneg (pow_nonneg this _) (prodExceptMax_nonneg Y))
        (sum_nonneg fun T' _ => prod_nonneg fun e _ => keptWeight_nonneg hcc e)
    exact hmain.trans (mul_le_mul_of_nonneg_left hpeel hK0)

end Data

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
