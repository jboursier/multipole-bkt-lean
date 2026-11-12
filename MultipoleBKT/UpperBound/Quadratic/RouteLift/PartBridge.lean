/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.Bridges
public import MultipoleBKT.UpperBound.Quadratic.RouteLift.Extracted

/-!
# The paper bridge estimate on the extracted part tree

The paper: Corollary 5.34. Bad distances on a part are their minimum over its vertices.
The extra local comparison factors are absorbed in an explicit constant.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic
open CoreForest Peeling

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)

/-- The bad distance of a part, defined on every nonempty part by its minimum. -/
noncomputable def partDistance (δ : X.biUnion id → ℝ) (S : X) : ℝ :=
  (univ.filter fun i => blockOf hX i = S).inf'
    (by obtain ⟨i, hi⟩ := blockOf_surjective hX S; exact ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩⟩) δ

theorem partDistance_attained (δ : X.biUnion id → ℝ) (S : X) :
    ∃ i, blockOf hX i = S ∧ δ i = partDistance hX δ S := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf'
    (s := univ.filter fun i => blockOf hX i = S)
    (by obtain ⟨i, hi⟩ := blockOf_surjective hX S; exact ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩⟩) δ
  exact ⟨i, (mem_filter.1 hi).2, he.symm⟩

theorem partDistance_le (δ : X.biUnion id → ℝ) {S : X} {i : X.biUnion id}
    (hi : blockOf hX i = S) : partDistance hX δ S ≤ δ i :=
  Finset.inf'_le δ (show i ∈ univ.filter (fun j => blockOf hX j = S) from mem_filter.2 ⟨mem_univ _, hi⟩)

theorem partDistance_pos {δ : X.biUnion id → ℝ} (hδ : ∀ i, 0 < δ i) (S : X) :
    0 < partDistance hX δ S := by
  obtain ⟨i, -, hi⟩ := partDistance_attained hX δ S
  rw [← hi]
  exact hδ i

/-- Steps 2–4 of the paper proof with transport on the extracted tree on X.
The factor K^6 absorbs the comparisons between vertex and part distances. -/
theorem bridges_marks_le_parts {V₁ : Finset (X.biUnion id)} {E₀ E : SimpleGraph (X.biUnion id)}
    (hE₀ : IsRelEulerianOffConnected X V₁ E₀) (hV₁ : V₁.Nonempty)
    (hE : IsMinimalSkeleton (blockOf hX) E₀ E)
    (hconn : (E ⊔ sameBlockGraph (blockOf hX)).Connected) {r δ : X.biUnion id → ℝ}
    {R : (bridgelessGraph (blockOf hX) E).ConnectedComponent → ℝ} {K : ℝ}
    {dist : Sym2 (X.biUnion id) → ℝ}
    {v₁ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent → X.biUnion id}
    {e₀ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent → Sym2 (X.biUnion id)}
    {Ts Fs : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent → SimpleGraph (X.biUnion id)}
    (hP : IsPlusPeeling (blockOf hX) E (blockInnerEdges (blockOf hX) E) r dist v₁ e₀ Ts Fs)
    (hr : ∀ x, 0 ≤ r x) (hδ : ∀ x, 0 < δ x) (hrδ : ∀ x, r x ≤ δ x)
    (hrR : ∀ x, r x ≤ R (bridgeBlock (blockOf hX) E x)) (hK : 1 ≤ K)
    (hKG : ∀ u w, (E ⊔ sameBlockGraph (blockOf hX)).Adj u w → δ w ≤ K * δ u)
    (i₀ : X.biUnion id) :
    (∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, radProd r e) * ∏ i ∈ V₁, (r i / δ i) ≤
      K ^ (6 * (X.biUnion id).card) * (∏ l, R l ^ 2) / δ i₀ ^ 2 := by
  set bb := bridgeBlock (blockOf hX) E with hbb
  set τ := bridgeTree (blockOf hX) E with hτdef
  set n := (X.biUnion id).card with hn
  have hcross₀ : E₀ ≤ crossBlockGraph (blockOf hX) := interEdges_eq hX ▸ hE₀.1.1
  have hcross : E ≤ crossBlockGraph (blockOf hX) := hE.le.trans hcross₀
  have hτ : τ.IsTree := bridgeTree_isTree hcross hconn
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hδ0 : ∀ x, 0 ≤ δ x := fun x => (hδ x).le
  have hcardV : Fintype.card (X.biUnion id) = n := Fintype.card_coe _
  -- the comparisons
  have hglob : ∀ x y, δ y ≤ K ^ n * δ x := fun x y => by
    have := le_pow_card_mul hK hKG hδ0 (S := univ) (hconn.preconnected x y)
      fun v _ => mem_univ v
    rwa [card_univ, hcardV] at this
  have hblk : ∀ x y, bb x = bb y →
      δ y ≤ K ^ (univ.filter fun v => bb v = bb x).card * δ x := by
    intro x y hxy
    refine le_pow_card_mul hK (G := bridgelessGraph (blockOf hX) E)
      (fun u w huw => hKG u w (bridgelessGraph_le_sup huw)) hδ0 (bridgeBlock_eq_iff.1 hxy)
      fun v hv => ?_
    rw [mem_filter]
    exact ⟨mem_univ v, (bridgeBlock_eq_iff.2 hv).symm⟩
  have hR0 : ∀ l, 0 ≤ R l := fun l => by
    induction l using ConnectedComponent.ind with
    | h x => exact (hr x).trans (hrR x)
  have hq0 : ∀ i, 0 ≤ r i / δ i := fun i => div_nonneg (hr i) (hδ0 i)
  have hq1 : ∀ i, r i / δ i ≤ 1 := fun i => (div_le_one (hδ i)).2 (hrδ i)
  have hRprod0 : 0 ≤ ∏ l, R l ^ 2 := prod_nonneg fun l _ => sq_nonneg _
  have hKn : 1 ≤ K ^ n := one_le_pow₀ hK
  -- `1 / (δ_x δ_y) ≤ K^{2n} / δ_{i_0}²`
  have htwo : ∀ x y, 1 / (δ x * δ y) ≤ K ^ (2 * n) / δ i₀ ^ 2 := fun x y => by
    have h1 := hglob x i₀
    have h2 := hglob y i₀
    have hxy : 0 < δ x * δ y := mul_pos (hδ x) (hδ y)
    rw [div_le_div_iff₀ hxy (pow_pos (hδ i₀) 2), one_mul]
    calc δ i₀ ^ 2 = δ i₀ * δ i₀ := sq _
      _ ≤ (K ^ n * δ x) * (K ^ n * δ y) :=
          mul_le_mul h1 h2 (hδ0 _) (mul_nonneg (pow_nonneg hK0 _) (hδ0 _))
      _ = K ^ (2 * n) * (δ x * δ y) := by rw [two_mul, pow_add]; ring
  have hpow24 : K ^ (2 * n) ≤ K ^ (6 * n) := pow_le_pow_right₀ hK (by omega)
  by_cases hnt : Nontrivial (bridgelessGraph (blockOf hX) E).ConnectedComponent
  swap
  · -- one bridge-block: no bridge, and two distinct marks
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hnobr : (relBridges (blockOf hX) E).edgeFinset = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false, mem_edgeFinset]
      induction e using Sym2.ind with
      | h u v =>
        intro huv
        exact bridgeBlock_ne_of_relBridges hcross huv (Subsingleton.elim _ _)
    rw [hnobr, Finset.prod_empty, one_mul]
    obtain ⟨i₁, hi₁⟩ := hV₁
    have heven := even_card_marks hX hE₀.1
    have hcard : 1 < V₁.card := by
      have h1 : 0 < V₁.card := Finset.card_pos.2 ⟨i₁, hi₁⟩
      rcases heven with ⟨k, hk⟩
      omega
    obtain ⟨i₂, hi₂, hne⟩ := Finset.exists_mem_ne hcard i₁
    have hsub : ({i₁, i₂} : Finset _) ⊆ V₁ := by
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi₁
      · exact hi₂
    have hmarks := prod_le_prod_of_subset_of_le_one hsub (fun i _ => hq0 i) fun i _ => hq1 i
    rw [Finset.prod_pair hne.symm] at hmarks
    set l₀ := bb i₁
    have hRuniv : ∏ l, R l ^ 2 = R l₀ ^ 2 := by
      rw [Fintype.prod_subsingleton _ l₀]
    rw [hRuniv]
    have hr1 : r i₁ ≤ R l₀ := hrR i₁
    have hr2 : r i₂ ≤ R l₀ := by
      have := hrR i₂
      rwa [Subsingleton.elim (bb i₂) l₀] at this
    have hRl0 : 0 ≤ R l₀ := hR0 l₀
    calc ∏ i ∈ V₁, r i / δ i ≤ r i₁ / δ i₁ * (r i₂ / δ i₂) := hmarks
      _ = r i₁ * r i₂ * (1 / (δ i₁ * δ i₂)) := by field_simp
      _ ≤ R l₀ ^ 2 * (K ^ (2 * n) / δ i₀ ^ 2) := by
          refine mul_le_mul ?_ (htwo i₁ i₂)
            (div_nonneg zero_le_one (mul_nonneg (hδ0 _) (hδ0 _))) (sq_nonneg _)
          rw [sq]
          exact mul_le_mul hr1 hr2 (hr _) hRl0
      _ ≤ R l₀ ^ 2 * (K ^ (6 * n) / δ i₀ ^ 2) := by gcongr
      _ = K ^ (6 * n) * R l₀ ^ 2 / δ i₀ ^ 2 := by ring
  · -- Step 2: root the bridge-tree at a leaf and select its actual bridges.
    obtain ⟨a, ha⟩ := hτ.exists_vert_degree_one_of_nontrivial
    have hcp : ∀ l : RouteLift.Nonroot a, ∃ q : X.biUnion id × X.biUnion id,
        bb q.2 = l ∧ IsParent τ a (bb q.1) l ∧
          (relBridges (blockOf hX) E).Adj q.1 q.2 := by
      intro l
      obtain ⟨q, hq⟩ := exists_isParent hτ l.property
      obtain ⟨-, u, v, hu, hv, huv⟩ := blockQuotient_adj.1 hq.1
      refine ⟨(u, v), hv, ?_, huv⟩
      change IsParent τ a (bb u) l
      rw [show bb u = q from hu]
      exact hq
    choose cp hcp using hcp
    let D : RouteLift.BlockTree τ a (E ⊔ sameBlockGraph (blockOf hX)) := {
      block := bb
      childEnd := fun l => (cp l).2
      parentEnd := fun l => (cp l).1
      child_block := fun l => (hcp l).1
      parent_block := fun l => (hcp l).2.1
      bridge_adj := fun l => Or.inl (relBridges_le (hcp l).2.2).symm
      inside := by
        intro x y hxy
        obtain ⟨w⟩ := bridgeBlock_eq_iff.1 hxy
        refine ⟨w.map (.ofLE bridgelessGraph_le_sup), ?_⟩
        intro z hz
        have hz' : z ∈ w.support := by
          rw [Walk.support_map] at hz
          change z ∈ List.map id w.support at hz
          simpa only [List.map_id] using hz
        exact (bridgeBlock_eq_iff.2 ⟨w.takeUntil z hz'⟩).symm }
    -- Step 3: parity supplies a mark in every leaf, including the root.
    obtain ⟨i₁, hi₁⟩ := hV₁
    have hm : ∀ l, ∃ x, τ.degree l = 1 → x ∈ V₁ ∧ bb x = l := by
      intro l
      by_cases hl : τ.degree l = 1
      · have hu : ∃! m, τ.Adj l m := degree_eq_one_iff_existsUnique_adj.1 hl
        have hodd := odd_card_marks_of_leaf hX hE₀.1 hE hu
        obtain ⟨x, hx⟩ := Finset.card_pos.1 hodd.pos
        rw [mem_inter, mem_filter] at hx
        exact ⟨x, fun _ => ⟨hx.2, hx.1.2⟩⟩
      · exact ⟨i₁, fun h => absurd h hl⟩
    choose m hm using hm
    set L := univ.filter fun l => τ.degree l = 1 with hL
    have hminj : Set.InjOn m L := fun l hl l' hl' he => by
      have h1 := (hm l (mem_filter.1 hl).2).2
      have h2 := (hm l' (mem_filter.1 hl').2).2
      rw [← h1, ← h2, he]
    have hmarks : ∏ i ∈ V₁, r i / δ i ≤
        (∏ l : RouteLift.Leaf τ a, r (m l) / δ (m l)) * (r (m a) / δ (m a)) := by
      have hsub : L.image m ⊆ V₁ := fun x hx => by
        obtain ⟨l, hl, rfl⟩ := mem_image.1 hx
        exact (hm l (mem_filter.1 hl).2).1
      have hle := prod_le_prod_of_subset_of_le_one hsub (fun i _ => hq0 i) fun i _ => hq1 i
      rw [Finset.prod_image hminj] at hle
      have hLa : a ∈ L := mem_filter.2 ⟨mem_univ _, ha⟩
      have hleafSet : L.erase a = (leaves τ).erase a := rfl
      rw [← Finset.mul_prod_erase L (fun l => r (m l) / δ (m l)) hLa,
        hleafSet, mul_comm] at hle
      have hleafProd : (∏ l : RouteLift.Leaf τ a, r (m l) / δ (m l)) =
          ∏ l ∈ (leaves τ).erase a, r (m l) / δ (m l) :=
        (Finset.prod_subtype ((leaves τ).erase a) (fun _ => Iff.rfl)
          (fun l => r (m l) / δ (m l))).symm
      rw [hleafProd]
      exact hle
    -- The bridge endpoint product is indexed by the nonroot blocks.
    have hbridges : ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, radProd r e =
        ∏ l : RouteLift.Nonroot a, (r (D.childEnd l) * r (D.parentEnd l)) := by
      symm
      refine Finset.prod_bij (fun l _ => s(D.childEnd l, D.parentEnd l))
        (fun l _ => mem_edgeFinset.2 (hcp l).2.2.symm) ?_ ?_ (fun l _ => rfl)
      · intro l _ l' _ he
        apply Subtype.ext
        rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, h2⟩
        · rw [← D.child_block l, ← D.child_block l', h1]
        · exfalso
          have hp1 := D.parent_block l
          have hp2 := D.parent_block l'
          rw [h2, D.child_block l'] at hp1
          rw [← h1, D.child_block l] at hp2
          have := hp1.dist_lt
          have := hp2.dist_lt
          omega
      · intro e he
        induction e using Sym2.ind with
        | h u v =>
          rw [mem_edgeFinset] at he
          have hne := bridgeBlock_ne_of_relBridges hcross he
          have hadj : τ.Adj (bb u) (bb v) := blockQuotient_adj_of_adj he hne
          have huniq := hasUniqueReps_relBridges hcross (bb u) (bb v) hadj
          rcases isParent_or_isParent_of_adj hτ (r := a) hadj with h | h
          · have hv0 : bb v ≠ a := fun he => not_isParent_root _ (he ▸ h)
            let l : RouteLift.Nonroot a := ⟨bb v, hv0⟩
            refine ⟨l, mem_univ _, ?_⟩
            have hpu : bb (D.parentEnd l) = bb u := (D.parent_block l).unique hτ h
            have huq := huniq.unique (y₁ := (D.parentEnd l, D.childEnd l)) (y₂ := (u, v))
              ⟨hpu, D.child_block l, (hcp l).2.2⟩ ⟨rfl, rfl, he⟩
            rw [Prod.mk.injEq] at huq
            rw [huq.1, huq.2, Sym2.eq_swap]
          · have hu0 : bb u ≠ a := fun he => not_isParent_root _ (he ▸ h)
            let l : RouteLift.Nonroot a := ⟨bb u, hu0⟩
            refine ⟨l, mem_univ _, ?_⟩
            have huniq' := hasUniqueReps_relBridges hcross (bb v) (bb u) hadj.symm
            have hpv : bb (D.parentEnd l) = bb v := (D.parent_block l).unique hτ h
            have huq := huniq'.unique (y₁ := (D.parentEnd l, D.childEnd l)) (y₂ := (v, u))
              ⟨hpv, D.child_block l, (hcp l).2.2⟩ ⟨rfl, rfl, he.symm⟩
            rw [Prod.mk.injEq] at huq
            rw [huq.1, huq.2]
    -- The actual extracted tree on X carries the lifted paths.
    obtain ⟨P, hPb, hPc, hPp, -⟩ := RouteLift.part_lift_of_bridges hX E hE₀ hE hP a
      D.childEnd D.parentEnd D.child_block D.parent_block
      (fun l => (hcp l).2.2.symm)
    let ρ := blockRadius hX r
    let δP := fun S : X => K * partDistance hX δ S
    let W := fun l => K ^ (univ.filter fun v => bb v = l).card
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
    have hδP : ∀ S, 0 < δP S := fun S => mul_pos hKpos (partDistance_pos hX hδ S)
    have hρP : ∀ S, 0 ≤ ρ S := fun S => by
      obtain ⟨i, hi⟩ := blockOf_surjective hX S
      exact (hr i).trans (hi ▸ le_blockRadius r i)
    have hρδ : ∀ S, ρ S ≤ δP S := by
      intro S
      obtain ⟨j, hj, hmin⟩ := partDistance_attained hX δ S
      apply Finset.sup'_le
      intro i hi
      have hib := (mem_filter.1 hi).2
      change r i ≤ K * partDistance hX δ S
      rw [← hmin]
      refine (hrδ i).trans ?_
      by_cases he : j = i
      · rw [he]
        exact le_mul_of_one_le_left (hδ i).le hK
      · exact hKG j i (Or.inr (sameBlockGraph_adj.2 ⟨he, hj.trans hib.symm⟩))
    have hρR : ∀ S, ρ S ≤ R (P.block S) := by
      intro S
      rw [hPb]
      apply Finset.sup'_le
      intro i hi
      have hib := (mem_filter.1 hi).2
      have hbi : RouteLift.partBlock hX E S = bb i := by
        rw [← hib, RouteLift.partBlock_blockOf]
      rw [hbi]
      exact hrR i
    have hedge : ∀ S S', (quotientGraph X (plusTree (blockOf hX) E Ts)).Adj S S' →
        δP S' ≤ K ^ 2 * δP S := by
      intro S S' hSS'
      rw [quotientGraph_eq hX] at hSS'
      obtain ⟨-, i, j, hi, hj, hij⟩ := blockQuotient_adj.1 hSS'
      have hle : plusTree (blockOf hX) E Ts ≤ E := by
        rw [plusTree_eq hcross]
        refine sup_le (iSup_le fun l => ?_) relBridges_le
        exact ((tree_sup_removed hcross
          (isMinimalSkeleton_self_of_isMinimalSkeleton hcross₀ hE) hP l).1 ▸ le_sup_left).trans
          (blockInnerEdges_le l)
      obtain ⟨k, hk, hmin⟩ := partDistance_attained hX δ S
      have hki : δ i ≤ K * δ k := by
        by_cases he : k = i
        · rw [he]
          exact le_mul_of_one_le_left (hδ i).le hK
        · exact hKG k i (Or.inr (sameBlockGraph_adj.2 ⟨he, hk.trans hi.symm⟩))
      have hji := hKG i j (Or.inl (hle hij))
      have hminj : partDistance hX δ S' ≤ δ j := partDistance_le hX δ hj
      dsimp only [δP]
      rw [← hmin]
      calc K * partDistance hX δ S' ≤ K * δ j := mul_le_mul_of_nonneg_left hminj hK0
        _ ≤ K * (K * (K * δ k)) :=
          mul_le_mul_of_nonneg_left (hji.trans (mul_le_mul_of_nonneg_left hki hK0)) hK0
        _ = _ := by ring
    have hinsideP : ∀ S S', P.block S = P.block S' →
        δP S' ≤ W (P.block S) * δP S := by
      intro S S' hSS'
      obtain ⟨i, hi, hmini⟩ := partDistance_attained hX δ S
      obtain ⟨j, hj, hminj⟩ := partDistance_attained hX δ S'
      have hPi : P.block S = bb i := by rw [hPb, ← hi, RouteLift.partBlock_blockOf]
      have hPj : P.block S' = bb j := by rw [hPb, ← hj, RouteLift.partBlock_blockOf]
      have he : bb i = bb j := hPi.symm.trans (hSS'.trans hPj)
      have hc := hblk i j he
      dsimp only [δP, W]
      rw [← hmini, ← hminj, hPi]
      calc K * δ j ≤ K * (K ^ (univ.filter fun v => bb v = bb i).card * δ i) := by gcongr
        _ = _ := by ring
    let mP := fun l => blockOf hX (m l)
    have hmP : ∀ l, τ.degree l = 1 → P.block (mP l) = l := by
      intro l hl
      rw [hPb, RouteLift.partBlock_blockOf]
      exact (hm l hl).2
    have hpartT := (isRelTree_plusTree_of_peeled hX hE₀ hE hP).2.1
    have hBM := lifted_bridge_bound_length P hτ hpartT ha (W := W) hρP hδP hρδ hR0 hρR
      (one_le_pow₀ hK) (fun l => one_le_pow₀ hK) hedge hinsideP mP hmP
    have hWprod : ∏ l, W l = K ^ n := by
      simp only [W, Finset.prod_pow_eq_pow_sum]
      rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => mem_univ (bb x)), card_univ, hcardV]
    rw [hWprod, Fintype.card_coe, ← pow_mul] at hBM
    have hXn : X.card ≤ n := by
      have := Fintype.card_le_of_surjective _ (blockOf_surjective hX)
      simpa only [Fintype.card_coe] using this
    have hlen : K ^ (2 * (X.card - 1)) ≤ K ^ (2 * n) := pow_le_pow_right₀ hK (by omega)
    have hblockn : Fintype.card (bridgelessGraph (blockOf hX) E).ConnectedComponent ≤ n := by
      have := Fintype.card_le_of_surjective bb fun l => by
        induction l using ConnectedComponent.ind with
        | h x => exact ⟨x, rfl⟩
      simpa only [hcardV] using this
    have hmarkP : ∀ i, r i / δ i ≤ K * (ρ (blockOf hX i) / δP (blockOf hX i)) := by
      intro i
      dsimp only [δP]
      rw [← mul_div_assoc, mul_div_mul_left _ _ (ne_of_gt hKpos)]
      exact div_le_div₀ (hρP _) (le_blockRadius r i) (partDistance_pos hX hδ _)
        (partDistance_le hX δ rfl)
    have hmarksP : (∏ l : RouteLift.Leaf τ a, r (m l) / δ (m l)) *
        (r (m a) / δ (m a)) ≤ K ^ n *
          ((∏ l : RouteLift.Leaf τ a, ρ (mP l) / δP (mP l)) *
            (ρ (mP a) / δP (mP a))) := by
      calc _ ≤ (∏ l : RouteLift.Leaf τ a, K * (ρ (mP l) / δP (mP l))) *
          (K * (ρ (mP a) / δP (mP a))) :=
          mul_le_mul (prod_le_prod₀ (fun l _ => hq0 _) fun l _ => hmarkP _)
            (hmarkP _) (hq0 _) (prod_nonneg fun l _ => mul_nonneg hK0 (div_nonneg (hρP _) (hδP _).le))
        _ = K ^ (Fintype.card (RouteLift.Leaf τ a) + 1) *
            ((∏ l : RouteLift.Leaf τ a, ρ (mP l) / δP (mP l)) *
              (ρ (mP a) / δP (mP a))) := by
          rw [prod_mul_distrib, prod_const, card_univ, pow_succ]
          ring
        _ ≤ _ := by
          have hcardLeaf : Fintype.card (RouteLift.Leaf τ a) + 1 ≤ n := by
            have hc : Fintype.card (RouteLift.Leaf τ a) = ((leaves τ).erase a).card := Fintype.card_coe _
            have hs : ((leaves τ).erase a).card < Fintype.card (bridgelessGraph (blockOf hX) E).ConnectedComponent := by
              have := card_le_card (show leaves τ ⊆ (univ : Finset _) from subset_univ _)
              have := card_erase_add_one (mem_leaves.2 ha)
              rw [card_univ] at *
              omega
            omega
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK hcardLeaf)
            (mul_nonneg (prod_nonneg fun l _ => div_nonneg (hρP _) (hδP _).le)
              (div_nonneg (hρP _) (hδP _).le))
    have hBrP : (∏ l : RouteLift.Nonroot a, r (D.childEnd l) * r (D.parentEnd l)) ≤
        ∏ l : RouteLift.Nonroot a, ρ (P.childEnd l) * ρ (P.parentEnd l) := by
      apply prod_le_prod₀ (fun l _ => mul_nonneg (hr _) (hr _))
      intro l _
      rw [hPc, hPp]
      exact mul_le_mul (le_blockRadius r _) (le_blockRadius r _) (hr _)
        ((hr _).trans (le_blockRadius r _))
    obtain ⟨j, hj, hmin⟩ := partDistance_attained hX δ (mP a)
    have htwoP : 1 / δP (mP a) ^ 2 ≤ K ^ (2 * n) / δ i₀ ^ 2 := by
      have hδle : δ j ≤ δP (mP a) := by
        dsimp only [δP]
        rw [← hmin]
        exact le_mul_of_one_le_left (hδ _).le hK
      have hjpos := hδ j
      have hsquare : δ j * δ j ≤ δP (mP a) ^ 2 := by
        rw [sq]
        exact mul_self_le_mul_self hjpos.le hδle
      exact (div_le_div_of_nonneg_left zero_le_one (mul_pos hjpos hjpos) hsquare).trans (htwo j j)
    rw [hbridges]
    let BP := ∏ l : RouteLift.Nonroot a, ρ (P.childEnd l) * ρ (P.parentEnd l)
    let MP := (∏ l : RouteLift.Leaf τ a, ρ (mP l) / δP (mP l)) * (ρ (mP a) / δP (mP a))
    have hBP0 : 0 ≤ BP := prod_nonneg fun l _ => mul_nonneg (hρP _) (hρP _)
    have hMP0 : 0 ≤ MP := mul_nonneg (prod_nonneg fun l _ => div_nonneg (hρP _) (hδP _).le)
      (div_nonneg (hρP _) (hδP _).le)
    have hBM' : BP * MP ≤ K ^ (2 * n) * K ^ n * (∏ l, R l ^ 2) / δP (mP a) ^ 2 := by
      have hb := hBM
      change BP * _ * _ ≤ _ at hb
      calc BP * MP = BP * _ * _ := by dsimp only [MP]; ring
        _ ≤ _ := hb
        _ ≤ _ := by gcongr
    calc (∏ l : RouteLift.Nonroot a, r (D.childEnd l) * r (D.parentEnd l)) * ∏ i ∈ V₁, r i / δ i
        ≤ (∏ l : RouteLift.Nonroot a, r (D.childEnd l) * r (D.parentEnd l)) *
          ((∏ l : RouteLift.Leaf τ a, r (m l) / δ (m l)) * (r (m a) / δ (m a))) :=
          mul_le_mul_of_nonneg_left hmarks (prod_nonneg fun l _ => mul_nonneg (hr _) (hr _))
      _ ≤ BP * (K ^ n * MP) := mul_le_mul hBrP hmarksP
        (mul_nonneg (prod_nonneg fun l _ => hq0 _) (hq0 _)) hBP0
      _ = K ^ n * (BP * MP) := by ring
      _ ≤ K ^ n * (K ^ (2 * n) * K ^ n * (∏ l, R l ^ 2) / δP (mP a) ^ 2) := by gcongr
      _ = (K ^ n * K ^ (2 * n) * K ^ n * ∏ l, R l ^ 2) * (1 / δP (mP a) ^ 2) := by ring
      _ ≤ (K ^ n * K ^ (2 * n) * K ^ n * ∏ l, R l ^ 2) * (K ^ (2 * n) / δ i₀ ^ 2) :=
        mul_le_mul_of_nonneg_left htwoP (by positivity)
      _ = K ^ (6 * n) * (∏ l, R l ^ 2) / δ i₀ ^ 2 := by
        rw [show 6 * n = n + 2 * n + n + 2 * n by ring, pow_add, pow_add, pow_add]
        ring

end MultipoleBKT.UpperBound.Quadratic

end
