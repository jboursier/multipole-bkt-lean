/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.RelTree
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Assembly of the local tree families

The paper: Corollary 5.34. Trees in a local family can use replacement edges. Their
endpoints remain in the same bridge-block, which recovers each local choice
from the assembled tree.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic

/-- A product over the edges of the empty graph is `1`. -/
theorem prod_edgeFinset_bot {V : Type*} {M : Type*} [CommMonoid M] (f : Sym2 V → M)
    [Fintype (⊥ : SimpleGraph V).edgeSet] : ∏ e ∈ (⊥ : SimpleGraph V).edgeFinset, f e = 1 :=
  Finset.prod_eq_one fun e he => by
    rw [mem_edgeFinset, edgeSet_bot] at he
    exact absurd he (Set.notMem_empty e)

end MultipoleBKT.UpperBound.Quadratic

namespace MultipoleBKT.UpperBound.Quadratic.RouteLift
open CoreForest Peeling

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
  {b : V → β} {E : SimpleGraph V}

/-- A spanning tree relative to the parts in one bridge-block, read on the
whole carrier. The support condition permits every edge inside that block. -/
structure IsLocalTree (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent)
    (U : SimpleGraph V) : Prop where
  cross : U ≤ crossBlockGraph b
  support : ∀ ⦃x y⦄, U.Adj x y → InBlock b E l x ∧ InBlock b E l y
  reachable : ∀ x y, InBlock b E l x → InBlock b E l y →
    (U ⊔ sameBlockGraph b).Reachable x y
  card : Nat.card U.edgeSet + 1 = (blockParts b E l).card

/-- The local family `B(·, T_l)`, including the empty tree on a singleton
block. Agreement is imposed only on long edges. -/
noncomputable def blockAgreeingTrees (r : V → ℝ) (d : Sym2 V → ℝ)
    (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) (T : SimpleGraph V) :
    Finset (SimpleGraph V) :=
  univ.filter fun U => IsLocalTree l U ∧
    ∀ e, (e ∈ U.edgeSet ∧ radMax r e ≤ d e) ↔
      (e ∈ T.edgeSet ∧ radMax r e ≤ d e)

variable {r : V → ℝ} {d : Sym2 V → ℝ}
  {v₁ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → V}
  {e₀ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → Sym2 V}
  {Ts Fs : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V}

omit [DecidableEq V] in
theorem localTree_of_peeling (hcross : E ≤ crossBlockGraph b)
    (hEE : IsMinimalSkeleton b E E)
    (hP : IsPlusPeeling b E (blockInnerEdges b E) r d v₁ e₀ Ts Fs)
    (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) : IsLocalTree l (Ts l) := by
  have hle : Ts l ≤ blockInnerEdges b E l := (tree_sup_removed hcross hEE hP l).1 ▸ le_sup_left
  exact ⟨hle.trans ((blockInnerEdges_le l).trans hcross),
    fun {_ _} h => blockInnerEdges_adj_inBlock (hle h),
    fun x y hx hy => reachable_tree_of_inBlock hP l hx hy, natCard_tree_add_one hP l⟩

/-- The extracted local tree is a member of its local family. -/
theorem self_mem_blockAgreeingTrees
    {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent} {T : SimpleGraph V} (hT : IsLocalTree (b := b) (E := E) l T) :
    T ∈ blockAgreeingTrees r d l T := by
  exact mem_filter.2 ⟨mem_univ _, hT, fun _ => Iff.rfl⟩

omit [DecidableEq V] in
private theorem local_disjoint {l l' : (bridgelessGraph b (coreEdges b E)).ConnectedComponent}
    {U U' : SimpleGraph V} (hU : IsLocalTree l U) (hU' : IsLocalTree l' U') (hne : l ≠ l') :
    Disjoint U U' := by
  rw [disjoint_iff]
  ext x y
  simp only [inf_adj, bot_adj, iff_false, not_and]
  intro h h'
  exact hne ((hU.support h).1.symm.trans (hU'.support h').1)

omit [DecidableEq V] in
private theorem local_disjoint_bridges (hcross : E ≤ crossBlockGraph b)
    {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent}
    {U : SimpleGraph V} (hU : IsLocalTree l U) : Disjoint U (relBridges b E) := by
  rw [disjoint_iff]
  ext x y
  simp only [inf_adj, bot_adj, iff_false, not_and]
  intro h hb
  apply bridgeBlock_ne_of_relBridges hcross hb
  exact (bridgeBlock_eq_iff_coreEdges hcross).2 ((hU.support h).1.trans (hU.support h).2.symm)

omit [DecidableEq V] in
/-- General injectivity of assembly. No edge-subset condition on a local
choice is needed, so replacement edges are covered. -/
theorem plusTree_injective_local (hcross : E ≤ crossBlockGraph b)
    {Us Ws : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V}
    (hU : ∀ l, IsLocalTree l (Us l)) (hW : ∀ l, IsLocalTree l (Ws l))
    (heq : plusTree b E Us = plusTree b E Ws) : Us = Ws := by
  have hle : ∀ {Us Ws : _}, (∀ l, IsLocalTree l (Us l)) → (∀ l, IsLocalTree l (Ws l)) →
      plusTree b E Us = plusTree b E Ws → ∀ l, Us l ≤ Ws l := by
    intro Us Ws hU hW heq l x y hxy
    have hf : (plusTree b E Ws).Adj x y := by
      rw [← heq, plusTree_eq hcross]
      exact Or.inl (iSup_adj.2 ⟨l, hxy⟩)
    rw [plusTree_eq hcross] at hf
    rcases hf with hf | hf
    · obtain ⟨l', hl'⟩ := iSup_adj.1 hf
      have he : l = l' := ((hU l).support hxy).1.symm.trans ((hW l').support hl').1
      simpa only [← he] using hl'
    · exact (disjoint_iff_inf_le.1 (local_disjoint_bridges hcross (hU l)) ⟨hxy, hf⟩).elim
  exact funext fun l => le_antisymm (hle hU hW heq l) (hle hW hU heq.symm l)

/-- The edges of an assembled choice factor into its local edges and the
unchanged bridges. -/
theorem prod_plusTree_local (hcross : E ≤ crossBlockGraph b)
    {Us : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V}
    (hU : ∀ l, IsLocalTree l (Us l)) {M : Type*} [CommMonoid M] (f : Sym2 V → M) :
    (∏ e ∈ (plusTree b E Us).edgeFinset, f e) =
      (∏ l, ∏ e ∈ (Us l).edgeFinset, f e) * ∏ e ∈ (relBridges b E).edgeFinset, f e := by
  rw [plusTree_eq hcross]
  convert prod_edgeFinset_iSup_sup (fun l l' h => local_disjoint (hU l) (hU l') h)
    (fun l => local_disjoint_bridges hcross (hU l)) f using 1
  exact prod_congr (Finset.ext fun e => by simp only [mem_edgeFinset]) fun _ _ => rfl

section Subpartition
variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
  {E : SimpleGraph (X.biUnion id)} {r : X.biUnion id → ℝ}
  {d : Sym2 (X.biUnion id) → ℝ}
  {Ts Us : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
    SimpleGraph (X.biUnion id)}

/-- Assembly preserves membership in `B(·, T)`. In particular replacement
edges need only stay within their bridge-block, not within the original graph. -/
theorem plusTree_mem_longAgreeingTrees
    (hcross : E ≤ crossBlockGraph (blockOf hX))
    (hT : IsRelTree X (plusTree (blockOf hX) E Ts))
    (hTs : ∀ l, IsLocalTree l (Ts l))
    (hUs : ∀ l, Us l ∈ blockAgreeingTrees r d l (Ts l)) :
    plusTree (blockOf hX) E Us ∈ longAgreeingTrees X r d (plusTree (blockOf hX) E Ts) := by
  let b := blockOf hX
  have hU : ∀ l, IsLocalTree l (Us l) := fun l => (mem_filter.1 (hUs l)).2.1
  have hagree : ∀ l e, (e ∈ (Us l).edgeSet ∧ radMax r e ≤ d e) ↔
      (e ∈ (Ts l).edgeSet ∧ radMax r e ≤ d e) := fun l => (mem_filter.1 (hUs l)).2.2
  have hcrossU : plusTree b E Us ≤ interEdges X := by
    rw [interEdges_eq hX, plusTree_eq hcross]
    exact sup_le (iSup_le fun l => (hU l).cross) (relBridges_le.trans hcross)
  have hconnT : (plusTree b E Ts ⊔ sameBlockGraph b).Connected := by
    rw [← intraEdges_eq hX, connected_sup_intraEdges_iff hX]
    exact hT.2.1.connected
  have hconnU : (plusTree b E Us ⊔ sameBlockGraph b).Connected := by
    have : Nonempty (X.biUnion id) := hconnT.nonempty
    refine ⟨fun x y => reachable_closed
      (P := fun z => (plusTree b E Us ⊔ sameBlockGraph b).Reachable x z)
      (fun u v hu huv => hu.trans ?_) (hconnT.preconnected x y) (Reachable.refl x)⟩
    rw [plusTree_eq hcross] at huv ⊢
    rcases huv with (hi | hb) | hs
    · obtain ⟨l, hl⟩ := iSup_adj.1 hi
      obtain ⟨hu, hv⟩ := (hTs l).support hl
      exact ((hU l).reachable u v hu hv).mono
        (sup_le_sup_right ((le_iSup Us l).trans le_sup_left) _)
    · exact Adj.reachable (Or.inl (Or.inr hb))
    · exact Adj.reachable (Or.inr hs)
  have hcard : Nat.card (plusTree b E Us).edgeSet = Nat.card (plusTree b E Ts).edgeSet := by
    rw [plusTree_eq hcross, plusTree_eq hcross,
      natCard_edgeSet_iSup_sup (fun l l' h => local_disjoint (hU l) (hU l') h)
        (fun l => local_disjoint_bridges hcross (hU l)),
      natCard_edgeSet_iSup_sup (fun l l' h => local_disjoint (hTs l) (hTs l') h)
        (fun l => local_disjoint_bridges hcross (hTs l))]
    congr 1
    exact sum_congr rfl fun l _ => by have := (hU l).card; have := (hTs l).card; omega
  have hcardT := ((isRelTree₀_iff_card hX).1 (Or.inl hT)).2.2
  change Nat.card (plusTree b E Ts).edgeSet + 1 = X.card at hcardT
  have hQconn : (quotientGraph X (plusTree b E Us)).Connected := by
    rwa [← intraEdges_eq hX, connected_sup_intraEdges_iff hX] at hconnU
  have hQle : Nat.card (quotientGraph X (plusTree b E Us)).edgeSet ≤
      Nat.card (plusTree b E Us).edgeSet := by
    rw [quotientGraph_eq hX]
    exact natCard_blockQuotient_edgeSet_le _ (interEdges_eq hX ▸ hcrossU)
  have hQge := hQconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hQge
  have hQU : (quotientGraph X (plusTree b E Us)).IsTree := by
    rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card (α := X), Fintype.card_coe]
    exact ⟨hQconn, by omega⟩
  have hUtree : IsRelTree X (plusTree b E Us) := by
    have hzero := (isRelTree₀_iff_card hX).2 ⟨hcrossU, hQU, by omega⟩
    exact hzero.resolve_right fun h => by
      obtain ⟨e, he⟩ := hT.1.2.1
      induction e using Sym2.ind with
      | h x y =>
        have hle : plusTree (blockOf hX) E Ts ≤ crossBlockGraph (blockOf hX) := interEdges_eq hX ▸ hT.1.1
        have hne := crossBlockGraph_adj.1 (hle he)
        have hc : 1 < Fintype.card X := Fintype.one_lt_card_iff.2 ⟨_, _, hne⟩
        rw [Fintype.card_coe] at hc
        omega
  refine mem_filter.2 ⟨mem_relTrees.2 hUtree, ?_⟩
  intro e
  induction e using Sym2.ind with
  | h x y =>
    simp only [mem_edgeSet, plusTree_eq hcross, sup_adj, iSup_adj]
    constructor
    · rintro ⟨(⟨l, hl⟩ | hb), hd⟩
      · exact ⟨Or.inl ⟨l, ((hagree l s(x, y)).1 ⟨hl, hd⟩).1⟩, hd⟩
      · exact ⟨Or.inr hb, hd⟩
    · rintro ⟨(⟨l, hl⟩ | hb), hd⟩
      · exact ⟨Or.inl ⟨l, ((hagree l s(x, y)).2 ⟨hl, hd⟩).1⟩, hd⟩
      · exact ⟨Or.inr hb, hd⟩

/-- The elementary sum step for an injective assembly of finite choices. -/
theorem sum_assembly_le {ι κ ω : Type*} [Fintype ι] [DecidableEq κ] [DecidableEq ω]
    (B : ι → Finset κ) (F : Finset ω) (assemble : (ι → κ) → ω)
    (g : ι → κ → ℝ) (w : ω → ℝ) (q : ℝ)
    (hw : ∀ x ∈ F, 0 ≤ w x)
    (hmem : ∀ u ∈ Fintype.piFinset B, assemble u ∈ F)
    (hinj : Set.InjOn assemble (Fintype.piFinset B))
    (hprod : ∀ u ∈ Fintype.piFinset B, (∏ i, g i (u i)) * q = w (assemble u)) :
    (∏ i, ∑ u ∈ B i, g i u) * q ≤ ∑ x ∈ F, w x := by
  rw [prod_univ_sum, sum_mul]
  calc (∑ u ∈ Fintype.piFinset B, (∏ i, g i (u i)) * q) =
      ∑ u ∈ Fintype.piFinset B, w (assemble u) := sum_congr rfl hprod
    _ = ∑ x ∈ (Fintype.piFinset B).image assemble, w x := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (fun x hx => by obtain ⟨u, hu, rfl⟩ := mem_image.1 hx; exact hmem u hu)
      (fun x hx _ => hw x hx)

/-- Multiplication of the local sums followed by injective assembly into the
full family, as in Step 3 of Corollary 5.34. -/
theorem prod_block_sums_le_tree_sum
    (hcross : E ≤ crossBlockGraph (blockOf hX))
    (hT : IsRelTree X (plusTree (blockOf hX) E Ts))
    (hTs : ∀ l, IsLocalTree l (Ts l)) (f : Sym2 (X.biUnion id) → ℝ)
    (hf : ∀ e, 0 ≤ f e) :
    (∏ l, ∑ U ∈ blockAgreeingTrees r d l (Ts l), ∏ e ∈ U.edgeFinset, f e) *
        (∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, f e) ≤
      ∑ U ∈ longAgreeingTrees X r d (plusTree (blockOf hX) E Ts),
        ∏ e ∈ U.edgeFinset, f e := by
  apply sum_assembly_le (fun l => blockAgreeingTrees r d l (Ts l))
    (longAgreeingTrees X r d (plusTree (blockOf hX) E Ts)) (plusTree (blockOf hX) E)
    (fun _ U => ∏ e ∈ U.edgeFinset, f e) (fun U => ∏ e ∈ U.edgeFinset, f e)
    (∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, f e)
  · exact fun U _ => prod_nonneg fun e _ => hf e
  · intro Us hUs
    exact plusTree_mem_longAgreeingTrees hX hcross hT hTs (Fintype.mem_piFinset.1 hUs)
  · intro Us hUs Ws hWs heq
    exact plusTree_injective_local hcross
      (fun l => (mem_filter.1 (Fintype.mem_piFinset.1 hUs l)).2.1)
      (fun l => (mem_filter.1 (Fintype.mem_piFinset.1 hWs l)).2.1) heq
  · intro Us hUs
    exact (prod_plusTree_local hcross
      (fun l => (mem_filter.1 (Fintype.mem_piFinset.1 hUs l)).2.1) f).symm

end Subpartition
end MultipoleBKT.UpperBound.Quadratic.RouteLift

end
