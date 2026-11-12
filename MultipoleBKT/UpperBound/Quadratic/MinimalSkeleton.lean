/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.Structure

/-!
# `Peeled_X(E₀)` is a minimal skeleton

The paper: Definitions 5.28–5.29 and Corollary 5.34
: Corollary 5.34 sets `E = Peeled_X(E₀)` and uses `T = 𝒯_+^X(·, E)`,
`F = 𝓕_+^X(·, E)` "as in Definition 5.29", which is stated for minimal skeletons. That
`Peeled_X(E₀)` is itself a minimal skeleton is used without proof (the docstring of
`MultipoleBKT.CoreForest.IsPlusPeeling`). We prove it.

Let `E = ⋃_l G_l' ∪ ⋃_i E(P_i) ∪ ℰ_br` be an admissible `Peeled_X(E₀)`, with skeletons
`G_l' = Ks l` of the bridge-blocks `G_l` of the 2-core of `E₀`. Then:

* `twoCore_eq_of_isMinimalSkeleton`: the 2-core of `E` has the same blocks as that of `E₀` (a core
  block keeps two edge-ends inside the core: through `G_l'`, which is 2-edge-connected, or through the
  core bridges, which are kept);
* `coreEdges_eq_of_isMinimalSkeleton`: its edges are `⋃_l G_l' ∪ ℰ_br`;
* `relBridges_coreEdges_eq_of_isMinimalSkeleton`: its bridges are `ℰ_br` (the edges of `G_l'` lie on
  cycles);
* `reachable_bridgeless_iff_of_isMinimalSkeleton`: its bridge-blocks have the vertex sets of those
  of `E₀`;
* `blockInnerEdges_eq_of_isMinimalSkeleton`: the bridge-block `G_l` of `E` is `G_l'`;
* `isMinimalSkeleton_self_of_isMinimalSkeleton`: **`Peeled_X(E)` = `E`**, i.e.
  `IsMinimalSkeleton b E E`.
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace Quadratic

open CoreForest

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] {b : V → β}

/-! ### Monotonicity of the 2-core -/

section Mono

omit [Fintype β] in
theorem degIn_mono_graph {E E' : SimpleGraph V} (h : E ≤ E') (F : Finset β) (S : β) :
    degIn b E F S ≤ degIn b E' F S := by
  classical
  unfold degIn
  refine Finset.card_le_card fun p hp => ?_
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hp.2.2.1, h hp.2.2.2⟩

theorem twoCore_mono {E E' : SimpleGraph V} (h : E ≤ E') : twoCore b E ⊆ twoCore b E' :=
  subset_twoCore fun S hS => (isTwoClosed_twoCore S hS).trans (degIn_mono_graph h _ S)

end Mono

/-! ### Two edge-ends at a block -/

section Exit

omit [Fintype V] [Fintype β] [DecidableEq β] in
/-- A walk of `K ⊔ same-block` leaving the block of its start uses an edge of `K` leaving it. -/
theorem exists_exit {K : SimpleGraph V} {x y : V} (h : (K ⊔ sameBlockGraph b).Reachable x y)
    (hy : b y ≠ b x) : ∃ u w, K.Adj u w ∧ b u = b x ∧ b w ≠ b x := by
  by_contra H
  push Not at H
  exact hy (reachable_closed (P := fun z => b z = b x) (fun u w hu huw => by
    rcases huw with hK | hs
    · exact H u w hK hu
    · rw [← (sameBlockGraph_adj.1 hs).2]
      exact hu) h rfl)

omit [Fintype β] in
/-- If `K ⊔ same-block` joins `x` to another block, also after deleting any edge of `K`, then two
edges of `K` leave the block of `x`; if they are edges of `E` ending in `F`, the block has degree at
least `2` inside `F`. -/
theorem two_le_degIn_of_twoEdge {E K : SimpleGraph V} {F : Finset β} {x y : V}
    (hK1 : (K ⊔ sameBlockGraph b).Reachable x y)
    (hK2 : ∀ a c, K.Adj a c → (K.deleteEdges {s(a, c)} ⊔ sameBlockGraph b).Reachable x y)
    (hy : b y ≠ b x) (hKE : K ≤ E) (hKF : ∀ u w, K.Adj u w → b w ∈ F) :
    2 ≤ degIn b E F (b x) := by
  classical
  obtain ⟨u, w, huw, hu, hw⟩ := exists_exit hK1 hy
  obtain ⟨u', w', huw', hu', hw'⟩ := exists_exit (hK2 u w huw) hy
  rw [deleteEdges_adj, Set.mem_singleton_iff] at huw'
  unfold degIn
  rw [Nat.succ_le_iff, Finset.one_lt_card]
  refine ⟨(u, w), ?_, (u', w'), ?_, fun he => huw'.2 ?_⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, hKF u w huw, hKE huw⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hu', hKF u' w' huw'.1, hKE huw'.1⟩
  · rw [Prod.mk.injEq] at he
    rw [he.1, he.2]

end Exit

/-! ### The structure of `Peeled_X(E₀)` -/

section Peeled

variable {E₀ E : SimpleGraph V} {Ks : (bridgelessGraph b (coreEdges b E₀)).ConnectedComponent →
  SimpleGraph V}

/-- The edges of a skeleton `G_l'` are non-bridge core edges of `E₀` inside `l`. -/
theorem adj_of_isBlockSkeleton {l : (bridgelessGraph b (coreEdges b E₀)).ConnectedComponent}
    {K : SimpleGraph V} (hK : IsBlockSkeleton b E₀ l K) {u v : V} (huv : K.Adj u v) :
    (coreEdges b E₀).Adj u v ∧ ¬ (relBridges b (coreEdges b E₀)).Adj u v ∧
      bridgeBlock b (coreEdges b E₀) u = l ∧ bridgeBlock b (coreEdges b E₀) v = l := by
  obtain ⟨hc, hnb, hu⟩ := blockInnerEdges_adj.1 (hK.1 huv)
  exact ⟨hc, hnb, hu, (bridgeBlock_eq_of_adj_of_not_relBridges hc hnb).symm.trans hu⟩

variable (hE₀ : E₀ ≤ crossBlockGraph b) (hKs : ∀ l, IsBlockSkeleton b E₀ l (Ks l))
  (hE : E = (⨆ l, Ks l) ⊔ pendantEdges b E₀ ⊔ relBridges b (coreEdges b E₀))
include hE₀ hKs hE

omit hE₀ in
theorem le_of_isMinimalSkeleton' : E ≤ E₀ := by
  rw [hE]
  refine sup_le (sup_le (iSup_le fun l => ?_) pendantEdges_le) (relBridges_le.trans coreEdges_le)
  exact fun u v huv => coreEdges_le (adj_of_isBlockSkeleton (hKs l) huv).1

/-- **The 2-core of `Peeled_X(E₀)` has the blocks of the 2-core of `E₀`.** -/
theorem twoCore_eq_of_isMinimalSkeleton : twoCore b E = twoCore b E₀ := by
  classical
  have hle := le_of_isMinimalSkeleton' hKs hE
  refine Finset.Subset.antisymm (twoCore_mono hle) (subset_twoCore fun S hS => ?_)
  by_cases hin : ∃ x y, b x = S ∧ (coreEdges b E₀).Adj x y ∧
      ¬ (relBridges b (coreEdges b E₀)).Adj x y
  · -- `S` meets a non-trivial bridge-block, spanned 2-edge-connectedly by its skeleton
    obtain ⟨x, y, rfl, hc, hnb⟩ := hin
    set l := bridgeBlock b (coreEdges b E₀) x
    have hy : bridgeBlock b (coreEdges b E₀) y = l :=
      (bridgeBlock_eq_of_adj_of_not_relBridges hc hnb).symm
    have hxy : b y ≠ b x := fun h => crossBlockGraph_adj.1 (hE₀ (coreEdges_le hc)) h.symm
    have hKE : Ks l ≤ E := by
      rw [hE]
      exact (le_iSup Ks l).trans (le_sup_left.trans le_sup_left)
    refine two_le_degIn_of_twoEdge ((hKs l).2.1.1 x y rfl hy)
      (fun a c hac => (hKs l).2.1.2 a c hac x y rfl hy) hxy hKE fun u w huw => ?_
    exact (coreEdges_adj.1 (adj_of_isBlockSkeleton (hKs l) huw).1).2.2
  · -- all core edges at `S` are bridges of the core, which are kept
    push Not at hin
    refine (isTwoClosed_twoCore S hS).trans (Finset.card_le_card fun p hp => ?_)
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨-, hpS, hpF, hpE⟩ := hp
    refine ⟨Finset.mem_univ _, hpS, hpF, ?_⟩
    have hc : (coreEdges b E₀).Adj p.1 p.2 := coreEdges_adj.2 ⟨hpE, hpS ▸ hS, hpF⟩
    have hb := hin p.1 p.2 hpS hc
    rw [hE]
    exact Or.inr hb

/-- **The core edges of `Peeled_X(E₀)`**: the skeletons and the bridges of the core of `E₀`. -/
theorem coreEdges_eq_of_isMinimalSkeleton :
    coreEdges b E = (⨆ l, Ks l) ⊔ relBridges b (coreEdges b E₀) := by
  have hcore := twoCore_eq_of_isMinimalSkeleton hE₀ hKs hE
  ext u v
  rw [coreEdges_adj, hcore, sup_adj, iSup_adj]
  constructor
  · rintro ⟨huv, hu, hv⟩
    rw [hE, sup_adj, sup_adj, iSup_adj] at huv
    rcases huv with (hK | hp) | hb
    · exact Or.inl hK
    · rcases (pendantEdges_adj.1 hp).2 with h | h
      · exact absurd hu h
      · exact absurd hv h
    · exact Or.inr hb
  · rintro (⟨l, hK⟩ | hb)
    · have hc := (adj_of_isBlockSkeleton (hKs l) hK).1
      refine ⟨?_, (coreEdges_adj.1 hc).2⟩
      rw [hE]
      exact Or.inl (Or.inl ((iSup_adj).2 ⟨l, hK⟩))
    · refine ⟨?_, (coreEdges_adj.1 (relBridges_le hb)).2⟩
      rw [hE]
      exact Or.inr hb

/-- **The bridges of the core of `Peeled_X(E₀)`** are those of the core of `E₀`. -/
theorem relBridges_coreEdges_eq_of_isMinimalSkeleton :
    relBridges b (coreEdges b E) = relBridges b (coreEdges b E₀) := by
  have hcE := coreEdges_eq_of_isMinimalSkeleton hE₀ hKs hE
  have hcle : coreEdges b E ≤ coreEdges b E₀ := by
    rw [hcE]
    refine sup_le (iSup_le fun l u v huv => (adj_of_isBlockSkeleton (hKs l) huv).1) relBridges_le
  ext u v
  constructor
  · intro huv
    obtain ⟨hc, hbr⟩ := relBridges_adj.1 huv
    rw [hcE, sup_adj, iSup_adj] at hc
    rcases hc with ⟨l, hK⟩ | hb
    · exfalso
      obtain ⟨-, -, hu, hv⟩ := adj_of_isBlockSkeleton (hKs l) hK
      have hr := (hKs l).2.1.2 u v hK u v hu hv
      refine (isBridge_iff.1 hbr) (hr.mono fun x y hxy => ?_)
      rw [deleteEdges_adj, Set.mem_singleton_iff]
      rcases hxy with hxy | hxy
      · rw [deleteEdges_adj, Set.mem_singleton_iff] at hxy
        refine ⟨Or.inl ?_, hxy.2⟩
        rw [hcE]
        exact Or.inl ((iSup_adj).2 ⟨l, hxy.1⟩)
      · refine ⟨Or.inr hxy, fun he => ?_⟩
        have hb' := (sameBlockGraph_adj.1 hxy).2
        have hcr := crossBlockGraph_adj.1 (hE₀ (coreEdges_le (adj_of_isBlockSkeleton (hKs l) hK).1))
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcr hb'
        · exact hcr hb'.symm
    · exact hb
  · intro huv
    obtain ⟨hc, hbr⟩ := relBridges_adj.1 huv
    refine relBridges_adj.2 ⟨?_, CoreForest.IsBridge.anti (sup_le_sup_right hcle _) hbr⟩
    rw [hcE]
    exact Or.inr huv

/-- **The bridge-blocks of the core of `Peeled_X(E₀)`** have the vertex sets of those of `E₀`. -/
theorem reachable_bridgeless_iff_of_isMinimalSkeleton {x y : V} :
    (bridgelessGraph b (coreEdges b E)).Reachable x y ↔
      (bridgelessGraph b (coreEdges b E₀)).Reachable x y := by
  have hcE := coreEdges_eq_of_isMinimalSkeleton hE₀ hKs hE
  have hbE := relBridges_coreEdges_eq_of_isMinimalSkeleton hE₀ hKs hE
  constructor
  · intro h
    refine h.mono fun u v huv => ?_
    rcases bridgelessGraph_adj.1 huv with ⟨hc, hnb⟩ | hs
    · rw [hbE] at hnb
      rw [hcE, sup_adj, iSup_adj] at hc
      rcases hc with ⟨l, hK⟩ | hb
      · obtain ⟨hc₀, hnb₀, -⟩ := adj_of_isBlockSkeleton (hKs l) hK
        exact bridgelessGraph_adj.2 (Or.inl ⟨hc₀, hnb₀⟩)
      · exact absurd hb hnb
    · exact bridgelessGraph_adj.2 (Or.inr hs)
  · intro h
    set l := bridgeBlock b (coreEdges b E₀) x
    have hyl : bridgeBlock b (coreEdges b E₀) y = l := (bridgeBlock_eq_iff.2 h).symm
    refine ((hKs l).2.1.1 x y rfl hyl).mono fun u v huv => ?_
    rcases huv with hK | hs
    · obtain ⟨-, hnb₀, -⟩ := adj_of_isBlockSkeleton (hKs l) hK
      refine bridgelessGraph_adj.2 (Or.inl ⟨?_, ?_⟩)
      · rw [hcE]
        exact Or.inl ((iSup_adj).2 ⟨l, hK⟩)
      · rw [hbE]
        exact hnb₀
    · exact bridgelessGraph_adj.2 (Or.inr hs)

theorem bridgeBlock_eq_iff_of_isMinimalSkeleton {x y : V} :
    bridgeBlock b (coreEdges b E) x = bridgeBlock b (coreEdges b E) y ↔
      bridgeBlock b (coreEdges b E₀) x = bridgeBlock b (coreEdges b E₀) y := by
  rw [bridgeBlock_eq_iff, bridgeBlock_eq_iff, reachable_bridgeless_iff_of_isMinimalSkeleton hE₀ hKs hE]

/-- **The bridge-block `G_l` of `Peeled_X(E₀)`** containing `x` is the skeleton `G_{l₀}'` of the
bridge-block `l₀` of `E₀` containing `x`. -/
theorem blockInnerEdges_eq_of_isMinimalSkeleton (x : V) :
    blockInnerEdges b E (bridgeBlock b (coreEdges b E) x) =
      Ks (bridgeBlock b (coreEdges b E₀) x) := by
  have hcE := coreEdges_eq_of_isMinimalSkeleton hE₀ hKs hE
  have hbE := relBridges_coreEdges_eq_of_isMinimalSkeleton hE₀ hKs hE
  ext u v
  rw [blockInnerEdges_adj, hbE, bridgeBlock_eq_iff_of_isMinimalSkeleton hE₀ hKs hE]
  constructor
  · rintro ⟨hc, hnb, hu⟩
    rw [hcE, sup_adj, iSup_adj] at hc
    rcases hc with ⟨l, hK⟩ | hb
    · obtain ⟨-, -, hul, -⟩ := adj_of_isBlockSkeleton (hKs l) hK
      rw [← hu, hul]
      exact hK
    · exact absurd hb hnb
  · intro hK
    obtain ⟨-, hnb₀, hu, -⟩ := adj_of_isBlockSkeleton (hKs _) hK
    refine ⟨?_, hnb₀, hu⟩
    rw [hcE]
    exact Or.inl ((iSup_adj).2 ⟨_, hK⟩)

theorem twoEdgeConnectsBlock_iff_of_isMinimalSkeleton (x : V) (K : SimpleGraph V) :
    TwoEdgeConnectsBlock b E (bridgeBlock b (coreEdges b E) x) K ↔
      TwoEdgeConnectsBlock b E₀ (bridgeBlock b (coreEdges b E₀) x) K := by
  have h := fun y => bridgeBlock_eq_iff_of_isMinimalSkeleton hE₀ hKs hE (x := y) (y := x)
  unfold TwoEdgeConnectsBlock
  simp only [h]

/-- **`Peeled_X(E₀)` is a minimal skeleton** (used without proof in Corollary 5.34 and
Definition 5.29): `IsMinimalSkeleton b E E`. -/
theorem isMinimalSkeleton_self_of_isMinimalSkeleton' : IsMinimalSkeleton b E E := by
  rw [isMinimalSkeleton_self_iff]
  intro l
  induction l using ConnectedComponent.ind with
  | h x =>
    show IsBlockSkeleton b E (bridgeBlock b (coreEdges b E) x)
      (blockInnerEdges b E (bridgeBlock b (coreEdges b E) x))
    rw [blockInnerEdges_eq_of_isMinimalSkeleton hE₀ hKs hE x]
    obtain ⟨hle, h2, hmin⟩ := hKs (bridgeBlock b (coreEdges b E₀) x)
    refine ⟨?_, (twoEdgeConnectsBlock_iff_of_isMinimalSkeleton hE₀ hKs hE x _).2 h2,
      fun K' hK' h2' => hmin K' hK'
        ((twoEdgeConnectsBlock_iff_of_isMinimalSkeleton hE₀ hKs hE x K').1 h2')⟩
    rw [blockInnerEdges_eq_of_isMinimalSkeleton hE₀ hKs hE x]

end Peeled

/-- **`Peeled_X(E₀)` is a minimal skeleton**: if `E` is an admissible `Peeled_X(E₀)` (with
`E₀ ⊆ ℰ^inter`), then `Peeled_X(E) = E`. -/
theorem isMinimalSkeleton_self_of_isMinimalSkeleton {E₀ E : SimpleGraph V}
    (hE₀ : E₀ ≤ crossBlockGraph b) (h : IsMinimalSkeleton b E₀ E) : IsMinimalSkeleton b E E := by
  obtain ⟨Ks, hKs, hE⟩ := h
  exact isMinimalSkeleton_self_of_isMinimalSkeleton' hE₀ hKs hE

end Quadratic

end UpperBound

end MultipoleBKT

end
