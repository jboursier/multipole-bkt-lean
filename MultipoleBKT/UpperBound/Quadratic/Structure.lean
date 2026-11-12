/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.CoreForest.BlockPeeling
public import MultipoleBKT.UpperBound.CoreForest.Pendant

/-!
# The bridge-blocks of the full quotient (setup of the proof of Corollary 5.34)

The paper: proof of Corollary 5.34: "Delete all bridges
of the multigraph quotient of `(V_X, E)` by `X`. … The nontrivial blocks are the original core
blocks, and the other edges are the core bridges and pendant edges. Hence this decomposition gives
the same `T` and `F` as Definition 5.29". As in `MultipoleBKT.UpperBound.CoreForest`, `b : V → β` is a block map and
`E ≤ crossBlockGraph b`.

* `relBridges_coreEdges_le`: a bridge of the 2-core is a bridge of `E` (a pendant tree is attached
  to the core at a single block, so it cannot close a cycle through a core bridge);
* `relBridges_eq_sup`: the bridges of `E` are the pendant edges and the bridges of the core;
* `bridgelessGraph_eq`: hence `E` and its core have the same bridgeless graph, so the bridge-blocks
  of the full quotient are those of the core (blocks outside the core are singleton bridge-blocks);
* `exists_componentEquiv`: the corresponding bijection of components;
* `reachable_sup_of_isMinimalSkeleton`, `connected_sup_of_isMinimalSkeleton`: `Peeled_X(E₀)` connects
  what `E₀` connects.
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace Quadratic

open CoreForest

/-- A predicate closed under the steps of a graph propagates along reachability. -/
theorem reachable_closed {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    (hP : ∀ x y, P x → G.Adj x y → P y) {u v : V} (huv : G.Reachable u v) (hu : P u) : P v := by
  obtain ⟨w⟩ := huv
  induction w with
  | nil => exact hu
  | cons h _ ih => exact ih (hP _ _ hu h)

/-- Equal graphs have canonically equivalent components. -/
theorem exists_componentEquiv {V : Type*} {G H : SimpleGraph V} (h : G = H) :
    ∃ e : G.ConnectedComponent ≃ H.ConnectedComponent,
      ∀ v, e (G.connectedComponentMk v) = H.connectedComponentMk v := by
  subst h
  exact ⟨Equiv.refl _, fun _ => rfl⟩

section Core

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] {b : V → β} {E : SimpleGraph V}

/-- The vertices reachable from a core vertex in `core ⊔ same-block` lie in core blocks. -/
theorem mem_twoCore_of_reachable {G : SimpleGraph V} (hG : G ≤ coreEdges b E ⊔ sameBlockGraph b)
    {x y : V} (h : G.Reachable x y) (hx : b x ∈ twoCore b E) : b y ∈ twoCore b E := by
  refine reachable_closed (P := fun z => b z ∈ twoCore b E) (fun u w hu huw => ?_) h hx
  rcases hG huw with hc | hs
  · exact (coreEdges_adj.1 hc).2.2
  · rw [← (sameBlockGraph_adj.1 hs).2]
    exact hu

variable (hE : E ≤ crossBlockGraph b)
include hE

/-- **A bridge of the 2-core is a bridge of `E`.** Starting from `u`, the vertices reachable in
`E ⊔ same-block` without the edge `uv` are the vertices reachable in `core ⊔ same-block` without
`uv`, extended by pendant trees; a pendant tree returns to the core only at its attachment block. -/
theorem relBridges_coreEdges_le : relBridges b (coreEdges b E) ≤ relBridges b E := by
  intro u v huv
  obtain ⟨hc, hbr⟩ := relBridges_adj.1 huv
  refine relBridges_adj.2 ⟨coreEdges_le hc, ?_⟩
  rw [isBridge_iff] at hbr ⊢
  intro hr
  apply hbr
  set Gc := (coreEdges b E ⊔ sameBlockGraph b).deleteEdges {s(u, v)} with hGc
  have hu : b u ∈ twoCore b E := (coreEdges_adj.1 hc).2.1
  have hv : b v ∈ twoCore b E := (coreEdges_adj.1 hc).2.2
  have huv' : b u ≠ b v := crossBlockGraph_adj.1 (hE (coreEdges_le hc))
  have hcoreY : ∀ y, Gc.Reachable u y → b y ∈ twoCore b E := fun y hy =>
    mem_twoCore_of_reachable (deleteEdges_le _) hy hu
  set P : V → Prop := fun x => ∃ y, Gc.Reachable u y ∧
    (pendantEdges b E ⊔ sameBlockGraph b).Reachable y x with hP
  -- a vertex of `P` in a core block is reachable in `Gc`
  have hkey : ∀ x, P x → b x ∈ twoCore b E → Gc.Reachable u x := by
    rintro x ⟨y, hy, hyx⟩ hx
    have hbyx : b y = b x :=
      eq_of_reachable_pendant (hcoreY y hy) hx (reachable_blockQuotient_of_reachable hyx)
    refine hy.trans ?_
    by_cases hyx' : y = x
    · rw [hyx']
    · refine Adj.reachable ?_
      rw [hGc, deleteEdges_adj, Set.mem_singleton_iff]
      refine ⟨Or.inr (sameBlockGraph_adj.2 ⟨hyx', hbyx⟩), fun he => ?_⟩
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv' hbyx
      · exact huv' hbyx.symm
  have hstep : ∀ x z, P x → ((E ⊔ sameBlockGraph b).deleteEdges {s(u, v)}).Adj x z → P z := by
    rintro x z ⟨y, hy, hyx⟩ hxz
    rw [deleteEdges_adj] at hxz
    obtain ⟨hxz, hne⟩ := hxz
    rcases hxz with hEa | hs
    · by_cases hcz : (coreEdges b E).Adj x z
      · have hx : b x ∈ twoCore b E := (coreEdges_adj.1 hcz).2.1
        have hux := hkey x ⟨y, hy, hyx⟩ hx
        refine ⟨z, hux.trans (Adj.reachable ?_), Reachable.refl _⟩
        rw [hGc, deleteEdges_adj]
        exact ⟨Or.inl hcz, hne⟩
      · have hp : (pendantEdges b E).Adj x z := by
          rw [pendantEdges, sdiff_adj]
          exact ⟨hEa, hcz⟩
        exact ⟨y, hy, hyx.trans (Adj.reachable (Or.inl hp))⟩
    · exact ⟨y, hy, hyx.trans (Adj.reachable (Or.inr hs))⟩
  exact hkey v (reachable_closed hstep hr ⟨u, Reachable.refl _, Reachable.refl _⟩) hv

/-- **The bridges of `E`** are its pendant edges and the bridges of its 2-core. -/
theorem relBridges_eq_sup :
    relBridges b E = pendantEdges b E ⊔ relBridges b (coreEdges b E) := by
  refine le_antisymm (fun u v huv => ?_) (sup_le (pendantEdges_le_relBridges hE)
    (relBridges_coreEdges_le hE))
  obtain ⟨hEuv, hbr⟩ := relBridges_adj.1 huv
  by_cases hc : (coreEdges b E).Adj u v
  · refine Or.inr (relBridges_adj.2 ⟨hc, ?_⟩)
    exact CoreForest.IsBridge.anti (sup_le_sup_right coreEdges_le _) hbr
  · refine Or.inl ?_
    rw [pendantEdges, sdiff_adj]
    exact ⟨hEuv, hc⟩

/-- **`E` and its 2-core have the same bridgeless graph**: the bridge-blocks of the full quotient
are the bridge-blocks of the core (the blocks outside the core being singleton bridge-blocks). -/
theorem bridgelessGraph_eq : bridgelessGraph b E = bridgelessGraph b (coreEdges b E) := by
  ext x y
  rw [bridgelessGraph_adj, bridgelessGraph_adj]
  refine or_congr_left ⟨fun ⟨hxy, hnb⟩ => ⟨?_, fun hb => hnb (relBridges_coreEdges_le hE hb)⟩,
    fun ⟨hxy, hnb⟩ => ⟨coreEdges_le hxy, fun hb => ?_⟩⟩
  · by_contra hc
    refine hnb (pendantEdges_le_relBridges hE ?_)
    rw [pendantEdges, sdiff_adj]
    exact ⟨hxy, hc⟩
  · rw [relBridges_eq_sup hE] at hb
    rcases hb with hp | hb
    · rw [pendantEdges, sdiff_adj] at hp
      exact hp.2 hxy
    · exact hnb hb

/-- The bridge-blocks of `E` and of its 2-core coincide. -/
theorem bridgeBlock_eq_iff_coreEdges {x y : V} :
    bridgeBlock b E x = bridgeBlock b E y ↔
      bridgeBlock b (coreEdges b E) x = bridgeBlock b (coreEdges b E) y := by
  rw [bridgeBlock_eq_iff, bridgeBlock_eq_iff, bridgelessGraph_eq hE]

end Core

/-! ### `Peeled_X(E₀)` keeps the connectivity -/

section Skeleton

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] {b : V → β} {E₀ E : SimpleGraph V}

/-- An edge of `E₀` dropped by the peeling joins two vertices that the skeleton still connects. -/
theorem reachable_sup_of_isMinimalSkeleton (h : IsMinimalSkeleton b E₀ E) {x y : V}
    (hxy : (E₀ ⊔ sameBlockGraph b).Reachable x y) : (E ⊔ sameBlockGraph b).Reachable x y := by
  refine reachable_closed (P := fun z => (E ⊔ sameBlockGraph b).Reachable x z)
    (fun u w hu huw => hu.trans ?_) hxy (Reachable.refl x)
  rcases huw with hE₀ | hs
  · by_cases hEuw : E.Adj u w
    · exact Adj.reachable (G := E ⊔ sameBlockGraph b) (Or.inl hEuw)
    · have hin : (coreEdges b E₀).Adj u w ∧ ¬ (relBridges b (coreEdges b E₀)).Adj u w := by
        by_contra hin
        exact hEuw (h.adj_of_not_inner hE₀ hin)
      have hbl := bridgeBlock_eq_of_adj_of_not_relBridges hin.1 hin.2
      obtain ⟨Ks, hKs, rfl⟩ := h
      have hr := (hKs (bridgeBlock b (coreEdges b E₀) u)).2.1.1 u w rfl hbl.symm
      refine hr.mono (sup_le_sup_right ?_ _)
      exact (le_iSup Ks _).trans (le_sup_left.trans le_sup_left)
  · exact Adj.reachable (G := E ⊔ sameBlockGraph b) (Or.inr hs)

/-- `Peeled_X(E₀) ∪ ℰ^intra` is connected when `E₀ ∪ ℰ^intra` is. -/
theorem connected_sup_of_isMinimalSkeleton (h : IsMinimalSkeleton b E₀ E)
    (hc : (E₀ ⊔ sameBlockGraph b).Connected) : (E ⊔ sameBlockGraph b).Connected := by
  have : Nonempty V := hc.nonempty
  exact ⟨fun x y => reachable_sup_of_isMinimalSkeleton h (hc.preconnected x y)⟩

end Skeleton

end Quadratic

end UpperBound

end MultipoleBKT

end
