/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.RelTree
public import MultipoleBKT.UpperBound.Quadratic.RouteLift.Compensation

/-!
# The lifted construction on the paper's actual parts

The paper: Corollary 5.34. The extracted relative tree projects to a tree
on `X`. Its bridge-block labels and bridge endpoints give the `BlockTree`
used by the lifted-path and attachment-fiber statements.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic
open CoreForest Peeling

/-- `𝒯_+^X(·, E) ∈ 𝖳^X` for `E = Peeled_X(E₀)`, `E₀ ∈ Eulc^X(V₁)`. -/
theorem isRelTree_plusTree_of_peeled {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {V₁ : Finset (X.biUnion id)} {E₀ E : SimpleGraph (X.biUnion id)}
    (hE₀ : IsRelEulerianOffConnected X V₁ E₀) (hE : IsMinimalSkeleton (blockOf hX) E₀ E)
    {r : X.biUnion id → ℝ} {dist : Sym2 (X.biUnion id) → ℝ}
    {v₁ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      X.biUnion id}
    {e₀ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      Sym2 (X.biUnion id)}
    {Ts Fs : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      SimpleGraph (X.biUnion id)}
    (hP : IsPlusPeeling (blockOf hX) E (blockInnerEdges (blockOf hX) E) r dist v₁ e₀ Ts Fs) :
    IsRelTree X (plusTree (blockOf hX) E Ts) := by
  have hcross₀ : E₀ ≤ crossBlockGraph (blockOf hX) := interEdges_eq hX ▸ hE₀.1.1
  have hcross : E ≤ crossBlockGraph (blockOf hX) := hE.le.trans hcross₀
  have hconn₀ : (E₀ ⊔ sameBlockGraph (blockOf hX)).Connected := intraEdges_eq hX ▸ hE₀.2.2.2
  have hconn := connected_sup_of_isMinimalSkeleton hE hconn₀
  have hEE := isMinimalSkeleton_self_of_isMinimalSkeleton hcross₀ hE
  have hX2 : 2 ≤ X.card := by
    obtain ⟨e, he⟩ := hE₀.2.2.1
    induction e using Sym2.ind with
    | h u v =>
      have hne := crossBlockGraph_adj.1 (hcross₀ he)
      have : 1 < Fintype.card X := Fintype.one_lt_card_iff.2 ⟨_, _, hne⟩
      rw [Fintype.card_coe] at this
      omega
  exact isRelTree_plusTree hX hcross hEE hP hconn hX2

end MultipoleBKT.UpperBound.Quadratic

namespace MultipoleBKT.UpperBound.Quadratic.RouteLift
open CoreForest

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
  (E : SimpleGraph (X.biUnion id))

theorem existsUnique_partBlock (S : X) :
    ∃! l, ∀ i, blockOf hX i = S → bridgeBlock (blockOf hX) E i = l := by
  obtain ⟨i, hi⟩ := blockOf_surjective hX S
  refine ⟨bridgeBlock (blockOf hX) E i, ?_, ?_⟩
  · intro j hj
    exact bridgeBlock_eq_of_eq (hj.trans hi.symm)
  · intro l hl
    exact (hl i hi).symm

/-- The unique bridge-block containing a part of `X`. -/
noncomputable def partBlock (S : X) : (bridgelessGraph (blockOf hX) E).ConnectedComponent :=
  (existsUnique_partBlock hX E S).choose

/-- Passing from a vertex to its part preserves the bridge-block label. -/
theorem partBlock_blockOf (i : X.biUnion id) :
    partBlock hX E (blockOf hX i) = bridgeBlock (blockOf hX) E i :=
  ((existsUnique_partBlock hX E (blockOf hX i)).choose_spec.1 i rfl).symm

/-- The original parts, rather than chosen vertices of the blocks, support
the lifted construction. In particular its total length is bounded by `|X|-1`.
The supplied endpoint functions are the actual parent bridges. -/
theorem part_lift_of_bridges {V₁ : Finset (X.biUnion id)} {E₀ : SimpleGraph (X.biUnion id)}
    (hE₀ : IsRelEulerianOffConnected X V₁ E₀) (hE : IsMinimalSkeleton (blockOf hX) E₀ E)
    {r : X.biUnion id → ℝ} {dist : Sym2 (X.biUnion id) → ℝ}
    {v₁ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent → X.biUnion id}
    {e₀ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent → Sym2 (X.biUnion id)}
    {Ts Fs : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      SimpleGraph (X.biUnion id)}
    (hP : IsPlusPeeling (blockOf hX) E (blockInnerEdges (blockOf hX) E) r dist v₁ e₀ Ts Fs)
    (a : (bridgelessGraph (blockOf hX) E).ConnectedComponent)
    (c p : Nonroot a → X.biUnion id)
    (hc : ∀ l, bridgeBlock (blockOf hX) E (c l) = l)
    (hp : ∀ l, IsParent (bridgeTree (blockOf hX) E) a (bridgeBlock (blockOf hX) E (p l)) l)
    (hbr : ∀ l, (relBridges (blockOf hX) E).Adj (c l) (p l)) :
    ∃ D : BlockTree (bridgeTree (blockOf hX) E) a
        (quotientGraph X (plusTree (blockOf hX) E Ts)),
      D.block = partBlock hX E ∧
      D.childEnd = (fun l => blockOf hX (c l)) ∧
      D.parentEnd = (fun l => blockOf hX (p l)) ∧
      ∀ (h : _ → _) (hτ : (bridgeTree (blockOf hX) E).IsTree),
        ∑ l : Leaf (bridgeTree (blockOf hX) E) a,
          (quotientGraph X (plusTree (blockOf hX) E Ts)).dist
            (D.start l) (loc (h := h) hτ D.parentEnd l) ≤ X.card - 1 := by
  let b := blockOf hX
  let bb := bridgeBlock b E
  let Q := quotientGraph X (plusTree b E Ts)
  have hcross₀ : E₀ ≤ crossBlockGraph b := interEdges_eq hX ▸ hE₀.1.1
  have hcross : E ≤ crossBlockGraph b := hE.le.trans hcross₀
  have hEE := isMinimalSkeleton_self_of_isMinimalSkeleton hcross₀ hE
  obtain ⟨eqv, heqv⟩ := exists_componentEquiv (bridgelessGraph_eq hcross)
  have hcomp : ∀ z, eqv (bb z) = bridgeBlock b (coreEdges b E) z := heqv
  have hTle : ∀ l, Ts l ≤ blockInnerEdges b E l := fun l =>
    (tree_sup_removed hcross hEE hP l).1 ▸ le_sup_left
  have hQadj : ∀ x y, (plusTree b E Ts).Adj x y → Q.Adj (b x) (b y) := by
    intro x y hxy
    dsimp only [Q]
    rw [quotientGraph_eq hX]
    exact blockQuotient_adj_of_adj hxy (crossBlockGraph_adj.1
      (hcross (by
        rw [plusTree_eq hcross] at hxy
        rcases hxy with hxy | hxy
        · obtain ⟨l, hl⟩ := iSup_adj.1 hxy
          exact blockInnerEdges_le l (hTle l hl)
        · exact relBridges_le hxy)))
  have hinside : ∀ x y : X, partBlock hX E x = partBlock hX E y →
      ∃ w : Q.Walk x y, ∀ z ∈ w.support, partBlock hX E z = partBlock hX E x := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := blockOf_surjective hX x
    obtain ⟨v, rfl⟩ := blockOf_surjective hX y
    rw [partBlock_blockOf, partBlock_blockOf] at hxy
    let l := eqv (bb u)
    have hu : bridgeBlock b (coreEdges b E) u = l := (hcomp u).symm
    have hv : bridgeBlock b (coreEdges b E) v = l := by
      rw [← hcomp v]
      exact congrArg eqv hxy.symm
    let U := {z : X.biUnion id // bridgeBlock b (coreEdges b E) z = l}
    let H : SimpleGraph U := (Ts l ⊔ sameBlockGraph b).comap Subtype.val
    have hr := reachable_tree_of_inBlock hP l hu hv
    have hrU : H.Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
      obtain ⟨w⟩ := hr
      have hw : ∀ z ∈ w.support, bridgeBlock b (coreEdges b E) z = l := by
        intro z hz
        have hkeep : Ts l ⊔ sameBlockGraph b ≤ bridgelessGraph b (coreEdges b E) := by
          intro s t hst
          rcases hst with hst | hst
          · obtain ⟨he, hnb, -⟩ := blockInnerEdges_adj.1 (hTle l hst)
            exact Or.inl ⟨he, hnb⟩
          · exact Or.inr hst
        exact ((bridgeBlock_eq_iff.2 ((w.takeUntil z hz).reachable.mono hkeep)).symm.trans hu)
      exact ⟨w.induce _ hw⟩
    let Z := {S : X // partBlock hX E S = bb u}
    let f : U → Z := fun z => ⟨b z, by
      rw [partBlock_blockOf]
      change bb z = bb u
      apply eqv.injective
      rw [hcomp, z.property]⟩
    have hz : (Q.comap (fun S : Z => S.val)).Reachable (f ⟨u, hu⟩) (f ⟨v, hv⟩) := by
      apply reachable_comp_of_forall_adj f _ hrU
      intro s t hst
      by_cases he : b s.val = b t.val
      · exact (show f s = f t from Subtype.ext he) ▸ Reachable.refl _
      · have hst' : (Ts l).Adj s t := by
          rcases hst with hst | hst
          · exact hst
          · exact (he (sameBlockGraph_adj.1 hst).2).elim
        have hstQ : (Q.comap (fun S : Z => S.val)).Adj (f s) (f t) :=
          hQadj s t (by rw [plusTree_eq hcross]; exact Or.inl (iSup_adj.2 ⟨l, hst'⟩))
        exact hstQ.reachable
    obtain ⟨w⟩ := hz
    refine ⟨w.map ⟨Subtype.val, fun {_ _} hst => hst⟩, ?_⟩
    intro z hz
    rw [Walk.support_map, List.mem_map] at hz
    obtain ⟨z', -, rfl⟩ := hz
    change partBlock hX E z'.val = partBlock hX E (blockOf hX u)
    rw [partBlock_blockOf]
    exact z'.property
  let D : BlockTree (bridgeTree (blockOf hX) E) a Q :=
          { block := partBlock hX E
            childEnd := fun l => b (c l)
            parentEnd := fun l => b (p l)
            child_block := fun l => (partBlock_blockOf hX E (c l)).trans (hc l)
            parent_block := fun l => by
              change IsParent (bridgeTree (blockOf hX) E) a
                (partBlock hX E (blockOf hX (p l))) l
              rw [partBlock_blockOf]
              exact hp l
            bridge_adj := fun l => hQadj _ _ (by rw [plusTree_eq hcross]; exact Or.inr (hbr l))
            inside := hinside }
  refine ⟨D, rfl, rfl, rfl, ?_⟩
  intro h hτ
  have hQ := (isRelTree_plusTree_of_peeled hX hE₀ hE hP).2.1
  simpa only [Fintype.card_coe] using D.total_lifted_length_le (h := h) hτ hQ


end MultipoleBKT.UpperBound.Quadratic.RouteLift

end
