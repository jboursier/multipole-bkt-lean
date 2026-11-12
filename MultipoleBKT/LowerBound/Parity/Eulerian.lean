/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Parity.Cancellation
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# Eulerian graphs relative to a subpartition (Definitions 4.33, 4.36; Lemma 4.37)

Sections 4.9–4.10. Throughout, `X` is a subpartition
of `ℕ`, `V_X = ⋃_{S ∈ X} S` is the type `X.biUnion id`, and edge sets on `V_X` are simple graphs
on it (as in `MultipoleBKT.Cluster.Relative`).

* `IsRelEulerian X E`, `relEulerian X`: `E ∈ Eul^X`, i.e. `E ⊆ ℰ^inter(X)` and
  `deg_E(S) = ∑_{i ∈ S} deg_E(i)` is even for every `S ∈ X` (Definition 4.33);
* `IsRelEulerianConnected X E`, `relEulerianConnected X`: `E ∈ Eulc^X = 𝖤^X ∩ Eul^X`;
* `IsRelTwoEdgeConnected X E`: `(V_X, E)` is 2-edge-connected relative to `X`, i.e. `E ∈ 𝖤^X` and
  `E ∖ {e} ∈ 𝖤^X` for every `e ∈ E` (Definition 4.36(1));
  `IsRelMinTwoEdgeConnected X E`: minimally so (Definition 4.36(2)).

Results:

* `isRelTwoEdgeConnected_iff`: the reformulation of Definition 4.36(1) given in the paper
  ("this means that `(V_X, E ∪ ℰ^intra(X))` has no bridge in `E`");
* `not_isBridge_of_isRelEulerian`: in `(V_X, E ∪ ℰ^intra(X))`, no edge of an `E ∈ Eul^X` is a
  bridge (connectedness is not needed);
* **Lemma 4.37** (`lemma_4_37`, Lemma 4.37): `E ∈ Eulc^X` is 2-edge-connected relative
  to `X`.

The proof of `not_isBridge_of_isRelEulerian` follows the written handshaking contradiction.
After deleting a proposed bridge `ab`, its component at `a` is a union of blocks `X'`.
Restrict the remaining edges to this component. The degree of `[a]` is odd and the
sum of the block degrees is twice the edge count. Thus another block of `X'` has
odd degree. Its degree equals its original degree, contradicting the Eulerian condition.
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace Parity

/-! ### Definitions 4.33 and 4.36 -/

section Definitions

variable (X : Finset (Finset ℕ))

/-- `E ∈ Eul^X`: `E` is Eulerian relative to `X` (Definition 4.33): `E ⊆ ℰ^inter(X)` and `∑_{i ∈ S} deg_E(i)` is even for every `S ∈ X`. -/
def IsRelEulerian (E : SimpleGraph (X.biUnion id)) : Prop :=
  E ≤ interEdges X ∧ ∀ S ∈ X, Even (blockDegree X E S)

/-- `E ∈ Eulc^X = 𝖤^X ∩ Eul^X` (Definition 4.33): `E` is Eulerian and
connected relative to `X`. -/
def IsRelEulerianConnected (E : SimpleGraph (X.biUnion id)) : Prop :=
  IsRelConnected X E ∧ IsRelEulerian X E

open scoped Classical in
/-- The finite set `Eul^X`. -/
noncomputable def relEulerian : Finset (SimpleGraph (X.biUnion id)) :=
  (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (IsRelEulerian X)

open scoped Classical in
/-- The finite set `Eulc^X`. -/
noncomputable def relEulerianConnected : Finset (SimpleGraph (X.biUnion id)) :=
  relConnected X ∩ relEulerian X

/-- `(V_X, E)` is 2-edge-connected relative to `X` (Definition 4.36(1)): `E ∈ 𝖤^X` and, for every edge `e ∈ E`, `(V_X, E ∖ {e})` is connected
relative to `X`, i.e. `E ∖ {e} ∈ 𝖤^X`. -/
def IsRelTwoEdgeConnected (E : SimpleGraph (X.biUnion id)) : Prop :=
  IsRelConnected X E ∧ ∀ u v, E.Adj u v → IsRelConnected X (E.deleteEdges {s(u, v)})

/-- `(V_X, E)` is minimally 2-edge-connected relative to `X` (Definition 4.36(2)): it is 2-edge-connected relative to `X` and, for every edge `e ∈ E`, `(V_X, E ∖ {e})` is
not. -/
def IsRelMinTwoEdgeConnected (E : SimpleGraph (X.biUnion id)) : Prop :=
  IsRelTwoEdgeConnected X E ∧
    ∀ u v, E.Adj u v → ¬ IsRelTwoEdgeConnected X (E.deleteEdges {s(u, v)})

variable {X}

theorem mem_relEulerian {E : SimpleGraph (X.biUnion id)} :
    E ∈ relEulerian X ↔ IsRelEulerian X E := by
  simp [relEulerian]

theorem mem_relEulerianConnected {E : SimpleGraph (X.biUnion id)} :
    E ∈ relEulerianConnected X ↔ IsRelEulerianConnected X E := by
  classical
  rw [relEulerianConnected, mem_inter, mem_relConnected, mem_relEulerian]
  rfl

end Definitions

/-! ### Deleting an inter-block edge -/

section Delete

variable {X : Finset (Finset ℕ)}

/-- Deleting an edge of `E ⊆ ℰ^inter(X)` from `E ∪ ℰ^intra(X)` deletes it from `E`. -/
theorem sup_intraEdges_deleteEdges (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (hE : E ≤ interEdges X) {a b : X.biUnion id} (hab : E.Adj a b) :
    (E ⊔ intraEdges X).deleteEdges {s(a, b)} = E.deleteEdges {s(a, b)} ⊔ intraEdges X := by
  ext u v
  simp only [deleteEdges_adj, sup_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h | h, hne⟩
    · exact Or.inl ⟨h, hne⟩
    · exact Or.inr h
  · rintro (⟨h, hne⟩ | h)
    · exact ⟨Or.inl h, hne⟩
    · refine ⟨Or.inr h, fun he => ?_⟩
      have hab' : (intraEdges X).Adj a b := by
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · exact h.symm
      exact not_intraEdges_adj_of_le hX hE hab hab'

open scoped Classical in
/-- Handshaking after grouping vertices into blocks. This counts inter-block edges
with their multiplicities, as in Lemma 4.37,
Section 4.10. -/
theorem sum_blockDegree_eq_twice_edges (hX : IsSubpartition X)
    (F : SimpleGraph (X.biUnion id)) :
    ∑ S : X, blockDegree X F S = 2 * F.edgeFinset.card := by
  have hfiber : ∀ S : X,
      (univ : Finset (X.biUnion id)).filter (fun i => blockOf hX i = S) = blockSet X S := by
    intro S
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_blockSet, blockOf_eq_iff hX]
  calc ∑ S : X, blockDegree X F S =
        ∑ S : X, ∑ i ∈ univ with blockOf hX i = S, F.degree i := by
          simp only [hfiber, blockDegree_eq_sum]
    _ = ∑ i, F.degree i := sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
    _ = 2 * F.edgeFinset.card := F.sum_degrees_eq_twice_card_edges

open scoped Classical in
/-- An even total degree and one odd block force a second odd block.
The proof first counts the odd blocks, exactly the handshaking step of
proof of Lemma 4.37. -/
theorem exists_second_odd_block {B : Type*} [Fintype B] (d : B → ℕ)
    (hsum : Even (∑ S, d S)) (A : B) (hA : Odd (d A)) :
    ∃ S, S ≠ A ∧ Odd (d S) := by
  have heven := (even_sum_iff_even_card_odd d).mp hsum
  have hpos : 0 < ((univ : Finset B).filter fun S => Odd (d S)).card :=
    card_pos.mpr ⟨A, mem_filter.mpr ⟨mem_univ _, hA⟩⟩
  have htwo : 1 < ((univ : Finset B).filter fun S => Odd (d S)).card := by
    rcases heven with ⟨k, hk⟩
    omega
  obtain ⟨S, hS, hne⟩ := exists_mem_ne htwo A
  exact ⟨S, hne, (mem_filter.mp hS).2⟩

open scoped Classical in
/-- No edge of an `E ∈ Eul^X` is a bridge of `(V_X, E ∪ ℰ^intra(X))`. -/
theorem not_isBridge_of_isRelEulerian (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (hE : IsRelEulerian X E) {a b : X.biUnion id} (hab : E.Adj a b) :
    ¬ (E ⊔ intraEdges X).IsBridge s(a, b) := by
  intro hbr
  set H := (E ⊔ intraEdges X).deleteEdges {s(a, b)} with hH
  have hnr : ¬ H.Reachable a b := isBridge_iff.1 hbr
  set C : Finset (X.biUnion id) := Finset.univ.filter fun v => H.Reachable a v with hCdef
  have hmemC : ∀ v, v ∈ C ↔ H.Reachable a v := fun v => by simp [hCdef]
  have haC : a ∈ C := (hmemC a).2 (Reachable.refl a)
  have hbC : b ∉ C := fun h => hnr ((hmemC b).1 h)
  -- an edge of `E` other than `ab` does not leave `C`
  have hclosed : ∀ u v, E.Adj u v → s(u, v) ≠ s(a, b) → (u ∈ C ↔ v ∈ C) := by
    intro u v huv hne
    have hHuv : H.Adj u v := by
      rw [hH, deleteEdges_adj]
      exact ⟨Or.inl huv, hne⟩
    rw [hmemC, hmemC]
    exact ⟨fun h => h.trans hHuv.reachable, fun h => h.trans hHuv.symm.reachable⟩
  -- `C` is a union of blocks
  have hsat : ∀ i ∈ C, ∀ j : X.biUnion id, blockOf hX i = blockOf hX j → j ∈ C := by
    intro i hi j hij
    by_cases hji : i = j
    · exact hji ▸ hi
    have hint : (intraEdges X).Adj i j := (intraEdges_adj hX).2 ⟨hji, hij⟩
    have hHij : H.Adj i j := by
      rw [hH, deleteEdges_adj]
      refine ⟨Or.inr hint, fun he => ?_⟩
      have hab' : (intraEdges X).Adj a b := by
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hint
        · exact hint.symm
      exact not_intraEdges_adj_of_le hX hE.1 hab hab'
    exact (hmemC j).2 (((hmemC i).1 hi).trans hHij.reachable)
  -- Keep the edges of the component after deleting the proposed bridge.
  let F : SimpleGraph (X.biUnion id) := {
    Adj := fun u v => (E.deleteEdges {s(a, b)}).Adj u v ∧ u ∈ C ∧ v ∈ C
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
    loopless := ⟨fun _ h => h.1.ne rfl⟩ }
  have hdeg_out : ∀ i, i ∉ C → F.degree i = 0 := by
    intro i hi
    rw [degree_eq_zero_iff_notMem_support, mem_support]
    rintro ⟨j, hij⟩
    exact hi hij.2.1
  have hdeg_a : F.degree a + 1 = E.degree a := by
    have hneigh : F.neighborFinset a = (E.neighborFinset a).erase b := by
      ext v
      simp only [mem_neighborFinset, mem_erase]
      constructor
      · rintro ⟨⟨hav, hne⟩, _, hv⟩
        exact ⟨fun hvb => hbC (hvb ▸ hv), hav⟩
      · rintro ⟨hvb, hav⟩
        have hne : s(a, v) ≠ s(a, b) := by
          intro he
          rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨h₁, h₂⟩
          · exact hvb h
          · exact hvb (h₂.trans h₁)
        exact ⟨deleteEdges_adj.mpr ⟨hav, hne⟩, haC, (hclosed a v hav hne).mp haC⟩
    rw [← card_neighborFinset_eq_degree, hneigh, card_erase_add_one (by simpa only [mem_neighborFinset] using hab),
      card_neighborFinset_eq_degree]
  have hdeg_other : ∀ i ∈ C, i ≠ a → F.degree i = E.degree i := by
    intro i hi hia
    have hneigh : F.neighborFinset i = E.neighborFinset i := by
      ext v
      simp only [mem_neighborFinset]
      constructor
      · exact fun h => h.1.1
      · intro hiv
        have hne : s(i, v) ≠ s(a, b) := by
          intro he
          rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
          · exact hia h
          · exact hbC (h ▸ hi)
        exact ⟨deleteEdges_adj.mpr ⟨hiv, hne⟩, hi, (hclosed i v hiv hne).mp hi⟩
    rw [← card_neighborFinset_eq_degree, hneigh, card_neighborFinset_eq_degree]
  let A : X := blockOf hX a
  have hA_sat : ∀ i ∈ blockSet X A, i ∈ C := by
    intro i hi
    exact hsat a haC i ((blockOf_eq_iff hX).mpr (mem_blockSet.mp hi)).symm
  have haA : a ∈ blockSet X A := mem_blockSet.mpr (mem_blockOf hX a)
  have hblock_a : blockDegree X E A = blockDegree X F A + 1 := by
    have hsum : (∑ i ∈ blockSet X A, E.degree i) =
        (∑ i ∈ blockSet X A, F.degree i) + 1 := by
      calc ∑ i ∈ blockSet X A, E.degree i =
            ∑ i ∈ blockSet X A, (F.degree i + if i = a then 1 else 0) := by
              refine sum_congr rfl fun i hi => ?_
              by_cases hia : i = a
              · subst i
                simpa only [ite_true] using hdeg_a.symm
              · rw [ite_eq_right hia, add_zero, hdeg_other i (hA_sat i hi) hia]
        _ = (∑ i ∈ blockSet X A, F.degree i) + 1 := by
            rw [sum_add_distrib]
            simp only [sum_ite_eq', ite_eq_left haA]
    simpa only [blockDegree_eq_sum, ← ncard_neighborSet] using hsum
  have hodd_a : Odd (blockDegree X F A) := by
    obtain ⟨k, hk⟩ := hE.2 A A.2
    rw [hblock_a] at hk
    exact Nat.odd_iff.mpr (by omega)
  -- The quotient component consists exactly of the blocks meeting `C`.
  let X' : Finset X := C.image (blockOf hX)
  have hAX' : A ∈ X' := mem_image.mpr ⟨a, haC, rfl⟩
  have hzero_outside : ∀ S : X, S ∉ X' → blockDegree X F S = 0 := by
    intro S hS
    rw [blockDegree_eq_sum]
    refine sum_eq_zero fun i hi => ?_
    have hiC : i ∉ C := fun h => hS
      (mem_image.mpr ⟨i, h, (blockOf_eq_iff hX).mpr (mem_blockSet.mp hi)⟩)
    simpa only [← ncard_neighborSet] using hdeg_out i hiC
  -- Handshaking on this component forces a second odd block in `X'`.
  have hhandshake : (∑ S ∈ X', blockDegree X F S) = 2 * F.edgeSet.ncard := by
    calc (∑ S ∈ X', blockDegree X F S) = ∑ S : X, blockDegree X F S :=
          sum_subset (subset_univ _) (fun S _ hS => hzero_outside S hS)
      _ = 2 * F.edgeSet.ncard := by
          simpa only [card_edgeFinset_eq_ncard] using sum_blockDegree_eq_twice_edges hX F
  have heven : Even (∑ S : X', blockDegree X F S) := by
    have hs : (∑ S : X', blockDegree X F S) = ∑ S ∈ X', blockDegree X F S :=
      sum_coe_sort X' (fun S : X => blockDegree X F S)
    rw [hs, hhandshake]
    exact ⟨F.edgeSet.ncard, by omega⟩
  obtain ⟨⟨S, hSX'⟩, hSA', hodd⟩ := exists_second_odd_block
    (fun S : X' => blockDegree X F S) heven ⟨A, hAX'⟩ hodd_a
  have hSA : S ≠ A := fun h => hSA' (Subtype.ext h)
  obtain ⟨i₀, hi₀C, hi₀S⟩ := mem_image.mp hSX'
  have hi₀ : i₀ ∈ blockSet X S := mem_blockSet.mpr ((blockOf_eq_iff hX).mp hi₀S)
  have hblock_S : blockDegree X F S = blockDegree X E S := by
    rw [blockDegree_eq_sum, blockDegree_eq_sum]
    refine sum_congr rfl fun i hi => ?_
    suffices h : i ∈ C ∧ i ≠ a by
      simpa only [← ncard_neighborSet] using hdeg_other i h.1 h.2
    constructor
    · apply hsat i₀ hi₀C i
      exact ((blockOf_eq_iff hX).mpr (mem_blockSet.mp hi₀)).trans
        ((blockOf_eq_iff hX).mpr (mem_blockSet.mp hi)).symm
    · intro hia
      apply hSA
      have := (blockOf_eq_iff hX).mpr (mem_blockSet.mp hi)
      simpa only [hia, A] using this.symm
  rw [hblock_S] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) (hE.2 S S.2)

/-- Definition 4.36(1) in the form stated by the paper ("this means that
`(V_X, E ∪ ℰ^intra(X))` has no bridge in `E`", Definition 4.36): `(V_X, E)` is 2-edge-connected relative
to `X` iff `E ∈ 𝖤^X` and no edge of `E` is a bridge of `(V_X, E ∪ ℰ^intra(X))`. -/
theorem isRelTwoEdgeConnected_iff (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)} :
    IsRelTwoEdgeConnected X E ↔
      IsRelConnected X E ∧ ∀ u v, E.Adj u v → ¬ (E ⊔ intraEdges X).IsBridge s(u, v) := by
  constructor
  · rintro ⟨hE, h⟩
    refine ⟨hE, fun u v huv hbr => ?_⟩
    have hc := (h u v huv).2.2
    rw [← sup_intraEdges_deleteEdges hX hE.1 huv] at hc
    exact isBridge_iff.1 hbr (hc.preconnected u v)
  · rintro ⟨hE, h⟩
    refine ⟨hE, fun u v huv => ?_⟩
    have hc : ((E ⊔ intraEdges X).deleteEdges {s(u, v)}).Connected :=
      hE.2.2.preconnected.connected_deleteEdges_of_not_isBridge (h u v huv)
    rw [sup_intraEdges_deleteEdges hX hE.1 huv] at hc
    refine ⟨(deleteEdges_le _).trans hE.1, ?_, hc⟩
    by_contra hne
    have hbot : E.deleteEdges {s(u, v)} = ⊥ := by
      rw [← edgeSet_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.1 hne
    rw [hbot, bot_sup_eq] at hc
    have hinter := interEdges_eq_bot_of_card_eq_one (card_eq_one_of_connected_intraEdges hX hc)
    have huv' := hE.1 huv
    rw [hinter] at huv'
    exact huv'

/-- **Lemma 4.37 in the paper's set-membership notation** (Lemma 4.37). -/
theorem lemma_4_37_of_mem (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (hE : E ∈ relEulerianConnected X) : IsRelTwoEdgeConnected X E := by
  have h := mem_relEulerianConnected.mp hE
  exact (isRelTwoEdgeConnected_iff hX).2
    ⟨h.1, fun _ _ huv => not_isBridge_of_isRelEulerian hX h.2 huv⟩

/-- **Lemma 4.37**: if `E ∈ Eulc^X`, then `(V_X, E)` is
2-edge-connected relative to `X`. -/
theorem lemma_4_37 (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (hE : IsRelEulerianConnected X E) : IsRelTwoEdgeConnected X E :=
  lemma_4_37_of_mem hX (mem_relEulerianConnected.mpr hE)

end Delete

/-! ### Eulerian relative to a family of groups of blocks -/

section Groups

variable {X : Finset (Finset ℕ)}

open scoped Classical in
/-- If no edge of `E₁` meets the block `S ∈ X`, then `deg_{E₁}(S) = 0`. -/
theorem blockDegree_eq_zero {E₁ : SimpleGraph (X.biUnion id)} {S : Finset ℕ}
    (h : ∀ i j : X.biUnion id, E₁.Adj i j → (i : ℕ) ∉ S) : blockDegree X E₁ S = 0 := by
  rw [blockDegree_eq_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [degree_eq_zero_iff_notMem_support, mem_support]
  rintro ⟨j, hij⟩
  exact h i j hij (mem_blockSet.1 hi)

/-- **The Eulerian condition of (4.61), group by group.** Let `G` be a family of groups of
blocks of `X` (in (4.61): `{X₁, …, Xₙ}`) and let every vertex incident to an edge of `E₁` lie in
a block of some group (in (4.61): `E₁ = E_{1,1} ∪ ⋯ ∪ E_{n,1}` with `E_{l,1} ⊆ ℰ^inter(X_l)`).
Then `E₁ ∈ Eul^X` iff `deg_{E₁}(S)` is even for every block `S` of every group, i.e. iff each
`E_{l,1}` is Eulerian relative to `X_l` (an edge of `E_{m,1}`, `m ≠ l`, meets no block of `X_l`
when the groups are disjoint). -/
theorem isRelEulerian_iff_forall_group (hX : IsSubpartition X)
    {G : Finset (Finset (Finset ℕ))} (hGX : ∀ Y ∈ G, Y ⊆ X) {E₁ : SimpleGraph (X.biUnion id)}
    (hE₁ : E₁ ≤ interEdges X)
    (hcov : ∀ i j : X.biUnion id, E₁.Adj i j → ∃ Y ∈ G, ∃ S ∈ Y, (i : ℕ) ∈ S) :
    IsRelEulerian X E₁ ↔ ∀ Y ∈ G, ∀ S ∈ Y, Even (blockDegree X E₁ S) := by
  constructor
  · exact fun h Y hY S hS => h.2 S (hGX Y hY hS)
  · intro h
    refine ⟨hE₁, fun S hS => ?_⟩
    by_cases hSG : ∃ Y ∈ G, S ∈ Y
    · obtain ⟨Y, hY, hSY⟩ := hSG
      exact h Y hY S hSY
    · rw [blockDegree_eq_zero fun i j hij hiS => ?_]
      · exact ⟨0, rfl⟩
      obtain ⟨Y, hY, S', hS', hiS'⟩ := hcov i j hij
      have hSS' : S' = S := by
        by_contra hne
        exact Finset.disjoint_left.1
          (hX.2 (Finset.mem_coe.2 (hGX Y hY hS')) (Finset.mem_coe.2 hS) hne) hiS' hiS
      exact hSG ⟨Y, hY, hSS' ▸ hS'⟩

end Groups

end Parity

end MultipoleBKT

end
