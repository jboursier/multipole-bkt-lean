/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.CoreForest.Skeleton
public import MultipoleBKT.LowerBound.Peeling.Quadratic

/-!
# Peeling the bridge-blocks of the 2-core (Definition 5.29) and eq. (5.85)

The paper: Definition 5.29 and
eq. (5.85) in the proof of Lemma 5.33, re-invoked for every nontrivial block in the
proof of Corollary 5.34 ((5.85)).

Definition 5.29 applies the peeling of Definition 4.43 (`MultipoleBKT.Peeling.IsPeelingOn`) to each bridge-block `G_l` of the 2-core of a minimal skeleton, relative to its blocks
`X_l = {S ∈ X : S ⊆ V(G_l)}`, "the weights `g_ij` being defined separately on each bridge-block".
The peeling of Definition 4.43 is stated for a graph on a whole vertex type whose block map is onto, so
a bridge-block is first restricted to its own vertex type: for a predicate `P` on `V` (here
`P v ↔ v ∈ G_l`), `blockOn b P` is the block map of the vertices of `P` onto the blocks they meet,
and `K.comap Subtype.val` is a graph `K` of `V` read on these vertices.

* `minTwoEdgeConnOn_of_isBlockSkeleton`: an admissible skeleton `G_l'` of a bridge-block
  (Definition 5.28) is minimally 2-edge-connected relative to the blocks of `G_l`;
* `IsBlockPeeling b E l K r d v₁ e₀ T F`: `T = 𝒯^{X_l}(·, K)`, `F = 𝓕^{X_l}(·, K)` are the kept and
  discarded edges of an admissible peeling of `K` (read back in `V`), started at `v₁` (a vertex of
  maximal radius of `G_l`) with longest edge `e₀`; the choices are not fixed and
  the results hold for every admissible choice;
* `exists_isBlockPeeling`: the peeling exists for every block with at least two parts;
* `IsBlockPeeling.sup_eq`, `IsBlockPeeling.disjoint`: `K = T ⊔ F`, `T ∩ F = ∅`;
* `IsBlockPeeling.prod_absWeight_le`: **eq. (5.85)** for the abstract peeling weights, with
  constant `1`: `∏_{ij ∈ K} a^abs_ij ≤ ∏_{S ∈ X_l, S ≠ [v₁]} ρ_S² ∏_{ij ∈ T} d_ij^{-2} c_ij
  ∏_{ij ∈ F} g_ij` (Corollary 4.47 on the block). The paper's form follows from
  `|a^{v^Z}_ij 1_{𝓑_ij^c}| ≤ C a^abs_ij` (eq. (5.73), proved in
  `MultipoleBKT.UpperBound.BoundedUpper.bornesabZ_Z`) and the sum over `B(·, T)` (a weakening, see
  `MultipoleBKT.Peeling.quadratic_estimate`);
* `IsPlusPeeling b E Ks r d v₁ e₀ Ts Fs`, `plusTree b E Ts`: **Definition 5.29** blockwise, for the
  minimal skeleton given by block skeletons `Ks` (Definition 5.28): `𝒯_+^X = ⋃_l Ts l ∪ ⋃ E(P_i) ∪ ℰ_br`,
  `𝓕_+^X = ⋃_l Fs l`, with empty extracted sets on one-part blocks; `exists_isPlusPeeling` and
  `IsPlusPeeling.plusTree_sup` (`Peeled_X(E) = 𝒯_+^X ∪ 𝓕_+^X`).

Not treated in this file (both are proved in `MultipoleBKT.UpperBound.Quadratic`): the claim
`𝒯_+^X ∈ 𝖳^X`, which is `MultipoleBKT.UpperBound.Quadratic.isRelTree_plusTree`,
and the identification of the bridge-blocks of the core of `Peeled_X(E)` with those of `E`.
Definition 5.29 applies the peeling to the blocks of `Peeled_X(E)`, here it is applied to the
skeletons `Ks l` of the blocks of `E`. The two agree when `E` is a minimal skeleton
(`Peeled_X(E) = E`, the hypothesis of Lemma 5.33; then `Ks l = G_l`,
`MultipoleBKT.CoreForest.isMinimalSkeleton_self_iff`). That `Peeled_X(E_0)` is itself a minimal
skeleton, which Corollary 5.34 uses tacitly, is
`MultipoleBKT.UpperBound.Quadratic.isMinimalSkeleton_self_of_isMinimalSkeleton`, with the
identification of the bridge-blocks in
`MultipoleBKT.UpperBound.Quadratic.blockInnerEdges_eq_of_isMinimalSkeleton`.
-/

@[expose] public section

namespace MultipoleBKT

namespace CoreForest

open Finset SimpleGraph Peeling

/-! ### Restriction to a set of vertices -/

section Restrict

variable {V β : Type*} (b : V → β) (P : V → Prop)

/-- The blocks met by the vertices satisfying `P`. -/
abbrev PartsOn : Type _ := {S : β // ∃ w : {v // P v}, b w.1 = S}

/-- The block map of the vertices satisfying `P` onto the blocks they meet. -/
def blockOn (w : {v // P v}) : PartsOn b P := ⟨b w.1, w, rfl⟩

variable {b P}

theorem blockOn_surjective : Function.Surjective (blockOn b P) := by
  rintro ⟨S, w, rfl⟩
  exact ⟨w, rfl⟩

theorem blockOn_eq_iff {w w' : {v // P v}} : blockOn b P w = blockOn b P w' ↔ b w.1 = b w'.1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem comap_le_crossBlockGraph {K : SimpleGraph V} (hK : K ≤ crossBlockGraph b) :
    K.comap Subtype.val ≤ crossBlockGraph (blockOn b P) := fun _ _ h =>
  crossBlockGraph_adj.2 fun h' => crossBlockGraph_adj.1 (hK h) (blockOn_eq_iff.1 h')

/-- Reachability inside `P` is reachability of the restricted graph, when the edges of `K` and the
same-block edges do not leave `P`. -/
theorem reachable_comap {K : SimpleGraph V} (hK : ∀ u v, K.Adj u v → P u → P v)
    (hP : ∀ u v, b u = b v → P u → P v) {x y : V} (h : (K ⊔ sameBlockGraph b).Reachable x y)
    (hx : P x) (hy : P y) :
    (K.comap Subtype.val ⊔ sameBlockGraph (blockOn b P)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z y hxz q ih =>
    have hz : P z := by
      rcases hxz with h' | h'
      · exact hK x z h' hx
      · exact hP x z (sameBlockGraph_adj.1 h').2 hx
    refine Adj.reachable ?_ |>.trans (ih hz hy)
    rcases hxz with h' | h'
    · exact Or.inl h'
    · obtain ⟨hne, hb⟩ := sameBlockGraph_adj.1 h'
      exact Or.inr (sameBlockGraph_adj.2 ⟨fun he => hne (congrArg Subtype.val he),
        blockOn_eq_iff.2 hb⟩)

/-- Reachability in the restricted graph gives reachability in `V`. -/
theorem reachable_of_reachable_comap {K : SimpleGraph V} {w w' : {v // P v}}
    (h : (K.comap Subtype.val ⊔ sameBlockGraph (blockOn b P)).Reachable w w') :
    (K ⊔ sameBlockGraph b).Reachable w.1 w'.1 := by
  refine reachable_comp_of_forall_adj Subtype.val (fun u v huv => Adj.reachable ?_) h
  rcases huv with h' | h'
  · exact Or.inl h'
  · obtain ⟨hne, hb⟩ := sameBlockGraph_adj.1 h'
    exact Or.inr (sameBlockGraph_adj.2 ⟨fun he => hne (Subtype.ext he), blockOn_eq_iff.1 hb⟩)

theorem comap_deleteEdges (K : SimpleGraph V) (a c : {v // P v}) :
    (K.deleteEdges {s(a.1, c.1)}).comap Subtype.val =
      (K.comap Subtype.val).deleteEdges {s(a, c)} := by
  ext u v
  simp only [comap_adj, deleteEdges_adj, Set.mem_singleton_iff]
  refine and_congr_right fun _ => not_congr ?_
  constructor
  · intro h
    exact Sym2.map.injective Subtype.val_injective (by rw [Sym2.map_mk, Sym2.map_mk]; exact h)
  · intro h
    simpa [Sym2.map_mk] using congrArg (Sym2.map Subtype.val) h

/-- A graph of `V` whose edges lie in `P` is the image of its restriction. -/
theorem map_comap_eq {K : SimpleGraph V} (hK : ∀ u v, K.Adj u v → P u ∧ P v) :
    (K.comap Subtype.val).map (Function.Embedding.subtype P) = K := by
  ext u v
  rw [map_adj]
  constructor
  · rintro ⟨u', v', h, rfl, rfl⟩
    exact h
  · intro h
    exact ⟨⟨u, (hK u v h).1⟩, ⟨v, (hK u v h).2⟩, h, rfl, rfl⟩

end Restrict

/-! ### The bridge-blocks of the core -/

section Block

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] {b : V → β} {E : SimpleGraph V}

/-- The vertices of the bridge-block `l` of the 2-core. -/
abbrev InBlock (b : V → β) (E : SimpleGraph V)
    (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) (v : V) : Prop :=
  bridgeBlock b (coreEdges b E) v = l

open scoped Classical in
/-- The blocks `X_l` of the bridge-block `l` of the 2-core. -/
noncomputable def blockParts (b : V → β) (E : SimpleGraph V)
    (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) : Finset β :=
  univ.filter fun S => ∃ v, bridgeBlock b (coreEdges b E) v = l ∧ b v = S

theorem mem_blockParts {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent} {S : β} :
    S ∈ blockParts b E l ↔ ∃ v, bridgeBlock b (coreEdges b E) v = l ∧ b v = S := by
  classical
  simp [blockParts]

theorem IsBlockSkeleton.adj_inBlock {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent}
    {K : SimpleGraph V} (hK : IsBlockSkeleton b E l K) {u v : V} (huv : K.Adj u v) :
    InBlock b E l u ∧ InBlock b E l v := by
  obtain ⟨hc, hnb, hu⟩ := blockInnerEdges_adj.1 (hK.1 huv)
  exact ⟨hu, (bridgeBlock_eq_of_adj_of_not_relBridges hc hnb).symm.trans hu⟩

theorem inBlock_of_eq {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent} {u v : V}
    (h : b u = b v) (hu : InBlock b E l u) : InBlock b E l v :=
  (bridgeBlock_eq_of_eq h).symm.trans hu

/-- **An admissible skeleton `G_l'` of a bridge-block is minimally 2-edge-connected relative to the
blocks of `G_l`.** -/
theorem minTwoEdgeConnOn_of_isBlockSkeleton
    {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent} {K : SimpleGraph V}
    (hK : IsBlockSkeleton b E l K) (hl : ∃ v, InBlock b E l v) :
    MinTwoEdgeConnOn (blockOn b (InBlock b E l)) (K.comap Subtype.val) := by
  have hKP : ∀ {K' : SimpleGraph V}, K' ≤ K → ∀ u v, K'.Adj u v → InBlock b E l u →
      InBlock b E l v := fun hle u v huv _ => (hK.adj_inBlock (hle huv)).2
  have hP : ∀ u v, b u = b v → InBlock b E l u → InBlock b E l v :=
    fun _ _ h hu => inBlock_of_eq h hu
  obtain ⟨v₀, hv₀⟩ := hl
  have hne : Nonempty {v // InBlock b E l v} := ⟨⟨v₀, hv₀⟩⟩
  refine ⟨⟨⟨fun w w' => ?_⟩, fun e he => ?_⟩, fun e he h2 => ?_⟩
  · exact reachable_comap (hKP le_rfl) hP (hK.2.1.1 w.1 w'.1 w.2 w'.2) w.2 w'.2
  · induction e using Sym2.ind with
    | _ a c =>
      have hac : K.Adj a.1 c.1 := he
      refine ⟨fun w w' => ?_⟩
      rw [← comap_deleteEdges]
      exact reachable_comap (hKP (deleteEdges_le _)) hP
        (hK.2.1.2 a.1 c.1 hac w.1 w'.1 w.2 w'.2) w.2 w'.2
  · induction e using Sym2.ind with
    | _ a c =>
      have hac : K.Adj a.1 c.1 := he
      set K₀ := K.deleteEdges {s(a.1, c.1)} with hK₀
      have h2' : TwoEdgeConnectsBlock b E l K₀ := by
        refine ⟨fun x y hx hy => ?_, fun a' c' hac' x y hx hy => ?_⟩
        · have := h2.1.preconnected ⟨x, hx⟩ ⟨y, hy⟩
          rw [← comap_deleteEdges] at this
          exact reachable_of_reachable_comap this
        · have ha' := (hK.adj_inBlock ((deleteEdges_le _) hac')).1
          have hc' := (hK.adj_inBlock ((deleteEdges_le _) hac')).2
          have hmem : s((⟨a', ha'⟩ : {v // InBlock b E l v}), ⟨c', hc'⟩) ∈
              ((K.comap Subtype.val).deleteEdges {s(a, c)}).edgeSet := by
            rw [← comap_deleteEdges]
            exact hac'
          have := (h2.2 _ hmem).preconnected ⟨x, hx⟩ ⟨y, hy⟩
          rw [← comap_deleteEdges, ← comap_deleteEdges] at this
          exact reachable_of_reachable_comap this
      have heq := hK.2.2 K₀ (deleteEdges_le _) h2'
      have : K₀.Adj a.1 c.1 := heq ▸ hac
      rw [hK₀, deleteEdges_adj] at this
      exact this.2 rfl

variable [DecidableEq V]

open scoped Classical in
/-- `T = 𝒯^{X_l}(·, K)`, `F = 𝓕^{X_l}(·, K)` (Definition 5.29): the kept and discarded edges of an
admissible peeling (Definition 4.43, `MultipoleBKT.Peeling.IsPeelingOn`) of the skeleton `K` of the
bridge-block `l`, restricted to the vertices of `l` and read back in `V`; `v₁` is the start vertex
(of maximal radius in `l`) and `e₀` the longest edge of `K`. -/
def IsBlockPeeling (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent)
    (K : SimpleGraph V) (r : V → ℝ) (d : Sym2 V → ℝ) (v₁ : V) (e₀ : Sym2 V)
    (T F : SimpleGraph V) : Prop :=
  ∃ (w₁ : {v // InBlock b E l v}) (e₀' : Sym2 {v // InBlock b E l v})
    (Qs : List (Ear {v // InBlock b E l v} × ({v // InBlock b E l v} × {v // InBlock b E l v}))),
    IsPeelingOn (blockOn b (InBlock b E l)) (K.comap Subtype.val) (fun w => r w.1)
        (fun e => d (e.map Subtype.val)) w₁ e₀' Qs ∧
      w₁.1 = v₁ ∧ e₀'.map Subtype.val = e₀ ∧
      T = (keptGraph (K.comap Subtype.val) Qs).map (Function.Embedding.subtype _) ∧
      F = (removedGraph Qs).map (Function.Embedding.subtype _)

open scoped Classical in
/-- **The peeling of a bridge-block exists** (Definition 5.29 is well defined) for every block with at
least two parts. -/
theorem exists_isBlockPeeling (hE : E ≤ crossBlockGraph b)
    {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent} {K : SimpleGraph V}
    (hK : IsBlockSkeleton b E l K) (h2 : (blockParts b E l).card ≠ 1) (r : V → ℝ)
    (d : Sym2 V → ℝ) : ∃ v₁ e₀ T F, IsBlockPeeling (b := b) (E := E) l K r d v₁ e₀ T F := by
  have hl : ∃ v, InBlock b E l v := by
    obtain ⟨v, hv⟩ := Quot.exists_rep l
    exact ⟨v, hv⟩
  have hcard : Fintype.card (PartsOn b (InBlock b E l)) ≠ 1 := by
    rw [Fintype.card_subtype]
    convert h2 using 2
    ext S
    rw [Finset.mem_filter, mem_blockParts]
    exact ⟨fun ⟨_, w, hw⟩ => ⟨w.1, w.2, hw⟩, fun ⟨v, hv, hvS⟩ => ⟨Finset.mem_univ _, ⟨v, hv⟩, hvS⟩⟩
  have hcross : K.comap Subtype.val ≤ crossBlockGraph (blockOn b (InBlock b E l)) :=
    comap_le_crossBlockGraph fun _ _ h => hE (coreEdges_le (blockInnerEdges_adj.1 (hK.1 h)).1)
  obtain ⟨w₁, e₀', Qs, h⟩ := exists_isPeelingOn blockOn_surjective hcross
    (minTwoEdgeConnOn_of_isBlockSkeleton hK hl) hcard (fun w => r w.1)
    (fun e => d (e.map Subtype.val))
  exact ⟨w₁.1, e₀'.map Subtype.val, _, _, w₁, e₀', Qs, h, rfl, rfl, rfl, rfl⟩

variable {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent} {K : SimpleGraph V}
  {r : V → ℝ} {d : Sym2 V → ℝ} {v₁ : V} {e₀ : Sym2 V} {T F : SimpleGraph V}

omit [DecidableEq V] in
/-- `K = 𝒯^{X_l} ∪ 𝓕^{X_l}`. -/
theorem IsBlockPeeling.sup_eq (hK : IsBlockSkeleton b E l K)
    (h : IsBlockPeeling (b := b) (E := E) l K r d v₁ e₀ T F) : T ⊔ F = K := by
  classical
  obtain ⟨w₁, e₀', Qs, hp, -, -, rfl, rfl⟩ := h
  conv_rhs => rw [← map_comap_eq (P := InBlock b E l) fun u v h => hK.adj_inBlock h,
    ← hp.keptGraph_sup_removedGraph]
  ext u v
  simp only [sup_adj, map_adj]
  constructor
  · rintro (⟨u', v', h', rfl, rfl⟩ | ⟨u', v', h', rfl, rfl⟩)
    · exact ⟨u', v', Or.inl h', rfl, rfl⟩
    · exact ⟨u', v', Or.inr h', rfl, rfl⟩
  · rintro ⟨u', v', h' | h', rfl, rfl⟩
    · exact Or.inl ⟨u', v', h', rfl, rfl⟩
    · exact Or.inr ⟨u', v', h', rfl, rfl⟩

omit [DecidableEq V] in
/-- `𝒯^{X_l} ∩ 𝓕^{X_l} = ∅`. -/
theorem IsBlockPeeling.disjoint (h : IsBlockPeeling (b := b) (E := E) l K r d v₁ e₀ T F) :
    Disjoint T F := by
  obtain ⟨w₁, e₀', Qs, -, -, -, rfl, rfl⟩ := h
  rw [disjoint_iff_inf_le]
  intro u v huv
  rw [inf_adj, map_adj, map_adj] at huv
  obtain ⟨⟨u', v', h₁, rfl, rfl⟩, ⟨u'', v'', h₂, hu, hv⟩⟩ := huv
  obtain rfl : u'' = u' := Subtype.ext hu
  obtain rfl : v'' = v' := Subtype.ext hv
  exact (disjoint_keptGraph_removedGraph _ Qs).le_bot ⟨h₁, h₂⟩

omit [Fintype V] [DecidableEq V] in
/-- Products over the edges of a graph read back from a set of vertices. -/
theorem prod_edgeFinset_map {W : Type*} [Fintype W] (f : W ↪ V) (H : SimpleGraph W)
    [DecidableRel H.Adj] [Fintype (H.map f).edgeSet] (g : Sym2 V → ℝ) :
    ∏ e ∈ (H.map f).edgeFinset, g e = ∏ e ∈ H.edgeFinset, g (e.map f) := by
  have : (H.map f).edgeFinset = H.edgeFinset.map f.sym2Map := by
    ext e
    rw [mem_edgeFinset, edgeSet_map, Finset.mem_map]
    simp only [Set.mem_image, mem_edgeFinset]
  rw [this, Finset.prod_map]
  rfl

omit [Fintype V] [Fintype β] [DecidableEq β] [DecidableEq V] in
theorem absWeight_map {W : Type*} (f : W → V) (r : V → ℝ) (d c : Sym2 V → ℝ) (e : Sym2 W) :
    absWeight r d c (e.map f) =
      absWeight (fun w => r (f w)) (fun e => d (e.map f)) (fun e => c (e.map f)) e := by
  induction e using Sym2.ind with
  | _ a a' => rfl

omit [Fintype V] [Fintype β] [DecidableEq β] in
theorem peelWeight_map {W : Type*} [DecidableEq W] {f : W → V} (hf : Function.Injective f)
    (r : V → ℝ) (d c : Sym2 V → ℝ) (R : ℝ) (e₀ e : Sym2 W) :
    peelWeight r d c R (e₀.map f) (e.map f) =
      peelWeight (fun w => r (f w)) (fun e => d (e.map f)) (fun e => c (e.map f)) R e₀ e := by
  have hrad : radMax r (e.map f) = radMax (fun w => r (f w)) e := by
    induction e using Sym2.ind with
    | _ a a' => rfl
  have heq : e.map f = e₀.map f ↔ e = e₀ := (Sym2.map.injective hf).eq_iff
  simp only [peelWeight, hrad, heq]

open scoped Classical in
/-- **Eq. (5.85)** (proof of Lemma 5.33, Corollary 5.34), for the abstract
weights `a^abs` and with constant `1`: for an admissible peeling of the skeleton `K`
of a bridge-block `l` of the core and radii bounded by block radii `ρ`,
`∏_{ij ∈ K} a^abs_ij ≤ ∏_{S ∈ X_l, S ≠ [v₁]} ρ_S² ∏_{ij ∈ 𝒯} d_ij^{-2} c_ij ∏_{ij ∈ 𝓕} g_ij`, the
weights `g_ij` being those of the block (`R = r_{v₁}`, longest edge `e₀`). -/
theorem IsBlockPeeling.prod_absWeight_le (hK : IsBlockSkeleton b E l K) {c : Sym2 V → ℝ}
    (h : IsBlockPeeling (b := b) (E := E) l K r d v₁ e₀ T F) (hr : ∀ v, 0 ≤ r v)
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (ρ : β → ℝ) (hrρ : ∀ v, r v ≤ ρ (b v)) :
    ∏ e ∈ K.edgeFinset, absWeight r d c e ≤
      (∏ S ∈ (blockParts b E l).erase (b v₁), ρ S ^ 2) *
        (∏ e ∈ T.edgeFinset, keptWeight d c e) *
          ∏ e ∈ F.edgeFinset, peelWeight r d c (r v₁) e₀ e := by
  obtain ⟨w₁, e₀', Qs, hp, rfl, rfl, rfl, rfl⟩ := h
  have key := hp.prod_absWeight_le (c := fun e => c (e.map Subtype.val)) (fun w => hr w.1)
    (fun e => hd _) (fun e => hc _) (fun S => ρ S.1) (fun w => hrρ w.1)
  have hKeq : K = (K.comap Subtype.val).map (Function.Embedding.subtype (InBlock b E l)) :=
    (map_comap_eq fun u v h => hK.adj_inBlock h).symm
  have hparts : (Finset.univ.erase (blockOn b (InBlock b E l) w₁)).map
      (Function.Embedding.subtype _) = (blockParts b E l).erase (b w₁.1) := by
    ext S
    rw [Finset.mem_map, Finset.mem_erase, mem_blockParts]
    constructor
    · rintro ⟨⟨S, w, hw⟩, hS', rfl⟩
      rw [Finset.mem_erase] at hS'
      exact ⟨fun h' => hS'.1 (Subtype.ext h'), w.1, w.2, hw⟩
    · rintro ⟨hne, v, hv, rfl⟩
      exact ⟨blockOn b _ ⟨v, hv⟩, Finset.mem_erase.2 ⟨fun h' => hne (congrArg Subtype.val h'),
        Finset.mem_univ _⟩, rfl⟩
  calc ∏ e ∈ K.edgeFinset, absWeight r d c e
      = ∏ e ∈ (K.comap Subtype.val).edgeFinset, absWeight (fun w => r w.1)
          (fun e => d (e.map Subtype.val)) (fun e => c (e.map Subtype.val)) e := by
        conv_lhs => rw [hKeq]
        rw [prod_edgeFinset_map]
        exact Finset.prod_congr rfl fun e _ => absWeight_map _ _ _ _ e
    _ ≤ _ := key
    _ = _ := by
        rw [prod_edgeFinset_map, prod_edgeFinset_map, ← hparts, Finset.prod_map]
        refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun e _ => ?_)
        exact (peelWeight_map Subtype.val_injective r d c _ e₀' e).symm

end Block

/-! ### Definition 5.29 -/

section Plus

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] [DecidableEq V] (b : V → β)
  (E : SimpleGraph V)

/-- `(𝒯_+^X(·, E'), 𝓕_+^X(·, E'))` for the minimal skeleton `E' = ⋃_l Ks l ∪ ⋃_i E(P_i) ∪ ℰ_br` of `E`
given by the block skeletons `Ks l = G_l'` (Definitions 5.28–5.29, Definition 5.29), blockwise:
for every bridge-block `l` of the 2-core of `E` with at least two parts, `Ts l`, `Fs l` are the kept
and discarded edges of an admissible peeling of `G_l'` started at `v₁ l` with longest edge `e₀ l`
(the weights `g_ij` are defined separately on each block); for a block consisting of one part,
both extracted edge sets are empty. When `E` is itself a minimal skeleton, `Ks l` is the bridge-block
`G_l` (`blockInnerEdges b E l`). -/
def IsPlusPeeling (Ks : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V)
    (r : V → ℝ) (d : Sym2 V → ℝ)
    (v₁ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → V)
    (e₀ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → Sym2 V)
    (Ts Fs : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V) : Prop :=
  ∀ l, ((blockParts b E l).card ≠ 1 →
      IsBlockPeeling (b := b) (E := E) l (Ks l) r d (v₁ l) (e₀ l) (Ts l) (Fs l)) ∧
    ((blockParts b E l).card = 1 → Ts l = ⊥ ∧ Fs l = ⊥)

/-- `𝒯_+^X = ⋃_l 𝒯^{X_l}(·, G_l') ∪ ⋃_i E(P_i) ∪ ℰ_br` (Definition 5.29). -/
def plusTree (Ts : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V) :
    SimpleGraph V :=
  (⨆ l, Ts l) ⊔ pendantEdges b E ⊔ relBridges b (coreEdges b E)

variable {b E}

omit [DecidableEq V] in
/-- A block with one part has no inner edge. -/
theorem blockInnerEdges_eq_bot_of_card_eq_one (hE : E ≤ crossBlockGraph b)
    {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent}
    (h1 : (blockParts b E l).card = 1) : blockInnerEdges b E l = ⊥ := by
  ext u v
  simp only [bot_adj, iff_false]
  intro huv
  obtain ⟨hc, hnb, hu⟩ := blockInnerEdges_adj.1 huv
  have hv : bridgeBlock b (coreEdges b E) v = l :=
    (bridgeBlock_eq_of_adj_of_not_relBridges hc hnb).symm.trans hu
  obtain ⟨S, hS⟩ := Finset.card_eq_one.1 h1
  have hbu : b u ∈ blockParts b E l := mem_blockParts.2 ⟨u, hu, rfl⟩
  have hbv : b v ∈ blockParts b E l := mem_blockParts.2 ⟨v, hv, rfl⟩
  rw [hS, Finset.mem_singleton] at hbu hbv
  exact crossBlockGraph_adj.1 (hE (coreEdges_le hc)) (hbu.trans hbv.symm)

/-- **The peeling of Definition 5.29 exists** for every choice of block skeletons. -/
theorem exists_isPlusPeeling (hE : E ≤ crossBlockGraph b)
    {Ks : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V}
    (hKs : ∀ l, IsBlockSkeleton b E l (Ks l)) (r : V → ℝ) (d : Sym2 V → ℝ) :
    ∃ v₁ e₀ Ts Fs, IsPlusPeeling b E Ks r d v₁ e₀ Ts Fs := by
  have hex : ∀ l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent, ∃ (v : V) (e : Sym2 V)
      (T F : SimpleGraph V), ((blockParts b E l).card ≠ 1 →
        IsBlockPeeling (b := b) (E := E) l (Ks l) r d v e T F) ∧
        ((blockParts b E l).card = 1 → T = ⊥ ∧ F = ⊥) := by
    intro l
    by_cases h1 : (blockParts b E l).card = 1
    · obtain ⟨v, -⟩ := Quot.exists_rep l
      exact ⟨v, s(v, v), ⊥, ⊥, fun h => absurd h1 h, fun _ => ⟨rfl, rfl⟩⟩
    · obtain ⟨v, e, T, F, h⟩ := exists_isBlockPeeling hE (hKs l) h1 r d
      exact ⟨v, e, T, F, fun _ => h, fun h => absurd h h1⟩
  choose v₁ e₀ Ts Fs hTF using hex
  exact ⟨v₁, e₀, Ts, Fs, hTF⟩

omit [DecidableEq V] in
/-- `Peeled_X(E) = 𝒯_+^X ∪ 𝓕_+^X`: the kept and discarded edges of the blocks, the pendant trees and
the bridges of the core make up the minimal skeleton. -/
theorem IsPlusPeeling.plusTree_sup (hE : E ≤ crossBlockGraph b)
    {Ks : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V}
    (hKs : ∀ l, IsBlockSkeleton b E l (Ks l)) {r : V → ℝ} {d : Sym2 V → ℝ}
    {v₁ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → V}
    {e₀ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → Sym2 V}
    {Ts Fs : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V}
    (h : IsPlusPeeling b E Ks r d v₁ e₀ Ts Fs) :
    plusTree b E Ts ⊔ (⨆ l, Fs l) =
      (⨆ l, Ks l) ⊔ pendantEdges b E ⊔ relBridges b (coreEdges b E) := by
  have hTF : ∀ l, Ts l ⊔ Fs l = Ks l := by
    intro l
    by_cases h1 : (blockParts b E l).card = 1
    · have hKb : Ks l = ⊥ :=
        le_bot_iff.1 ((hKs l).1.trans (blockInnerEdges_eq_bot_of_card_eq_one hE h1).le)
      rw [(h l).2 h1 |>.1, (h l).2 h1 |>.2, hKb, sup_bot_eq]
    · exact ((h l).1 h1).sup_eq (hKs l)
  ext u v
  simp only [plusTree, sup_adj, iSup_adj]
  constructor
  · rintro (((⟨l, hl⟩ | hp) | hb) | ⟨l, hl⟩)
    · exact Or.inl (Or.inl ⟨l, hTF l ▸ Or.inl hl⟩)
    · exact Or.inl (Or.inr hp)
    · exact Or.inr hb
    · exact Or.inl (Or.inl ⟨l, hTF l ▸ Or.inr hl⟩)
  · rintro ((⟨l, hl⟩ | hp) | hb)
    · rw [← hTF l] at hl
      rcases hl with hT | hF
      · exact Or.inl (Or.inl (Or.inl ⟨l, hT⟩))
      · exact Or.inr ⟨l, hF⟩
    · exact Or.inl (Or.inl (Or.inr hp))
    · exact Or.inl (Or.inr hb)

end Plus

end CoreForest

end MultipoleBKT

end
