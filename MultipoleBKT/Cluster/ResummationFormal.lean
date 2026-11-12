/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.Ursell
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Connected-cluster resummation: the combinatorial recursion

This file proves the combinatorial core of Lemma 4.7: the coefficient recursion behind the identity
`exp (∑ connected clusters) = ∑ disjoint families`, i.e. the derivative form `Z' = F' Z` of
the exponential formula, with the Ursell function `MultipoleBKT.ursell` (Definition 2.4).

Fix a finite type `C` of polymers, a relation `R` on `C` and an activity `K : C → ℝ`. For a
tuple `X : ι → C`, `relGraph R X` is its connection graph (`i ~ j` iff `i ≠ j` and `X i`, `X j`
are related). Write

* `disjointSum R K ι = ∑_{X : ι → C, relGraph R X = ⊥} ∏ᵢ K (X i)`,
* `clusterSum R K ι = ∑_{X : ι → C} (∏ᵢ K (X i)) I(relGraph R X)`.

Main results:

* `MultipoleBKT.Resummation.ite_eq_bot_eq_sum`: for a finite graph `G` and a vertex `v`,
  `𝟙[G = ⊥] = ∑_{T ∋ v} I(G[T]) 𝟙[G has no edge outside T]`. This is the expansion of
  `∏_{ij ∈ E(G)} (1 - 1)` over spanning subgraphs, grouped by the component of `v`.
* `MultipoleBKT.Resummation.disjointSum_succ`: the recursion
  `D_{n+1} = ∑_{k ≤ n} C(n, k) A_{k+1} D_{n-k}` for `D_m = disjointSum R K (Fin m)` and
  `A_m = clusterSum R K (Fin m)`;
* `MultipoleBKT.Resummation.succ_mul_disjointCoeff_succ`: its normalized form
  `(n + 1) z_{n+1} = ∑_{k ≤ n} (k + 1) a_{k+1} z_{n-k}` with `z_m = D_m / m!`,
  `a_m = A_m / m!`;
* the boundary values `D_0 = 1`, `A_0 = 0`, and `D_m = 0` for `m > |C|` when `K` vanishes off
  the reflexive elements of `R` (`disjointSum_eq_zero_of_card_lt`).
-/

@[expose] public section

namespace MultipoleBKT.Resummation

open Finset SimpleGraph

section Alternating

variable {V : Type*} [Fintype V]

open scoped Classical

omit [Fintype V] in
/-- The number of edges, independently of the `Fintype` instance on the edge set. -/
theorem card_edgeFinset_eq_ncard_edgeSet (H : SimpleGraph V) [Fintype H.edgeSet] :
    H.edgeFinset.card = H.edgeSet.ncard :=
  (Set.ncard_eq_toFinset_card' _).symm

/-- The number of edges is additive over edge-disjoint unions. -/
theorem ncard_edgeSet_sup_of_disjoint {H₁ H₂ : SimpleGraph V} (h : Disjoint H₁ H₂) :
    (H₁ ⊔ H₂).edgeSet.ncard = H₁.edgeSet.ncard + H₂.edgeSet.ncard := by
  rw [edgeSet_sup, Set.ncard_union_eq (disjoint_edgeSet.mpr h) (Set.toFinite _)
    (Set.toFinite _)]

/-- Spanning subgraphs of `K` correspond to subsets of its edge set. -/
theorem sum_le_eq_sum_powerset_edgeFinset {M : Type*} [AddCommMonoid M] (K : SimpleGraph V)
    (f : SimpleGraph V → M) :
    ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (· ≤ K), f H =
      ∑ F ∈ K.edgeFinset.powerset, f (fromEdgeSet (F : Set (Sym2 V))) := by
  have hF : ∀ F ∈ K.edgeFinset.powerset, (fromEdgeSet (F : Set (Sym2 V))).edgeFinset = F := by
    intro F hF
    rw [mem_powerset] at hF
    ext e
    simp only [mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      and_iff_left_iff_imp]
    intro he
    exact not_isDiag_of_mem_edgeSet _ (by simpa using hF he)
  refine Finset.sum_nbij' (fun H => H.edgeFinset) (fun F => fromEdgeSet (F : Set (Sym2 V)))
    ?_ ?_ ?_ ?_ ?_
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    simpa using edgeFinset_mono hH
  · intro F hF'
    simp only [mem_filter, mem_univ, true_and]
    rw [← edgeFinset_subset_edgeFinset, hF F hF']
    exact mem_powerset.mp hF'
  · intro H _
    simp
  · intro F hF'
    convert hF F hF'
  · intro H _
    simp

/-- The alternating sum over the spanning subgraphs of `K` is `1` if `K` has no edge and `0`
otherwise: the expansion of `∏_{e ∈ E(K)} (1 - 1)`. -/
theorem sum_le_neg_one_pow_card_edgeFinset (K : SimpleGraph V) :
    ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (· ≤ K), ((-1 : ℤ) ^ H.edgeFinset.card) =
      if K = ⊥ then 1 else 0 := by
  rw [sum_le_eq_sum_powerset_edgeFinset]
  rw [Finset.sum_congr rfl fun F hF => ?_, Finset.sum_powerset_neg_one_pow_card]
  · simp
  · rw [mem_powerset] at hF
    congr 2
    ext e
    simp only [mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      and_iff_left_iff_imp]
    intro he
    exact not_isDiag_of_mem_edgeSet _ (by simpa using hF he)

end Alternating

section Restrict

variable {V : Type*}

/-- The complete graph on the vertices satisfying `p`, as a graph on `V`. -/
def cliqueOn (p : V → Prop) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => p x ∧ p y

theorem cliqueOn_adj {p : V → Prop} {x y : V} :
    (cliqueOn p).Adj x y ↔ x ≠ y ∧ p x ∧ p y := by
  simp only [cliqueOn, fromRel_adj]
  constructor
  · rintro ⟨h, h' | h'⟩
    exacts [⟨h, h'⟩, ⟨h, h'.2, h'.1⟩]
  · rintro ⟨h, h'⟩
    exact ⟨h, Or.inl h'⟩

/-- The cliques on complementary vertex sets share no edge. -/
theorem disjoint_cliqueOn_not (p : V → Prop) :
    Disjoint (cliqueOn p) (cliqueOn fun x => ¬ p x) := by
  rw [disjoint_iff]
  ext x y
  simp only [inf_adj, cliqueOn_adj, bot_adj, iff_false]
  rintro ⟨⟨-, hx, -⟩, ⟨-, hx', -⟩⟩
  exact hx' hx

/-- The restriction of `H` to the vertices satisfying `p` (the induced subgraph). -/
def restrict (p : V → Prop) (H : SimpleGraph V) : SimpleGraph {x // p x} :=
  H.comap (Function.Embedding.subtype p)

theorem restrict_adj {p : V → Prop} {H : SimpleGraph V} {x y : {x // p x}} :
    (restrict p H).Adj x y ↔ H.Adj x y :=
  Iff.rfl

theorem restrict_mono {p : V → Prop} {H H' : SimpleGraph V} (h : H ≤ H') :
    restrict p H ≤ restrict p H' :=
  fun _ _ hxy => h hxy

/-- Adjacency-closed sets contain every vertex reachable from one of their points. -/
theorem of_reachable_of_closed {H : SimpleGraph V} {p : V → Prop}
    (hp : ∀ a b, H.Adj a b → p a → p b) {u x : V} (hux : H.Reachable u x) (hu : p u) :
    p x := by
  obtain ⟨w⟩ := hux
  induction w with
  | nil => exact hu
  | cons h _ ih => exact ih (hp _ _ h hu)

/-- Walks starting in an adjacency-closed set lift to the restricted graph. -/
theorem reachable_restrict_of_closed {H : SimpleGraph V} {p : V → Prop}
    (hp : ∀ a b, H.Adj a b → p a → p b) {u x : V} (hux : H.Reachable u x) (hu : p u) :
    (restrict p H).Reachable ⟨u, hu⟩ ⟨x, of_reachable_of_closed hp hux hu⟩ := by
  obtain ⟨w⟩ := hux
  induction w with
  | nil => rfl
  | cons h _ ih =>
    exact (Adj.reachable (show (restrict p H).Adj ⟨_, hu⟩ ⟨_, hp _ _ h hu⟩ from h)).trans
      (ih _)

/-- Reachability in a restriction gives reachability in the graph. -/
theorem reachable_of_restrict {H : SimpleGraph V} {p : V → Prop} {x y : {x // p x}}
    (h : (restrict p H).Reachable x y) : H.Reachable x y :=
  h.map (Hom.comap _ H)

variable [Fintype V]

open scoped Classical in
/-- The vertex set of the connected component of `v` in `H`. -/
noncomputable def reachSet (H : SimpleGraph V) (v : V) : Finset V :=
  univ.filter (H.Reachable v)

theorem mem_reachSet {H : SimpleGraph V} {v x : V} : x ∈ reachSet H v ↔ H.Reachable v x := by
  simp [reachSet]

/-- The component of `v` in `H` is `T` iff `H` has no edge between `T` and its complement and
`H` restricted to `T` is connected. -/
theorem reachSet_eq_iff {H : SimpleGraph V} {v : V} {T : Finset V} (hv : v ∈ T) :
    reachSet H v = T ↔
      H ≤ cliqueOn (· ∈ T) ⊔ cliqueOn (· ∉ T) ∧ (restrict (· ∈ T) H).Connected := by
  constructor
  · intro h
    have hmem : ∀ x, H.Reachable v x ↔ x ∈ T := fun x => by rw [← h, mem_reachSet]
    have hclosed : ∀ a b, H.Adj a b → a ∈ T → b ∈ T := fun a b hab ha =>
      (hmem b).1 (((hmem a).2 ha).trans hab.reachable)
    refine ⟨fun a b hab => ?_, ?_⟩
    · rw [sup_adj, cliqueOn_adj, cliqueOn_adj]
      by_cases ha : a ∈ T
      · exact Or.inl ⟨hab.ne, ha, hclosed a b hab ha⟩
      · exact Or.inr ⟨hab.ne, ha, fun hb => ha (hclosed b a hab.symm hb)⟩
    · have : Nonempty {x // x ∈ T} := ⟨⟨v, hv⟩⟩
      refine ⟨fun x y => ?_⟩
      have hx := reachable_restrict_of_closed hclosed ((hmem x).2 x.2) hv
      have hy := reachable_restrict_of_closed hclosed ((hmem y).2 y.2) hv
      exact hx.symm.trans hy
  · rintro ⟨hcut, hconn⟩
    have hclosed : ∀ a b, H.Adj a b → a ∈ T → b ∈ T := fun a b hab ha => by
      have := hcut hab
      rw [sup_adj, cliqueOn_adj, cliqueOn_adj] at this
      rcases this with h | h
      · exact h.2.2
      · exact absurd ha h.2.1
    ext x
    rw [mem_reachSet]
    constructor
    · intro hx
      exact of_reachable_of_closed hclosed hx hv
    · intro hx
      exact reachable_of_restrict (hconn.preconnected ⟨v, hv⟩ ⟨x, hx⟩)

end Restrict

section GraphIdentity

variable {V : Type*} [Fintype V]

open scoped Classical

omit [Fintype V] in
/-- A graph whose edges lie inside `{p}` is the image of its restriction to `{p}`. -/
theorem map_restrict_eq_of_le {p : V → Prop} {H : SimpleGraph V} (hH : H ≤ cliqueOn p) :
    (restrict p H).map (Function.Embedding.subtype p) = H := by
  ext x y
  rw [map_adj]
  constructor
  · rintro ⟨x', y', h, rfl, rfl⟩
    exact h
  · intro h
    obtain ⟨-, hx, hy⟩ := cliqueOn_adj.1 (hH h)
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, h, rfl, rfl⟩

omit [Fintype V] in
theorem restrict_map_subtype (p : V → Prop) (H : SimpleGraph {x // p x}) :
    restrict p (H.map (Function.Embedding.subtype p)) = H :=
  comap_map_eq _ _

omit [Fintype V] in
theorem ncard_edgeSet_map_subtype (p : V → Prop) (H : SimpleGraph {x // p x}) :
    (H.map (Function.Embedding.subtype p)).edgeSet.ncard = H.edgeSet.ncard := by
  rw [edgeSet_map, Set.ncard_image_of_injective _ (Function.Embedding.sym2Map _).injective]

/-- The Ursell function of `G` restricted to `{p}`, as a sum over the spanning subgraphs of `G`
with edges inside `{p}` that are connected on `{p}`. -/
theorem ursell_restrict_eq_sum (G : SimpleGraph V) (p : V → Prop) [Fintype {x // p x}] :
    ursell (restrict p G) =
      ∑ H ∈ (univ : Finset (SimpleGraph V)).filter
          (fun H => H ≤ G ⊓ cliqueOn p ∧ (restrict p H).Connected),
        ((-1 : ℤ) ^ H.edgeFinset.card) := by
  rw [ursell]
  symm
  refine Finset.sum_nbij' (fun H => restrict p H)
    (fun H' => H'.map (Function.Embedding.subtype p)) ?_ ?_ ?_ ?_ ?_
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH ⊢
    exact ⟨restrict_mono (hH.1.trans inf_le_left), hH.2⟩
  · intro H' hH'
    simp only [mem_filter, mem_univ, true_and] at hH' ⊢
    refine ⟨fun x y hxy => ?_, by rw [restrict_map_subtype]; exact hH'.2⟩
    rw [map_adj] at hxy
    obtain ⟨x', y', h, rfl, rfl⟩ := hxy
    exact ⟨hH'.1 h, cliqueOn_adj.2 ⟨fun he => h.ne (Subtype.ext he), x'.2, y'.2⟩⟩
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    exact map_restrict_eq_of_le (hH.1.trans inf_le_right)
  · intro H' _
    exact restrict_map_subtype p H'
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    simp only [card_edgeFinset_eq_ncard_edgeSet]
    conv_lhs => rw [← map_restrict_eq_of_le (hH.1.trans inf_le_right)]
    rw [ncard_edgeSet_map_subtype]

/-- The spanning subgraphs of `G` in which the component of `v` is `T` are the unions of a
spanning subgraph of `G` on `T`, connected on `T`, and a spanning subgraph of `G` off `T`. -/
theorem sum_filter_reachSet_eq (G : SimpleGraph V) {v : V} {T : Finset V} (hv : v ∈ T) :
    ∑ H ∈ ((univ : Finset (SimpleGraph V)).filter (· ≤ G)).filter (fun H => reachSet H v = T),
        ((-1 : ℤ) ^ H.edgeFinset.card) =
      (∑ H ∈ (univ : Finset (SimpleGraph V)).filter
          (fun H => H ≤ G ⊓ cliqueOn (· ∈ T) ∧ (restrict (· ∈ T) H).Connected),
          ((-1 : ℤ) ^ H.edgeFinset.card)) *
        ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (· ≤ G ⊓ cliqueOn (· ∉ T)),
          ((-1 : ℤ) ^ H.edgeFinset.card) := by
  have hdisj : Disjoint (cliqueOn (· ∈ T)) (cliqueOn (· ∉ T)) := disjoint_cliqueOn_not _
  rw [sum_mul_sum, ← sum_product']
  symm
  refine Finset.sum_nbij' (fun q => q.1 ⊔ q.2)
    (fun H => (H ⊓ cliqueOn (· ∈ T), H ⊓ cliqueOn (· ∉ T))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨H₁, H₂⟩ hq
    simp only [mem_product, mem_filter, mem_univ, true_and] at hq ⊢
    obtain ⟨⟨h₁, hc⟩, h₂⟩ := hq
    refine ⟨sup_le (h₁.trans inf_le_left) (h₂.trans inf_le_left),
      (reachSet_eq_iff hv).2 ⟨?_, ?_⟩⟩
    · exact sup_le_sup (h₁.trans inf_le_right) (h₂.trans inf_le_right)
    · exact hc.mono (restrict_mono le_sup_left)
  · intro H hH
    simp only [mem_product, mem_filter, mem_univ, true_and] at hH ⊢
    obtain ⟨hG, hT⟩ := hH
    obtain ⟨-, hc⟩ := (reachSet_eq_iff hv).1 hT
    refine ⟨⟨inf_le_inf_right _ hG, ?_⟩, inf_le_inf_right _ hG⟩
    convert hc using 1
    ext x y
    simp only [restrict_adj, inf_adj, cliqueOn_adj, and_iff_left_iff_imp]
    intro h
    exact ⟨h.ne, x.2, y.2⟩
  · rintro ⟨H₁, H₂⟩ hq
    simp only [mem_product, mem_filter, mem_univ, true_and] at hq
    obtain ⟨⟨h₁, -⟩, h₂⟩ := hq
    have h₁' : H₁ ≤ cliqueOn (· ∈ T) := h₁.trans inf_le_right
    have h₂' : H₂ ≤ cliqueOn (· ∉ T) := h₂.trans inf_le_right
    simp only [inf_sup_right, inf_eq_left.mpr h₁', inf_eq_left.mpr h₂',
      disjoint_iff.mp (hdisj.mono_left h₁'), disjoint_iff.mp (hdisj.symm.mono_left h₂'),
      sup_bot_eq, bot_sup_eq]
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    obtain ⟨hcut, -⟩ := (reachSet_eq_iff hv).1 hH.2
    simp only [← inf_sup_left, inf_eq_left.mpr hcut]
  · rintro ⟨H₁, H₂⟩ hq
    simp only [mem_product, mem_filter, mem_univ, true_and] at hq
    obtain ⟨⟨h₁, -⟩, h₂⟩ := hq
    have hd : Disjoint H₁ H₂ := hdisj.mono (h₁.trans inf_le_right) (h₂.trans inf_le_right)
    simp only [card_edgeFinset_eq_ncard_edgeSet, ncard_edgeSet_sup_of_disjoint hd, pow_add]

/-- **Graph identity behind the resummation.** For a finite graph `G` and a vertex `v`,
`𝟙[G = ⊥] = ∑_{T ∋ v} I(G[T]) 𝟙[G has no edge outside T]`: expand `𝟙[G = ⊥]` as the
alternating sum over spanning subgraphs `H ≤ G` and group by the component `T` of `v` in `H`. -/
theorem ite_eq_bot_eq_sum (G : SimpleGraph V) (v : V) :
    (if G = ⊥ then 1 else 0 : ℤ) =
      ∑ T ∈ (univ : Finset (Finset V)).filter (v ∈ ·),
        ursell (restrict (· ∈ T) G) * (if G ⊓ cliqueOn (· ∉ T) = ⊥ then 1 else 0) := by
  rw [← sum_le_neg_one_pow_card_edgeFinset G,
    ← Finset.sum_fiberwise_of_maps_to (g := fun H => reachSet H v)
      (t := (univ : Finset (Finset V)).filter (v ∈ ·)) (fun H _ => ?_)]
  · refine Finset.sum_congr rfl fun T hT => ?_
    rw [sum_filter_reachSet_eq G (mem_filter.1 hT).2, ursell_restrict_eq_sum,
      sum_le_neg_one_pow_card_edgeFinset]
  · simp [mem_reachSet]

end GraphIdentity

section Ursell

open scoped Classical

/-- The Ursell function of a disconnected graph vanishes. -/
theorem ursell_eq_zero_of_not_connected' {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : ¬ G.Connected) : ursell G = 0 := by
  rw [ursell]
  refine Finset.sum_eq_zero fun H hH => ?_
  simp only [mem_filter, mem_univ, true_and] at hH
  exact absurd (hH.2.mono hH.1) hG

/-- The Ursell function is invariant under graph isomorphism. -/
theorem ursell_eq_of_iso {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {G' : SimpleGraph W} (e : G ≃g G') : ursell G = ursell G' := by
  rw [ursell, ursell]
  refine Finset.sum_equiv e.toEquiv.simpleGraph (fun H => ?_) (fun H _ => ?_)
  · simp only [mem_filter, mem_univ, true_and, Equiv.simpleGraph_apply]
    have hiso : H.comap e.toEquiv.symm ≃g H := Iso.comap e.toEquiv.symm H
    refine and_congr ⟨fun hle x y hxy => ?_, fun hle x y hxy => ?_⟩ hiso.connected_iff.symm
    · have h1 : G.Adj (e.symm x) (e.symm y) := hle hxy
      exact e.symm.map_adj_iff.mp h1
    · have h1 : (H.comap e.toEquiv.symm).Adj (e x) (e y) := by
        show H.Adj (e.toEquiv.symm (e.toEquiv x)) (e.toEquiv.symm (e.toEquiv y))
        simpa only [Equiv.symm_apply_apply] using hxy
      have h2 : G'.Adj (e x) (e y) := hle h1
      exact e.map_adj_iff.mp h2
  · exact congrArg _ (Iso.card_edgeFinset_eq (Iso.comap e.toEquiv.symm H)).symm

end Ursell

section Tuples

variable {C : Type*} (R : C → C → Prop)

/-- The connection graph of a tuple `X : ι → C`: `i ~ j` iff `i ≠ j` and `X i`, `X j` are
related. For `R` = "intersect" on finite sets it is `MultipoleBKT.connectionGraph`. -/
def relGraph {ι : Type*} (X : ι → C) : SimpleGraph ι :=
  SimpleGraph.fromRel fun i j => R (X i) (X j)

variable {R}

theorem relGraph_adj {ι : Type*} {X : ι → C} {i j : ι} :
    (relGraph R X).Adj i j ↔ i ≠ j ∧ (R (X i) (X j) ∨ R (X j) (X i)) :=
  Iff.rfl

theorem relGraph_eq_bot_iff {ι : Type*} {X : ι → C} :
    relGraph R X = ⊥ ↔ ∀ i j, i ≠ j → ¬ R (X i) (X j) := by
  rw [eq_bot_iff_forall_not_adj]
  simp only [relGraph_adj, not_and, not_or]
  exact ⟨fun h i j hij => (h i j hij).1, fun h i j hij => ⟨h i j hij, h j i hij.symm⟩⟩

theorem restrict_relGraph {ι : Type*} (X : ι → C) (p : ι → Prop) :
    restrict p (relGraph R X) = relGraph R (fun i : {x // p x} => X i) := by
  ext i j
  rw [restrict_adj, relGraph_adj, relGraph_adj, ne_eq, ne_eq, Subtype.ext_iff]

theorem relGraph_inf_cliqueOn_eq_bot_iff {ι : Type*} (X : ι → C) (p : ι → Prop) :
    relGraph R X ⊓ cliqueOn p = ⊥ ↔ relGraph R (fun i : {x // p x} => X i) = ⊥ := by
  rw [relGraph_eq_bot_iff, eq_bot_iff_forall_not_adj]
  simp only [inf_adj, relGraph_adj, cliqueOn_adj]
  constructor
  · intro h i j hij hR
    exact h i j ⟨⟨fun he => hij (Subtype.ext he), Or.inl hR⟩,
      fun he => hij (Subtype.ext he), i.2, j.2⟩
  · rintro h a b ⟨⟨hab, hR⟩, -, ha, hb⟩
    rcases hR with hR | hR
    · exact h ⟨a, ha⟩ ⟨b, hb⟩ (fun he => hab (congrArg Subtype.val he)) hR
    · exact h ⟨b, hb⟩ ⟨a, ha⟩ (fun he => hab (congrArg Subtype.val he).symm) hR

theorem relGraph_comp_equiv {ι κ : Type*} (X : κ → C) (e : ι ≃ κ) :
    relGraph R (X ∘ e) = (relGraph R X).comap e := by
  ext i j
  simp only [relGraph_adj, comap_adj, Function.comp_apply, ne_eq, e.injective.eq_iff]

theorem relGraph_comp_equiv_eq_bot_iff {ι κ : Type*} (X : κ → C) (e : ι ≃ κ) :
    relGraph R (X ∘ e) = ⊥ ↔ relGraph R X = ⊥ := by
  simp only [relGraph_eq_bot_iff, Function.comp_apply]
  exact ⟨fun h i j hij => by simpa using h (e.symm i) (e.symm j) (e.symm.injective.ne hij),
    fun h i j hij => h _ _ (e.injective.ne hij)⟩

open scoped Classical

variable [Fintype C] (R) (K : C → ℝ)

/-- `∑_{X : ι → C disjoint} ∏ᵢ K (X i)`, where `X` is disjoint if `relGraph R X = ⊥`. -/
noncomputable def disjointSum (ι : Type*) [Fintype ι] [DecidableEq ι] : ℝ :=
  ∑ X : ι → C, (∏ i, K (X i)) * if relGraph R X = ⊥ then 1 else 0

/-- `∑_{X : ι → C} (∏ᵢ K (X i)) I(relGraph R X)`. -/
noncomputable def clusterSum (ι : Type*) [Fintype ι] [DecidableEq ι] : ℝ :=
  ∑ X : ι → C, (∏ i, K (X i)) * (ursell (relGraph R X) : ℝ)

theorem disjointSum_congr {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : disjointSum R K ι = disjointSum R K κ := by
  unfold disjointSum
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl C)) _ _ fun X => ?_
  have hX : e.arrowCongr (Equiv.refl C) X = X ∘ e.symm := rfl
  rw [hX, ← Equiv.prod_comp e.symm (fun i => K (X i))]
  simp only [relGraph_comp_equiv_eq_bot_iff, Function.comp_apply]

theorem clusterSum_congr {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : clusterSum R K ι = clusterSum R K κ := by
  unfold clusterSum
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl C)) _ _ fun X => ?_
  have hX : e.arrowCongr (Equiv.refl C) X = X ∘ e.symm := rfl
  rw [hX, ← Equiv.prod_comp e.symm (fun i => K (X i)), relGraph_comp_equiv,
    ursell_eq_of_iso (Iso.comap e.symm (relGraph R X))]
  rfl

/-- Splitting a sum over tuples `ι → C` along `T` and its complement. -/
theorem sum_mul_sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι)
    (f : ({x // x ∈ T} → C) → ℝ) (g : ({x // x ∉ T} → C) → ℝ) :
    ∑ X : ι → C, f (fun i => X i) * g (fun i => X i) = (∑ Y, f Y) * ∑ W, g W := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ T) fun _ => C) _ _ fun X => rfl

/-- **Root decomposition.** Grouping a disjoint family by the cluster of a fixed index `v`:
`D(ι) = ∑_{T ∋ v} A(T) D(ι ∖ T)`. -/
theorem disjointSum_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι) :
    disjointSum R K ι = ∑ T ∈ (univ : Finset (Finset ι)).filter (v ∈ ·),
      clusterSum R K {x // x ∈ T} * disjointSum R K {x // x ∉ T} := by
  have key : ∀ X : ι → C, (if relGraph R X = ⊥ then (1 : ℝ) else 0) =
      ∑ T ∈ (univ : Finset (Finset ι)).filter (v ∈ ·),
        (ursell (relGraph R (fun i : {x // x ∈ T} => X i)) : ℝ) *
          (if relGraph R (fun i : {x // x ∉ T} => X i) = ⊥ then 1 else 0) := by
    intro X
    have h := congrArg (Int.cast : ℤ → ℝ) (ite_eq_bot_eq_sum (relGraph R X) v)
    push_cast at h
    rw [h]
    refine Finset.sum_congr (by ext; simp) fun T _ => ?_
    rw [restrict_relGraph]
    simp only [relGraph_inf_cliqueOn_eq_bot_iff]
  have hT : ∀ T : Finset ι, clusterSum R K {x // x ∈ T} * disjointSum R K {x // x ∉ T} =
      ∑ X : ι → C, (∏ i, K (X i)) * ((ursell (relGraph R (fun i : {x // x ∈ T} => X i)) : ℝ) *
          (if relGraph R (fun i : {x // x ∉ T} => X i) = ⊥ then 1 else 0)) := by
    intro T
    unfold disjointSum clusterSum
    rw [← sum_mul_sum_split T (fun Y => (∏ i, K (Y i)) * (ursell (relGraph R Y) : ℝ))
      (fun W => (∏ i, K (W i)) * if relGraph R W = ⊥ then 1 else 0)]
    refine Finset.sum_congr rfl fun X _ => ?_
    have hsplit : ∏ i, K (X i) =
        (∏ i : {x // x ∈ T}, K (X i)) * ∏ i : {x // x ∉ T}, K (X i) := by
      convert (Fintype.prod_subtype_mul_prod_subtype (· ∈ T) (fun i => K (X i))).symm using 2
      exact Finset.prod_congr (by ext; simp) fun _ _ => rfl
    rw [hsplit]
    ring
  rw [Finset.sum_congr rfl fun T _ => hT T, Finset.sum_comm]
  unfold disjointSum
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [key X, mul_sum]

end Tuples

section Recursion

open scoped Classical

/-- Sets containing `v` are `insert v` of subsets of the other points. -/
theorem sum_filter_mem_eq_sum_powerset_erase {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι)
    (f : ℕ → ℝ) :
    ∑ T ∈ (univ : Finset (Finset ι)).filter (v ∈ ·), f T.card =
      ∑ T ∈ (univ.erase v).powerset, f (T.card + 1) := by
  refine Finset.sum_nbij' (fun T => T.erase v) (fun T => insert v T) ?_ ?_ ?_ ?_ ?_
  · intro T _
    exact mem_powerset.2 (erase_subset_erase v (subset_univ T))
  · intro T _
    simp
  · intro T hT
    exact insert_erase (mem_filter.1 hT).2
  · intro T hT
    exact erase_insert fun h => by simpa using mem_powerset.1 hT h
  · intro T hT
    rw [card_erase_add_one (mem_filter.1 hT).2]

variable {C : Type*} [Fintype C] (R : C → C → Prop) (K : C → ℝ)

/-- **Recursion.** `D_{n+1} = ∑_{k ≤ n} C(n, k) A_{k+1} D_{n-k}`, where `D_m` and `A_m` are the
disjoint and cluster sums over `m`-tuples. -/
theorem disjointSum_succ (n : ℕ) :
    disjointSum R K (Fin (n + 1)) = ∑ k ∈ range (n + 1),
      (n.choose k : ℝ) * (clusterSum R K (Fin (k + 1)) * disjointSum R K (Fin (n - k))) := by
  rw [disjointSum_eq_sum R K (0 : Fin (n + 1))]
  have h1 : ∀ T : Finset (Fin (n + 1)),
      clusterSum R K {x // x ∈ T} * disjointSum R K {x // x ∉ T} =
        clusterSum R K (Fin T.card) * disjointSum R K (Fin (n + 1 - T.card)) := by
    intro T
    congr 1
    · exact clusterSum_congr R K (Fintype.equivFinOfCardEq (by simp))
    · refine disjointSum_congr R K (Fintype.equivFinOfCardEq ?_)
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      simp
  rw [Finset.sum_congr rfl fun T _ => h1 T,
    sum_filter_mem_eq_sum_powerset_erase (0 : Fin (n + 1))
      (fun m => clusterSum R K (Fin m) * disjointSum R K (Fin (n + 1 - m))),
    Finset.sum_powerset_apply_card
      (fun m => clusterSum R K (Fin (m + 1)) * disjointSum R K (Fin (n + 1 - (m + 1))))]
  simp only [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.add_sub_cancel,
    nsmul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show n + 1 - (k + 1) = n - k by omega]

/-- `D_0 = 1`: the empty tuple. -/
theorem disjointSum_zero : disjointSum R K (Fin 0) = 1 := by
  unfold disjointSum
  rw [Fintype.sum_unique]
  simp [relGraph_eq_bot_iff]

/-- `A_0 = 0`: the empty graph is not connected. -/
theorem clusterSum_zero : clusterSum R K (Fin 0) = 0 := by
  unfold clusterSum
  refine Finset.sum_eq_zero fun X _ => ?_
  rw [ursell_eq_zero_of_not_connected' fun h => (isEmpty_iff.1 inferInstance) h.nonempty.some,
    Int.cast_zero, mul_zero]

/-- If `K` vanishes off the reflexive points of `R`, a disjoint family with nonzero weight is
injective, so `D_m = 0` for `m > |C|`. -/
theorem disjointSum_eq_zero_of_card_lt (hK : ∀ x, ¬ R x x → K x = 0) {m : ℕ}
    (hm : Fintype.card C < m) : disjointSum R K (Fin m) = 0 := by
  unfold disjointSum
  refine Finset.sum_eq_zero fun X _ => ?_
  by_cases hX : relGraph R X = ⊥
  · rw [ite_eq_left hX, mul_one]
    by_contra hne
    have hrefl : ∀ i, R (X i) (X i) := fun i =>
      by_contra fun h => (prod_ne_zero_iff.1 hne) i (mem_univ _) (hK _ h)
    have hinj : Function.Injective X := fun i j hij =>
      by_contra fun hne' => relGraph_eq_bot_iff.1 hX i j hne' (by rw [← hij]; exact hrefl i)
    have := Fintype.card_le_of_injective X hinj
    rw [Fintype.card_fin] at this
    omega
  · rw [ite_eq_right hX, mul_zero]

/-- The normalized disjoint sum `z_m = D_m / m!`. -/
noncomputable def disjointCoeff (m : ℕ) : ℝ :=
  disjointSum R K (Fin m) / m.factorial

/-- The normalized cluster sum `a_m = A_m / m!`. -/
noncomputable def clusterCoeff (m : ℕ) : ℝ :=
  clusterSum R K (Fin m) / m.factorial

/-- **Normalized recursion** (the coefficients of `Z' = F' Z`):
`(n + 1) z_{n+1} = ∑_{k ≤ n} (k + 1) a_{k+1} z_{n-k}`. -/
theorem succ_mul_disjointCoeff_succ (n : ℕ) :
    (n + 1 : ℝ) * disjointCoeff R K (n + 1) = ∑ k ∈ range (n + 1),
      (k + 1 : ℝ) * clusterCoeff R K (k + 1) * disjointCoeff R K (n - k) := by
  unfold disjointCoeff clusterCoeff
  rw [disjointSum_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_div_assoc',
    mul_div_mul_left _ _ (by positivity : (n + 1 : ℝ) ≠ 0), Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  have hc : (n.choose k : ℝ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, ← hc]
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (k + 1 : ℝ) ≠ 0 := by positivity
  have h4 : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  field_simp

/-- `z_0 = 1`. -/
theorem disjointCoeff_zero : disjointCoeff R K 0 = 1 := by
  simp [disjointCoeff, disjointSum_zero]

/-- `a_0 = 0`. -/
theorem clusterCoeff_zero : clusterCoeff R K 0 = 0 := by
  simp [clusterCoeff, clusterSum_zero]

/-- `z_m = 0` for `m > |C|` when `K` vanishes off the reflexive points of `R`. -/
theorem disjointCoeff_eq_zero_of_card_lt (hK : ∀ x, ¬ R x x → K x = 0) {m : ℕ}
    (hm : Fintype.card C < m) : disjointCoeff R K m = 0 := by
  simp [disjointCoeff, disjointSum_eq_zero_of_card_lt R K hK hm]

end Recursion

end MultipoleBKT.Resummation

end
