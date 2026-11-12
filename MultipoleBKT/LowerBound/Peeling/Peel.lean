/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.EarExists
public import MultipoleBKT.LowerBound.Peeling.Weights
public import MultipoleBKT.LowerBound.Peeling.Pseudoforest

/-!
# The peeling of a minimally 2-edge-connected graph (Definition 4.43)

We formalize Definition 4.43 and its structural properties.

The definition depends on choices: a vertex `v₁` with `r_{[v₁]}` maximal, a strict ear decomposition
whose base cycle passes through `[v₁]`, a longest edge `e₀`, and tie-breaks ("lexicographical
tie-breaking", Definition 4.43) in the deletion rules. We do not fix these choices.
`MultipoleBKT.Peeling.IsPeelingOn b E r d v₁ e₀ Qs` says that `Qs` (each ear paired with its
deleted oriented edge) is the outcome of Definition 4.43 for some admissible choices; every result
below holds for every admissible choice, in particular for the paper's. The tie-breaks are
relaxed to "any maximizer", which only enlarges the set of admissible outcomes.

The deletion rules, for the ear `P_ℓ` written `(a₁, b₁), …, (a_m, b_m)` (the base cycle written
from `[v₁]`):

1. if `e₀ ∈ P_ℓ` and `d_{e₀} ≥ max_i r_i`, delete `e₀`, oriented from an endpoint whose block first
   appears in `P_ℓ`;
2. otherwise delete the first edge, oriented `b₁ → a₁`, or the last edge, oriented `a_m → b_m`,
   whichever has the larger score `min(d_ij, max(r_i, r_j))`.

The kept edges `𝒯^X = E ∖ 𝓕^X` are `MultipoleBKT.Peeling.keptGraph E Qs`, the discarded edges
`𝓕^X` are `MultipoleBKT.Peeling.removedGraph Qs` and their orientation `F⃗^X` is `Qs.map Prod.snd`.

Main results:

* `MultipoleBKT.Peeling.exists_isPeeling`: the peeling exists for every graph minimally
  2-edge-connected relative to `X` (with Lemma 4.40);
* `MultipoleBKT.Peeling.IsPeeling.isRelTree`: `𝒯^X ∈ 𝖳^X` (Definition 4.43);
* `MultipoleBKT.Peeling.IsPeelingOn.isPseudoforest`: `𝓕^X ∈ PF(V_X)` (Lemma 4.49(1), first claim,
  proof of Lemma 4.49): every vertex is the tail of at most one discarded edge;
* `MultipoleBKT.Peeling.IsPeelingOn.longest_mem_removedEdges`: if `d_{e₀} ≥ max_i r_i` then
  `e₀ ∈ 𝓕^X` (used in the proof of (4.70) in the proof of Lemma 4.49).
-/

@[expose] public section

namespace MultipoleBKT

namespace Peeling

open Finset SimpleGraph

variable {V β : Type*} (b : V → β)

/-- The deletion rule of Definition 4.43 for one ear `P`, whose deleted oriented edge is `t`. `U`
is the set of blocks covered by the previous ears (`∅` for the base cycle), so that `[t.1] ∉ U`
says that the block of the tail first appears in `P`; `R = max_i r_i`. -/
def IsEarRemoval (r : V → ℝ) (d : Sym2 V → ℝ) (R : ℝ) (e₀ : Sym2 V) (U : Finset β) (P : Ear V)
    (t : V × V) : Prop :=
  (e₀ ∈ P.edges ∧ R ≤ d e₀ ∧ edge t = e₀ ∧ b t.1 ∉ U) ∨
    (¬ (e₀ ∈ P.edges ∧ R ≤ d e₀) ∧
      ((t = P.first.swap ∧ peelScore r d (edge P.last) ≤ peelScore r d (edge P.first)) ∨
        (t = P.last ∧ peelScore r d (edge P.first) ≤ peelScore r d (edge P.last))))

variable [DecidableEq β]

/-- The deletion rule along a sequence of ears; `U` is the set of blocks covered before the
current ear. -/
def IsPeelingSeq (r : V → ℝ) (d : Sym2 V → ℝ) (R : ℝ) (e₀ : Sym2 V) :
    Finset β → List (Ear V × (V × V)) → Prop
  | _, [] => True
  | U, Q :: Qs => IsEarRemoval b r d R e₀ U Q.1 Q.2 ∧
      IsPeelingSeq r d R e₀ (U ∪ Q.1.blocks b) Qs

/-- `Qs` is an admissible outcome of the peeling of `E` (Definition 4.43): `v₁` has maximal radius,
`Qs.map Prod.fst` is a strict ear decomposition of `E` whose base cycle starts at `[v₁]`, `e₀` is a
longest edge of `E`, and each ear is paired with the oriented edge deleted from it by the rules
(1)–(3) with `R = r_{v₁} = max_i r_i`. -/
structure IsPeelingOn [Fintype β] (E : SimpleGraph V) (r : V → ℝ) (d : Sym2 V → ℝ) (v₁ : V)
    (e₀ : Sym2 V) (Qs : List (Ear V × (V × V))) : Prop where
  le_radius : ∀ i, r i ≤ r v₁
  decomp : IsStrictEarDecompOn b E (b v₁) (Qs.map Prod.fst)
  longest_mem : e₀ ∈ E.edgeSet
  le_longest : ∀ e ∈ E.edgeSet, d e ≤ d e₀
  rule : IsPeelingSeq b r d (r v₁) e₀ ∅ Qs

/-- The peeling of Definition 4.43 relative to a subpartition `X`. -/
def IsPeeling {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (E : SimpleGraph (X.biUnion id))
    (r : X.biUnion id → ℝ) (d : Sym2 (X.biUnion id) → ℝ) (v₁ : X.biUnion id)
    (e₀ : Sym2 (X.biUnion id)) (Qs : List (Ear (X.biUnion id) × (X.biUnion id × X.biUnion id))) :
    Prop :=
  IsPeelingOn (blockOf hX) E r d v₁ e₀ Qs

variable {b}

/-! ### Facts about one ear -/

section OneEar

variable {E : SimpleGraph V} {r : V → ℝ} {d : Sym2 V → ℝ} {R : ℝ} {e₀ : Sym2 V}

omit [DecidableEq β] in
theorem IsEarRemoval.edge_mem {U : Finset β} {P : Ear V} {t : V × V}
    (h : IsEarRemoval b r d R e₀ U P t) : edge t ∈ P.edges := by
  rcases h with ⟨he, -, ht, -⟩ | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
  · exact ht ▸ he
  · rw [edge_swap]
    exact List.mem_map_of_mem P.first_mem_toList
  · exact List.mem_map_of_mem P.last_mem_toList

/-- The tail of the deleted edge lies in a block of the ear that first appears in it. -/
theorem IsEarRemoval.tail_mem {W U : Finset β} {P : Ear V} {t : V × V} (hP : IsEar b E W P)
    (hUW : U ⊆ W) (h : IsEarRemoval b r d R e₀ U P t) : b t.1 ∉ U ∧ b t.1 ∈ P.blocks b := by
  rcases h with ⟨he, -, ht, hU⟩ | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
  · refine ⟨hU, ?_⟩
    obtain ⟨p, hp, hpe⟩ := Ear.mem_edges.mp he
    rw [← ht, edge_apply, edge_apply] at hpe
    rcases Sym2.eq_iff.mp hpe with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1 ▸ (hP.mem_blocks p hp).1
    · exact h2 ▸ (hP.mem_blocks p hp).2
  · have hmem : b P.first.2 ∈ P.interior b := List.mem_cons_self
    refine ⟨fun h => hP.interior_notMem _ hmem (hUW h), ?_⟩
    simp only [Ear.blocks, mem_insert, List.mem_toFinset]
    exact Or.inr (Or.inr hmem)
  · have hmem : b P.last.1 ∈ P.interior b := by
      rw [hP.isChain |> Ear.interior_eq_fst]
      exact List.mem_map_of_mem (List.mem_append_right _ (List.mem_singleton_self _))
    refine ⟨fun h => hP.interior_notMem _ hmem (hUW h), ?_⟩
    simp only [Ear.blocks, mem_insert, List.mem_toFinset]
    exact Or.inr (Or.inr hmem)

omit [DecidableEq β] in
/-- A deletion rule always applies. -/
theorem exists_isEarRemoval {W U : Finset β} {P : Ear V} (hP : IsEar b E W P) (hUW : U ⊆ W) :
    ∃ t, IsEarRemoval b r d R e₀ U P t := by
  by_cases hex : e₀ ∈ P.edges ∧ R ≤ d e₀
  · obtain ⟨p, hp, hpe⟩ := Ear.mem_edges.mp hex.1
    rcases hP.exists_interior p hp with h | h
    · exact ⟨p, Or.inl ⟨hex.1, hex.2, hpe, fun hU => hP.interior_notMem _ h (hUW hU)⟩⟩
    · refine ⟨p.swap, Or.inl ⟨hex.1, hex.2, by rw [edge_swap, hpe], ?_⟩⟩
      exact fun hU => hP.interior_notMem _ h (hUW hU)
  · rcases le_total (peelScore r d (edge P.last)) (peelScore r d (edge P.first)) with h | h
    · exact ⟨P.first.swap, Or.inr ⟨hex, Or.inl ⟨rfl, h⟩⟩⟩
    · exact ⟨P.last, Or.inr ⟨hex, Or.inr ⟨rfl, h⟩⟩⟩

end OneEar

/-! ### Facts about a sequence of ears -/

section Seq

variable {E : SimpleGraph V} {r : V → ℝ} {d : Sym2 V → ℝ} {R : ℝ} {e₀ : Sym2 V}

theorem IsPeelingSeq.isRemoval : ∀ {U : Finset β} {Qs : List (Ear V × (V × V))},
    IsPeelingSeq b r d R e₀ U Qs → IsRemoval Qs
  | _, [], _ => fun _ h => absurd h List.not_mem_nil
  | _, Q :: Qs, ⟨hQ, hQs⟩ => by
    intro Q' hQ'
    rcases List.mem_cons.mp hQ' with rfl | hQ'
    · exact hQ.edge_mem
    · exact hQs.isRemoval Q' hQ'

/-- Each ear of the sequence follows the deletion rule relative to some set of blocks. -/
theorem IsPeelingSeq.exists_rule : ∀ {U : Finset β} {Qs : List (Ear V × (V × V))},
    IsPeelingSeq b r d R e₀ U Qs → ∀ Q ∈ Qs, ∃ U', IsEarRemoval b r d R e₀ U' Q.1 Q.2
  | _, [], _ => fun _ h => absurd h List.not_mem_nil
  | U, Q :: Qs, ⟨hQ, hQs⟩ => by
    intro Q' hQ'
    rcases List.mem_cons.mp hQ' with rfl | hQ'
    · exact ⟨U, hQ⟩
    · exact hQs.exists_rule Q' hQ'

/-- The tails of the deleted edges lie in pairwise distinct blocks outside `U`. -/
theorem IsPeelingSeq.tails : ∀ {U W : Finset β} {Qs : List (Ear V × (V × V))},
    U ⊆ W → IsEarSeq b E W (Qs.map Prod.fst) → IsPeelingSeq b r d R e₀ U Qs →
      (∀ Q ∈ Qs, b Q.2.1 ∉ U) ∧ (Qs.map fun Q => b Q.2.1).Nodup
  | _, _, [], _, _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩
  | U, W, Q :: Qs, hUW, ⟨hP, hPs⟩, ⟨hQ, hQs⟩ => by
    have ih := IsPeelingSeq.tails (union_subset_union hUW le_rfl) hPs hQs
    have ht := hQ.tail_mem hP hUW
    refine ⟨fun Q' hQ' => ?_, ?_⟩
    · rcases List.mem_cons.mp hQ' with rfl | hQ'
      · exact ht.1
      · exact fun h => ih.1 Q' hQ' (mem_union_left _ h)
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun h => ?_, ih.2⟩
      obtain ⟨Q', hQ', heq⟩ := List.mem_map.mp h
      exact ih.1 Q' hQ' (heq ▸ mem_union_right _ ht.2)

/-- Existence of the deletions along a sequence of ears. -/
theorem exists_isPeelingSeq : ∀ {U W : Finset β} {Ps : List (Ear V)},
    U ⊆ W → IsEarSeq b E W Ps →
      ∃ Qs : List (Ear V × (V × V)), Qs.map Prod.fst = Ps ∧ IsPeelingSeq b r d R e₀ U Qs
  | _, _, [], _, _ => ⟨[], rfl, trivial⟩
  | U, W, P :: Ps, hUW, ⟨hP, hPs⟩ => by
    obtain ⟨t, ht⟩ := exists_isEarRemoval (r := r) (d := d) (R := R) (e₀ := e₀) hP hUW
    obtain ⟨Qs, hQs, hrule⟩ := exists_isPeelingSeq
      (union_subset_union hUW (le_refl (P.blocks b))) hPs
    exact ⟨(P, t) :: Qs, by rw [List.map_cons, hQs], ht, hrule⟩

end Seq

/-! ### Properties of the peeling -/

section Peeling

variable [Fintype β] {E : SimpleGraph V} {r : V → ℝ} {d : Sym2 V → ℝ} {v₁ : V} {e₀ : Sym2 V}
  {Qs : List (Ear V × (V × V))}

theorem IsPeelingOn.isRemoval (h : IsPeelingOn b E r d v₁ e₀ Qs) : IsRemoval Qs :=
  h.rule.isRemoval

/-- The tails of the discarded edges are pairwise distinct (indeed in distinct blocks). -/
theorem IsPeelingOn.nodup_tails (h : IsPeelingOn b E r d v₁ e₀ Qs) :
    ((Qs.map Prod.snd).map Prod.fst).Nodup := by
  have := (h.rule.tails (empty_subset _) h.decomp.isEarSeq).2
  refine List.Nodup.of_map b ?_
  rw [List.map_map, List.map_map]
  exact this

theorem IsPeelingOn.removedEdges_mem (h : IsPeelingOn b E r d v₁ e₀ Qs) {e : Sym2 V}
    (he : e ∈ removedEdges Qs) : e ∈ E.edgeSet :=
  (h.decomp.mem_iff e).mp (h.isRemoval.mem_flatMap he)

/-- `𝓕^X ∈ PF(V_X)` (Lemma 4.49(1), proof of Lemma 4.49): each discarded edge is oriented from a
vertex whose block first appears in its ear, so every vertex has out-degree at most `1`. -/
theorem IsPeelingOn.isPseudoforest (h : IsPeelingOn b E r d v₁ e₀ Qs) :
    IsPseudoforest (removedGraph Qs) := by
  have hrem : removedEdges Qs = (Qs.map Prod.snd).map edge := by
    rw [removedEdges, List.map_map]
    rfl
  rw [removedGraph, hrem]
  refine isPseudoforest_fromEdgeSet h.nodup_tails ?_ fun t ht => ?_
  · rw [← hrem]
    exact h.isRemoval.nodup_removedEdges h.decomp.nodup
  · have : edge t ∈ removedEdges Qs := by
      rw [hrem]
      exact List.mem_map_of_mem ht
    exact (h.removedEdges_mem this : E.Adj t.1 t.2).ne

/-- If `d_{e₀} ≥ max_i r_i`, the longest edge `e₀` is discarded (rule (1)). -/
theorem IsPeelingOn.longest_mem_removedEdges (h : IsPeelingOn b E r d v₁ e₀ Qs)
    (hR : r v₁ ≤ d e₀) : e₀ ∈ removedEdges Qs := by
  obtain ⟨P, hP, he⟩ := List.mem_flatMap.mp ((h.decomp.mem_iff e₀).mpr h.longest_mem)
  obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
  obtain ⟨U, hrule⟩ := h.rule.exists_rule Q hQ
  rcases hrule with ⟨-, -, ht, -⟩ | ⟨hne, -⟩
  · exact ht ▸ List.mem_map_of_mem hQ
  · exact absurd ⟨he, hR⟩ hne

/-- `E = 𝒯 ∪ 𝓕`. -/
theorem IsPeelingOn.keptGraph_sup_removedGraph (h : IsPeelingOn b E r d v₁ e₀ Qs) :
    keptGraph E Qs ⊔ removedGraph Qs = E := by
  ext u v
  simp only [sup_adj, keptGraph, removedGraph, deleteEdges_adj, fromEdgeSet_adj,
    Set.mem_ofPred_eq]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact h1
    · exact h.removedEdges_mem h1
  · intro huv
    by_cases hmem : s(u, v) ∈ removedEdges Qs
    · exact Or.inr ⟨hmem, huv.ne⟩
    · exact Or.inl ⟨huv, hmem⟩

theorem IsPeelingOn.removedGraph_le (h : IsPeelingOn b E r d v₁ e₀ Qs) : removedGraph Qs ≤ E :=
  h.keptGraph_sup_removedGraph ▸ le_sup_right

omit [DecidableEq β] [Fintype β] in
theorem disjoint_keptGraph_removedGraph (E : SimpleGraph V) (Qs : List (Ear V × (V × V))) :
    Disjoint (keptGraph E Qs) (removedGraph Qs) := by
  rw [disjoint_iff_inf_le]
  intro u v huv
  rw [inf_adj, keptGraph, deleteEdges_adj, removedGraph, fromEdgeSet_adj] at huv
  exact absurd huv.2.1 huv.1.2

/-- The deletions exist (generic form): every graph minimally 2-edge-connected relative to the
blocks of a surjective block map has an admissible peeling. -/
theorem exists_isPeelingOn [Fintype V] [DecidableEq V] (hb : Function.Surjective b)
    (hE : E ≤ crossBlockGraph b) (hmin : MinTwoEdgeConnOn b E) (h1 : Fintype.card β ≠ 1)
    (r : V → ℝ) (d : Sym2 V → ℝ) : ∃ v₁ e₀ Qs, IsPeelingOn b E r d v₁ e₀ Qs := by
  classical
  have : Nonempty V := hmin.1.1.nonempty
  obtain ⟨v₁, -, hv₁⟩ := Finset.exists_max_image univ r univ_nonempty
  obtain ⟨Ps, hPs⟩ := exists_isStrictEarDecompOn hb hE hmin h1 (b v₁)
  have hEne : E.edgeFinset.Nonempty := by
    obtain ⟨P, Ps', rfl⟩ := List.exists_cons_of_ne_nil hPs.ne_nil
    refine ⟨edge P.first, mem_edgeFinset.mpr ((hPs.mem_iff _).mp ?_)⟩
    exact List.mem_flatMap.mpr ⟨P, List.mem_cons_self, List.mem_map_of_mem P.first_mem_toList⟩
  obtain ⟨e₀, he₀, hle⟩ := Finset.exists_max_image E.edgeFinset d hEne
  obtain ⟨Qs, hQs, hrule⟩ := exists_isPeelingSeq (r := r) (d := d) (R := r v₁) (e₀ := e₀)
    (empty_subset {b v₁}) hPs.isEarSeq
  refine ⟨v₁, e₀, Qs, fun i => hv₁ i (mem_univ _), hQs ▸ hPs, mem_edgeFinset.mp he₀,
    fun e he => hle e (mem_edgeFinset.mpr he), hrule⟩

end Peeling

/-! ### The peeling relative to a subpartition -/

section Subpartition

variable {X : Finset (Finset ℕ)} {hX : IsSubpartition X} {E : SimpleGraph (X.biUnion id)}
  {r : X.biUnion id → ℝ} {d : Sym2 (X.biUnion id) → ℝ}

/-- The peeling of Definition 4.43 exists for every graph minimally 2-edge-connected relative to
`X`, whatever the positions (`r`, `d`). -/
theorem exists_isPeeling (hE : Parity.IsRelMinTwoEdgeConnected X E) (r : X.biUnion id → ℝ)
    (d : Sym2 (X.biUnion id) → ℝ) : ∃ v₁ e₀ Qs, IsPeeling hX E r d v₁ e₀ Qs := by
  obtain ⟨hle, h1, hmin⟩ := (isRelMinTwoEdgeConnected_iff_on hX).mp hE
  rw [interEdges_eq hX] at hle
  exact exists_isPeelingOn (blockOf_surjective hX) hle hmin (by rwa [Fintype.card_coe]) r d

/-- `𝒯^X ∈ 𝖳^X` (Definition 4.43). -/
theorem IsPeeling.isRelTree {v₁ : X.biUnion id} {e₀ : Sym2 (X.biUnion id)}
    {Qs : List (Ear (X.biUnion id) × (X.biUnion id × X.biUnion id))}
    (hE : E ≤ interEdges X) (h : IsPeeling hX E r d v₁ e₀ Qs) : IsRelTree X (keptGraph E Qs) :=
  IsStrictEarDecomp.isRelTree_keptGraph hE h.decomp h.isRemoval

end Subpartition

end Peeling

end MultipoleBKT

end
