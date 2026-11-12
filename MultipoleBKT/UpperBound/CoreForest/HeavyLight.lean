/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Heavy-light decomposition of a rooted tree (Definition 5.30, Lemma 5.31)

The paper: Definition 5.30 and
Lemma 5.31 ("the proof is standard and is therefore omitted").

Throughout, `T` is a finite tree (`SimpleGraph.IsTree`) on a type `V` and `r : V` is its root.

* `IsParent T r u v`: `u` is the parent of `v`, i.e. a neighbour of `v` closer to the root;
  `IsDesc T r u v`: `v` is a descendant of `u` or `u` itself; `children T r u`,
  `descendants T r u` (the vertex set of the subtree rooted at `u`).
* `parent hT hv`: the parent of a vertex `v ≠ r` (it exists and is unique, `exists_isParent`,
  `IsParent.unique`).
* `IsChildChoice T r h`: `h u` is a child of every internal vertex `u`; `IsHeavyChoice T r h`:
  moreover its subtree is largest (Definition 5.30). The paper breaks ties "arbitrarily", so the
  heavy child is a parameter `h : V → V` and every result below holds for every admissible
  choice (in fact for every child choice); heavy choices exist (`exists_isHeavyChoice`). The
  edge `(u, h u)` is heavy, the other child edges of `u` are light.
* `loc hT r h i`: the vertex reached from `i` by the procedure of Definition 5.30: move upward
  along heavy edges until meeting a light edge (then stop at its parent endpoint) or reaching the
  root (then stop at `r`). The paper applies it to the leaves `i ≠ r`; this is `loc_T`.
* `leaves T`: the vertices of degree one; `pathEdges T u v`: the edges of the unique path of `T`
  between `u` and `v` (`P(u, v)` in Lemma 5.31).

**Lemma 5.31** for every child choice `h` (in particular every heavy choice), with
`L = Leaves(T) ∖ {r}`:

* `lemma_5_31_sqcup` (eq. (5.74)): the sets `P(i, loc_T(i))`, `i ∈ L`, are pairwise disjoint
  and their union is the edge set of `T`;
* `lemma_5_31_boundSV` (eq. (5.75)): `∑_{i ∈ L} dist_T(i, loc_T(i)) = |V| - 1`;
* `lemma_5_31_degree1` (eq. (5.76)): for `i ≠ r`, `|{l ∈ L : loc_T(l) = i}| = deg_T(i) - 2`
  (truncated subtraction, i.e. `max(deg_T(i) - 2, 0)`);
* `lemma_5_31_degree2` (eq. (5.77)): `|{l ∈ L : loc_T(l) = r}| = deg_T(r)`;
* `existsUnique_heavyLeaf`: every vertex `v ≠ r` is a non-terminal vertex of exactly one path
  (Step 3 of the proof of Lemma 5.32).

Proof (the standard one). Every edge is `s(u, v)` with `u` the parent of `v`. Following heavy
children from `v` reaches a unique leaf `ℓ` (the *heavy leaf* of `v`), and the edge `s(u, v)`
lies on `P(ℓ, loc_T(ℓ))` exactly for this `ℓ` (`mem_pathEdges_loc_iff`). The path
`P(ℓ, loc_T(ℓ))` ends with the edge from `loc_T(ℓ)` to a child `c` which is light or a child
of the root (`exists_locWitness`, `locWitness_unique`), and `c ↦ heavy leaf of c` is a bijection
from these children of `i` onto `{l ∈ L : loc_T(l) = i}`.
-/

@[expose] public section

namespace MultipoleBKT

namespace CoreForest

open Finset SimpleGraph

/-! ### Rooted trees -/

section Rooted

variable {V : Type*} (T : SimpleGraph V) (r : V)

/-- `u` is the parent of `v` in `T` rooted at `r`: `u` is a neighbour of `v` closer to `r`. -/
def IsParent (u v : V) : Prop := T.Adj u v ∧ T.dist r u < T.dist r v

/-- `v` is a descendant of `u`, or `u` itself, in `T` rooted at `r`. -/
def IsDesc : V → V → Prop := Relation.ReflTransGen (IsParent T r)

/-- `h` chooses a child `h u` of every internal vertex `u` (a vertex with at least one child). -/
def IsChildChoice (h : V → V) : Prop := ∀ u v, IsParent T r u v → IsParent T r u (h u)

variable {T r}

theorem IsDesc.refl (u : V) : IsDesc T r u u := Relation.ReflTransGen.refl

theorem IsDesc.tail {u v w : V} (h : IsDesc T r u v) (hvw : IsParent T r v w) :
    IsDesc T r u w := Relation.ReflTransGen.tail h hvw

theorem IsDesc.trans {u v w : V} (h : IsDesc T r u v) (h' : IsDesc T r v w) : IsDesc T r u w :=
  Relation.ReflTransGen.trans h h'

theorem IsParent.isDesc {u v : V} (h : IsParent T r u v) : IsDesc T r u v :=
  Relation.ReflTransGen.single h

theorem IsParent.adj {u v : V} (h : IsParent T r u v) : T.Adj u v := h.1

theorem IsParent.dist_lt {u v : V} (h : IsParent T r u v) : T.dist r u < T.dist r v := h.2

theorem IsParent.ne {u v : V} (h : IsParent T r u v) : u ≠ v := h.1.ne

/-- The root has no parent. -/
theorem not_isParent_root (u : V) : ¬ IsParent T r u r := fun h => by
  have := h.2
  rw [dist_self] at this
  exact Nat.not_lt_zero _ this

theorem IsDesc.dist_le {u v : V} (h : IsDesc T r u v) : T.dist r u ≤ T.dist r v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hvw ih => exact ih.trans hvw.2.le

theorem IsDesc.eq_or_dist_lt {u v : V} (h : IsDesc T r u v) :
    u = v ∨ T.dist r u < T.dist r v := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨w, huw, hwv⟩
  · exact Or.inl h.symm
  · exact Or.inr ((show IsDesc T r u w from huw).dist_le.trans_lt hwv.2)

theorem IsDesc.antisymm {u v : V} (h : IsDesc T r u v) (h' : IsDesc T r v u) : u = v := by
  rcases h.eq_or_dist_lt with h1 | h1
  · exact h1
  · exact absurd h'.dist_le (not_le.mpr h1)

/-- Nothing but the root is an ancestor of the root. -/
theorem IsDesc.eq_root {u : V} (h : IsDesc T r u r) : u = r := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨w, -, hw⟩
  · exact h.symm
  · exact absurd hw (not_isParent_root w)

/-- `IsDesc u w` with `u ≠ w` ends with a parent step. -/
theorem IsDesc.exists_isParent_of_ne {u w : V} (h : IsDesc T r u w) (hne : u ≠ w) :
    ∃ v, IsDesc T r u v ∧ IsParent T r v w := by
  rcases Relation.ReflTransGen.cases_tail h with h | h
  · exact absurd h.symm hne
  · exact h

variable (hT : T.IsTree)
include hT

/-- Two neighbours in a tree: one is the parent of the other. -/
theorem isParent_or_isParent_of_adj {u v : V} (huv : T.Adj u v) :
    IsParent T r u v ∨ IsParent T r v u := by
  rcases hT.dist_eq_dist_add_one_of_adj r huv with h | h
  · exact Or.inr ⟨huv.symm, by omega⟩
  · exact Or.inl ⟨huv, by omega⟩

theorem IsParent.dist_eq {u v : V} (h : IsParent T r u v) : T.dist r v = T.dist r u + 1 := by
  rcases hT.dist_eq_dist_add_one_of_adj r h.1 with h' | h'
  · exact absurd h.2 (by omega)
  · exact h'

/-- Every vertex but the root has a parent. -/
theorem exists_isParent {v : V} (hv : v ≠ r) : ∃ u, IsParent T r u v := by
  obtain ⟨p, -, hlen⟩ := hT.connected.exists_path_of_dist r v
  have hnil : ¬ p.Nil := fun h => hv h.eq.symm
  refine ⟨p.penultimate, p.adj_penultimate hnil, ?_⟩
  have hpos : 0 < T.dist r v := hT.connected.pos_dist_of_ne (Ne.symm hv)
  calc T.dist r p.penultimate ≤ p.dropLast.length := dist_le _
    _ = p.length - 1 := p.length_dropLast
    _ < T.dist r v := by omega

/-- The parent is unique. -/
theorem IsParent.unique {u u' v : V} (h : IsParent T r u v) (h' : IsParent T r u' v) :
    u = u' := by
  have key : ∀ {w : V}, IsParent T r w v → ∃ q : T.Walk r v, q.IsPath ∧ q.penultimate = w := by
    intro w hw
    obtain ⟨p, hp, hlen⟩ := hT.connected.exists_path_of_dist r w
    have hv : v ∉ p.support := by
      intro hv
      classical
      have h1 : T.dist r v ≤ (p.takeUntil v hv).length := dist_le _
      have h2 : (p.takeUntil v hv).length ≤ p.length := p.length_takeUntil_le_length hv
      have h3 := hw.2
      omega
    exact ⟨p.concat hw.1, hp.concat hv hw.1, p.penultimate_concat hw.1⟩
  obtain ⟨q, hq, rfl⟩ := key h
  obtain ⟨q', hq', rfl⟩ := key h'
  rw [(hT.existsUnique_path r v).unique hq hq']

/-- Every vertex is a descendant of the root. -/
theorem isDesc_root (v : V) : IsDesc T r r v := by
  induction hd : T.dist r v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = r
    · rw [hv]
      exact IsDesc.refl r
    · obtain ⟨u, hu⟩ := exists_isParent hT hv
      exact (ih _ (hd ▸ hu.2) u rfl).tail hu

/-- The ancestors of a vertex are linearly ordered. -/
theorem IsDesc.total {a b v : V} (ha : IsDesc T r a v) (hb : IsDesc T r b v) :
    IsDesc T r a b ∨ IsDesc T r b a := by
  induction hd : T.dist r v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hav : a = v
    · subst hav
      exact Or.inr hb
    by_cases hbv : b = v
    · subst hbv
      exact Or.inl ha
    obtain ⟨u, hau, huv⟩ := ha.exists_isParent_of_ne hav
    obtain ⟨u', hbu', hu'v⟩ := hb.exists_isParent_of_ne hbv
    obtain rfl := huv.unique hT hu'v
    exact ih _ (hd ▸ huv.2) hau hbu' rfl

/-- If `w` is an ancestor of `v` and `u` is the parent of `v`, then `w = v` or `w` is an ancestor
of `u`. -/
theorem IsDesc.eq_or_isDesc_of_isParent {w u v : V} (h : IsDesc T r w v)
    (huv : IsParent T r u v) : w = v ∨ IsDesc T r w u := by
  by_cases hwv : w = v
  · exact Or.inl hwv
  obtain ⟨u', hwu', hu'v⟩ := h.exists_isParent_of_ne hwv
  exact Or.inr (hu'v.unique hT huv ▸ hwu')

omit hT in
/-- The parent of a vertex `v ≠ r` of a tree `T` rooted at `r`. -/
noncomputable def parent (hT : T.IsTree) {v : V} (hv : v ≠ r) : V :=
  (exists_isParent hT hv).choose

theorem isParent_parent {v : V} (hv : v ≠ r) : IsParent T r (parent hT hv) v :=
  (exists_isParent hT hv).choose_spec

theorem parent_eq_iff {u v : V} (hv : v ≠ r) : parent hT hv = u ↔ IsParent T r u v :=
  ⟨fun h => h ▸ isParent_parent hT hv, fun h => (isParent_parent hT hv).unique hT h⟩

end Rooted

/-! ### Children, subtrees, degrees and leaves -/

section Finite

variable {V : Type*} [Fintype V] (T : SimpleGraph V) (r : V)

open scoped Classical in
/-- The children of `u` in `T` rooted at `r`. -/
noncomputable def children (u : V) : Finset V := univ.filter (IsParent T r u)

open scoped Classical in
/-- The vertex set of the subtree of `T` rooted at `u` (`u` and its descendants). -/
noncomputable def descendants (u : V) : Finset V := univ.filter (IsDesc T r u)

/-- `h` is a heavy choice (Definition 5.30): for every internal vertex `u`, `h u` is a child of `u`
whose subtree is largest (ties broken arbitrarily). -/
def IsHeavyChoice (h : V → V) : Prop :=
  IsChildChoice T r h ∧
    ∀ u c, IsParent T r u c → (descendants T r c).card ≤ (descendants T r (h u)).card

/-- The leaves of `T`: the vertices of degree one. -/
noncomputable def leaves [DecidableRel T.Adj] : Finset V := univ.filter fun v => T.degree v = 1

open scoped Classical in
/-- `P(u, v)` (Lemma 5.31): the edges of the unique path of the tree `T` between `u` and `v`. -/
noncomputable def pathEdges (u v : V) : Finset (Sym2 V) :=
  univ.filter fun e => ∃ p : T.Walk u v, p.IsPath ∧ e ∈ p.edges

variable {T r}

theorem mem_children {u v : V} : v ∈ children T r u ↔ IsParent T r u v := by
  simp [children]

theorem mem_descendants {u v : V} : v ∈ descendants T r u ↔ IsDesc T r u v := by
  simp [descendants]

theorem IsHeavyChoice.isChildChoice {h : V → V} (hh : IsHeavyChoice T r h) :
    IsChildChoice T r h := hh.1

theorem mem_leaves [DecidableRel T.Adj] {v : V} : v ∈ leaves T ↔ T.degree v = 1 := by
  simp [leaves]

/-- Heavy choices exist. -/
theorem exists_isHeavyChoice : ∃ h, IsHeavyChoice T r h := by
  classical
  have hex : ∀ u, ∃ c, (∃ v, IsParent T r u v) → IsParent T r u c ∧
      ∀ c', IsParent T r u c' → (descendants T r c').card ≤ (descendants T r c).card := by
    intro u
    by_cases hu : (children T r u).Nonempty
    · obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image (children T r u)
        (fun c => (descendants T r c).card) hu
      exact ⟨c, fun _ => ⟨mem_children.1 hc, fun c' hc' => hmax c' (mem_children.2 hc')⟩⟩
    · refine ⟨u, fun ⟨v, hv⟩ => absurd ⟨v, mem_children.2 hv⟩ hu⟩
  choose h hh using hex
  exact ⟨h, fun u v huv => (hh u ⟨v, huv⟩).1, fun u c huc => (hh u ⟨c, huc⟩).2 c huc⟩

theorem mem_pathEdges {u v : V} {e : Sym2 V} :
    e ∈ pathEdges T u v ↔ ∃ p : T.Walk u v, p.IsPath ∧ e ∈ p.edges := by
  simp [pathEdges]

section Tree

variable (hT : T.IsTree)
include hT

/-- In a tree, `P(u, v)` is the edge set of any path from `u` to `v`. -/
theorem mem_pathEdges_iff_of_isPath {u v : V} {p : T.Walk u v} (hp : p.IsPath) {e : Sym2 V} :
    e ∈ pathEdges T u v ↔ e ∈ p.edges := by
  rw [mem_pathEdges]
  refine ⟨fun ⟨q, hq, he⟩ => ?_, fun he => ⟨p, hp, he⟩⟩
  rwa [(hT.existsUnique_path u v).unique hq hp] at he

omit hT in
theorem pathEdges_subset_edgeFinset [DecidableRel T.Adj] (u v : V) :
    pathEdges T u v ⊆ T.edgeFinset := by
  intro e he
  obtain ⟨p, -, he⟩ := mem_pathEdges.1 he
  rw [mem_edgeFinset]
  exact p.edges_subset_edgeSet he

/-- `|P(u, v)| = dist_T(u, v)`. -/
theorem card_pathEdges (u v : V) : (pathEdges T u v).card = T.dist u v := by
  classical
  obtain ⟨p, hp, hlen⟩ := hT.connected.exists_path_of_dist u v
  have : pathEdges T u v = p.edges.toFinset := by
    ext e
    rw [mem_pathEdges_iff_of_isPath hT hp, List.mem_toFinset]
  rw [this, List.toFinset_card_of_nodup (Walk.edges_nodup_of_support_nodup hp.support_nodup),
    Walk.length_edges, hlen]

omit [Fintype V] in
/-- The path from a vertex `x` up to an ancestor `w` consists of the parent edges `s(u, v)` with
`v` between `x` and `w` (`w` excluded). -/
theorem exists_isPath_of_isDesc {w x : V} (hwx : IsDesc T r w x) :
    ∃ p : T.Walk x w, p.IsPath ∧ (∀ y ∈ p.support, IsDesc T r y x) ∧
      ∀ e, e ∈ p.edges ↔
        ∃ u v, IsParent T r u v ∧ IsDesc T r w u ∧ IsDesc T r v x ∧ e = s(u, v) := by
  induction hwx with
  | refl =>
    refine ⟨Walk.nil, Walk.IsPath.nil, fun y hy => ?_, fun e => ?_⟩
    · rw [Walk.support_nil, List.mem_singleton] at hy
      exact hy ▸ IsDesc.refl _
    · simp only [Walk.edges_nil, List.not_mem_nil, false_iff]
      rintro ⟨u, v, huv, hwu, hvw, -⟩
      have h1 := hwu.dist_le
      have h2 := hvw.dist_le
      have h3 := huv.2
      omega
  | @tail u x hwu hux ih =>
    obtain ⟨p, hp, hsupp, hedges⟩ := ih
    have hxp : x ∉ p.support := fun hx => by
      have h1 := (hsupp x hx).dist_le
      have h2 := hux.2
      omega
    refine ⟨Walk.cons hux.1.symm p, hp.cons hxp, fun y hy => ?_, fun e => ?_⟩
    · rw [Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact IsDesc.refl _
      · exact (hsupp y hy).tail hux
    · rw [Walk.edges_cons, List.mem_cons, hedges]
      constructor
      · rintro (rfl | ⟨u', v', hu'v', hwu', hv'u, rfl⟩)
        · exact ⟨u, x, hux, hwu, IsDesc.refl x, Sym2.eq_swap⟩
        · exact ⟨u', v', hu'v', hwu', hv'u.tail hux, rfl⟩
      · rintro ⟨u', v', hu'v', hwu', hv'x, rfl⟩
        rcases hv'x.eq_or_isDesc_of_isParent hT hux with rfl | hv'u
        · left
          rw [hu'v'.unique hT hux]
          exact Sym2.eq_swap
        · exact Or.inr ⟨u', v', hu'v', hwu', hv'u, rfl⟩

/-- `P(x, w)` for an ancestor `w` of `x`. -/
theorem mem_pathEdges_of_isDesc {w x : V} (hwx : IsDesc T r w x) {e : Sym2 V} :
    e ∈ pathEdges T x w ↔
      ∃ u v, IsParent T r u v ∧ IsDesc T r w u ∧ IsDesc T r v x ∧ e = s(u, v) := by
  obtain ⟨p, hp, -, hedges⟩ := exists_isPath_of_isDesc hT hwx
  rw [mem_pathEdges_iff_of_isPath hT hp, hedges]

/-- The neighbours of `u` are its children and, for `u ≠ r`, its parent. -/
theorem degree_eq [DecidableEq V] [DecidableRel T.Adj] (u : V) :
    T.degree u = (children T r u).card + if u = r then 0 else 1 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  split_ifs with hu
  · subst hu
    congr 1
    ext v
    rw [mem_neighborFinset, mem_children]
    refine ⟨fun h => ?_, fun h => h.1⟩
    rcases isParent_or_isParent_of_adj hT h with h | h
    · exact h
    · exact absurd h (not_isParent_root v)
  · have hset : T.neighborFinset u = insert (parent hT hu) (children T r u) := by
      ext v
      rw [mem_neighborFinset, Finset.mem_insert, mem_children]
      refine ⟨fun h => ?_, ?_⟩
      · rcases isParent_or_isParent_of_adj hT h with h | h
        · exact Or.inr h
        · exact Or.inl ((parent_eq_iff hT hu).2 h).symm
      · rintro (rfl | h)
        · exact (isParent_parent hT hu).1.symm
        · exact h.1
    rw [hset, Finset.card_insert_of_notMem, add_comm]
    rw [mem_children]
    intro h
    have h1 := h.2
    have h2 := (isParent_parent hT hu).2
    omega

/-- A vertex `v ≠ r` is a leaf iff it has no child. -/
theorem mem_leaves_iff_of_ne [DecidableEq V] [DecidableRel T.Adj] {v : V} (hv : v ≠ r) :
    v ∈ leaves T ↔ ∀ c, ¬ IsParent T r v c := by
  rw [mem_leaves, degree_eq (r := r) hT, ite_eq_right hv, Nat.add_eq_right, Finset.card_eq_zero,
    Finset.eq_empty_iff_forall_notMem]
  simp only [mem_children]

end Tree

end Finite

/-! ### Heavy chains and the map `loc_T` -/

section Loc

variable {V : Type*} [DecidableEq V] {T : SimpleGraph V}

/-- `loc_T(i)` (Definition 5.30): starting at `i`, move upward along heavy edges `(u, h u)` until
meeting a light edge, and stop at its parent endpoint, or until reaching the root `r`, and stop
there. The paper applies it to the leaves `i ≠ r` of `T`. -/
noncomputable def loc (hT : T.IsTree) (r : V) (h : V → V) (i : V) : V :=
  if hi : i = r then r
  else if h (parent hT hi) = i then loc hT r h (parent hT hi) else parent hT hi
termination_by T.dist r i
decreasing_by exact (isParent_parent hT hi).2

variable (T) (r : V) (h : V → V)

/-- `(u, v)` is a heavy edge: `u` is the parent of `v` and `v = h u` is its heavy child. -/
def IsHeavyStep (u v : V) : Prop := IsParent T r u v ∧ h u = v

/-- `ℓ` is reached from `c` by moving down along heavy edges. -/
def IsHeavyChain : V → V → Prop := Relation.ReflTransGen (IsHeavyStep T r h)

/-- `(w, c)` is the last edge of the path of Definition 5.30 started at `i`: `w` is the parent of
`c`, the path from `c` down to `i` is made of heavy edges, and `(w, c)` is light or `w = r`. -/
def IsLocWitness (i w c : V) : Prop :=
  IsParent T r w c ∧ IsHeavyChain T r h c i ∧ (w = r ∨ h w ≠ c)

variable {T r h}

omit [DecidableEq V] in
theorem IsHeavyChain.isDesc {c ℓ : V} (hc : IsHeavyChain T r h c ℓ) : IsDesc T r c ℓ :=
  Relation.ReflTransGen.mono (fun a b (hs : IsHeavyStep T r h a b) => hs.1) _ _ hc

theorem loc_root (hT : T.IsTree) : loc hT r h r = r := by
  rw [loc, dite_eq_left rfl]

theorem loc_of_heavy (hT : T.IsTree) {i : V} (hi : i ≠ r) (hh : h (parent hT hi) = i) :
    loc hT r h i = loc hT r h (parent hT hi) := by
  rw [loc, dite_eq_right hi, ite_eq_left hh]

theorem loc_of_light (hT : T.IsTree) {i : V} (hi : i ≠ r) (hh : h (parent hT hi) ≠ i) :
    loc hT r h i = parent hT hi := by
  rw [loc, dite_eq_right hi, ite_eq_right hh]

variable (hT : T.IsTree)
include hT

/-- The procedure of Definition 5.30 ends with an edge `(loc_T(i), c)` as in `IsLocWitness`. -/
theorem exists_locWitness {i : V} (hi : i ≠ r) : ∃ c, IsLocWitness T r h i (loc hT r h i) c := by
  induction hd : T.dist r i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    have hp := isParent_parent hT hi
    by_cases hh : h (parent hT hi) = i
    · rw [loc_of_heavy hT hi hh]
      by_cases hpr : parent hT hi = r
      · refine ⟨i, ?_, Relation.ReflTransGen.refl, Or.inl ?_⟩
        · rw [hpr, loc_root hT]
          rw [hpr] at hp
          exact hp
        · rw [hpr, loc_root hT]
      · obtain ⟨c, hwc, hci, hcond⟩ := ih _ (hd ▸ hp.2) hpr rfl
        exact ⟨c, hwc, hci.tail ⟨hp, hh⟩, hcond⟩
    · rw [loc_of_light hT hi hh]
      exact ⟨i, hp, Relation.ReflTransGen.refl, Or.inr hh⟩

omit [DecidableEq V] in
/-- The witness edge of `IsLocWitness` is unique. -/
theorem locWitness_unique {i w c w' c' : V} (h₁ : IsLocWitness T r h i w c)
    (h₂ : IsLocWitness T r h i w' c') : w = w' ∧ c = c' := by
  induction hd : T.dist r i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    -- a witness edge strictly above `i` passes through the parent `x` of `i`, along `(x, i)` heavy
    have key : ∀ {w c : V}, IsLocWitness T r h i w c → c ≠ i →
        ∃ x, IsParent T r x i ∧ h x = i ∧ IsLocWitness T r h x w c := by
      intro w c hw hci
      obtain ⟨hwc, hch, hcond⟩ := hw
      rcases Relation.ReflTransGen.cases_tail hch with h' | ⟨x, hcx, hxi, hhx⟩
      · exact absurd h'.symm hci
      · exact ⟨x, hxi, hhx, hwc, hcx, hcond⟩
    -- a witness edge `(w, i)` excludes a witness edge strictly above `i`
    have bottom : ∀ {w w' c' : V}, IsLocWitness T r h i w i → IsLocWitness T r h i w' c' →
        c' ≠ i → False := by
      intro w w' c' h₁ h₂ hc'
      obtain ⟨x, hxi, hhx, hw'c', hc'x, -⟩ := key h₂ hc'
      have hwx : w = x := h₁.1.unique hT hxi
      rcases h₁.2.2 with hr | hne
      · have hxr : x = r := hwx ▸ hr
        have hdesc : IsDesc T r c' r := by
          have := hc'x.isDesc
          rwa [hxr] at this
        rw [hdesc.eq_root] at hw'c'
        exact not_isParent_root w' hw'c'
      · exact hne (hwx ▸ hhx)
    by_cases hc : c = i
    · rw [hc] at h₁
      by_cases hc' : c' = i
      · rw [hc'] at h₂
        exact ⟨h₁.1.unique hT h₂.1, hc.trans hc'.symm⟩
      · exact (bottom h₁ h₂ hc').elim
    · by_cases hc' : c' = i
      · rw [hc'] at h₂
        exact (bottom h₂ h₁ hc).elim
      · obtain ⟨x, hxi, -, hx⟩ := key h₁ hc
        obtain ⟨x', hx'i, -, hx'⟩ := key h₂ hc'
        obtain rfl := hxi.unique hT hx'i
        exact ih _ (hd ▸ hxi.2) hx hx' rfl

theorem loc_eq_of_locWitness {i w c : V} (hw : IsLocWitness T r h i w c) : loc hT r h i = w := by
  have hi : i ≠ r := by
    intro hir
    have := hw.2.1.isDesc
    rw [hir] at this
    rw [this.eq_root] at hw
    exact not_isParent_root w hw.1
  obtain ⟨c', hc'⟩ := exists_locWitness hT (h := h) hi
  exact (locWitness_unique hT hc' hw).1

omit [DecidableEq V] in
/-- Following heavy children reaches a leaf. -/
theorem exists_isHeavyChain_leaf [Fintype V] (hh : IsChildChoice T r h) (c : V) :
    ∃ ℓ, IsHeavyChain T r h c ℓ ∧ ∀ x, ¬ IsParent T r ℓ x := by
  have hlt : ∀ v, T.dist r v < Fintype.card V := fun v => by
    obtain ⟨p, hp, hlen⟩ := hT.connected.exists_path_of_dist r v
    exact hlen ▸ hp.length_lt
  induction hn : Fintype.card V - T.dist r c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases hc : ∃ x, IsParent T r c x
    · obtain ⟨x, hx⟩ := hc
      have hhc := hh c x hx
      have h1 := hhc.dist_eq hT
      have h2 := hlt (h c)
      obtain ⟨ℓ, hℓ, hleaf⟩ := ih _ (by omega) (h c) rfl
      exact ⟨ℓ, Relation.ReflTransGen.head ⟨hhc, rfl⟩ hℓ, hleaf⟩
    · push Not at hc
      exact ⟨c, Relation.ReflTransGen.refl, hc⟩

omit hT [DecidableEq V] in
/-- The heavy chain from a vertex ends at a unique leaf. -/
theorem IsHeavyChain.eq_of_leaf {c ℓ ℓ' : V} (h₁ : IsHeavyChain T r h c ℓ)
    (h₂ : IsHeavyChain T r h c ℓ') (hℓ : ∀ x, ¬ IsParent T r ℓ x)
    (hℓ' : ∀ x, ¬ IsParent T r ℓ' x) : ℓ = ℓ' := by
  induction h₁ using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rcases Relation.ReflTransGen.cases_head h₂ with h | ⟨d, hd, -⟩
    · exact h
    · exact absurd hd.1 (hℓ d)
  | @head a d had hdℓ ih =>
    rcases Relation.ReflTransGen.cases_head h₂ with h | ⟨d', had', hd'ℓ'⟩
    · rw [← h] at hℓ'
      exact absurd had.1 (hℓ' d)
    · have hdd : d = d' := had.2.symm.trans had'.2
      rw [← hdd] at hd'ℓ'
      exact ih hd'ℓ'

omit [DecidableEq V] in
/-- Every edge `(x, y)` between a vertex `v` and a vertex `ℓ` of its heavy chain is heavy. -/
theorem IsHeavyChain.heavy_of_isParent {v ℓ x y : V} (hc : IsHeavyChain T r h v ℓ)
    (hxy : IsParent T r x y) (hvx : IsDesc T r v x) (hyℓ : IsDesc T r y ℓ) : h x = y := by
  induction hc with
  | refl =>
    have h1 := hvx.dist_le
    have h2 := hxy.2
    have h3 := hyℓ.dist_le
    omega
  | @tail m ℓ _ hmℓ ih =>
    rcases hyℓ.eq_or_isDesc_of_isParent hT hmℓ.1 with rfl | hym
    · rw [hxy.unique hT hmℓ.1]
      exact hmℓ.2
    · exact ih hym

omit [DecidableEq V] in
/-- A heavy chain restricts to its intermediate vertices. -/
theorem IsHeavyChain.of_isDesc {c ℓ v : V} (hc : IsHeavyChain T r h c ℓ)
    (hcv : IsDesc T r c v) (hvℓ : IsDesc T r v ℓ) : IsHeavyChain T r h v ℓ := by
  induction hc using Relation.ReflTransGen.head_induction_on generalizing v with
  | refl =>
    rw [← hcv.antisymm hvℓ]
    exact Relation.ReflTransGen.refl
  | @head a d had hdℓ ih =>
    by_cases hva : v = a
    · rw [hva]
      exact Relation.ReflTransGen.head had hdℓ
    · rcases (show IsHeavyChain T r h d ℓ from hdℓ).isDesc.total hT hvℓ with hdv | hvd
      · exact ih hdv hvℓ
      · rcases hvd.eq_or_isDesc_of_isParent hT had.1 with rfl | hva'
        · exact hdℓ
        · exact absurd (hva'.antisymm hcv) hva

/-- **The edges of `P(ℓ, loc_T(ℓ))`.** For `ℓ ≠ r`, the parent edge `s(u, v)` of `v` lies on the
path from `ℓ` to `loc_T(ℓ)` iff `ℓ` is on the heavy chain of `v`. -/
theorem mem_pathEdges_loc_iff [Fintype V] {ℓ : V} (hℓ : ℓ ≠ r) {u v : V}
    (huv : IsParent T r u v) :
    s(u, v) ∈ pathEdges T ℓ (loc hT r h ℓ) ↔ IsHeavyChain T r h v ℓ := by
  obtain ⟨c, hwc, hcℓ, hcond⟩ := exists_locWitness hT (h := h) hℓ
  have hlocℓ : IsDesc T r (loc hT r h ℓ) ℓ := hwc.isDesc.trans hcℓ.isDesc
  rw [mem_pathEdges_of_isDesc hT hlocℓ]
  constructor
  · rintro ⟨u', v', hu'v', hlu', hv'ℓ, he⟩
    have huu : u = u' ∧ v = v' := by
      rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, h2⟩
      · rw [h1, h2] at huv
        have := huv.2
        have := hu'v'.2
        omega
    obtain ⟨rfl, rfl⟩ := huu
    refine hcℓ.of_isDesc hT ?_ hv'ℓ
    rcases hcℓ.isDesc.total hT hv'ℓ with hcv | hvc
    · exact hcv
    · rcases hvc.eq_or_isDesc_of_isParent hT hwc with rfl | hvl
      · exact IsDesc.refl _
      · exfalso
        have := hvl.dist_le
        have := hlu'.dist_le
        have := huv.2
        omega
  · intro hvℓ
    refine ⟨u, v, huv, ?_, hvℓ.isDesc, rfl⟩
    have hcase : IsDesc T r c v ∨ v = c ∨ IsDesc T r v (loc hT r h ℓ) := by
      rcases hcℓ.isDesc.total hT hvℓ.isDesc with hcv | hvc
      · exact Or.inl hcv
      · exact Or.inr (hvc.eq_or_isDesc_of_isParent hT hwc)
    rcases hcase with hcv | rfl | hvl
    · rcases hcv.eq_or_isDesc_of_isParent hT huv with rfl | hcu
      · rw [hwc.unique hT huv]
        exact IsDesc.refl _
      · exact hwc.isDesc.trans hcu
    · rw [hwc.unique hT huv]
      exact IsDesc.refl _
    · exfalso
      have hheavy := hvℓ.heavy_of_isParent hT hwc hvl hcℓ.isDesc
      rcases hcond with hr | hne
      · rw [hr] at hvl
        rw [hvl.eq_root] at huv
        exact not_isParent_root u huv
      · exact hne hheavy

omit [DecidableEq V] in
/-- Every edge of a rooted tree is the edge between a vertex and its parent. -/
theorem exists_isParent_of_mem_edgeSet {e : Sym2 V} (he : e ∈ T.edgeSet) :
    ∃ u v, IsParent T r u v ∧ e = s(u, v) := by
  induction e using Sym2.ind with
  | _ a b =>
    rcases isParent_or_isParent_of_adj (r := r) hT ((mem_edgeSet T).1 he) with h | h
    · exact ⟨a, b, h, rfl⟩
    · exact ⟨b, a, h, Sym2.eq_swap⟩

/-- **The paths partition the non-root vertices**: every vertex `v ≠ r` lies on the path of exactly
one leaf `ℓ ≠ r` as a non-terminal vertex (its parent edge lies on `P(ℓ, loc_T(ℓ))`): the leaf at
the end of the heavy chain of `v` (used in Step 3 of the proof of Lemma 5.32). -/
theorem existsUnique_heavyLeaf [Fintype V] [DecidableRel T.Adj] (hh : IsChildChoice T r h)
    {v : V} (hv : v ≠ r) :
    ∃! ℓ, ℓ ∈ (leaves T).erase r ∧ IsHeavyChain T r h v ℓ := by
  obtain ⟨ℓ, hvℓ, hℓ⟩ := exists_isHeavyChain_leaf hT hh v
  have hℓr : ℓ ≠ r := by
    intro hℓr
    have := hvℓ.isDesc
    rw [hℓr] at this
    exact hv this.eq_root
  refine ⟨ℓ, ⟨?_, hvℓ⟩, fun ℓ' ⟨hℓ', hvℓ'⟩ => ?_⟩
  · rw [Finset.mem_erase, mem_leaves_iff_of_ne hT hℓr]
    exact ⟨hℓr, hℓ⟩
  · rw [Finset.mem_erase] at hℓ'
    exact hvℓ'.eq_of_leaf hvℓ ((mem_leaves_iff_of_ne hT hℓ'.1).1 hℓ'.2) hℓ

/-- **Lemma 5.31, eq. (5.74)**: for every child choice `h` (in particular every heavy choice of
Definition 5.30), the paths `P(i, loc_T(i))`, `i ∈ Leaves(T) ∖ {r}`, are pairwise disjoint and
their union is the edge set of `T`. -/
theorem lemma_5_31_sqcup [Fintype V] [DecidableRel T.Adj] (hh : IsChildChoice T r h) :
    (((leaves T).erase r : Finset V) : Set V).PairwiseDisjoint
        (fun i => pathEdges T i (loc hT r h i)) ∧
      T.edgeFinset = ((leaves T).erase r).biUnion fun i => pathEdges T i (loc hT r h i) := by
  have hleaf : ∀ {ℓ : V}, ℓ ∈ (leaves T).erase r → ℓ ≠ r ∧ ∀ x, ¬ IsParent T r ℓ x := by
    intro ℓ hℓ
    rw [Finset.mem_erase] at hℓ
    exact ⟨hℓ.1, (mem_leaves_iff_of_ne hT hℓ.1).1 hℓ.2⟩
  refine ⟨fun i hi j hj hij => ?_, ?_⟩
  · rw [Function.onFun, Finset.disjoint_left]
    intro e hei hej
    have he : e ∈ T.edgeSet :=
      (mem_edgeFinset (G := T)).1 (pathEdges_subset_edgeFinset (T := T) _ _ hei)
    obtain ⟨u, v, huv, rfl⟩ := exists_isParent_of_mem_edgeSet (r := r) hT he
    have hi' := hleaf (Finset.mem_coe.1 hi)
    have hj' := hleaf (Finset.mem_coe.1 hj)
    rw [mem_pathEdges_loc_iff hT hi'.1 huv] at hei
    rw [mem_pathEdges_loc_iff hT hj'.1 huv] at hej
    exact hij (hei.eq_of_leaf hej hi'.2 hj'.2)
  · ext e
    rw [Finset.mem_biUnion]
    constructor
    · intro he
      obtain ⟨u, v, huv, rfl⟩ :=
        exists_isParent_of_mem_edgeSet (r := r) hT ((mem_edgeFinset (G := T)).1 he)
      obtain ⟨ℓ, hvℓ, hℓ⟩ := exists_isHeavyChain_leaf hT hh v
      have hℓr : ℓ ≠ r := by
        intro hℓr
        have := hvℓ.isDesc
        rw [hℓr] at this
        rw [this.eq_root] at huv
        exact not_isParent_root u huv
      refine ⟨ℓ, ?_, (mem_pathEdges_loc_iff hT hℓr huv).2 hvℓ⟩
      rw [Finset.mem_erase, mem_leaves_iff_of_ne hT hℓr]
      exact ⟨hℓr, hℓ⟩
    · rintro ⟨i, -, he⟩
      exact pathEdges_subset_edgeFinset (T := T) _ _ he

/-- **Lemma 5.31, eq. (5.75)**: `∑_{i ∈ Leaves(T) ∖ {r}} dist_T(i, loc_T(i)) = |V| - 1`. -/
theorem lemma_5_31_boundSV [Fintype V] [DecidableRel T.Adj] (hh : IsChildChoice T r h) :
    ∑ i ∈ (leaves T).erase r, T.dist i (loc hT r h i) = Fintype.card V - 1 := by
  obtain ⟨hdisj, heq⟩ := lemma_5_31_sqcup hT hh
  have hcard := hT.card_edgeFinset
  calc ∑ i ∈ (leaves T).erase r, T.dist i (loc hT r h i)
      = ∑ i ∈ (leaves T).erase r, (pathEdges T i (loc hT r h i)).card :=
        Finset.sum_congr rfl fun i _ => (card_pathEdges hT _ _).symm
    _ = (((leaves T).erase r).biUnion fun i => pathEdges T i (loc hT r h i)).card :=
        (Finset.card_biUnion hdisj).symm
    _ = T.edgeFinset.card := by rw [← heq]
    _ = Fintype.card V - 1 := by omega

/-- The leaves `l ≠ r` with `loc_T(l) = i` correspond to the children `c` of `i` with `(i, c)`
light or `i = r` (through the heavy leaf of `c`). -/
theorem card_filter_loc_eq [Fintype V] [DecidableRel T.Adj] (hh : IsChildChoice T r h) (i : V) :
    (((leaves T).erase r).filter fun l => loc hT r h l = i).card =
      ((children T r i).filter fun c => i = r ∨ h i ≠ c).card := by
  classical
  choose hl hlchain hlleaf using exists_isHeavyChain_leaf hT hh
  have hlr : ∀ {u c : V}, IsParent T r u c → hl c ≠ r := by
    intro u c huc hcr
    have := (hlchain c).isDesc
    rw [hcr] at this
    rw [this.eq_root] at huc
    exact not_isParent_root u huc
  symm
  refine Finset.card_bij (fun c _ => hl c) ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter, mem_children] at hc
    have hw : IsLocWitness T r h (hl c) i c := ⟨hc.1, hlchain c, hc.2⟩
    rw [Finset.mem_filter, Finset.mem_erase, mem_leaves_iff_of_ne hT (hlr hc.1)]
    exact ⟨⟨hlr hc.1, hlleaf c⟩, loc_eq_of_locWitness hT hw⟩
  · intro c₁ hc₁ c₂ hc₂ heq
    rw [Finset.mem_filter, mem_children] at hc₁ hc₂
    have hw₁ : IsLocWitness T r h (hl c₁) i c₁ := ⟨hc₁.1, hlchain c₁, hc₁.2⟩
    have hw₂ : IsLocWitness T r h (hl c₂) i c₂ := ⟨hc₂.1, hlchain c₂, hc₂.2⟩
    rw [heq] at hw₁
    exact (locWitness_unique hT hw₁ hw₂).2
  · intro ℓ hℓ
    rw [Finset.mem_filter, Finset.mem_erase] at hℓ
    obtain ⟨⟨hℓr, hℓleaf⟩, hloc⟩ := hℓ
    obtain ⟨c, hwc, hcℓ, hcond⟩ := exists_locWitness hT (h := h) hℓr
    rw [hloc] at hwc hcond
    refine ⟨c, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_children]
      exact ⟨hwc, hcond⟩
    · exact (hlchain c).eq_of_leaf hcℓ (hlleaf c) ((mem_leaves_iff_of_ne hT hℓr).1 hℓleaf)

/-- **Lemma 5.31, eq. (5.76)**: for `i ≠ r`, `|{l ∈ Leaves(T) ∖ {r} : loc_T(l) = i}|` is
`deg_T(i) - 2` in truncated subtraction, i.e. `max(deg_T(i) - 2, 0)`. -/
theorem lemma_5_31_degree1 [Fintype V] [DecidableRel T.Adj] (hh : IsChildChoice T r h) {i : V}
    (hi : i ≠ r) :
    (((leaves T).erase r).filter fun l => loc hT r h l = i).card = T.degree i - 2 := by
  rw [card_filter_loc_eq hT hh, degree_eq hT i, ite_eq_right hi]
  have hset : (children T r i).filter (fun c => i = r ∨ h i ≠ c) = (children T r i).erase (h i) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_erase, hi, false_or]
    exact ⟨fun h' => ⟨Ne.symm h'.2, h'.1⟩, fun h' => ⟨h'.2, Ne.symm h'.1⟩⟩
  rw [hset]
  by_cases hne : (children T r i).Nonempty
  · obtain ⟨c, hc⟩ := hne
    rw [Finset.card_erase_of_mem (mem_children.2 (hh i c (mem_children.1 hc)))]
    have := Finset.card_pos.2 ⟨c, hc⟩
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

/-- Eq. (5.76) with the paper's `max(deg_T(i) - 2, 0)`, in `ℤ`. -/
theorem lemma_5_31_degree1' [Fintype V] [DecidableRel T.Adj] (hh : IsChildChoice T r h) {i : V}
    (hi : i ≠ r) :
    ((((leaves T).erase r).filter fun l => loc hT r h l = i).card : ℤ) =
      max ((T.degree i : ℤ) - 2) 0 := by
  rw [lemma_5_31_degree1 hT hh hi]
  omega

/-- **Lemma 5.31, eq. (5.77)**: `|{l ∈ Leaves(T) ∖ {r} : loc_T(l) = r}| = deg_T(r)`. -/
theorem lemma_5_31_degree2 [Fintype V] [DecidableRel T.Adj] (hh : IsChildChoice T r h) :
    (((leaves T).erase r).filter fun l => loc hT r h l = r).card = T.degree r := by
  rw [card_filter_loc_eq hT hh, degree_eq hT r, ite_eq_left rfl, add_zero]
  congr 1
  exact Finset.filter_true_of_mem fun c _ => Or.inl rfl

end Loc

end CoreForest

end MultipoleBKT

end
