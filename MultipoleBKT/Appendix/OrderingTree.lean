/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RoutePrufer.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Lemma A.1: ordering the radii along a tree

The proof follows Lemma A.1. Remove a leaf, apply the induction hypothesis on the remaining tree,
and split according to whether the removed leaf is the chosen maximum radius.

`ordering_tree` gives the maximum-root estimate. `prod_edgeMin_le_prod_erase` derives
the stronger any-root interface by comparing the two omitted factors. `ordering_tree_fin`
is the literal statement for a permutation sorting the radii in decreasing order.
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

universe u

variable {V : Type u}


/-- The function `{i, j} ↦ f (min (r i) (r j))` on unordered pairs of vertices. -/
def edgeMin (f : ℝ → ℝ) (r : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun i j => f (min (r i) (r j)), fun i j => by dsimp only; rw [min_comm]⟩

@[simp]
theorem edgeMin_mk (f : ℝ → ℝ) (r : V → ℝ) (i j : V) :
    edgeMin f r s(i, j) = f (min (r i) (r j)) := rfl

/-- In a connected graph every vertex `c ≠ i₀` has a neighbour one step closer to `i₀`. -/
theorem Connected.exists_adj_dist_add_one {T : SimpleGraph V} (hT : T.Connected) {i₀ c : V}
    (hc : c ≠ i₀) : ∃ y, T.Adj c y ∧ T.dist y i₀ + 1 = T.dist c i₀ := by
  obtain ⟨p, hp⟩ := hT.exists_walk_length_eq_dist c i₀
  cases p with
  | nil => exact absurd rfl hc
  | cons h q =>
    rename_i y
    refine ⟨y, h, ?_⟩
    have h1 : T.dist y i₀ ≤ q.length := SimpleGraph.dist_le q
    have h2 : T.dist c i₀ ≤ T.dist c y + T.dist y i₀ := hT.dist_triangle
    have h3 : T.dist c y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
    rw [Walk.length_cons] at hp
    lia

/-- Removing a leaf separates its single edge from the product on the smaller tree. -/
private theorem prod_edgeMin_leaf [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    [DecidableRel T.Adj]
    {v : V} (hv : Cayley.deg T v = 1) (p : {i // i ≠ v}) (hp : T.Adj v p.1)
    (f : ℝ → ℝ) (r : V → ℝ) :
    ∏ e ∈ T.edgeFinset, edgeMin f r e = f (min (r v) (r p.1)) *
      ∏ e ∈ (T.comap (Subtype.val : {i // i ≠ v} → V)).edgeFinset,
        edgeMin f (fun i => r i.1) e := by
  classical
  let T' := T.comap (Subtype.val : {i // i ≠ v} → V)
  have hsplit := Cayley.addLeaf_comap hv hp
  have hn : ¬ (T'.map (Function.Embedding.subtype _)).Adj v p.1 := by
    rw [Cayley.map_subtype_adj]
    rintro ⟨h, -⟩
    exact h rfl
  have heq : T.edgeFinset = (Cayley.addLeaf v p T').edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [hsplit]
  rw [heq]
  have hedges : (Cayley.addLeaf v p T').edgeFinset =
      insert s(v, p.1) (T'.edgeFinset.map (Function.Embedding.subtype _).sym2Map) := by
    ext e
    simp only [Finset.mem_insert, SimpleGraph.mem_edgeFinset, Finset.mem_map]
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [Cayley.addLeaf, SimpleGraph.mem_edgeSet, SimpleGraph.sup_adj,
        SimpleGraph.map_adj, SimpleGraph.edge_adj, Sym2.eq_iff]
      constructor
      · rintro (⟨x, y, h, rfl, rfl⟩ | ⟨h, hne⟩)
        · exact Or.inr ⟨s(x, y), by simpa using h, rfl⟩
        · exact Or.inl (by rcases h with h | h <;> tauto)
      · rintro (h | ⟨e, he, hab⟩)
        · rcases h with h | h
          · exact Or.inr ⟨Or.inl h, by simpa [h.1, h.2] using p.2.symm⟩
          · exact Or.inr ⟨Or.inr h, by simpa [h.1, h.2] using p.2⟩
        · induction e using Sym2.inductionOn with
          | _ x y =>
            change T'.Adj x y at he
            change s(x.1, y.1) = s(a, b) at hab
            rcases Sym2.eq_iff.mp hab with h | h
            · exact Or.inl ⟨x, y, he, h.1, h.2⟩
            · exact Or.inl ⟨y, x, he.symm, h.2, h.1⟩
  have hnot : s(v, p.1) ∉ T'.edgeFinset.map (Function.Embedding.subtype _).sym2Map := by
    rw [← SimpleGraph.edgeFinset_map]
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hn
  rw [hedges, Finset.prod_insert hnot, Finset.prod_map, edgeMin_mk]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | _ i j => rfl

/-- Products on the remaining vertices, with one further vertex omitted. -/
private theorem prod_erase_leaf [Fintype V] [DecidableEq V] (g : V → ℝ)
    {v a : V} (ha : a ≠ v) :
    ∏ i ∈ univ.erase a, g i = g v *
      ∏ j ∈ (univ : Finset {i // i ≠ v}).erase ⟨a, ha⟩, g j.1 := by
  rw [← mul_prod_erase _ _ (mem_erase.mpr ⟨ha.symm, mem_univ v⟩)]
  congr 1
  refine prod_bij (fun i hi => (⟨i, (mem_erase.mp hi).1⟩ : {i // i ≠ v}))
    (fun i hi => ?_) (fun a ha b hb hab => congrArg Subtype.val hab)
    (fun b hb => ?_) (fun i hi => rfl)
  · simp only [mem_erase, ne_eq, mem_univ, and_true] at hi ⊢
    exact fun h => hi.2 (congrArg Subtype.val h)
  · refine ⟨b.1, ?_, rfl⟩
    simp only [mem_erase, ne_eq, mem_univ, and_true] at hb ⊢
    exact ⟨b.2, fun h => hb (Subtype.ext h)⟩

/-- **Lemma A.1**. The proof removes a leaf and splits according to whether it is the
chosen maximum. -/
theorem ordering_tree [Fintype V] [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) {f : ℝ → ℝ} (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x) (r : V → ℝ)
    (i₀ : V) (_hi₀ : ∀ i, r i ≤ r i₀) :
    ∏ e ∈ T.edgeFinset, edgeMin f r e ≤ ∏ i ∈ univ.erase i₀, f (r i) := by
  classical
  have main : ∀ n, ∀ (W : Type u) [Fintype W] [DecidableEq W], Fintype.card W = n →
      ∀ (G : SimpleGraph W) [DecidableRel G.Adj], G.IsTree → ∀ (r : W → ℝ) (a : W),
      (∀ i, r i ≤ r a) →
      ∏ e ∈ G.edgeFinset, edgeMin f r e ≤ ∏ i ∈ univ.erase a, f (r i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ hcard G _ hG r a ha
      by_cases hsmall : Fintype.card W ≤ 1
      · have hall : ∀ i : W, i = a := fun i => Fintype.card_le_one_iff.mp hsmall i a
        have hGbot : G = ⊥ := by
          ext i j
          simp only [bot_adj, iff_false]
          exact fun h => h.ne ((hall i).trans (hall j).symm)
        have huniv : (univ : Finset W) = {a} := by ext i; simp [hall i]
        have hempty : G.edgeFinset = ∅ := by
          ext e
          simp only [SimpleGraph.mem_edgeFinset, Finset.notMem_empty, iff_false]
          rw [hGbot]
          simp
        rw [hempty]
        simp only [prod_empty, huniv, erase_singleton, le_refl]
      · have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
        have hv' : Cayley.deg G v = 1 := by rw [Cayley.deg_eq_degree, hv]
        obtain ⟨p, hp, -⟩ := (Cayley.deg_eq_one_iff G v).mp hv'
        let W' := {i // i ≠ v}
        let p' : W' := ⟨p, hp.ne'⟩
        let G' : SimpleGraph W' := G.comap Subtype.val
        have hG' : G'.IsTree := Cayley.isTree_comap hG hv'
        have hsize : Fintype.card W' + 1 = Fintype.card W :=
          by convert Cayley.card_subtype_ne_add_one v
        have hlt : Fintype.card W' < n := by omega
        have hnonempty : (univ : Finset W').Nonempty := ⟨p', mem_univ _⟩
        obtain ⟨b, -, hb⟩ := univ.exists_max_image (fun i : W' => r i.1) hnonempty
        -- If the leaf is the maximum, retain the maximum of the smaller tree.
        by_cases hva : v = a
        · subst a
          have hind := ih _ hlt W' rfl G' hG' (fun i => r i.1) b (fun i => hb i (mem_univ i))
          have hedge : f (min (r v) (r p)) ≤ f (r b.1) :=
            (hf (min_le_right _ _)).trans (hf (hb p' (mem_univ _)))
          rw [prod_edgeMin_leaf hv' p' hp]
          calc f (min (r v) (r p'.1)) * ∏ e ∈ G'.edgeFinset, edgeMin f (fun i => r i.1) e
              ≤ f (r b.1) * ∏ i ∈ univ.erase b, f (r i.1) :=
                mul_le_mul hedge hind (prod_nonneg fun e _ => Sym2.inductionOn e (fun i j => hf0 _)) (hf0 _)
            _ = ∏ i ∈ univ.erase v, f (r i) := by
              rw [mul_prod_erase _ (fun i : W' => f (r i.1)) (mem_univ b)]
              exact (Finset.prod_subtype (univ.erase v) (by simp) (fun i => f (r i))).symm
        -- Otherwise the original maximum remains in the smaller tree.
        · let a' : W' := ⟨a, Ne.symm hva⟩
          have hind := ih _ hlt W' rfl G' hG' (fun i => r i.1) a' (fun i => ha i.1)
          rw [prod_edgeMin_leaf hv' p' hp, prod_erase_leaf (fun i => f (r i)) (Ne.symm hva)]
          exact mul_le_mul (hf (min_le_left _ _)) hind
            (prod_nonneg fun e _ => Sym2.inductionOn e (fun i j => hf0 _)) (hf0 _)
  exact main _ V rfl T hT r i₀ _hi₀

/-- **Lemma A.1, any root.** The maximum-root bound implies the bound for every root,
since replacing the omitted maximum by another omitted factor increases the product. -/
theorem prod_edgeMin_le_prod_erase [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    [DecidableRel T.Adj] (hT : T.IsTree) {f : ℝ → ℝ} (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x)
    (r : V → ℝ) (i₀ : V) :
    ∏ e ∈ T.edgeFinset, edgeMin f r e ≤ ∏ i ∈ univ.erase i₀, f (r i) := by
  obtain ⟨a, -, ha⟩ := univ.exists_max_image r ⟨i₀, mem_univ _⟩
  refine (ordering_tree hT hf hf0 r a (fun i => ha i (mem_univ i))).trans ?_
  by_cases h : a = i₀
  · subst a
    exact le_rfl
  · rw [← mul_prod_erase _ _ (mem_erase.mpr ⟨Ne.symm h, mem_univ i₀⟩),
      ← mul_prod_erase (univ.erase i₀) _ (mem_erase.mpr ⟨h, mem_univ a⟩),
      Finset.erase_right_comm]
    exact mul_le_mul_of_nonneg_right (hf (ha i₀ (mem_univ _)))
      (prod_nonneg fun _ _ => hf0 _)

/-- **Lemma A.1**, literal form. Let `T` be a tree on `{1, …, k + 1}` (`Fin (k + 1)`),
`f` a nonnegative nondecreasing function, `r : Fin (k + 1) → ℝ`, and `φ` a permutation with
`r_{φ(1)} ≥ ⋯ ≥ r_{φ(k+1)}`. Then `∏_{ij ∈ E} f (min (r i) (r j)) ≤ f (r_{φ(2)}) ⋯ f (r_{φ(k+1)})`
(the vertices of `Fin (k + 1)` are numbered from `0`, so `φ(1)` is `φ 0`). -/
theorem ordering_tree_fin {k : ℕ} {T : SimpleGraph (Fin (k + 1))} [DecidableRel T.Adj]
    (hT : T.IsTree) {f : ℝ → ℝ} (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x) (r : Fin (k + 1) → ℝ)
    (φ : Fin (k + 1) ≃ Fin (k + 1)) (_hφ : Antitone fun i => r (φ i)) :
    ∏ e ∈ T.edgeFinset, edgeMin f r e ≤ ∏ i : Fin k, f (r (φ i.succ)) := by
  have hmax : ∀ i, r i ≤ r (φ 0) := by
    intro i
    have h := _hφ (Fin.zero_le (φ.symm i))
    simpa only [Equiv.apply_symm_apply] using h
  refine (ordering_tree hT hf hf0 r (φ 0) hmax).trans (le_of_eq ?_)
  have h1 : ∏ i ∈ univ.erase (φ 0), f (r i) = ∏ j ∈ univ.erase (0 : Fin (k + 1)), f (r (φ j)) :=
    Finset.prod_equiv φ.symm (fun i => by simp [Equiv.symm_apply_eq]) (by simp)
  have h2 : univ.erase (0 : Fin (k + 1)) = Finset.Ioi 0 := by
    ext i
    simp
  rw [h1, h2]
  exact Fin.prod_Ioi_zero (fun j => f (r (φ j)))

end MultipoleBKT

end
