/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteOdd.Majorant

/-!
# Radius cancellation for the separate near and even trees

See Lemma A.5, and Lemma 4.26. The coarse even
tree supplies the radii missing from the odd-component prefactor.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open Finset SimpleGraph
open scoped Classical

/-- A representative product and its complement omit exactly the chosen root. -/
theorem prod_complement_range_erase {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (r : J → I) (hr : Function.Injective r)
    (f : I → ℝ) (hf : ∀ i, 0 < f i) (j₀ : J) :
    (∏ i ∈ univ.filter (fun i => i ∉ Set.range r), f i) *
      (∏ j ∈ univ.erase j₀, f (r j)) = ∏ i ∈ univ.erase (r j₀), f i := by
  have himg : (univ : Finset J).image r = univ.filter (fun i => i ∈ Set.range r) := by
    ext i
    simp
  have hall : (∏ i ∈ univ.filter (fun i => i ∉ Set.range r), f i) *
      (∏ j, f (r j)) = ∏ i, f i := by
    rw [← prod_image hr.injOn, himg, mul_comm, prod_filter_mul_prod_filter_not]
  apply mul_left_cancel₀ (hf (r j₀)).ne'
  calc
    f (r j₀) * ((∏ i ∈ univ.filter (fun i => i ∉ Set.range r), f i) *
        ∏ j ∈ univ.erase j₀, f (r j)) =
      (∏ i ∈ univ.filter (fun i => i ∉ Set.range r), f i) *
        (f (r j₀) * ∏ j ∈ univ.erase j₀, f (r j)) := by ring
    _ = ∏ i, f i := by rw [mul_prod_erase _ (fun j => f (r j)) (mem_univ j₀), hall]
    _ = _ := (mul_prod_erase _ f (mem_univ (r j₀))).symm

/-- A relative tree with the specified edge count has one original edge per
quotient edge. Its radius product is bounded by Lemma A.1 on that quotient. -/
theorem relative_tree_radius {I J : Type*} [Fintype J] [DecidableEq I] [DecidableEq J]
    (ends : I → Sym2 J) (T : Finset I) (hT : (nodeGraph ends T).IsTree)
    (hcard : T.card + 1 = Fintype.card J) (r : J → ℝ) (_hr : ∀ i, 0 ≤ r i)
    (root : J) (hroot : ∀ i, r i ≤ r root) :
    ∏ e ∈ T, edgeMin sqPos r (ends e) ≤ ∏ i ∈ univ.erase root, sqPos (r i) := by
  let Q := nodeGraph ends T
  have hsub : Q.edgeFinset ⊆ T.image ends := by
    intro e he
    induction e using Sym2.ind with
    | h i j =>
      obtain ⟨_, d, hd, hde⟩ := nodeGraph_adj.mp (mem_edgeFinset.mp he)
      exact mem_image.mpr ⟨d, hd, hde⟩
  have hcnt : Q.edgeFinset.card = T.card := by
    have h : Q.edgeFinset.card + 1 = Fintype.card J := hT.card_edgeFinset
    omega
  have heq : T.image ends = Q.edgeFinset := by
    apply (eq_of_subset_of_card_le hsub ?_).symm
    exact card_image_le.trans (le_of_eq hcnt.symm)
  have hinj : Set.InjOn ends T := by
    apply card_image_iff.mp
    rw [heq, hcnt]
  rw [← prod_image hinj, heq]
  exact ordering_tree hT sqPos_mono sqPos_nonneg r root hroot

/-- The two radius allocations for a merged block system.
The near forest is used through its already proved ordered product bound.
No power loss is incurred before the spatial logarithms are integrated. -/
theorem merged_radius_allocation {I B C : Type*} [Fintype I] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq B] [DecidableEq C]
    (blk : I → B) (rep : B → I) (hrep : ∀ b, blk (rep b) = b)
    (grp : B → C) (root : C → B) (hroot : ∀ d, grp (root d) = d)
    (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (hmax : ∀ i, r i ≤ r (rep (blk i)))
    (hgroup : ∀ b, r (rep b) ≤ r (rep (root (grp b))))
    (NT E : Finset (Sym2 I))
    (hnear : (∏ e ∈ NT, edgeMin sqPos r e) ≤
      ∏ i ∈ univ.filter (fun i => i ≠ rep (blk i)), sqPos (r i))
    (hE : (nodeGraph (Sym2.map grp ∘ Sym2.map blk) E).IsTree)
    (hEc : E.card + 1 = Fintype.card C) (d₀ : C)
    (hglobal : ∀ d, r (rep (root d)) ≤ r (rep (root d₀))) :
    (∏ e ∈ NT, edgeMin sqPos r e) *
      (∏ b ∈ univ.filter (fun b => b ∉ Set.range root), r (rep b) ^ 2) *
      (∏ e ∈ E, edgeMin sqPos r e) ≤
        ∏ i ∈ univ.erase (rep (root d₀)), r i ^ 2 := by
  have hir : Function.Injective rep := Function.LeftInverse.injective hrep
  have hig : Function.Injective root := Function.LeftInverse.injective hroot
  have hfilter : univ.filter (fun i => i ≠ rep (blk i)) =
      univ.filter (fun i => i ∉ Set.range rep) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hi ⟨b, hb⟩
      apply hi
      rw [← hb, hrep]
    · intro hi hh
      exact hi ⟨blk i, hh.symm⟩
  have hEven : (∏ e ∈ E, edgeMin sqPos r e) ≤
      ∏ d ∈ univ.erase d₀, r (rep (root d)) ^ 2 := by
    have hb := relative_tree_radius (Sym2.map grp ∘ Sym2.map blk) E hE hEc
      (fun d => r (rep (root d))) (fun d => (hr _).le) d₀ hglobal
    have hp : (∏ e ∈ E, edgeMin sqPos r e) ≤
        ∏ e ∈ E, edgeMin sqPos (fun d => r (rep (root d)))
          ((Sym2.map grp ∘ Sym2.map blk) e) := by
      apply prod_le_prod₀ (fun e _ => Sym2.inductionOn e fun _ _ => sqPos_nonneg _)
      intro e _
      induction e using Sym2.ind with
      | h i j =>
        simp only [Function.comp_apply, Sym2.map_mk, edgeMin_mk]
        apply sqPos_mono
        exact min_le_min ((hmax i).trans (hgroup _)) ((hmax j).trans (hgroup _))
    exact (hp.trans hb).trans_eq (prod_congr rfl fun d _ => sqPos_of_nonneg (hr _).le)
  have hnear' : (∏ e ∈ NT, edgeMin sqPos r e) ≤
      ∏ i ∈ univ.filter (fun i => i ∉ Set.range rep), r i ^ 2 := by
    rw [hfilter] at hnear
    exact hnear.trans_eq (prod_congr rfl fun i _ => sqPos_of_nonneg (hr i).le)
  calc
    _ ≤ (∏ i ∈ univ.filter (fun i => i ∉ Set.range rep), r i ^ 2) *
        ((∏ b ∈ univ.filter (fun b => b ∉ Set.range root), r (rep b) ^ 2) *
          ∏ d ∈ univ.erase d₀, r (rep (root d)) ^ 2) := by
      rw [← mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hnear'
        (prod_nonneg fun _ _ => sq_nonneg _)) hEven
        (prod_nonneg fun e _ => Sym2.inductionOn e fun _ _ => sqPos_nonneg _)
        (mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _) (prod_nonneg fun _ _ => sq_nonneg _))
    _ = _ := by
      rw [prod_complement_range_erase root hig (fun b => r (rep b) ^ 2)
        (fun b => sq_pos_of_pos (hr _)) d₀,
        prod_complement_range_erase rep hir (fun i => r i ^ 2)
          (fun i => sq_pos_of_pos (hr i)) (root d₀)]

end MultipoleBKT.Limits.RouteDirect

end
