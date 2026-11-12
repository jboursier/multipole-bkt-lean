/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TreeIntegral
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.GroupedRadius

/-!
# The two-sided radius allocation for case E

See (A.62) and Step 3 of the proof of Lemma A.7. Delete the marked even edge
on the coarse tree and order both resulting trees. Then restore the odd
component representatives and order the near trees inside every multipole.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open Finset SimpleGraph Limits SmallIntegral SmallIntegral.RouteJ
open scoped Classical

/-- Restoring every representative in a partition restores its full product. -/
theorem full_fibre_product {B C : Type*} [Fintype B] [Fintype C] [DecidableEq B]
    [DecidableEq C] (grp : B → C) (rep : C → B) (hrep : ∀ c, grp (rep c) = c)
    (f : B → ℝ) :
    (∏ c, f (rep c)) * (∏ c, ∏ b ∈ (univ.filter fun b => grp b = c).erase (rep c), f b) =
      ∏ b, f b := by
  rw [← prod_mul_distrib]
  have hm (c : C) : rep c ∈ univ.filter (fun b => grp b = c) :=
    mem_filter.2 ⟨mem_univ _,hrep c⟩
  simp_rw [mul_prod_erase _ f (hm _)]
  exact Finset.prod_fiberwise univ grp f

/-- Restoring all block representatives and ordering the near trees supplies
the complete regularized label-radius product. -/
theorem full_near_radius_allocation {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] [DecidableEq B] (blk : V → B) (root : B → V)
    (hroot : ∀ b, blk (root b) = b) (r : V → ℝ)
    (hmax : ∀ b i, blk i = b → r i ≤ r (root b)) {lam : ℝ} (hlam : 0 < lam)
    (R : ∀ b, SimpleGraph {i // blk i = b}) (hR : ∀ b, (R b).IsTree) :
    (∏ b, max (r (root b)) lam ^ 2) *
        (∏ e ∈ nearForest blk R, edgeMin (fun a => max a lam ^ 2) r e) ≤
      ∏ i, max (r i) lam ^ 2 := by
  have hf : Monotone (fun a : ℝ => max a lam ^ 2) :=
    fun a b hab => pow_le_pow_left₀ (hlam.le.trans (le_max_right _ _)) (max_le_max hab le_rfl) 2
  have hb (b : B) : (∏ e ∈ (R b).edgeFinset,
      edgeMin (fun a => max a lam ^ 2) (fun i => r i.val) e) ≤
      ∏ i ∈ (univ.filter fun i => blk i = b).erase (root b), max (r i) lam ^ 2 := by
    have h := ordering_tree (hR b) hf (fun _ => sq_nonneg _) (fun i => r i.val)
      ⟨root b,hroot b⟩ (fun i => hmax b i.val i.property)
    refine h.trans_eq ?_
    apply prod_bij (fun i _ => i.val)
    · intro i hi
      exact mem_erase.2 ⟨fun he => (mem_erase.1 hi).1 (Subtype.ext he),
        mem_filter.2 ⟨mem_univ _,i.property⟩⟩
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro i hi
      refine ⟨⟨i,(mem_filter.1 (mem_erase.1 hi).2).2⟩,mem_erase.2 ⟨?_,mem_univ _⟩,rfl⟩
      exact fun he => (mem_erase.1 hi).1 (congrArg Subtype.val he)
    · intro _ _
      rfl
  have hn : (∏ e ∈ nearForest blk R, edgeMin (fun a => max a lam ^ 2) r e) =
      ∏ b, ∏ e ∈ (R b).edgeFinset, edgeMin (fun a => max a lam ^ 2) (fun i => r i.val) e := by
    rw [prod_nearForest]
    apply prod_congr rfl
    intro b _
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with
    | h i j => rfl
  rw [hn]
  refine (mul_le_mul_of_nonneg_left (prod_le_prod₀
    (fun b _ => prod_nonneg fun e _ => Sym2.inductionOn e fun _ _ => sq_nonneg _)
    (fun b _ => hb b)) (prod_nonneg fun _ _ => sq_nonneg _)).trans_eq ?_
  exact full_fibre_product blk root hroot (fun i => max (r i) lam ^ 2)

/-- Case E on the grouped original tree. The marked endpoint squares are retained
until the two trees obtained by deleting the mark have both been ordered. -/
theorem grouped_marked_radius_allocation {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] [DecidableEq B] [Nonempty V] {n : ℕ}
    (blk : V → B) (root : B → V) (hroot : ∀ b, blk (root b) = b)
    (G : Fin n → Finset B) (hG : ∀ l l', l ≠ l' → Disjoint (G l) (G l'))
    (A : Fin n → Finset (Sym2 V)) (E : Finset (Sym2 V))
    (hAG : ∀ l, ∀ e ∈ A l, ∀ i ∈ e, blk i ∈ G l)
    (hAc : ∀ l, (A l).card + 1 = (G l).card)
    (hc : ∀ i j, (sameBlockGraph blk ⊔
      fromEdgeSet ((univ.biUnion A ∪ E : Finset (Sym2 V)) : Set (Sym2 V))).Reachable i j)
    (hcard : (∑ l, (A l).card) + E.card + 1 ≤ Fintype.card B)
    (hat : Fin n → B) (hhat : ∀ l, hat l ∈ G l)
    (r : V → ℝ) (hmax : ∀ b i, blk i = b → r i ≤ r (root b))
    (hhatmax : ∀ l b, b ∈ G l → r (root b) ≤ r (root (hat l)))
    (R : ∀ b, SimpleGraph {i // blk i = b}) (hR : ∀ b, (R b).IsTree)
    {lam : ℝ} (hlam : 0 < lam) {i j : V} (hmark : s(i,j) ∈ E) :
    (∏ l, ∏ b ∈ (G l).erase (hat l), max (r (root b)) lam ^ 2) *
      (max (r i) lam ^ 2 * max (r j) lam ^ 2) *
      (∏ e ∈ E.erase s(i,j), edgeMin (fun a => max a lam ^ 2) r e) *
      (∏ e ∈ nearForest blk R, edgeMin (fun a => max a lam ^ 2) r e) ≤
        ∏ v, max (r v) lam ^ 2 := by
  let grp := groupedOf G hG
  let rep := groupedHat G hat
  let b := grp ∘ blk
  let rad := fun c => r (root (rep c))
  have hrep := groupedHat_right_inverse G hG hat hhat
  have hdom (v : V) : r v ≤ rad (b v) :=
    (hmax (blk v) v rfl).trans (grouped_hat_max G hG hat (fun c => r (root c)) hhatmax (blk v))
  obtain ⟨hQ,hQE,hinj⟩ := grouped_even_tree blk (fun c => ⟨root c,hroot c⟩)
    G hG A E hAG hAc hc hcard hat hhat
  let Q := fromEdgeSet (E.image (Sym2.map b) : Set (Sym2 (GroupedBlock G)))
  have hm : s(b i,b j) ∈ Q.edgeFinset := by
    rw [hQE]
    exact mem_image.2 ⟨s(i,j),hmark,rfl⟩
  have he : Q.edgeFinset.erase s(b i,b j) = (E.erase s(i,j)).image (Sym2.map b) := by
    rw [hQE]
    ext e
    constructor
    · intro he
      obtain ⟨a,ha,hea⟩ := mem_image.1 (mem_erase.1 he).2
      exact mem_image.2 ⟨a,mem_erase.2 ⟨fun h => (mem_erase.1 he).1 (h ▸ hea).symm,ha⟩,hea⟩
    · intro he
      obtain ⟨a,ha,rfl⟩ := mem_image.1 he
      exact mem_erase.2 ⟨fun h => (mem_erase.1 ha).1 (hinj (mem_of_mem_erase ha) hmark h),
        mem_image.2 ⟨a,mem_of_mem_erase ha,rfl⟩⟩
  have hf : Monotone (fun a : ℝ => max a lam ^ 2) :=
    fun a c hac => pow_le_pow_left₀ (hlam.le.trans (le_max_right _ _)) (max_le_max hac le_rfl) 2
  have hE : (∏ e ∈ E.erase s(i,j), edgeMin (fun a => max a lam ^ 2) r e) ≤
      ∏ e ∈ Q.edgeFinset.erase s(b i,b j), edgeMin (fun a => max a lam ^ 2) rad e := by
    rw [he,prod_image (hinj.mono (erase_subset _ _))]
    apply prod_le_prod₀
    · intro e _
      induction e using Sym2.ind with
      | h v w => exact sq_nonneg _
    · intro e _
      induction e using Sym2.ind with
      | h v w => exact hf (min_le_min (hdom v) (hdom w))
  have hmarked : max (rad (b i)) lam ^ 2 * max (rad (b j)) lam ^ 2 *
      (∏ e ∈ Q.edgeFinset.erase s(b i,b j), edgeMin (fun a => max a lam ^ 2) rad e) ≤
        ∏ c, max (rad c) lam ^ 2 := by
    convert! marked_radius_allocation hQ (mem_edgeFinset.1 hm) rad hlam using 1
    congr 2
    ext e
    simp only [mem_erase,mem_edgeFinset]
    rfl
  have hends : max (r i) lam ^ 2 * max (r j) lam ^ 2 ≤
      max (rad (b i)) lam ^ 2 * max (rad (b j)) lam ^ 2 :=
    mul_le_mul (hf (hdom i)) (hf (hdom j)) (sq_nonneg _) (sq_nonneg _)
  have hcoarse : (max (r i) lam ^ 2 * max (r j) lam ^ 2) *
      (∏ e ∈ E.erase s(i,j), edgeMin (fun a => max a lam ^ 2) r e) ≤
        ∏ c, max (rad c) lam ^ 2 := by
    apply le_trans _ hmarked
    exact mul_le_mul hends hE
      (prod_nonneg fun e _ => Sym2.inductionOn e fun _ _ => sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  let P := ∏ l, ∏ a ∈ (G l).erase (hat l), max (r (root a)) lam ^ 2
  have hP : 0 ≤ P := prod_nonneg fun _ _ => prod_nonneg fun _ _ => sq_nonneg _
  have hrestore : P * (∏ c, max (rad c) lam ^ 2) = ∏ a, max (r (root a)) lam ^ 2 := by
    rw [mul_comm, show P = ∏ c : GroupedBlock G,
      ∏ a ∈ (univ.filter fun a => grp a = c).erase (rep c), max (r (root a)) lam ^ 2 from
        (grouped_prefactor G hG hat (fun a => max (r (root a)) lam ^ 2)).symm]
    exact full_fibre_product grp rep hrep (fun a => max (r (root a)) lam ^ 2)
  calc
    _ = P * ((max (r i) lam ^ 2 * max (r j) lam ^ 2) *
      ∏ e ∈ E.erase s(i,j), edgeMin (fun a => max a lam ^ 2) r e) *
      (∏ e ∈ nearForest blk R, edgeMin (fun a => max a lam ^ 2) r e) := by ring
    _ ≤ (P * ∏ c, max (rad c) lam ^ 2) *
      (∏ e ∈ nearForest blk R, edgeMin (fun a => max a lam ^ 2) r e) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoarse hP)
          (prod_nonneg fun e _ => Sym2.inductionOn e fun _ _ => sq_nonneg _)
    _ ≤ _ := by
      rw [hrestore]
      exact full_near_radius_allocation blk root hroot r hmax hlam R hR

end MultipoleBKT.ExpansionK.RouteSpatial

end
