/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.OrderingTree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Radius allocation in the logarithmic J estimate

See Lemma A.4, especially (A.25). Apply Lemma A.1 to the coarse even tree,
combine its radii with the odd prefactor, and apply Lemma A.1 inside each block.
The maps below describe the two quotient partitions. A chosen representative in
each fibre carries its largest radius.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open Finset SimpleGraph

private theorem prod_erase_fibres {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] [DecidableEq B] (blk : V → B) (root : B → V)
    (hroot : ∀ b, blk (root b) = b) (f : V → ℝ) (hf : ∀ i, 0 < f i) (b₀ : B) :
    (∏ b ∈ univ.erase b₀, f (root b)) *
        (∏ b, ∏ i ∈ (univ.filter fun i => blk i = b).erase (root b), f i) =
      ∏ i ∈ univ.erase (root b₀), f i := by
  have hmem (b : B) : root b ∈ univ.filter (fun i => blk i = b) := by simp [hroot]
  have hall : (∏ b, f (root b)) *
      (∏ b, ∏ i ∈ (univ.filter fun i => blk i = b).erase (root b), f i) = ∏ i, f i := by
    rw [← prod_mul_distrib]
    simp_rw [mul_prod_erase _ f (hmem _)]
    exact Finset.prod_fiberwise univ blk f
  apply mul_left_cancel₀ (hf (root b₀)).ne'
  rw [← mul_assoc, mul_prod_erase _ (fun b => f (root b)) (mem_univ b₀), hall,
    mul_prod_erase _ f (mem_univ (root b₀))]

/-- The coarse even tree supplies one squared radius per coarse block except the
largest. Combining it with the odd prefactor supplies one per fine block except
its global maximum. This is the first radius allocation in (A.25). -/
theorem coarse_radius_allocation {B C : Type*} [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (grp : B → C) (hat : C → B)
    (hhat : ∀ c, grp (hat c) = c) (r : B → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (Q : SimpleGraph C) [DecidableRel Q.Adj] (hQ : Q.IsTree) (c₀ : C)
    (hmax : ∀ c, r (hat c) ≤ r (hat c₀)) :
    (∏ c, ∏ b ∈ (univ.filter fun b => grp b = c).erase (hat c), max (r b) lam ^ 2) *
        (∏ e ∈ Q.edgeFinset, edgeMin (fun x => max x lam ^ 2) (fun c => r (hat c)) e) ≤
      ∏ b ∈ univ.erase (hat c₀), max (r b) lam ^ 2 := by
  have hf : Monotone (fun x : ℝ => max x lam ^ 2) := by
    intro x y hxy
    exact pow_le_pow_left₀ (hlam.le.trans (le_max_right _ _)) (max_le_max hxy le_rfl) 2
  have h := ordering_tree hQ hf (fun _ => sq_nonneg _) (fun c => r (hat c)) c₀ hmax
  calc
    _ ≤ (∏ c, ∏ b ∈ (univ.filter fun b => grp b = c).erase (hat c), max (r b) lam ^ 2) *
        ∏ c ∈ univ.erase c₀, max (r (hat c)) lam ^ 2 :=
      mul_le_mul_of_nonneg_left h (prod_nonneg fun _ _ => prod_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by
      rw [mul_comm]
      exact prod_erase_fibres grp hat hhat _ (fun i => sq_pos_of_pos (lt_max_of_lt_right hlam)) c₀

/-- Ordering every near tree supplies all label radii except the representative
of each block. The block prefactor then cancels these omissions except the
largest radius of the entire cluster. This is (A.25) after the coarse allocation. -/
theorem near_radius_allocation {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] [DecidableEq B] (blk : V → B) (root : B → V)
    (hroot : ∀ b, blk (root b) = b) (r : V → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (T : ∀ b, SimpleGraph {i // blk i = b}) [∀ b, DecidableRel (T b).Adj]
    (hT : ∀ b, (T b).IsTree) (hmax : ∀ b i, blk i = b → r i ≤ r (root b)) (b₀ : B) :
    (∏ b ∈ univ.erase b₀, max (r (root b)) lam ^ 2) *
        (∏ b, ∏ e ∈ (T b).edgeFinset,
          edgeMin (fun x => max x lam ^ 2) (fun i => r i.1) e) ≤
      ∏ i ∈ univ.erase (root b₀), max (r i) lam ^ 2 := by
  classical
  have hf : Monotone (fun x : ℝ => max x lam ^ 2) := by
    intro x y hxy
    exact pow_le_pow_left₀ (hlam.le.trans (le_max_right _ _)) (max_le_max hxy le_rfl) 2
  have hb (b : B) : (∏ e ∈ (T b).edgeFinset,
      edgeMin (fun x => max x lam ^ 2) (fun i => r i.1) e) ≤
      ∏ i ∈ (univ.filter fun i => blk i = b).erase (root b), max (r i) lam ^ 2 := by
    have h := ordering_tree (hT b) hf (fun _ => sq_nonneg _) (fun i => r i.1)
      ⟨root b, hroot b⟩ (fun i => hmax b i.1 i.2)
    refine h.trans_eq ?_
    refine prod_bij (fun i _ => i.1) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro i hi
      simp only [mem_erase, mem_univ, and_true] at hi
      simp only [mem_erase, mem_filter, mem_univ, true_and]
      exact ⟨fun heq => hi (Subtype.ext heq), i.2⟩
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro i hi
      simp only [mem_erase, mem_filter, mem_univ, true_and] at hi
      exact ⟨⟨i, hi.2⟩, mem_erase.mpr ⟨fun h => hi.1 (congrArg Subtype.val h), mem_univ _⟩, rfl⟩
  calc
    _ ≤ (∏ b ∈ univ.erase b₀, max (r (root b)) lam ^ 2) *
        ∏ b, ∏ i ∈ (univ.filter fun i => blk i = b).erase (root b), max (r i) lam ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun _ _ => sq_nonneg _)
      exact prod_le_prod₀ (fun _ _ => prod_nonneg fun e _ => Sym2.inductionOn e fun _ _ => sq_nonneg _)
        fun b _ => hb b
    _ = _ := prod_erase_fibres blk root hroot _ (fun i => sq_pos_of_pos (lt_max_of_lt_right hlam)) b₀

/-- The complete radius allocation (A.25). The odd prefactor uses the original
block radii. Apply the coarse-tree bound first, followed by the near-tree bounds. -/
theorem radius_allocation {V B C : Type*} [Fintype V] [Fintype B] [Fintype C]
    [DecidableEq V] [DecidableEq B] [DecidableEq C]
    (blk : V → B) (root : B → V) (hroot : ∀ b, blk (root b) = b)
    (grp : B → C) (hat : C → B) (hhat : ∀ c, grp (hat c) = c)
    (r : V → ℝ) (hr : ∀ i, 0 ≤ r i) (lam : ℝ) (hlam : 0 < lam)
    (Q : SimpleGraph C) [DecidableRel Q.Adj] (hQ : Q.IsTree)
    (T : ∀ b, SimpleGraph {i // blk i = b}) [∀ b, DecidableRel (T b).Adj]
    (hT : ∀ b, (T b).IsTree) (hmax : ∀ b i, blk i = b → r i ≤ r (root b))
    (c₀ : C) (hglobal : ∀ c, r (root (hat c)) ≤ r (root (hat c₀))) :
    (∏ c, ∏ b ∈ (univ.filter fun b => grp b = c).erase (hat c), r (root b) ^ 2) *
        (∏ e ∈ Q.edgeFinset,
          edgeMin (fun x => max x lam ^ 2) (fun c => r (root (hat c))) e) *
        (∏ b, ∏ e ∈ (T b).edgeFinset,
          edgeMin (fun x => max x lam ^ 2) (fun i => r i.1) e) ≤
      ∏ i ∈ univ.erase (root (hat c₀)), max (r i) lam ^ 2 := by
  have hodd : (∏ c, ∏ b ∈ (univ.filter fun b => grp b = c).erase (hat c), r (root b) ^ 2) ≤
      ∏ c, ∏ b ∈ (univ.filter fun b => grp b = c).erase (hat c), max (r (root b)) lam ^ 2 := by
    exact prod_le_prod₀ (fun _ _ => prod_nonneg fun _ _ => sq_nonneg _) fun c _ =>
      prod_le_prod₀ (fun _ _ => sq_nonneg _) fun b _ => pow_le_pow_left₀ (hr _) (le_max_left _ _) 2
  have hcoarse := coarse_radius_allocation grp hat hhat (fun b => r (root b)) lam hlam Q hQ c₀ hglobal
  have hnear := near_radius_allocation blk root hroot r lam hlam T hT hmax (hat c₀)
  apply le_trans _ hnear
  apply mul_le_mul_of_nonneg_right _
    (prod_nonneg fun _ _ => prod_nonneg fun e _ => Sym2.inductionOn e fun _ _ => sq_nonneg _)
  exact (mul_le_mul_of_nonneg_right hodd
    (prod_nonneg fun e _ => Sym2.inductionOn e fun _ _ => sq_nonneg _)).trans hcoarse

end MultipoleBKT.SmallIntegral.RouteJ

end
