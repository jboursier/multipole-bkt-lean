/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.GroupedTree

/-!
# Radius allocation for the retained original trees

See Lemma A.4, (A.25). The odd groups are the
tagged coarse partition of `GroupedBlocks`. The near trees remain on the
original block fibres.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open Finset SimpleGraph Limits
open scoped Classical

variable {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B] {n : ℕ}

/-- Reindex the near-forest product by the original fibre trees. -/
theorem prod_nearForest {K : Type*} [CommMonoid K] (blk : V → B)
    (R : ∀ b, SimpleGraph {i // blk i = b}) (f : Sym2 V → K) :
    (∏ e ∈ nearForest blk R, f e) =
      ∏ b, ∏ e ∈ (R b).edgeFinset, f (Sym2.map Subtype.val e) := by
  unfold nearForest
  rw [prod_biUnion (nearForest_disjoint blk R)]
  apply prod_congr rfl
  intro b _
  exact prod_image (Sym2.map.injective Subtype.val_injective).injOn

omit [Fintype V] [Fintype B] [DecidableEq V] in
/-- The selected representative of a coarse block dominates every fine radius
inside it, including singleton coarse blocks. -/
theorem grouped_hat_max (G : Fin n → Finset B)
    (hG : ∀ l l', l ≠ l' → Disjoint (G l) (G l')) (hat : Fin n → B)
    (r : B → ℝ) (hhat : ∀ l b, b ∈ G l → r b ≤ r (hat l)) (b : B) :
    r b ≤ r (groupedHat G hat (groupedOf G hG b)) := by
  generalize heq : groupedOf G hG b = c
  cases c with
  | inl l => exact hhat l b ((groupedOf_eq_inl G hG b l).mp heq)
  | inr c =>
    have he := (groupedOf_eq_inr G hG b c).mp heq
    simp only [groupedHat, Sum.elim_inr, he, le_refl]

/-- The prefactor and the actual even and near edges supply every
regularized label radius except a largest one. This instantiates the two
applications of Lemma A.1 in `radius_allocation` with the odd groups.
See (A.25). -/
theorem grouped_radius_allocation [Nonempty V] (blk : V → B)
    (root : B → V) (hroot : ∀ b, blk (root b) = b)
    (G : Fin n → Finset B) (hG : ∀ l l', l ≠ l' → Disjoint (G l) (G l'))
    (A : Fin n → Finset (Sym2 V)) (E : Finset (Sym2 V))
    (hAG : ∀ l, ∀ e ∈ A l, ∀ i ∈ e, blk i ∈ G l)
    (hAc : ∀ l, (A l).card + 1 = (G l).card)
    (hc : ∀ i j, (sameBlockGraph blk ⊔
      fromEdgeSet ((univ.biUnion A ∪ E : Finset (Sym2 V)) : Set (Sym2 V))).Reachable i j)
    (hcard : (∑ l, (A l).card) + E.card + 1 ≤ Fintype.card B)
    (hat : Fin n → B) (hhat : ∀ l, hat l ∈ G l)
    (r : V → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hmax : ∀ b i, blk i = b → r i ≤ r (root b))
    (hhatmax : ∀ l b, b ∈ G l → r (root b) ≤ r (root (hat l)))
    (R : ∀ b, SimpleGraph {i // blk i = b}) (hR : ∀ b, (R b).IsTree)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ i₀ : V, (∀ i, r i ≤ r i₀) ∧
      (∏ l, ∏ b ∈ (G l).erase (hat l), r (root b) ^ 2) *
        (∏ e ∈ E, edgeMin (fun x => max x lam ^ 2) r e) *
        (∏ e ∈ nearForest blk R, edgeMin (fun x => max x lam ^ 2) r e) ≤
          ∏ i ∈ univ.erase i₀, max (r i) lam ^ 2 := by
  let grp := groupedOf G hG
  let rep := groupedHat G hat
  let b := grp ∘ blk
  have hbs : Function.Surjective blk := fun c => ⟨root c, hroot c⟩
  obtain ⟨hQ, hQE, hinj⟩ := grouped_even_tree blk hbs G hG A E hAG hAc hc hcard hat hhat
  let Q := fromEdgeSet (E.image (Sym2.map b) : Set (Sym2 (GroupedBlock G)))
  have hrep : ∀ c, grp (rep c) = c := groupedHat_right_inverse G hG hat hhat
  have hB : Nonempty B := Nonempty.map blk inferInstance
  have hC : Nonempty (GroupedBlock G) := Nonempty.map grp hB
  obtain ⟨c₀, _, hglobal⟩ := exists_max_image univ (fun c => r (root (rep c))) univ_nonempty
  have hglobal' : ∀ c, r (root (rep c)) ≤ r (root (rep c₀)) := fun c => hglobal c (mem_univ _)
  have hdom (i : V) : r i ≤ r (root (rep (b i))) :=
    (hmax (blk i) i rfl).trans (grouped_hat_max G hG hat (fun c => r (root c)) hhatmax (blk i))
  refine ⟨root (rep c₀), fun i => (hdom i).trans (hglobal' _), ?_⟩
  have hE : (∏ e ∈ E, edgeMin (fun x => max x lam ^ 2) r e) ≤
      ∏ e ∈ Q.edgeFinset, edgeMin (fun x => max x lam ^ 2) (fun c => r (root (rep c))) e := by
    change _ ≤ ∏ e ∈ (fromEdgeSet (E.image (Sym2.map b) : Set (Sym2 (GroupedBlock G)))).edgeFinset, _
    rw [hQE, prod_image hinj]
    apply prod_le_prod₀
    · intro e _
      induction e using Sym2.ind with
      | h i j => exact sq_nonneg _
    · intro e _
      induction e using Sym2.ind with
      | h i j =>
        simp only [Sym2.map_mk, edgeMin_mk]
        exact pow_le_pow_left₀ (hlam.le.trans (le_max_right _ _))
          (max_le_max (min_le_min (hdom i) (hdom j)) le_rfl) 2
  have halloc := radius_allocation blk root hroot grp rep hrep r hr lam hlam Q hQ R hR hmax c₀ hglobal'
  rw [grouped_prefactor G hG hat (fun c => r (root c) ^ 2)] at halloc
  have hnear : (∏ e ∈ nearForest blk R, edgeMin (fun x => max x lam ^ 2) r e) =
      ∏ c, ∏ e ∈ (R c).edgeFinset, edgeMin (fun x => max x lam ^ 2) (fun i => r i.val) e := by
    rw [prod_nearForest]
    apply prod_congr rfl
    intro c _
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with
    | h i j => rfl
  rw [hnear]
  apply le_trans _ halloc
  apply mul_le_mul_of_nonneg_right _
    (prod_nonneg fun _ _ => prod_nonneg fun e _ => Sym2.inductionOn e fun _ _ => sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _
    (prod_nonneg fun _ _ => prod_nonneg fun _ _ => sq_nonneg _)
  convert! hE using 1
  congr 2
  exact Subsingleton.elim _ _

end MultipoleBKT.SmallIntegral.RouteJ

end
