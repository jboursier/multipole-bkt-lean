/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteOdd.Bonds

/-!
# Near trees, odd component trees and one even quotient tree

See the proof of Lemma A.5, and proof of Lemma 4.26.
This pointwise bound is used for spatial integration and limiting integrands. It applies to singleton blocks and
multipole blocks after merging the parts joined by near edges.
-/

@[expose] public section

namespace MultipoleBKT.Limits

open Finset SimpleGraph

variable {χ : ℂ → ℝ} {β lam M : ℝ}
variable {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

open scoped Classical in
/-- The product before the tree-coordinate integrations, with a single odd tail.
The two radius products come from the near trees and the odd component roots. -/
noncomputable def paperTreeMajorant {γ : Type*} (M lam : ℝ) (c : ι → ℂ × ℂ)
    (s : κ → ℝ) (root : γ → κ) (NT A B : Finset (Sym2 ι)) : ℝ :=
  (∏ e ∈ NT, edgeMin sqPos (fun i => rhoD lam (c i)) e) *
    (∏ S ∈ univ.filter (fun S => S ∉ Set.range root), s S ^ 2) *
    globalTail (maxRad lam c) (paperDistE c) A *
    (∏ e ∈ NT, nearE M lam c e) * (∏ e ∈ A, paperOddE M lam c e) *
      ∏ e ∈ B, paperEvenE M lam c e

omit [Fintype ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ] in
/-- The endpoint description of a simple label-edge family. -/
theorem nodeGraph_id_eq (D : Finset (Sym2 ι)) :
    nodeGraph id D = SimpleGraph.fromEdgeSet (D : Set (Sym2 ι)) := by
  ext i j
  simp [nodeGraph_adj, fromEdgeSet_adj, and_comm]

open scoped Classical in
/-- The paper-shaped majorant for singleton and multipole block systems.
The near edges, odd edges and even edges form a tree on the original labels.
The quotient on each odd component is a tree, and the even edges form a separate
coarse tree. The radius roots are maxima, with every choice constructed here.
One coefficient works for all positive `lam`, all `M ≥ 1`, all block maps and
both edge families, as required by Lemma A.5. -/
theorem exists_paper_majorant (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ M : ℝ, 1 ≤ M →
      ∀ blk : ι → κ, Function.Surjective blk → ∀ E : SimpleGraph ι,
      (∀ i j, E.Adj i j → blk i ≠ blk j) →
      (nodeGraph (Sym2.map blk) E.edgeFinset).Connected →
      ∀ F : Finset (Sym2 ι), F ⊆ E.edgeFinset → CutEven (Sym2.map blk) F →
      ∀ c : ι → ℂ × ℂ,
      (∀ S, ((nearGraph M lam c).induce {i | blk i = S}).Connected) →
      ∃ (r : κ → ι) (root : (nodeGraph (Sym2.map blk) F).ConnectedComponent → κ)
        (NT A B : Finset (Sym2 ι)),
        (∀ S, blk (r S) = S) ∧
        (∀ i, rhoD lam (c i) ≤ rhoD lam (c (r (blk i)))) ∧
        (∀ D, (nodeGraph (Sym2.map blk) F).connectedComponentMk (root D) = D) ∧
        (∀ D v, (nodeGraph (Sym2.map blk) F).connectedComponentMk v = D →
          rhoD lam (c (r v)) ≤ rhoD lam (c (r (root D)))) ∧
        (∀ i j, s(i, j) ∈ NT → i ≠ j ∧ blk i = blk j ∧ MultipoleLinked M lam (c i) (c j)) ∧
        A ⊆ F ∧ B ⊆ E.edgeFinset \ F ∧ Disjoint NT (A ∪ B) ∧
        (nodeGraph id (NT ∪ (A ∪ B))).IsTree ∧
        (∀ D : (nodeGraph (Sym2.map blk) F).ConnectedComponent,
          ((nodeGraph (Sym2.map blk) A).induce D.supp).IsTree) ∧
        (nodeGraph (Sym2.map (nodeGraph (Sym2.map blk) F).connectedComponentMk ∘ Sym2.map blk) B).IsTree ∧
        A.card + Nat.card (nodeGraph (Sym2.map blk) F).ConnectedComponent = Fintype.card κ ∧
        B.card + 1 = Nat.card (nodeGraph (Sym2.map blk) F).ConnectedComponent ∧
        NT.card + Fintype.card κ = Fintype.card ι ∧
        (∏ e ∈ NT, edgeMin sqPos (fun i => rhoD lam (c i)) e) ≤
          ∏ i ∈ univ.filter (fun i => i ≠ r (blk i)), sqPos (rhoD lam (c i)) ∧
        (∏ e ∈ E.edgeFinset \ F, |alphaE hχ β lam M c e|) * ∏ e ∈ F, |gammaE hχ β lam M c e| ≤
          C ^ E.edgeFinset.card * paperTreeMajorant M lam c (fun S => rhoD lam (c (r S))) root NT A B := by
  classical
  obtain ⟨C, hC, hmajor⟩ := exists_paper_term_le (ι := ι) (κ := κ) hχ hβ
  refine ⟨C, hC, fun lam hlam M hM blk hblk E hEinter hconn F hFE hcut c hB => ?_⟩
  have hroots : ∀ S, ∃ i, blk i = S ∧ ∀ j, blk j = S → rhoD lam (c j) ≤ rhoD lam (c i) := by
    intro S
    obtain ⟨i, hi⟩ := hblk S
    obtain ⟨r, hr, hm⟩ := exists_max_image (univ.filter (fun j => blk j = S)) (fun j => rhoD lam (c j))
      ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩⟩
    exact ⟨r, (mem_filter.1 hr).2, fun j hj => hm j (mem_filter.2 ⟨mem_univ _, hj⟩)⟩
  choose r hr hrmax using hroots
  let s := fun S => rhoD lam (c (r S))
  have hs : ∀ S, 0 < s S := fun S => hlam.trans_le (le_max_right _ _)
  obtain ⟨root, A, B, hroot, hrootmax, hAF, hBE, hT, hAT, hBT, hAc, hBc, hb⟩ :=
    hmajor lam hlam M hM blk E hEinter hconn F hFE hcut c s hs
      (fun i => hrmax (blk i) i rfl) (maxRad lam c) (fun S => rhoD_le_maxRad lam c _)
  obtain ⟨NT, hNTedge, hNTreach, hNTprod, hNTc⟩ :=
    exists_near_forest_with_card blk c hB r hr (fun i => rhoD lam (c i))
  have hAB : A ∪ B ⊆ E.edgeFinset := union_subset (hAF.trans hFE) (hBE.trans sdiff_subset)
  have hdisj : Disjoint NT (A ∪ B) := by
    refine disjoint_left.2 fun e heN heAB => ?_
    induction e using Sym2.ind with
    | h i j => exact hEinter i j (mem_edgeFinset.1 (hAB heAB)) (hNTedge i j heN).2.1
  have hABc : (A ∪ B).card + 1 = Nat.card κ := by
    have hdisjAB : Disjoint A B :=
      disjoint_of_subset_left hAF (disjoint_of_subset_right hBE disjoint_sdiff_self_right)
    rw [card_union_of_disjoint hdisjAB, Nat.card_eq_fintype_card]
    omega
  have hNTtree : (nodeGraph id (NT ∪ (A ∪ B))).IsTree := by
    apply lift_tree_isTree id blk hblk (fun i j hij => ?_)
      (by simpa only [Nat.card_eq_fintype_card] using hNTc) hdisj
      (by simpa only [Function.comp_id] using hT) hABc
    rw [nodeGraph_id_eq]
    exact hNTreach i j hij
  refine ⟨r, root, NT, A, B, hr, fun i => hrmax (blk i) i rfl, hroot, hrootmax,
    hNTedge, hAF, hBE, hdisj, hNTtree, hAT, hBT, hAc, hBc, hNTc, hNTprod, hb.trans_eq ?_⟩
  have hnear : (∏ e ∈ NT, edgeMin sqPos (fun i => rhoD lam (c i)) e) *
      ∏ e ∈ NT, nearE M lam c e = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro e he
    induction e using Sym2.ind with
    | h i j =>
      obtain ⟨-, -, hlink⟩ := hNTedge i j he
      have hm : 0 < min (rhoD lam (c i)) (rhoD lam (c j)) :=
        lt_min (hlam.trans_le (le_max_right _ _)) (hlam.trans_le (le_max_right _ _))
      change sqPos (min (rhoD lam (c i)) (rhoD lam (c j))) * nearW M lam (c i) (c j) = 1
      have hlink' : dipoleDist (c i) (c j) ≤ M * min (rhoD lam (c i)) (rhoD lam (c j)) := hlink
      rw [nearW, ite_eq_left hlink', sqPos_of_nonneg hm.le, one_div]
      exact mul_inv_cancel₀ (pow_pos hm 2).ne'
  unfold paperTreeMajorant
  have hrewrite : ∀ (x y z w : ℝ), C ^ E.edgeFinset.card * x * y * z * w =
      C ^ E.edgeFinset.card *
        ((∏ e ∈ NT, edgeMin sqPos (fun i => rhoD lam (c i)) e) * x * y *
          (∏ e ∈ NT, nearE M lam c e) * z * w) := by
    intro x y z w
    calc C ^ E.edgeFinset.card * x * y * z * w =
        C ^ E.edgeFinset.card * x * y * z * w *
          ((∏ e ∈ NT, edgeMin sqPos (fun i => rhoD lam (c i)) e) * ∏ e ∈ NT, nearE M lam c e) := by
            rw [hnear, mul_one]
      _ = _ := by ring
  convert hrewrite _ _ _ _ using 1
  simp [s]

end MultipoleBKT.Limits

end
