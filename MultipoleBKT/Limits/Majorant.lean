/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Symmetrize

/-!
# The pointwise majorant of a cut-even term

See the proof of Lemma A.5,
(A.30), and proof of Lemma 4.26.

`exists_near_forest_with_card` chooses the near trees and records their edge count
and radius product bound by Lemma A.1. These trees are used by the separate
odd-component and even-quotient construction in `RouteOdd/Majorant.lean`.
The largest radius and normalized near weights are also used by the appendix.

-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal

variable {χ : ℂ → ℝ} {β lam M : ℝ}

section Weights

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The largest dipole radius `R = max_i ρ_i` (at least `λ`). -/
noncomputable def maxRad (lam : ℝ) (c : ι → ℂ × ℂ) : ℝ := univ.fold max lam fun i => rhoD lam (c i)

omit [LinearOrder ι] in
theorem rhoD_le_maxRad (lam : ℝ) (c : ι → ℂ × ℂ) (i : ι) : rhoD lam (c i) ≤ maxRad lam c :=
  (Finset.le_fold_max (rhoD lam (c i))).2 (Or.inr ⟨i, mem_univ _, le_rfl⟩)

omit [LinearOrder ι] in
theorem lam_le_maxRad (lam : ℝ) (c : ι → ℂ × ℂ) : lam ≤ maxRad lam c :=
  (Finset.le_fold_max lam).2 (Or.inl le_rfl)

theorem nearW_comm (M lam : ℝ) (d e : ℂ × ℂ) : nearW M lam d e = nearW M lam e d := by
  unfold nearW
  rw [dipoleDist_comm, min_comm (rhoD lam d)]

/-- The near weight as a function of unordered pairs of labels. -/
noncomputable def nearE (M lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => nearW M lam (c i) (c j)) fun _ _ => nearW_comm M lam _ _

omit [Fintype ι] [LinearOrder ι] in
theorem nearE_nonneg (M lam : ℝ) (c : ι → ℂ × ℂ) (e : Sym2 ι) : 0 ≤ nearE M lam c e := by
  induction e using Sym2.ind with
  | h i j => exact nearW_nonneg M lam _ _

end Weights

section NearForest

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [Fintype β'] [DecidableEq β']

open scoped Classical in
/-- **Near trees in the blocks.** If every block is near-connected, there is a set `NT` of near
edges inside the blocks connecting the labels of each block, with
`∏_{ij ∈ NT} min(rᵢ, rⱼ)² ≤ ∏_{i ≠ root(blk i)} rᵢ²` for any choice of roots (Lemma A.1). -/
theorem exists_near_forest_with_card (blk : ι → β') (c : ι → ℂ × ℂ)
    (hB : ∀ S, ((nearGraph M lam c).induce {i | blk i = S}).Connected) (rootLab : β' → ι)
    (hroot : ∀ S, blk (rootLab S) = S) (r : ι → ℝ) :
    ∃ NT : Finset (Sym2 ι), (∀ i j, s(i, j) ∈ NT → i ≠ j ∧ blk i = blk j ∧
        MultipoleLinked M lam (c i) (c j)) ∧
      (∀ i j, blk i = blk j → (SimpleGraph.fromEdgeSet (NT : Set (Sym2 ι))).Reachable i j) ∧
      ∏ e ∈ NT, edgeMin sqPos r e ≤ ∏ i ∈ univ.filter (fun i => i ≠ rootLab (blk i)), sqPos (r i) ∧
      NT.card + Fintype.card β' = Fintype.card ι := by
  -- a spanning tree in each block
  have hT : ∀ S, ∃ T : SimpleGraph {i | blk i = S},
      T ≤ (nearGraph M lam c).induce {i | blk i = S} ∧ T.IsTree := fun S =>
    (hB S).exists_isTree_le
  choose T hTle hTtree using hT
  let emb : ∀ S, {i | blk i = S} → ι := fun S i => i.val
  let NT : Finset (Sym2 ι) := univ.biUnion fun S => (T S).edgeFinset.image (Sym2.map (emb S))
  have hmemNT : ∀ e, e ∈ NT ↔ ∃ S, ∃ e' ∈ (T S).edgeFinset, Sym2.map (emb S) e' = e := by
    intro e
    simp [NT]
  have hdisj : ((univ : Finset β') : Set β').PairwiseDisjoint
      fun S => (T S).edgeFinset.image (Sym2.map (emb S)) := by
    intro S _ S' _ hSS'
    refine Finset.disjoint_left.2 fun e he he' => ?_
    obtain ⟨e₁, -, rfl⟩ := mem_image.1 he
    obtain ⟨e₂, -, h₂⟩ := mem_image.1 he'
    induction e₁ using Sym2.ind with
    | h a b =>
      induction e₂ using Sym2.ind with
      | h a' b' =>
        simp only [Sym2.map_mk, Sym2.eq_iff, emb] at h₂
        have ha := a.property
        have hb := b.property
        have ha' := a'.property
        simp only [Set.mem_ofPred_eq] at ha hb ha'
        rcases h₂ with ⟨h, -⟩ | ⟨h, -⟩
        · exact hSS' (ha.symm.trans ((congrArg blk h).symm.trans ha'))
        · exact hSS' (hb.symm.trans ((congrArg blk h).symm.trans ha'))
  refine ⟨NT, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    obtain ⟨S, e', he', hee'⟩ := (hmemNT _).1 hij
    induction e' using Sym2.ind with
    | h a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he'
      have hadj := hTle S he'
      rw [comap_adj, nearGraph_adj] at hadj
      simp only [Sym2.map_mk, Sym2.eq_iff, emb] at hee'
      have ha := a.property
      have hb := b.property
      simp only [Set.mem_ofPred_eq] at ha hb
      rcases hee' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨fun h => hadj.1 (by simpa using h), by rw [ha, hb], hadj.2⟩
      · exact ⟨fun h => hadj.1 (by simpa using h.symm), by rw [ha, hb],
          multipoleLinked_comm.1 hadj.2⟩
  · intro i j hij
    set S := blk i
    have hi : i ∈ {k | blk k = S} := rfl
    have hj : j ∈ {k | blk k = S} := hij.symm
    have hreach := (hTtree S).connected.preconnected ⟨i, hi⟩ ⟨j, hj⟩
    let f : T S →g SimpleGraph.fromEdgeSet (NT : Set (Sym2 ι)) :=
      { toFun := emb S
        map_rel' := by
          intro a b hab
          rw [fromEdgeSet_adj]
          refine ⟨(hmemNT _).2 ⟨S, s(a, b), by rw [mem_edgeFinset]; exact hab, rfl⟩, ?_⟩
          intro h
          exact (T S).ne_of_adj hab (Subtype.ext h) }
    exact hreach.map f
  · -- the product
    rw [prod_biUnion hdisj]
    have hinj : ∀ S, Set.InjOn (Sym2.map (emb S)) (T S).edgeFinset := fun S =>
      (Sym2.map.injective Subtype.val_injective).injOn
    simp_rw [prod_image (hinj _)]
    have hfib : ∏ i ∈ univ.filter (fun i => i ≠ rootLab (blk i)), sqPos (r i) =
        ∏ S : β', ∏ i : {i | blk i = S}, if (i : ι) = rootLab S then 1 else sqPos (r i) := by
      rw [prod_filter, ← prod_fiberwise univ blk]
      refine prod_congr rfl fun S _ => ?_
      rw [Finset.prod_set_coe (f := fun x => if x = rootLab S then 1 else sqPos (r x))
        {i | blk i = S}, Set.toFinset_ofPred]
      refine prod_congr rfl fun i hi => ?_
      have : blk i = S := (mem_filter.1 hi).2
      by_cases h : i = rootLab S
      · rw [ite_eq_left h, ite_eq_right (by rw [this]; exact not_not.2 h)]
      · rw [ite_eq_right h, ite_eq_left (by rw [this]; exact h)]
    rw [hfib]
    refine prod_le_prod₀ (fun S _ => prod_nonneg fun e _ => ?_) fun S _ => ?_
    · induction e using Sym2.ind with
      | h a b => exact sqPos_nonneg _
    · have hle := prod_edgeMin_le_prod_erase (hTtree S) sqPos_mono sqPos_nonneg
        (fun i => r (emb S i)) ⟨rootLab S, hroot S⟩
      have he : ∀ e ∈ (T S).edgeFinset, edgeMin sqPos r (Sym2.map (emb S) e) =
          edgeMin sqPos (fun i => r (emb S i)) e := by
        intro e _
        induction e using Sym2.ind with
        | h a b => rfl
      rw [prod_congr rfl he]
      refine hle.trans (le_of_eq ?_)
      rw [← prod_erase_mul _ _ (mem_univ (⟨rootLab S, hroot S⟩ : {i | blk i = S}))]
      rw [ite_eq_left rfl, mul_one]
      refine prod_congr rfl fun i hi => ?_
      rw [ite_eq_right]
      intro h
      exact (mem_erase.1 hi).1 (Subtype.ext h)
  · have hcardNT : NT.card = ∑ S, (T S).edgeFinset.card := by
      rw [show NT = univ.biUnion (fun S => (T S).edgeFinset.image (Sym2.map (emb S))) from rfl,
        card_biUnion hdisj]
      exact sum_congr rfl fun S _ => card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
    have hβ : Fintype.card β' = ∑ _ : β', (1 : ℕ) := by simp
    rw [hcardNT, hβ, ← sum_add_distrib]
    have hfib := Fintype.card_congr (Equiv.sigmaFiberEquiv blk)
    rw [Fintype.card_sigma] at hfib
    rw [← hfib]
    exact sum_congr rfl fun S _ => (hTtree S).card_edgeFinset

end NearForest

section Term

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

/-- The edge length `max(d_ij, λ)` as a function of unordered pairs of labels. -/
noncomputable def lenE (lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => max (dipoleDist (c i) (c j)) lam) fun i j => by rw [dipoleDist_comm]

end Term

end Limits

end MultipoleBKT

end
