/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.Pointwise
public import MultipoleBKT.Appendix.SmallIntegral.LemmaA6

/-!
# Comparing the upper integral with the Appendix A model

The paper: Proposition 5.18,
 and Lemma A.4, eq. (A.19).
The pointwise comparison `jFullIntegrand_le_integrandJ` identifies tree edges,
radial factors, separation indicators and densities. The left side vanishes
when a selected radius is zero. The bridge is shared by the logarithmic integral
proofs in `RouteRaw` and the lower activity estimates.
-/

@[expose] public section

open MeasureTheory Finset SimpleGraph
open TwoComponentCoulomb (box)
open scoped NNReal ENNReal

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Parity Quadratic Peeling Multipole SetPartition

variable {χ : ℂ → ℝ}

theorem graphPairs_eq_edgesOf {W : Finset ℕ} (G : SimpleGraph W) :
    graphPairs G = Multipole.edgesOf G := by
  ext p
  rw [mem_graphPairs, Multipole.mem_edgesOf]

theorem edgesOf_subset_pairsOn {W : Finset ℕ} (G : SimpleGraph W) :
    Multipole.edgesOf G ⊆ pairsOn W := by
  rw [← graphPairs_eq_edgesOf]
  exact graphPairs_subset_pairsOn G

theorem extendConfig_apply_coe (W : Finset ℕ) (y : W → ℂ × ℂ) (i : W) :
    extendConfig W y i = y i := by
  simp [extendConfig, i.2]

open scoped Classical in
/-- **The pointwise comparison of the integrands of `J`.** -/
theorem jFullIntegrand_le_integrandJ {β lam M ε₀ : ℝ} (p₀ : ℕ) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id))
    (hW : (coarsen X (Finset.univ.image Xs)).biUnion id = X.biUnion id)
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X)
    (hhat : ∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S ∈ (Xs l).subtype (· ∈ X),
      blockRadius hX (fun i => dipoleLength (z i)) S ≤
        blockRadius hX (fun i => dipoleLength (z i)) (hatS l z))
    (y : X.biUnion id → ℂ × ℂ) :
    jFullIntegrand M lam ε₀ (truncationScale p₀ β lam) χ β X Xs Ta Tb y ≤
      SmallIntegral.integrandJ χ β lam M ε₀ p₀ hX Xs (fun l => Multipole.edgesOf (Ta l))
        (Multipole.edgesOf Tb) hatS y := by
  set R := truncationScale p₀ β lam with hR
  set c := extendConfig (X.biUnion id) y with hc
  have hcy : ∀ i : (X.biUnion id), c i = y i := extendConfig_apply_coe (X.biUnion id) y
  -- the factors of the right side
  set U := univ.biUnion fun l => (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta l))).edgeFinset
    with hU
  set kw : Sym2 (X.biUnion id) → ℝ := keptWeight (dipoleDistOn y) (absIndicator M lam ε₀ R y) with hkw
  set KEPT' := ∏ e ∈ U, kw e with hKEPT'
  set RAD' := ∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hatS l y),
      blockRadius hX (fun i => dipoleLength (y i)) S ^ 2 with hRAD'
  set EVEN' := ∏ e ∈ (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf Tb)).edgeFinset,
      (absWeight (fun i => dipoleLength (y i)) (dipoleDistOn y)
        (absIndicator M lam ε₀ R y) e ^ 2 + SmallIntegral.linkE M lam y e) with hEVEN'
  set IND := ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) with hIND
  set DENS' := ∏ i, SmallIntegral.cutDens χ β lam (ε₀ * R) (y i) with hDENS'
  set TAIL' := SmallIntegral.tailJ (fun i => dipoleLength (y i)) (dipoleDistOn y) U with hTAIL'
  have hRHS : SmallIntegral.integrandJ χ β lam M ε₀ p₀ hX Xs (fun l => Multipole.edgesOf (Ta l))
      (Multipole.edgesOf Tb) hatS y = TAIL' * RAD' * KEPT' * EVEN' * IND * DENS' := rfl
  -- the factors of the left side
  set KEPT := ∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e with hKEPT
  set RAD := ∏ l, radialExceptMax c (Xs l) with hRAD
  set EVEN := ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e with hEVEN
  set DENS := ∏ i : (X.biUnion id), (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
      (Metric.closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((y i).1 - (y i).2)) with hDENS
  have hLHS : jFullIntegrand M lam ε₀ R χ β X Xs Ta Tb y =
      jTail c X Xs Ta * RAD * KEPT * EVEN * IND * DENS := rfl
  rw [hLHS, hRHS]
  -- the densities
  have hdens : DENS = DENS' := by
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold SmallIntegral.cutDens Limits.pairDensity
    congr 1
    by_cases hz : ‖(y i).1 - (y i).2‖ ≤ ε₀ * R
    · rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_zero_right] using hz),
        Set.indicator_of_mem (show ‖(y i).1 - (y i).2‖ ∈ Set.Iic (ε₀ * R) from hz)]
      rfl
    · rw [Set.indicator_of_notMem (by simpa [Metric.mem_closedBall, dist_zero_right] using hz),
        Set.indicator_of_notMem (show ‖(y i).1 - (y i).2‖ ∉ Set.Iic (ε₀ * R) from hz)]
  -- the even weights
  have hTbW : Multipole.edgesOf Tb ⊆ pairsOn (X.biUnion id) := hW ▸ edgesOf_subset_pairsOn Tb
  have heven : EVEN = EVEN' := by
    have h1 := prod_graphPairs Tb (fun i j => absEvenWeight M lam ε₀ R (c i) (c j))
      fun i j => absEvenWeight_comm M lam ε₀ R _ _
    have h2 := prod_pairs_eq_prod_edgeFinset (W := X.biUnion id) hTbW
      (fun i j => absEvenWeight M lam ε₀ R (c i) (c j)) fun i j => absEvenWeight_comm M lam ε₀ R _ _
    rw [graphPairs_eq_edgesOf] at h1
    rw [hEVEN]
    refine (h1.symm.trans h2).trans (Finset.prod_congr rfl fun e _ => ?_)
    induction e using Sym2.ind with
    | h i j =>
      simp only [Sym2.lift_mk, hcy]
      have habs : absWeight (fun i => dipoleLength (y i)) (dipoleDistOn y)
          (absIndicator M lam ε₀ R y) s(i, j) = absOddWeight M lam ε₀ R (y i) (y j) := by
        unfold absOddWeight
        exact absWeight_on M lam ε₀ R y i j
      rw [habs]
      unfold absEvenWeight SmallIntegral.linkE
      rw [Limits.symmLift_mk]
  -- the kept weights
  have hkwf : ∀ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e =
      ∏ e ∈ (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta l))).edgeFinset, kw e := by
    intro l
    have hsub : Multipole.edgesOf (Ta l) ⊆ pairsOn (X.biUnion id) :=
      (edgesOf_subset_pairsOn (Ta l)).trans
        (pairsOn_mono (Finset.biUnion_subset_biUnion_of_subset_left _ (hXs l)))
    set f : ℕ → ℕ → ℝ := fun i j => ((if MultipoleLinked M lam (c i) (c j) then 0 else 1) *
        (if dipoleDist (c i) (c j) ≤ 17 * ε₀ * R then 1 else 0)) / dipoleDist (c i) (c j) ^ 2
      with hf
    have hfs : ∀ i j, f i j = f j i := by
      intro i j
      simp only [hf, dipoleDist_comm (c i) (c j), propext (Quadratic.multipoleLinked_comm (a := c i))]
    have h1 := prod_graphPairs (Ta l) f hfs
    have h2 := prod_pairs_eq_prod_edgeFinset (W := X.biUnion id) hsub f hfs
    rw [graphPairs_eq_edgesOf] at h1
    calc ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e
        = ∏ e ∈ (Ta l).edgeFinset, Sym2.lift ⟨fun i j : (Xs l).biUnion id => f i j,
            fun i j => hfs i j⟩ e := by
          refine Finset.prod_congr rfl fun e _ => ?_
          induction e using Sym2.ind with
          | h i j => rfl
      _ = ∏ e ∈ (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta l))).edgeFinset,
            Sym2.lift ⟨fun i j : (X.biUnion id) => f i j, fun i j => hfs i j⟩ e := h1.symm.trans h2
      _ = _ := by
          refine Finset.prod_congr rfl fun e _ => ?_
          induction e using Sym2.ind with
          | h i j =>
            simp only [Sym2.lift_mk, hf, hcy, hkw]
            rfl
  have hdisjE : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      fun l => (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta l))).edgeFinset := by
    intro l _ l' _ hll'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | h i j =>
      rw [mem_edgeFinset, mem_edgeSet] at he he'
      have hmem : ∀ m, (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta m))).Adj i j →
          (i : ℕ) ∈ (Xs m).biUnion id := by
        intro m hadj
        rw [Multipole.graphOf, fromRel_adj] at hadj
        rcases hadj.2 with h | h
        · exact (mem_pairsOn.1 (edgesOf_subset_pairsOn (Ta m) h)).1
        · exact (mem_pairsOn.1 (edgesOf_subset_pairsOn (Ta m) h)).2.1
      exact Finset.disjoint_left.1 (disjoint_biUnion_of_disjoint hX (hXs l) (hXs l')
        (hdisj l l' hll')) (hmem l he) (hmem l' he')
  have hkept : KEPT = KEPT' := by
    rw [hKEPT, hKEPT', hU, Finset.prod_biUnion hdisjE]
    exact Finset.prod_congr rfl fun l _ => hkwf l
  -- nonnegativity
  have hkw0 : ∀ e, 0 ≤ kw e := fun e => div_nonneg (absIndicator_nonneg M lam ε₀ R y e) (sq_nonneg _)
  have hKEPT0 : 0 ≤ KEPT' := prod_nonneg fun e _ => hkw0 e
  have hEVEN0 : 0 ≤ EVEN := prod_nonneg fun e _ => absEvenLift_nonneg M lam ε₀ R c e
  have hIND0 : 0 ≤ IND := prod_nonneg fun S _ => by split_ifs <;> norm_num
  have hDENS0 : 0 ≤ DENS' := prod_nonneg fun i _ => SmallIntegral.cutDens_nonneg _ _
  have hRAD0 : 0 ≤ RAD := prod_nonneg fun l _ => radialExceptMax_nonneg c _
  have hRAD'0 : 0 ≤ RAD' := prod_nonneg fun l _ => prod_nonneg fun S _ => sq_nonneg _
  have hTAIL'0 : 0 ≤ TAIL' := by
    rw [hTAIL']
    unfold SmallIntegral.tailJ
    split_ifs
    · exact sq_nonneg _
    · exact zero_le_one
  rw [hkept, heven, hdens]
  by_cases hK0 : KEPT' = 0
  · rw [hK0]
    simp only [mul_zero, zero_mul, le_refl]
  -- the radial factors
  have hr : (fun i : (X.biUnion id) => dipoleLength (y i)) = fun i : (X.biUnion id) => ‖(c i).1 - (c i).2‖ := by
    funext i
    rw [hcy]
    rfl
  have hrad : RAD ≤ RAD' := by
    refine Finset.prod_le_prod₀ (fun l _ => radialExceptMax_nonneg c _) fun l _ => ?_
    set Y := Xs l
    obtain ⟨hmemS, hmax⟩ := hhat l y
    set Ŝ : X := hatS l y
    have hŜY : (Ŝ : Finset ℕ) ∈ Y := (Finset.mem_subtype.1 hmemS)
    have hbr : ∀ S : X, blockRadius hX (fun i => dipoleLength (y i)) S = blockRad c S := by
      intro S
      rw [hr]
      exact blockRadius_eq_blockRad hX c S
    have hŜmax : ∀ S : Y, blockRad c S ≤ blockRad c (Ŝ : Finset ℕ) := by
      intro S
      have := hmax ⟨S, hXs l S.2⟩ (Finset.mem_subtype.2 S.2)
      rwa [hbr, hbr] at this
    have hYeq : blockRad c (Ŝ : Finset ℕ) = blockRad c (Y.biUnion id) :=
      blockRad_biUnion_eq c (Ŝ := ⟨Ŝ, hŜY⟩) hŜmax
    rcases (blockRad_nonneg c (Ŝ : Finset ℕ)).eq_or_lt with h0 | hpos
    · unfold radialExceptMax
      rw [← hYeq, ← h0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      exact prod_nonneg fun S _ => sq_nonneg _
    · rw [radialExceptMax_eq hŜY hYeq hpos]
      refine le_of_eq (Eq.symm ?_)
      refine Finset.prod_bij (fun S _ => (S : Finset ℕ)) (fun S hS => ?_)
        (fun S _ S' _ h => Subtype.ext h) (fun T hT => ?_) (fun S _ => ?_)
      · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
        exact Finset.mem_erase.2 ⟨fun h => hne (Subtype.ext h), Finset.mem_subtype.1 hS⟩
      · obtain ⟨hne, hT⟩ := Finset.mem_erase.1 hT
        refine ⟨⟨T, hXs l hT⟩, Finset.mem_erase.2 ⟨fun h => hne (congrArg Subtype.val h),
          Finset.mem_subtype.2 hT⟩, rfl⟩
      · rw [hbr]
  -- the tails
  have htail : jTail c X Xs Ta ≤ TAIL' := by
    have hjT1 : jTail c X Xs Ta ≤ 1 := by
      unfold jTail
      refine pow_le_one₀ (div_nonneg (blockRad_nonneg c _) (le_max_of_le_right
        (blockRad_nonneg c _))) ?_
      exact div_le_one_of_le₀ (le_max_right _ _) (le_max_of_le_right (blockRad_nonneg c _))
    rw [hTAIL']
    unfold SmallIntegral.tailJ
    split_ifs with hUne
    swap
    · exact hjT1
    set F := univ.fold max 0 fun i : (X.biUnion id) => dipoleLength (y i) with hF
    set m₁ := U.sup' hUne (dipoleDistOn y) with hm₁
    set m := ((Finset.univ.sup fun l => maxEdgeDist c (Ta l) : ℝ≥0) : ℝ) with hm
    set Rr := blockRad c (X.biUnion id) with hRr
    have hF0 : 0 ≤ F := (Finset.le_fold_max _).2 (Or.inl le_rfl)
    have hRF : Rr ≤ F := by
      refine blockRad_le hF0 fun i hi => ?_
      refine (Finset.le_fold_max _).2 (Or.inr ⟨⟨i, hi⟩, mem_univ _, ?_⟩)
      rw [← hcy ⟨i, hi⟩]
      rfl
    -- `m₁ ≤ m`
    have hm₁m : m₁ ≤ m := by
      refine Finset.sup'_le _ _ fun e he => ?_
      obtain ⟨l, -, hel⟩ := Finset.mem_biUnion.1 he
      induction e using Sym2.ind with
      | h i j =>
        rw [mem_edgeFinset, mem_edgeSet, Multipole.graphOf, fromRel_adj] at hel
        have key : ∀ a b : (X.biUnion id), ((a : ℕ), (b : ℕ)) ∈ Multipole.edgesOf (Ta l) →
            dipoleDistOn y s(a, b) ≤ m := by
          intro a b hab
          obtain ⟨h1, h2, -, hadj⟩ := Multipole.mem_edgesOf.1 hab
          have hmemE : s((⟨a, h1⟩ : (Xs l).biUnion id), ⟨b, h2⟩) ∈ (Ta l).edgeFinset :=
            mem_edgeFinset.2 hadj
          have hle : (distOn (fun x : (Xs l).biUnion id => c x) s(⟨a, h1⟩, ⟨b, h2⟩)).toNNReal ≤
              maxEdgeDist c (Ta l) :=
            Finset.le_sup (f := fun e => (distOn (fun x : (Xs l).biUnion id => c x) e).toNNReal)
              hmemE
          have hle' : maxEdgeDist c (Ta l) ≤ Finset.univ.sup fun l => maxEdgeDist c (Ta l) :=
            Finset.le_sup (f := fun l => maxEdgeDist c (Ta l)) (mem_univ l)
          have hd : dipoleDistOn y s(a, b) =
              distOn (fun x : (Xs l).biUnion id => c x) s(⟨a, h1⟩, ⟨b, h2⟩) := by
            show dipoleDist (y a) (y b) = dipoleDist (c a) (c b)
            rw [hcy, hcy]
          rw [hd]
          have h3 := (Real.toNNReal_le_iff_le_coe).1 (hle.trans hle')
          exact h3
        rcases hel.2 with h | h
        · exact key i j h
        · rw [Sym2.eq_swap]
          exact key j i h
    -- `m₁ > 0`
    have hm₁pos : 0 < m₁ := by
      obtain ⟨e, he⟩ := hUne
      have hkne : kw e ≠ 0 := fun h0 => hK0 (Finset.prod_eq_zero he h0)
      have hd : dipoleDistOn y e ≠ 0 := by
        intro h0
        apply hkne
        rw [hkw, keptWeight, h0]
        simp
      exact lt_of_lt_of_le ((dipoleDistOn_nonneg y e).lt_of_ne (Ne.symm hd))
        (Finset.le_sup' _ he)
    have hmpos : 0 < m := hm₁pos.trans_le hm₁m
    refine pow_le_pow_left₀ (div_nonneg (blockRad_nonneg c _)
      (le_max_of_le_right (blockRad_nonneg c _))) ?_ 2
    refine le_min ?_ (div_le_one_of_le₀ (le_max_right _ _) (le_max_of_le_right
      (blockRad_nonneg c _)))
    calc Rr / max m Rr ≤ Rr / m :=
          div_le_div_of_nonneg_left (blockRad_nonneg c _) hmpos (le_max_left _ _)
      _ ≤ F / m := div_le_div_of_nonneg_right hRF hmpos.le
      _ ≤ F / m₁ := div_le_div_of_nonneg_left hF0 hm₁pos hm₁m
  -- assembling
  have hjT0 : 0 ≤ jTail c X Xs Ta := sq_nonneg _
  have h1 : jTail c X Xs Ta * RAD ≤ TAIL' * RAD' := mul_le_mul htail hrad hRAD0 hTAIL'0
  have hrest : 0 ≤ KEPT' * EVEN' * IND * DENS' := by
    rw [← heven]
    exact mul_nonneg (mul_nonneg (mul_nonneg hKEPT0 hEVEN0) hIND0) hDENS0
  calc jTail c X Xs Ta * RAD * KEPT' * EVEN' * IND * DENS'
      = (jTail c X Xs Ta * RAD) * (KEPT' * EVEN' * IND * DENS') := by ring
    _ ≤ (TAIL' * RAD') * (KEPT' * EVEN' * IND * DENS') := mul_le_mul_of_nonneg_right h1 hrest
    _ = TAIL' * RAD' * KEPT' * EVEN' * IND * DENS' := by ring

end BoundedUpper

end UpperBound

end MultipoleBKT

end
