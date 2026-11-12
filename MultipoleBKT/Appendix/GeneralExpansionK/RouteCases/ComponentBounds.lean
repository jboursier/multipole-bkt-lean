/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.LongEdge

/-!
# Pointwise component bounds for cases A, B and D

See (A.55), (A.57)
and (A.60). Drop surplus factors only after extracting the
marked error. The standard and marked component trees are relative to the
component's own subpartition. The marked tree comes from prescribed strict ears.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Peeling

variable {V : Type*}

/-- The far geometry makes the absolute odd weight at most one. -/
theorem absWeight_le_one_of_far {r : V → ℝ} {d c : Sym2 V → ℝ}
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    {i j : V} (hfar : min (r i) (r j) ≤ d s(i, j)) : absWeight r d c s(i, j) ≤ 1 := by
  have hd0 := hd s(i, j)
  rcases hd0.eq_or_lt with hzero | hpos
  · simp [absWeight, ← hzero]
  have hm : 0 < d s(i, j) * max (max (r i) (r j)) (d s(i, j)) :=
    mul_pos hpos (hpos.trans_le (le_max_right _ _))
  have hn : r i * r j ≤ d s(i, j) * max (max (r i) (r j)) (d s(i, j)) := by
    calc r i * r j = min (r i) (r j) * max (r i) (r j) := (min_mul_max _ _).symm
         _ ≤ d s(i, j) * max (r i) (r j) :=
           mul_le_mul_of_nonneg_right hfar ((hr i).trans (le_max_left _ _))
         _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hpos.le
  unfold absWeight
  exact (mul_le_mul_of_nonneg_right ((div_le_one hm).2 hn) (hc _)).trans
    ((one_mul _).le.trans (hc1 _))

/-- A long odd edge has its full quadratic gain, before any tree is chosen. -/
theorem absWeight_le_quadratic {r : V → ℝ} {d c : Sym2 V → ℝ}
    (hr : ∀ i, 0 ≤ r i) (_hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    {i j : V} {R H : ℝ} (hR : ∀ i, r i ≤ R) (hH : 0 < H) (hHd : H ≤ d s(i, j)) :
    absWeight r d c s(i, j) ≤ R ^ 2 / H ^ 2 := by
  have hd : 0 < d s(i, j) := hH.trans_le hHd
  have hden : 0 < d s(i, j) * max (max (r i) (r j)) (d s(i, j)) :=
    mul_pos hd (hd.trans_le (le_max_right _ _))
  have hn : r i * r j ≤ R ^ 2 := by
    rw [sq]
    exact mul_le_mul (hR i) (hR j) (hr j) ((hr i).trans (hR i))
  have hD : H ^ 2 ≤ d s(i, j) * max (max (r i) (r j)) (d s(i, j)) := by
    rw [sq]
    exact mul_le_mul hHd (hHd.trans (le_max_right _ _)) hH.le hd.le
  unfold absWeight
  have hnon : 0 ≤ radProd r s(i, j) / (d s(i, j) * max (radMax r s(i, j)) (d s(i, j))) :=
    div_nonneg (mul_nonneg (hr i) (hr j)) hden.le
  exact (mul_le_of_le_one_right hnon (hc1 _)).trans
    (div_le_div₀ (sq_nonneg R) hn (pow_pos hH 2) hD)

section Components

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
variable {E : SimpleGraph (X.biUnion id)}
variable (hE : Parity.IsRelEulerianConnected X E)
variable (r : X.biUnion id → ℝ) (d c : Sym2 (X.biUnion id) → ℝ)
variable (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e)
variable (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
variable (hfar : ∀ i j, E.Adj i j → min (r i) (r j) ≤ d s(i, j))

include hr hd hc hc1 hfar

private theorem component_weights_one {e : Sym2 (X.biUnion id)} (he : e ∈ E.edgeSet) :
    absWeight r d c e ≤ 1 := by
  induction e using Sym2.ind with
  | h i j => exact absWeight_le_one_of_far hr hd hc hc1 (hfar i j he)

open scoped Classical in
/-- Cases A, B, C and E use this standard component reduction, after any surplus
mark has been extracted. The skeleton is selected before the error subsets. -/
theorem standard_odd_component :
    ∃ (v : X.biUnion id) (T : SimpleGraph (X.biUnion id)),
      IsRelTree X T ∧ T ≤ oddSkeleton hX E hE ∧ (∀ i, r i ≤ r v) ∧
      ∏ e ∈ E.edgeFinset, absWeight r d c e ≤
        (∏ S ∈ univ.erase (MultipoleBKT.blockOf hX v), blockRadius hX r S ^ 2) *
          ∏ e ∈ T.edgeFinset, keptWeight d c e := by
  obtain ⟨v, T, hT, hTK, hmax, hb⟩ := ordinary_component hX hE r d c hr hd hc hc1
  have hsub := edgeFinset_mono (oddSkeleton_spec hX hE).1
  have hdrop : ∏ e ∈ E.edgeFinset, absWeight r d c e ≤
      ∏ e ∈ (oddSkeleton hX E hE).edgeFinset, absWeight r d c e := by
    rw [← prod_sdiff hsub]
    exact mul_le_of_le_one_left (prod_nonneg fun e _ => absWeight_nonneg hr hd hc e)
      (prod_le_one₀ (fun e _ => absWeight_nonneg hr hd hc e)
        (fun e he => component_weights_one r d c hr hd hc hc1 hfar
          (mem_edgeFinset.1 (mem_sdiff.1 he).1)))
  exact ⟨v, T, hT, hTK, hmax, hdrop.trans hb⟩

open scoped Classical in
/-- Case B retains the error on a surplus odd edge while dropping the other
surplus factors. The two endpoint radii are bounded by the global radius `R`. -/
theorem surplus_odd_component {x y : X.biUnion id}
    (_hxy : E.Adj x y) (hnot : ¬ (oddSkeleton hX E hE).Adj x y)
    {R : ℝ} (hR : ∀ i, r i ≤ R) :
    ∃ (v : X.biUnion id) (T : SimpleGraph (X.biUnion id)),
      IsRelTree X T ∧ T ≤ oddSkeleton hX E hE ∧
      r x * r y * (∏ e ∈ E.edgeFinset.erase s(x, y), absWeight r d c e) ≤
        R ^ 2 * (∏ S ∈ univ.erase (MultipoleBKT.blockOf hX v), blockRadius hX r S ^ 2) *
          ∏ e ∈ T.edgeFinset, keptWeight d c e := by
  obtain ⟨v, T, hT, hTK, -, hb⟩ := ordinary_component hX hE r d c hr hd hc hc1
  have hsub : (oddSkeleton hX E hE).edgeFinset ⊆ E.edgeFinset.erase s(x, y) := by
    intro e he
    refine mem_erase.2 ⟨fun heq => hnot (mem_edgeFinset.1 (heq ▸ he)),
      mem_edgeFinset.2 ((edgeSet_mono (oddSkeleton_spec hX hE).1) (mem_edgeFinset.1 he))⟩
  have hdrop : ∏ e ∈ E.edgeFinset.erase s(x, y), absWeight r d c e ≤
      ∏ e ∈ (oddSkeleton hX E hE).edgeFinset, absWeight r d c e := by
    rw [← prod_sdiff hsub]
    exact mul_le_of_le_one_left (prod_nonneg fun e _ => absWeight_nonneg hr hd hc e)
      (prod_le_one₀ (fun e _ => absWeight_nonneg hr hd hc e)
        (fun e he => component_weights_one r d c hr hd hc hc1 hfar
          (mem_edgeFinset.1 (mem_of_mem_erase (mem_sdiff.1 he).1))))
  have hrad : r x * r y ≤ R ^ 2 := by
    rw [sq]
    exact mul_le_mul (hR x) (hR y) (hr y) ((hr x).trans (hR x))
  refine ⟨v, T, hT, hTK, ?_⟩
  calc _ ≤ R ^ 2 * ((∏ S ∈ univ.erase (MultipoleBKT.blockOf hX v), blockRadius hX r S ^ 2) *
          ∏ e ∈ T.edgeFinset, keptWeight d c e) :=
      mul_le_mul hrad (hdrop.trans hb) (prod_nonneg fun e _ => absWeight_nonneg hr hd hc e) (sq_nonneg _)
       _ = _ := by ring

open scoped Classical in
/-- Case D for the full original component, including all its surplus edges.
The prescribed marked base-cycle deletion remains visible in `caseD_component`. -/
theorem marked_odd_component {x y : X.biUnion id}
    (hxy : (oddSkeleton hX E hE).Adj x y) :
    ∃ T : SimpleGraph (X.biUnion id), IsRelTree X T ∧ T ≤ oddSkeleton hX E hE ∧
      s(x, y) ∉ T.edgeSet ∧
      r x * r y * (∏ e ∈ E.edgeFinset.erase s(x, y), absWeight r d c e) ≤
        (∏ S : X, blockRadius hX r S ^ 2) * ∏ e ∈ T.edgeFinset, keptWeight d c e := by
  have hblock0 : ∀ S : X, 0 ≤ blockRadius hX r S := by
    intro S
    obtain ⟨i, hi⟩ := MultipoleBKT.blockOf_surjective hX S
    exact (hr i).trans (hi ▸ le_blockRadius (hX := hX) r i)
  obtain ⟨P, Qs, T, -, -, hT, hTK, hmark, hb⟩ := caseD_component hX hE hxy r (blockRadius hX r) d c
    hr hblock0 (le_blockRadius r) hd hc hc1
  have hsub := Finset.erase_subset_erase s(x, y) (edgeFinset_mono (oddSkeleton_spec hX hE).1)
  have hdrop : ∏ e ∈ E.edgeFinset.erase s(x, y), absWeight r d c e ≤
      ∏ e ∈ (oddSkeleton hX E hE).edgeFinset.erase s(x, y), absWeight r d c e := by
    rw [← prod_sdiff hsub]
    exact mul_le_of_le_one_left (prod_nonneg fun e _ => absWeight_nonneg hr hd hc e)
      (prod_le_one₀ (fun e _ => absWeight_nonneg hr hd hc e)
        (fun e he => component_weights_one r d c hr hd hc hc1 hfar
          (mem_edgeFinset.1 (mem_of_mem_erase (mem_sdiff.1 he).1))))
  exact ⟨T, hT, hTK, hmark, (mul_le_mul_of_nonneg_left hdrop (mul_nonneg (hr x) (hr y))).trans hb⟩

open scoped Classical in
/-- An omitted long surplus odd edge supplies `R²/H²` without weakening the
exponent. The remaining skeleton has its ordinary component tree. -/
theorem long_surplus_odd_component {x y : X.biUnion id}
    (hxy : E.Adj x y) (hnot : ¬ (oddSkeleton hX E hE).Adj x y)
    {R H : ℝ} (hR : ∀ i, r i ≤ R) (hH : 0 < H) (hHd : H ≤ d s(x, y)) :
    ∃ (v : X.biUnion id) (T : SimpleGraph (X.biUnion id)),
      IsRelTree X T ∧ T ≤ oddSkeleton hX E hE ∧
      ∏ e ∈ E.edgeFinset, absWeight r d c e ≤
        (R ^ 2 / H ^ 2) *
          (∏ S ∈ univ.erase (MultipoleBKT.blockOf hX v), blockRadius hX r S ^ 2) *
          ∏ e ∈ T.edgeFinset, keptWeight d c e := by
  obtain ⟨v, T, hT, hTK, -, hb⟩ := ordinary_component hX hE r d c hr hd hc hc1
  have he : s(x, y) ∈ E.edgeFinset \ (oddSkeleton hX E hE).edgeFinset :=
    mem_sdiff.2 ⟨mem_edgeFinset.2 hxy, fun h => hnot (mem_edgeFinset.1 h)⟩
  have hdrop := internal_surplus_product E.edgeFinset (oddSkeleton hX E hE).edgeFinset
    (edgeFinset_mono (oddSkeleton_spec hX hE).1) (absWeight r d c)
    (fun e _ => absWeight_nonneg hr hd hc e)
    (fun e he => component_weights_one r d c hr hd hc hc1 hfar (mem_edgeFinset.1 he))
    he (absWeight_le_quadratic hr hc hc1 hR hH hHd)
  refine ⟨v, T, hT, hTK, hdrop.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hb (div_nonneg (sq_nonneg _) (sq_nonneg _))).trans_eq (by ring)

end Components

end MultipoleBKT.ExpansionK.RouteCases

end
