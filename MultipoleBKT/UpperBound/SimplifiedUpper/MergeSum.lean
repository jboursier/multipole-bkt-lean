/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.MergeTree

/-!
# The merged sum over trees (proof of Lemma 5.37)

The paper: the paragraph before Lemma 5.37: "For each outer
group `X'`, we retain its full separation indicator through Lemma 4.56, then discard it. For
`|X| ≥ 2`, as in the proof of Lemma 4.57, marking the outer edges of the merged `b`-tree determines
the former groups. The multiplicity is at most `2^{|T^b|} ≤ 2^{|X|-1}`, absorbed into `e^{C|V_X|}`."

**`merge_le`**: for nonnegative group weights `w_A` and pair weights `b`,
`∑_{𝒲} (∑_{T^b ∈ 𝖳_0^{Coarse_X(𝒲)}} ∏_{T^b} b) ∏_{X' ∈ 𝒲} ∑_{𝒱'} ∏_{Y ∈ 𝒱'} w_A(Y)
∑_{T̃ ∈ 𝖳_0^{Coarse_{X'}(𝒱')}} ∏_{T̃} b
≤ 2^{|X|} ∑_{𝒱} ∏_{Y ∈ 𝒱} w_A(Y) ∑_{T ∈ 𝖳_0^{Coarse_X(𝒱)}} ∏_T b`,
the sums over the disjoint families of groups of at least two blocks. The inner choices are
flattened (`innerFlatten`, an injection of `∏_{X' ∈ 𝒲}` of the inner sums into the compatible
pairs `(𝒱, T̃)`), and `(𝒲, T^b, 𝒱, T̃) ↦ (𝒱, T^b ∪ T̃, T^b)` is injective
(`MultipoleBKT.UpperBound.SimplifiedUpper.eq_of_compat`).
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Finset SimpleGraph Multipole Hierarchical SetPartition AbsoluteLower

section Inner

open scoped Classical

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)

/-- The inner choices of an outer group `X'`: the pairs `(𝒱', T̃)` of a disjoint family of groups of
`X'` and a tree of `Coarse_{X'}(𝒱')`. -/
noncomputable def innerChoices (X' : Finset (Finset ℕ)) :
    Finset (Σ _ : Finset (Finset (Finset ℕ)), Finset (ℕ × ℕ)) :=
  (disjointFamilies X' (fun Y => 2 ≤ Y.card)).sigma fun 𝒱' => relTreePairs₀ (coarsen X' 𝒱')

/-- The flattening of a choice of inner groups and trees for each outer group. -/
noncomputable def innerFlatten (𝒲 : Finset (Finset (Finset ℕ)))
    (σ : (X' : Finset (Finset ℕ)) → X' ∈ 𝒲 → Σ _ : Finset (Finset (Finset ℕ)), Finset (ℕ × ℕ)) :
    Finset (Finset (Finset ℕ)) × Finset (ℕ × ℕ) :=
  (𝒲.attach.biUnion fun x => (σ x.1 x.2).1, 𝒲.attach.biUnion fun x => (σ x.1 x.2).2)

variable {𝒲 : Finset (Finset (Finset ℕ))} (h𝒲 : 𝒲 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card))
  {σ : (X' : Finset (Finset ℕ)) → X' ∈ 𝒲 → Σ _ : Finset (Finset (Finset ℕ)), Finset (ℕ × ℕ)}
  (hσ : σ ∈ 𝒲.pi innerChoices)
include hX h𝒲 hσ

omit hX h𝒲 in
theorem innerChoice_mem {X' : Finset (Finset ℕ)} (hX' : X' ∈ 𝒲) :
    (σ X' hX').1 ∈ disjointFamilies X' (fun Y => 2 ≤ Y.card) ∧
      (σ X' hX').2 ∈ relTreePairs₀ (coarsen X' (σ X' hX').1) := by
  have h := mem_pi.1 hσ X' hX'
  rw [innerChoices, mem_sigma] at h
  exact h

/-- The inner pairs of an outer group are inter-block pairs of it. -/
theorem innerChoice_subset_interPairs {X' : Finset (Finset ℕ)} (hX' : X' ∈ 𝒲) :
    (σ X' hX').2 ⊆ interPairs X' := by
  obtain ⟨hsub, -, -⟩ := mem_disjointFamilies.1 h𝒲
  obtain ⟨h1, h2⟩ := innerChoice_mem hσ hX'
  obtain ⟨hsub', hd', h2'⟩ := mem_disjointFamilies.1 h1
  have hX's : IsSubpartition X' := isSubpartition_mono hX (hsub X' hX')
  have hY' : IsSubpartition (coarsen X' (σ X' hX').1) := isSubpartition_coarsen hX's hsub'
    (fun Y hY => card_pos.1 (by have := h2' Y hY; omega)) hd'
  exact (subset_interPairs_of_mem_relTreePairs₀ hY' h2).trans (interPairs_coarsen_subset hsub')

/-- **The flattening restricts to the choices**: the groups of `𝒱` in `X'` and the pairs of `T̃` in
`ℰ^inter(X')` are those chosen for `X'`. -/
theorem innerFlatten_restrict {X' : Finset (Finset ℕ)} (hX' : X' ∈ 𝒲) :
    (innerFlatten 𝒲 σ).1.filter (· ⊆ X') = (σ X' hX').1 ∧
      (innerFlatten 𝒲 σ).2 ∩ interPairs X' = (σ X' hX').2 := by
  obtain ⟨hsub, hdisj, -⟩ := mem_disjointFamilies.1 h𝒲
  -- the outer group of a point
  have hgroup : ∀ (x : 𝒲) {i : ℕ}, i ∈ x.1.biUnion id → i ∈ X'.biUnion id → x.1 = X' :=
    fun x i h1 h2 => eq_of_mem_biUnion_of_mem_biUnion hX h𝒲 x.2 hX' h1 h2
  constructor
  · ext Y
    simp only [innerFlatten, mem_filter, mem_biUnion, mem_attach, true_and]
    constructor
    · rintro ⟨⟨x, hYx⟩, hYX'⟩
      obtain ⟨hsub', -, h2'⟩ := mem_disjointFamilies.1 (innerChoice_mem hσ x.2).1
      obtain ⟨S, hS⟩ := card_pos.1 (by have := h2' Y hYx; omega : 0 < Y.card)
      obtain ⟨i, hi⟩ := hX.1 S (hsub x.1 x.2 (hsub' Y hYx hS))
      have hx := hgroup x (subset_biUnion_of_mem (hsub' Y hYx hS) hi)
        (subset_biUnion_of_mem (hYX' hS) hi)
      obtain ⟨x, hx'⟩ := x
      subst hx
      exact hYx
    · intro hY
      obtain ⟨hsub', -, -⟩ := mem_disjointFamilies.1 (innerChoice_mem hσ hX').1
      exact ⟨⟨⟨X', hX'⟩, hY⟩, hsub' Y hY⟩
  · ext q
    simp only [innerFlatten, mem_inter, mem_biUnion, mem_attach, true_and]
    constructor
    · rintro ⟨⟨x, hqx⟩, hqX'⟩
      have hqI := innerChoice_subset_interPairs hX h𝒲 hσ x.2 hqx
      have hx := hgroup x (interPairs_subset_pairsOn_biUnion _ hqI).1
        (interPairs_subset_pairsOn_biUnion _ hqX').1
      obtain ⟨x, hx'⟩ := x
      subst hx
      exact hqx
    · intro hq
      exact ⟨⟨⟨X', hX'⟩, hq⟩, innerChoice_subset_interPairs hX h𝒲 hσ hX' hq⟩

/-- The flattening is a compatible choice. -/
theorem innerFlatten_mem :
    (innerFlatten 𝒲 σ).1 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card) ∧
      (innerFlatten 𝒲 σ).2 ⊆ interPairs X ∧
      Compat 𝒲 (innerFlatten 𝒲 σ).1 (innerFlatten 𝒲 σ).2 := by
  obtain ⟨hsub, hdisj, -⟩ := mem_disjointFamilies.1 h𝒲
  refine ⟨mem_disjointFamilies.2 ⟨fun Y hY => ?_, fun Y hY Y' hY' hne => ?_, fun Y hY => ?_⟩,
    fun q hq => ?_, ⟨fun Y hY => ?_, fun X' hX' => ?_, fun q hq => ?_⟩⟩
  · obtain ⟨x, -, hYx⟩ := mem_biUnion.1 hY
    exact ((mem_disjointFamilies.1 (innerChoice_mem hσ x.2).1).1 Y hYx).trans (hsub x.1 x.2)
  · obtain ⟨x, -, hYx⟩ := mem_biUnion.1 (mem_coe.1 hY)
    obtain ⟨x', -, hYx'⟩ := mem_biUnion.1 (mem_coe.1 hY')
    obtain ⟨hsub₁, hd₁, -⟩ := mem_disjointFamilies.1 (innerChoice_mem hσ x.2).1
    obtain ⟨hsub₂, hd₂, -⟩ := mem_disjointFamilies.1 (innerChoice_mem hσ x'.2).1
    by_cases hxx : x = x'
    · subst hxx
      exact hd₁ hYx hYx' hne
    · have hd := hdisj x.2 x'.2 fun h => hxx (Subtype.ext h)
      exact Finset.disjoint_left.2 fun S hS hS' =>
        Finset.disjoint_left.1 hd (hsub₁ Y hYx hS) (hsub₂ Y' hYx' hS')
  · obtain ⟨x, -, hYx⟩ := mem_biUnion.1 hY
    exact (mem_disjointFamilies.1 (innerChoice_mem hσ x.2).1).2.2 Y hYx
  · obtain ⟨x, -, hqx⟩ := mem_biUnion.1 hq
    exact interPairs_subset_of_subset hX (hsub x.1 x.2)
      (innerChoice_subset_interPairs hX h𝒲 hσ x.2 hqx)
  · obtain ⟨x, -, hYx⟩ := mem_biUnion.1 hY
    exact ⟨x.1, x.2, (mem_disjointFamilies.1 (innerChoice_mem hσ x.2).1).1 Y hYx⟩
  · obtain ⟨h1, h2⟩ := innerFlatten_restrict hX h𝒲 hσ hX'
    rw [h1, h2]
    exact (innerChoice_mem hσ hX').2
  · obtain ⟨x, -, hqx⟩ := mem_biUnion.1 hq
    exact mem_biUnion.2 ⟨x.1, x.2, innerChoice_subset_interPairs hX h𝒲 hσ x.2 hqx⟩

end Inner

/-! ### The product of the inner sums -/

section Product

open scoped Classical

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
include hX

/-- **The product of the inner sums of the outer groups** is bounded by the sum over the compatible
flattened choices `(𝒱, T̃)`. -/
theorem prod_inner_le {𝒲 : Finset (Finset (Finset ℕ))}
    (h𝒲 : 𝒲 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card)) (wA : Finset (Finset ℕ) → ℝ)
    (hwA : ∀ Y, 0 ≤ wA Y) (b : ℕ × ℕ → ℝ) (hb : ∀ q, 0 ≤ b q) :
    ∏ X' ∈ 𝒲, (∑ 𝒱' ∈ disjointFamilies X' (fun Y => 2 ≤ Y.card),
        (∏ Y ∈ 𝒱', wA Y) * ∑ T ∈ relTreePairs₀ (coarsen X' 𝒱'), ∏ q ∈ T, b q) ≤
      ∑ q ∈ (disjointFamilies X (fun Y => 2 ≤ Y.card) ×ˢ (interPairs X).powerset).filter
          (fun q => Compat 𝒲 q.1 q.2), (∏ Y ∈ q.1, wA Y) * ∏ p ∈ q.2, b p := by
  obtain ⟨hsub, hdisj, h2⟩ := mem_disjointFamilies.1 h𝒲
  set w : (Σ _ : Finset (Finset (Finset ℕ)), Finset (ℕ × ℕ)) → ℝ :=
    fun r => (∏ Y ∈ r.1, wA Y) * ∏ p ∈ r.2, b p with hw
  set w' : Finset (Finset (Finset ℕ)) × Finset (ℕ × ℕ) → ℝ :=
    fun q => (∏ Y ∈ q.1, wA Y) * ∏ p ∈ q.2, b p with hw'
  have hL : ∀ X', (∑ 𝒱' ∈ disjointFamilies X' (fun Y => 2 ≤ Y.card),
      (∏ Y ∈ 𝒱', wA Y) * ∑ T ∈ relTreePairs₀ (coarsen X' 𝒱'), ∏ q ∈ T, b q) =
      ∑ r ∈ innerChoices X', w r := by
    intro X'
    rw [innerChoices, sum_sigma]
    exact sum_congr rfl fun 𝒱' _ => mul_sum _ _ _
  simp_rw [hL]
  rw [prod_sum]
  -- the weight of a choice is that of its flattening
  have hweight : ∀ σ ∈ 𝒲.pi innerChoices,
      ∏ x ∈ 𝒲.attach, w (σ x.1 x.2) = w' (innerFlatten 𝒲 σ) := by
    intro σ hσ
    have hd1 : ((𝒲.attach : Finset 𝒲) : Set 𝒲).PairwiseDisjoint fun x => (σ x.1 x.2).1 := by
      intro x _ x' _ hxx
      obtain ⟨hsub₁, -, h2₁⟩ := mem_disjointFamilies.1 (innerChoice_mem hσ x.2).1
      obtain ⟨hsub₂, -, -⟩ := mem_disjointFamilies.1 (innerChoice_mem hσ x'.2).1
      have hd := hdisj x.2 x'.2 fun h => hxx (Subtype.ext h)
      rw [Function.onFun, Finset.disjoint_left]
      intro Y hY hY'
      obtain ⟨S, hS⟩ := card_pos.1 (by have := h2₁ Y hY; omega : 0 < Y.card)
      exact Finset.disjoint_left.1 hd (hsub₁ Y hY hS) (hsub₂ Y hY' hS)
    have hd2 : ((𝒲.attach : Finset 𝒲) : Set 𝒲).PairwiseDisjoint fun x => (σ x.1 x.2).2 := by
      intro x _ x' _ hxx
      rw [Function.onFun, Finset.disjoint_left]
      intro q hq hq'
      have h1 := innerChoice_subset_interPairs hX h𝒲 hσ x.2 hq
      have h2' := innerChoice_subset_interPairs hX h𝒲 hσ x'.2 hq'
      exact hxx (Subtype.ext (eq_of_mem_biUnion_of_mem_biUnion hX h𝒲 x.2 x'.2
        (interPairs_subset_pairsOn_biUnion _ h1).1 (interPairs_subset_pairsOn_biUnion _ h2').1))
    simp only [hw, hw', innerFlatten]
    rw [prod_mul_distrib, prod_biUnion hd1, prod_biUnion hd2]
  -- the flattening is injective
  have hinj : Set.InjOn (innerFlatten 𝒲) (𝒲.pi innerChoices : Set _) := by
    intro σ₁ hσ₁ σ₂ hσ₂ heq
    funext X' hX'
    obtain ⟨h1, h2⟩ := innerFlatten_restrict hX h𝒲 (mem_coe.1 hσ₁) hX'
    obtain ⟨h1', h2'⟩ := innerFlatten_restrict hX h𝒲 (mem_coe.1 hσ₂) hX'
    rw [heq] at h1 h2
    exact Sigma.ext (h1.symm.trans h1') (heq_of_eq (h2.symm.trans h2'))
  have hmaps : ∀ σ ∈ 𝒲.pi innerChoices, innerFlatten 𝒲 σ ∈
      (disjointFamilies X (fun Y => 2 ≤ Y.card) ×ˢ (interPairs X).powerset).filter
        (fun q => Compat 𝒲 q.1 q.2) := by
    intro σ hσ
    obtain ⟨h1, h2, h3⟩ := innerFlatten_mem hX h𝒲 hσ
    exact mem_filter.2 ⟨mem_product.2 ⟨h1, mem_powerset.2 h2⟩, h3⟩
  rw [sum_congr rfl hweight, ← sum_image hinj]
  refine sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun q _ _ => ?_
  · obtain ⟨σ, hσ, rfl⟩ := mem_image.1 hq
    exact hmaps σ hσ
  · exact mul_nonneg (prod_nonneg fun Y _ => hwA Y) (prod_nonneg fun p _ => hb p)

end Product

/-! ### The merge -/

section Merge

open scoped Classical

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
include hX

/-- A tree of a coarsening of `X` has fewer than `|X|` pairs. -/
theorem card_le_of_mem_relTreePairs₀_coarsen {𝒱 : Finset (Finset (Finset ℕ))}
    (h𝒱 : 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card)) {T : Finset (ℕ × ℕ)}
    (hT : T ∈ relTreePairs₀ (coarsen X 𝒱)) : T.card ≤ X.card := by
  obtain ⟨hsub, hd, h2⟩ := mem_disjointFamilies.1 h𝒱
  have hV := isSubpartition_of_mem_disjointFamilies h𝒱 hX
  have h1 := card_add_one_of_mem_relTreePairs₀ hV hT
  have hc := card_coarsen_add hX hsub (fun Y hY => card_pos.1 (by have := h2 Y hY; omega)) hd
  have hsum : 𝒱.card ≤ ∑ Y ∈ 𝒱, Y.card := by
    rw [card_eq_sum_ones]
    exact sum_le_sum fun Y hY => by have := h2 Y hY; omega
  omega

/-- **The merged sum over trees** (proof of Lemma 5.37): see the module docstring. -/
theorem merge_le (wA : Finset (Finset ℕ) → ℝ) (hwA : ∀ Y, 0 ≤ wA Y) (b : ℕ × ℕ → ℝ)
    (hb : ∀ q, 0 ≤ b q) :
    ∑ 𝒲 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
        (∑ Tb ∈ relTreePairs₀ (coarsen X 𝒲), ∏ q ∈ Tb, b q) *
          ∏ X' ∈ 𝒲, (∑ 𝒱' ∈ disjointFamilies X' (fun Y => 2 ≤ Y.card),
            (∏ Y ∈ 𝒱', wA Y) * ∑ T ∈ relTreePairs₀ (coarsen X' 𝒱'), ∏ q ∈ T, b q) ≤
      2 ^ X.card * ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
        (∏ Y ∈ 𝒱, wA Y) * ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ q ∈ T, b q := by
  set DF := disjointFamilies X (fun Y => 2 ≤ Y.card) with hDF
  set Inner : Finset (Finset (Finset ℕ)) → Finset (Finset (Finset (Finset ℕ)) × Finset (ℕ × ℕ)) :=
    fun 𝒲 => (DF ×ˢ (interPairs X).powerset).filter (fun q => Compat 𝒲 q.1 q.2) with hInner
  set g : (Σ _ : Finset (Finset (Finset ℕ)), Σ _ : Finset (ℕ × ℕ), Finset (ℕ × ℕ)) → ℝ :=
    fun r => (∏ Y ∈ r.1, wA Y) * ∏ q ∈ r.2.1, b q with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r =>
    mul_nonneg (prod_nonneg fun Y _ => hwA Y) (prod_nonneg fun q _ => hb q)
  set Θ : (Σ _ : Finset (Finset (Finset ℕ)),
      Finset (ℕ × ℕ) × (Finset (Finset (Finset ℕ)) × Finset (ℕ × ℕ))) →
      (Σ _ : Finset (Finset (Finset ℕ)), Σ _ : Finset (ℕ × ℕ), Finset (ℕ × ℕ)) :=
    fun z => ⟨z.2.2.1, ⟨z.2.1 ∪ z.2.2.2, z.2.1⟩⟩ with hΘ
  set Dom := DF.sigma fun 𝒲 => relTreePairs₀ (coarsen X 𝒲) ×ˢ Inner 𝒲 with hDom
  set Ω := DF.sigma fun 𝒱 => (relTreePairs₀ (coarsen X 𝒱)).sigma fun T => T.powerset with hΩ
  -- step 1: the inner products
  have hstep1 : ∑ 𝒲 ∈ DF, (∑ Tb ∈ relTreePairs₀ (coarsen X 𝒲), ∏ q ∈ Tb, b q) *
      ∏ X' ∈ 𝒲, (∑ 𝒱' ∈ disjointFamilies X' (fun Y => 2 ≤ Y.card),
        (∏ Y ∈ 𝒱', wA Y) * ∑ T ∈ relTreePairs₀ (coarsen X' 𝒱'), ∏ q ∈ T, b q) ≤
      ∑ z ∈ Dom, g (Θ z) := by
    rw [hDom, sum_sigma]
    refine sum_le_sum fun 𝒲 h𝒲 => ?_
    rw [sum_product, sum_mul]
    refine sum_le_sum fun Tb hTb => ?_
    refine (mul_le_mul_of_nonneg_left (prod_inner_le hX h𝒲 wA hwA b hb)
      (prod_nonneg fun q _ => hb q)).trans (le_of_eq ?_)
    rw [mul_sum]
    refine sum_congr rfl fun q hq => ?_
    have hC := (mem_filter.1 hq).2
    have h𝒱 := (mem_product.1 (mem_filter.1 hq).1).1
    simp only [hg, hΘ]
    rw [prod_union (disjoint_outer_inner hX h𝒲 hC hTb)]
    ring
  -- step 2: the injection into `Ω`
  have hmaps : ∀ z ∈ Dom, Θ z ∈ Ω := by
    intro z hz
    obtain ⟨h𝒲, hz2⟩ := mem_sigma.1 hz
    obtain ⟨hTb, hq⟩ := mem_product.1 hz2
    obtain ⟨hq1, hC⟩ := mem_filter.1 hq
    have h𝒱 := (mem_product.1 hq1).1
    exact mem_sigma.2 ⟨h𝒱, mem_sigma.2 ⟨merged_mem_relTreePairs₀ hX h𝒲 h𝒱 hC hTb,
      mem_powerset.2 subset_union_left⟩⟩
  have hinj : Set.InjOn Θ (Dom : Set _) := by
    intro z₁ hz₁ z₂ hz₂ heq
    obtain ⟨h𝒲₁, hz₁'⟩ := mem_sigma.1 (mem_coe.1 hz₁)
    obtain ⟨h𝒲₂, hz₂'⟩ := mem_sigma.1 (mem_coe.1 hz₂)
    obtain ⟨hTb₁, hq₁⟩ := mem_product.1 hz₁'
    obtain ⟨hTb₂, hq₂⟩ := mem_product.1 hz₂'
    obtain ⟨hq₁', hC₁⟩ := mem_filter.1 hq₁
    obtain ⟨hq₂', hC₂⟩ := mem_filter.1 hq₂
    simp only [hΘ, Sigma.mk.inj_iff, heq_iff_eq] at heq
    obtain ⟨h𝒱, hT, hB⟩ := heq
    have h𝒱₁ := (mem_product.1 hq₁').1
    rw [← h𝒱] at hC₂
    have hdis₁ := disjoint_outer_inner hX h𝒲₁ hC₁ hTb₁
    have hdis₂ := disjoint_outer_inner hX h𝒲₂ hC₂ hTb₂
    have hT' : z₁.2.2.2 = z₂.2.2.2 := by
      rw [← union_sdiff_cancel_left hdis₁, ← union_sdiff_cancel_left hdis₂, hT, hB]
    have hW : z₁.1 = z₂.1 := by
      rw [← hT'] at hC₂
      exact eq_of_compat hX h𝒲₁ h𝒲₂ h𝒱₁ hC₁ hC₂
    obtain ⟨𝒲₁, Tb₁, 𝒱₁, T₁⟩ := z₁
    obtain ⟨𝒲₂, Tb₂, 𝒱₂, T₂⟩ := z₂
    simp only at hW hB h𝒱 hT'
    subst hW hB h𝒱 hT'
    rfl
  have hstep2 : ∑ z ∈ Dom, g (Θ z) ≤ ∑ r ∈ Ω, g r := by
    rw [← sum_image hinj]
    exact sum_le_sum_of_subset_of_nonneg (fun r hr => by
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hr
      exact hmaps z hz) fun r _ _ => hg0 r
  -- step 3: the multiplicity
  have hstep3 : ∑ r ∈ Ω, g r ≤ 2 ^ X.card * ∑ 𝒱 ∈ DF,
      (∏ Y ∈ 𝒱, wA Y) * ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ q ∈ T, b q := by
    rw [hΩ, sum_sigma, mul_sum]
    refine sum_le_sum fun 𝒱 h𝒱 => ?_
    rw [sum_sigma, mul_sum, mul_sum]
    refine sum_le_sum fun T hT => ?_
    simp only [hg]
    rw [sum_const, card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hv0 : 0 ≤ (∏ Y ∈ 𝒱, wA Y) * ∏ q ∈ T, b q :=
      mul_nonneg (prod_nonneg fun Y _ => hwA Y) (prod_nonneg fun q _ => hb q)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num)
      (card_le_of_mem_relTreePairs₀_coarsen hX h𝒱 hT)) hv0
  exact hstep1.trans (hstep2.trans hstep3)

end Merge

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
