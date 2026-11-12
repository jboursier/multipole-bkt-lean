/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.SumEuler
public import MultipoleBKT.LowerBound.AbsoluteLower.LXi

/-!
# Grouping by the components of the odd graph, with external marks

The paper: Lemma 5.35, whose proof
"follows Lemma 4.54, starting from Corollary 5.24": Step 1 of the proof of Lemma 4.54
(Lemma 4.54, eqs. (4.91)–(4.92)) with external marks `V_1^∞` (Definition 5.23).

Edge sets are sets of pairs `(i, j)`, `i < j`, and the marks are a finite set `U` of labels.

* `markEulerPairs X U = Eul^X(U)` (Definition 5.23): the
  `E ⊆ ℰ^inter(X)` with `deg_E(S) + |S ∩ U|` even for every `S ∈ X`;
  `markEulerConnPairs Y U = Eulc^Y(U) = 𝖤^Y ∩ Eul^Y(U)`. For `U = ∅` these are `Eul^X`, `Eulc^Y`.
* `inter_mem_markEulerConnPairs`: the part of `E₁ ∈ Eul^X(U)` in one of its components `Y`
  (`MultipoleBKT.AbsoluteLower.comps`) is in `Eulc^Y(U)`.
* `sum_le_sum_disjointFamilies`: a sum over edge sets grouped by their components is bounded by the
  sum over the disjoint families of groups ("resumming according to the nontrivial connected
  components of the odd graph").
* `sum_evenEdges_le'`: the Penrose bound of the even bonds over a fixed odd skeleton
  (`MultipoleBKT.AbsoluteLower.sum_evenEdges_le`, which only uses `E₁ ⊆ ℰ^inter(X)`).
* `stepOne_le` (the combinatorial core of Lemma 5.35, abstract weights): with odd weights
  `A ≥ 0`, even weights `0 ≤ B ≤ C_b b` on `ℰ^inter(X)`, and mark weights `0 ≤ m ≤ C_m` on
  `U ∩ V_X`,
  `∑_{E₁ ∈ Eul^X(U)} ∏_{E₁} A ∏_{U ∩ V_X} m ∑_{E₂ : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝖤^X} ∏_{E₂} B
  ≤ (C_m C_b)^{|V_X|} ∏_{ℰ^inter(X)} (1 + B) ∑_{𝒱} ∏_{Y ∈ 𝒱} (∑_{E ∈ Eulc^Y(U)} ∏_E A
  ∏_{U ∩ V_Y} m) ∑_{T ∈ 𝖳_0^{Coarse_X(𝒱)}} ∏_T b`,
  the sum over the disjoint families `𝒱` of groups of at least two blocks.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Finset Multipole Hierarchical SetPartition AbsoluteLower

/-! ### Eulerian edge sets with marks -/

section Defs

open scoped Classical

/-- `Eul^X(U)` (Definition 5.23) as edge sets of pairs: the
`E ⊆ ℰ^inter(X)` such that `deg_E(S) + |S ∩ U|` is even for every block `S ∈ X`. -/
noncomputable def markEulerPairs (X : Finset (Finset ℕ)) (U : Finset ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  (interPairs X).powerset.filter fun E => ∀ S ∈ X, Even (blockDeg E S + (S ∩ U).card)

/-- `Eulc^Y(U) = 𝖤^Y ∩ Eul^Y(U)` (Definition 5.23) as edge sets of pairs. -/
noncomputable def markEulerConnPairs (Y : Finset (Finset ℕ)) (U : Finset ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  relEdgeSets Y ∩ markEulerPairs Y U

variable {X : Finset (Finset ℕ)} {U : Finset ℕ}

theorem mem_markEulerPairs {E : Finset (ℕ × ℕ)} :
    E ∈ markEulerPairs X U ↔ E ⊆ interPairs X ∧ ∀ S ∈ X, Even (blockDeg E S + (S ∩ U).card) := by
  rw [markEulerPairs, mem_filter, mem_powerset]

theorem mem_markEulerConnPairs {E : Finset (ℕ × ℕ)} :
    E ∈ markEulerConnPairs X U ↔ E ∈ relEdgeSets X ∧ E ∈ markEulerPairs X U :=
  mem_inter

/-- Without marks, `Eul^X(∅) = Eul^X`. -/
theorem markEulerPairs_empty : markEulerPairs X ∅ = relEulerianPairs X := by
  ext E
  rw [mem_markEulerPairs, mem_relEulerianPairs]
  simp

/-- Without marks, `Eulc^Y(∅) = Eulc^Y`. -/
theorem markEulerConnPairs_empty : markEulerConnPairs X ∅ = relEulerianConnectedPairs X := by
  rw [markEulerConnPairs, markEulerPairs_empty]
  rfl

theorem markEulerConnPairs_eq_empty_of_card_le_one (h : X.card ≤ 1) :
    markEulerConnPairs X U = ∅ := by
  rw [markEulerConnPairs, relEdgeSets_eq_empty_of_card_le_one h, empty_inter]

/-- The part of `E₁ ∈ Eul^X(U)` in a component `Y` of `E₁` is in `Eulc^Y(U)`. -/
theorem inter_mem_markEulerConnPairs (hX : IsSubpartition X) {E₁ : Finset (ℕ × ℕ)}
    (hE₁ : E₁ ∈ markEulerPairs X U) {Y : Finset (Finset ℕ)} (hY : Y ∈ comps X E₁) :
    E₁ ∩ interPairs Y ∈ markEulerConnPairs Y U := by
  have hE := (mem_markEulerPairs.1 hE₁).1
  obtain ⟨q, hq, hqY⟩ := mem_comps.1 hY
  have hq1 := (mem_pairsOn.1 (interPairs_subset_pairsOn (hE hq))).1
  obtain ⟨B₀, hB₀, hqB₀⟩ := mem_biUnion_id.1 hq1
  have hspec := reachedBlocks_spec hX hE hB₀ hqB₀
  rw [hqY] at hspec
  have hqI : q ∈ interPairs Y := mem_interPairs_of_mem_comps hX hE hY hq
    (Or.inl (subset_biUnion_of_mem (hqY ▸ mem_reachedBlocks_self hB₀ hqB₀) hqB₀))
  refine mem_markEulerConnPairs.2 ⟨mem_relEdgeSets.2 ⟨inter_subset_right,
    ⟨q, mem_inter.2 ⟨hq, hqI⟩⟩, hspec.2⟩, mem_markEulerPairs.2 ⟨inter_subset_right,
    fun S hS => ?_⟩⟩
  have hSV : S ⊆ Y.biUnion id := subset_biUnion_of_mem hS
  have heq : blockDeg (E₁ ∩ interPairs Y) S = blockDeg E₁ S := by
    rw [blockDeg, blockDeg]
    congr 2
    · ext p
      simp only [mem_filter, mem_inter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, mem_interPairs_of_mem_comps hX hE hY h.1
        (Or.inl (hSV h.2))⟩, h.2⟩⟩
    · ext p
      simp only [mem_filter, mem_inter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, mem_interPairs_of_mem_comps hX hE hY h.1
        (Or.inr (hSV h.2))⟩, h.2⟩⟩
  rw [heq]
  exact (mem_markEulerPairs.1 hE₁).2 S (comps_subset hY hS)

end Defs

/-! ### Grouping by components -/

section Grouping

open scoped Classical

variable {X : Finset (Finset ℕ)}

/-- **Grouping a sum over edge sets by their components**: if the parts `E ∩ ℰ^inter(Y)` of the
edge sets `E ∈ 𝒮` in their components `Y` lie in `𝒞 Y`, then for nonnegative weights,
`∑_{E ∈ 𝒮} ∏_{Y ∈ comps E} w_Y(E ∩ ℰ^inter(Y)) h(comps E)
≤ ∑_{𝒱} ∏_{Y ∈ 𝒱} ∑_{E ∈ 𝒞 Y} w_Y(E) h(𝒱)`, over the disjoint families `𝒱` of groups of at least two
blocks. -/
theorem sum_le_sum_disjointFamilies (hX : IsSubpartition X) (𝒮 : Finset (Finset (ℕ × ℕ)))
    (h𝒮 : ∀ E ∈ 𝒮, E ⊆ interPairs X) (𝒞 : Finset (Finset ℕ) → Finset (Finset (ℕ × ℕ)))
    (h𝒞 : ∀ E ∈ 𝒮, ∀ Y ∈ comps X E, E ∩ interPairs Y ∈ 𝒞 Y)
    (w : Finset (Finset ℕ) → Finset (ℕ × ℕ) → ℝ) (hw : ∀ Y E, 0 ≤ w Y E)
    (h : Finset (Finset (Finset ℕ)) → ℝ) (hh : ∀ 𝒱, 0 ≤ h 𝒱) :
    ∑ E ∈ 𝒮, (∏ Y ∈ comps X E, w Y (E ∩ interPairs Y)) * h (comps X E) ≤
      ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card), (∏ Y ∈ 𝒱, ∑ E ∈ 𝒞 Y, w Y E) * h 𝒱 := by
  have hmaps : ∀ E ∈ 𝒮, comps X E ∈ disjointFamilies X (fun Y => 2 ≤ Y.card) := fun E hE =>
    comps_mem_disjointFamilies hX (h𝒮 E hE)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun 𝒱 _ => ?_
  set Fib := 𝒮.filter fun E => comps X E = 𝒱 with hFib
  have hE : ∀ E ∈ Fib, E ⊆ interPairs X := fun E hE => h𝒮 E (mem_filter.1 hE).1
  have hcomps : ∀ E ∈ Fib, comps X E = 𝒱 := fun E hE => (mem_filter.1 hE).2
  set Ψ : Finset (ℕ × ℕ) → ((Y : Finset (Finset ℕ)) → Y ∈ 𝒱 → Finset (ℕ × ℕ)) :=
    fun E Y _ => E ∩ interPairs Y with hΨ
  have hΨinj : Set.InjOn Ψ Fib := by
    intro E₁ hE₁ E₁' hE₁' heq
    rw [eq_biUnion_comps hX (hE E₁ hE₁), eq_biUnion_comps hX (hE E₁' hE₁'),
      hcomps E₁ hE₁, hcomps E₁' hE₁']
    refine biUnion_congr rfl fun Y hY => ?_
    exact congrFun (congrFun heq Y) hY
  have hΨmem : ∀ E ∈ Fib, Ψ E ∈ 𝒱.pi 𝒞 := by
    intro E hEF
    refine mem_pi.2 fun Y hY => ?_
    have hY' : Y ∈ comps X E := (hcomps E hEF).symm ▸ hY
    exact h𝒞 E (mem_filter.1 hEF).1 Y hY'
  have hterm : ∀ E ∈ Fib, (∏ Y ∈ comps X E, w Y (E ∩ interPairs Y)) * h (comps X E) =
      (∏ Y ∈ 𝒱.attach, w Y.1 (Ψ E Y.1 Y.2)) * h 𝒱 := by
    intro E hEF
    rw [hcomps E hEF]
    congr 1
    exact (prod_attach 𝒱 fun Y => w Y (E ∩ interPairs Y)).symm
  have hnn : ∀ ψ ∈ 𝒱.pi 𝒞, 0 ≤ (∏ Y ∈ 𝒱.attach, w Y.1 (ψ Y.1 Y.2)) * h 𝒱 := fun ψ _ =>
    mul_nonneg (prod_nonneg fun _ _ => hw _ _) (hh 𝒱)
  calc ∑ E ∈ Fib, (∏ Y ∈ comps X E, w Y (E ∩ interPairs Y)) * h (comps X E)
      = ∑ ψ ∈ Fib.image Ψ, (∏ Y ∈ 𝒱.attach, w Y.1 (ψ Y.1 Y.2)) * h 𝒱 := by
        rw [sum_image hΨinj]
        exact sum_congr rfl hterm
    _ ≤ ∑ ψ ∈ 𝒱.pi 𝒞, (∏ Y ∈ 𝒱.attach, w Y.1 (ψ Y.1 Y.2)) * h 𝒱 := by
        refine sum_le_sum_of_subset_of_nonneg (fun ψ hψ => ?_) fun ψ hψ _ => hnn ψ hψ
        obtain ⟨E, hEF, rfl⟩ := mem_image.1 hψ
        exact hΨmem E hEF
    _ = (∏ Y ∈ 𝒱, ∑ E ∈ 𝒞 Y, w Y E) * h 𝒱 := by
        rw [← sum_mul, prod_sum]

end Grouping

/-! ### The even bonds over a fixed odd skeleton -/

section Even

open scoped Classical

variable {X : Finset (Finset ℕ)} {E₁ : Finset (ℕ × ℕ)}

/-- **The even-bond sum over a fixed odd skeleton** (Step 1 of the proof of Lemma 4.54, the inner
sum of (4.91) and its Penrose bound), for any `E₁ ⊆ ℰ^inter(X)` and
`b ≥ 0` on `ℰ^inter(X)`, with `Y₀ = Coarse_X(comps X E₁)`:
`∑_{E₂ ⊆ ℰ^inter(X) : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝖤^X} ∏_{ij ∈ E₂} b_ij
≤ ∑_{T ∈ 𝖳_0^{Y₀}} ∏_{ij ∈ T} b_ij ∏_{ij ∈ ℰ^inter(X)} (1 + b_ij)` (the proof of
`MultipoleBKT.AbsoluteLower.sum_evenEdges_le`, which only uses `E₁ ⊆ ℰ^inter(X)`). -/
theorem sum_evenEdges_le' (hX : IsSubpartition X) (hE : E₁ ⊆ interPairs X)
    (b : ℕ × ℕ → ℝ) (hb : ∀ p ∈ interPairs X, 0 ≤ b p) :
    ∑ E₂ ∈ (interPairs X).powerset.filter
        (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ p ∈ E₂, b p ≤
      (∑ T ∈ relTreePairs₀ (coarsen X (comps X E₁)), ∏ p ∈ T, b p) *
        ∏ p ∈ interPairs X, (1 + b p) := by
  set G := comps X E₁ with hG
  set Y₀ := coarsen X G with hY₀def
  have hGX : ∀ Y ∈ G, Y ⊆ X := fun _ hY => comps_subset hY
  have hY₀ : IsSubpartition Y₀ := isSubpartition_coarsen_comps hX hE
  set I₀ := interPairs Y₀ with hI₀def
  have hI₀ : I₀ ⊆ interPairs X := interPairs_coarsen_subset hGX
  set F := (interPairs X).powerset.filter
    (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X) with hF
  have hconn : ∀ E₂ ∈ F, E₂ ∩ I₀ ∈ relEdgeSets₀ Y₀ := by
    intro E₂ hE₂
    rw [hF, mem_filter, mem_powerset] at hE₂
    obtain ⟨hE₂I, -, hE₁₂⟩ := hE₂
    obtain ⟨-, -, hcon⟩ := mem_relEdgeSets.1 hE₁₂
    refine mem_relEdgeSets₀.2 ⟨inter_subset_right, ?_⟩
    rw [biUnion_coarsen hGX]
    refine ⟨hcon.1, fun i hi j hj => (hcon.2 i hi j hj).mono (edgeGraph_mono ?_)⟩
    intro p hp
    rcases mem_union.1 hp with hp | hp
    · rcases mem_union.1 hp with hp | hp
      · apply mem_union_right
        rw [eq_biUnion_comps hX hE, mem_biUnion] at hp
        obtain ⟨Y, hY, hpY⟩ := hp
        exact mem_intraPairs.2 ⟨Y.biUnion id, mem_union_left _ (mem_image_of_mem _ hY),
          interPairs_subset_pairsOn (mem_inter.1 hpY).2⟩
      · rcases mem_intraPairs_or_mem_interPairs_coarsen hGX
          (interPairs_subset_pairsOn (hE₂I hp)) with h | h
        · exact mem_union_right _ h
        · exact mem_union_left _ (mem_inter.2 ⟨hp, h⟩)
    · obtain ⟨S, hS, hpS⟩ := mem_intraPairs.1 hp
      obtain ⟨B, hB, hSB⟩ := exists_mem_coarsen_superset (G := G) hS
      exact mem_union_right _ (mem_intraPairs.2 ⟨B, hB, pairsOn_mono hSB hpS⟩)
  set φ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ) × Finset (ℕ × ℕ) := fun E₂ => (E₂ \ I₀, E₂ ∩ I₀)
  have hφinj : Set.InjOn φ F := by
    intro E₂ _ E₂' _ h
    simp only [φ, Prod.mk.injEq] at h
    rw [← sdiff_union_inter E₂ I₀, ← sdiff_union_inter E₂' I₀, h.1, h.2]
  set W := ((interPairs X \ I₀).powerset ×ˢ relEdgeSets₀ Y₀) with hW
  have hφW : ∀ E₂ ∈ F, φ E₂ ∈ W := by
    intro E₂ hE₂
    refine mem_product.2 ⟨mem_powerset.2 (sdiff_subset_sdiff ?_ le_rfl), hconn E₂ hE₂⟩
    exact mem_powerset.1 (mem_filter.1 hE₂).1
  have hWnn : ∀ q ∈ W, 0 ≤ (∏ p ∈ q.1, b p) * ∏ p ∈ q.2, b p := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := mem_product.1 hq
    refine mul_nonneg (prod_nonneg fun p hp => hb p ?_) (prod_nonneg fun p hp => hb p ?_)
    · exact (sdiff_subset (mem_powerset.1 hq1 hp))
    · exact hI₀ ((mem_relEdgeSets₀.1 hq2).1 hp)
  have hsplit : ∀ E₂ ∈ F, ∏ p ∈ E₂, b p = (∏ p ∈ (φ E₂).1, b p) * ∏ p ∈ (φ E₂).2, b p := by
    intro E₂ _
    rw [mul_comm]
    exact (prod_inter_mul_prod_sdiff E₂ I₀ b).symm
  calc ∑ E₂ ∈ F, ∏ p ∈ E₂, b p
      = ∑ q ∈ F.image φ, (∏ p ∈ q.1, b p) * ∏ p ∈ q.2, b p := by
        rw [sum_image hφinj]
        exact sum_congr rfl hsplit
    _ ≤ ∑ q ∈ W, (∏ p ∈ q.1, b p) * ∏ p ∈ q.2, b p := by
        refine sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun q hq _ => hWnn q hq
        obtain ⟨E₂, hE₂, rfl⟩ := mem_image.1 hq
        exact hφW E₂ hE₂
    _ = (∏ p ∈ interPairs X \ I₀, (1 + b p)) * ∑ H ∈ relEdgeSets₀ Y₀, ∏ p ∈ H, b p := by
        rw [hW, sum_product, prod_one_add, sum_mul]
        refine sum_congr rfl fun A _ => ?_
        rw [mul_sum]
    _ ≤ (∏ p ∈ interPairs X \ I₀, (1 + b p)) *
          ((∑ T ∈ relTreePairs₀ Y₀, ∏ p ∈ T, b p) * ∏ p ∈ I₀, (1 + b p)) := by
        refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun p hp => ?_)
        · rw [sum_mul]
          exact sum_relEdgeSets₀_le hY₀ b fun p hp => hb p (hI₀ hp)
        · have := hb p (sdiff_subset hp)
          linarith
    _ = (∑ T ∈ relTreePairs₀ Y₀, ∏ p ∈ T, b p) * ∏ p ∈ interPairs X, (1 + b p) := by
        rw [← prod_sdiff hI₀ (f := fun p => 1 + b p)]
        ring

end Even

/-! ### The combinatorial core of Lemma 5.35 -/

section Core

open scoped Classical

variable {X : Finset (Finset ℕ)}

/-- The marks of the components of `E₁` lie in `U ∩ V_X`, disjointly. -/
theorem prod_marks_le (hX : IsSubpartition X) {E₁ : Finset (ℕ × ℕ)} (U : Finset ℕ)
    (m : ℕ → ℝ) (hm0 : ∀ i, 0 ≤ m i) {Cm : ℝ} (hCm : 1 ≤ Cm)
    (hm : ∀ i ∈ U ∩ X.biUnion id, m i ≤ Cm) :
    ∏ i ∈ U ∩ X.biUnion id, m i ≤
      Cm ^ (X.biUnion id).card * ∏ Y ∈ comps X E₁, ∏ i ∈ U ∩ Y.biUnion id, m i := by
  set G := comps X E₁
  set I := G.biUnion fun Y => U ∩ Y.biUnion id with hI
  have hIsub : I ⊆ U ∩ X.biUnion id := by
    intro i hi
    obtain ⟨Y, hY, hiY⟩ := mem_biUnion.1 hi
    exact mem_inter.2 ⟨(mem_inter.1 hiY).1,
      biUnion_subset_biUnion_of_subset_left id (comps_subset hY) (mem_inter.1 hiY).2⟩
  have hdisj : (G : Set (Finset (Finset ℕ))).PairwiseDisjoint fun Y => U ∩ Y.biUnion id := by
    intro Y hY Y' hY' hne
    have hd := disjoint_biUnion_of_disjoint hX (comps_subset (mem_coe.1 hY))
      (comps_subset (mem_coe.1 hY')) (pairwiseDisjoint_comps hY hY' hne)
    exact hd.mono inter_subset_right inter_subset_right
  have hprodI : ∏ i ∈ I, m i = ∏ Y ∈ G, ∏ i ∈ U ∩ Y.biUnion id, m i := prod_biUnion hdisj
  rw [← prod_sdiff hIsub, hprodI]
  refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun Y _ => prod_nonneg fun i _ => hm0 i)
  calc ∏ i ∈ (U ∩ X.biUnion id) \ I, m i ≤ ∏ _i ∈ (U ∩ X.biUnion id) \ I, Cm :=
        prod_le_prod₀ (fun i _ => hm0 i) fun i hi => hm i (mem_sdiff.1 hi).1
    _ = Cm ^ ((U ∩ X.biUnion id) \ I).card := prod_const _
    _ ≤ Cm ^ (X.biUnion id).card :=
        pow_le_pow_right₀ hCm (card_le_card (sdiff_subset.trans inter_subset_right))

/-- **The combinatorial core of Lemma 5.35** (Step 1 of the proof of Lemma 4.54 with marks, eqs.
(4.91)–(4.92)): see the module docstring. -/
theorem stepOne_le (hX : IsSubpartition X) (U : Finset ℕ) {Cm Cb : ℝ} (hCm : 1 ≤ Cm)
    (hCb : 1 ≤ Cb) (A B b : ℕ × ℕ → ℝ) (m : ℕ → ℝ)
    (hA : ∀ p, 0 ≤ A p) (hB0 : ∀ p ∈ interPairs X, 0 ≤ B p) (hb : ∀ p, 0 ≤ b p)
    (hB : ∀ p ∈ interPairs X, B p ≤ Cb * b p)
    (hm0 : ∀ i, 0 ≤ m i) (hm : ∀ i ∈ U ∩ X.biUnion id, m i ≤ Cm) :
    ∑ E₁ ∈ markEulerPairs X U, (∏ p ∈ E₁, A p) * (∏ i ∈ U ∩ X.biUnion id, m i) *
        ∑ E₂ ∈ (interPairs X).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ p ∈ E₂, B p ≤
      (Cm * Cb) ^ (X.biUnion id).card * (∏ p ∈ interPairs X, (1 + B p)) *
        ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
          (∏ Y ∈ 𝒱, ∑ E ∈ markEulerConnPairs Y U,
            (∏ p ∈ E, A p) * ∏ i ∈ U ∩ Y.biUnion id, m i) *
            ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ p ∈ T, b p := by
  set n := (X.biUnion id).card with hn
  have hCm0 : 0 ≤ Cm := zero_le_one.trans hCm
  have hCb0 : 0 ≤ Cb := zero_le_one.trans hCb
  set Q := ∏ p ∈ interPairs X, (1 + B p) with hQ
  have hQ0 : 0 ≤ Q := prod_nonneg fun p hp => by have := hB0 p hp; linarith
  set h : Finset (Finset (Finset ℕ)) → ℝ :=
    fun 𝒱 => ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ p ∈ T, b p with hh
  have hh0 : ∀ 𝒱, 0 ≤ h 𝒱 := fun 𝒱 => sum_nonneg fun T _ => prod_nonneg fun p _ => hb p
  set w : Finset (Finset ℕ) → Finset (ℕ × ℕ) → ℝ :=
    fun Y E => (∏ p ∈ E, A p) * ∏ i ∈ U ∩ Y.biUnion id, m i with hw
  have hw0 : ∀ Y E, 0 ≤ w Y E := fun Y E =>
    mul_nonneg (prod_nonneg fun p _ => hA p) (prod_nonneg fun i _ => hm0 i)
  -- the bound for one `E₁`
  have hone : ∀ E₁ ∈ markEulerPairs X U,
      (∏ p ∈ E₁, A p) * (∏ i ∈ U ∩ X.biUnion id, m i) *
        ∑ E₂ ∈ (interPairs X).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ p ∈ E₂, B p ≤
      (Cm * Cb) ^ n * Q * ((∏ Y ∈ comps X E₁, w Y (E₁ ∩ interPairs Y)) * h (comps X E₁)) := by
    intro E₁ hE₁
    have hE := (mem_markEulerPairs.1 hE₁).1
    have hY₀ := isSubpartition_coarsen_comps hX hE
    have hGX : ∀ Y ∈ comps X E₁, Y ⊆ X := fun _ hY => comps_subset hY
    -- the even bonds
    have hev := sum_evenEdges_le' hX hE B hB0
    have htree : ∑ T ∈ relTreePairs₀ (coarsen X (comps X E₁)), ∏ p ∈ T, B p ≤
        Cb ^ n * h (comps X E₁) := by
      rw [hh, mul_sum]
      refine sum_le_sum fun T hT => ?_
      have hTI : T ⊆ interPairs X :=
        (subset_interPairs_of_mem_relTreePairs₀ hY₀ hT).trans (interPairs_coarsen_subset hGX)
      have hTn : T.card ≤ n := by
        have := card_le_of_mem_relTreePairs₀ hY₀ hT
        rwa [biUnion_coarsen hGX] at this
      calc ∏ p ∈ T, B p ≤ ∏ p ∈ T, Cb * b p :=
            prod_le_prod₀ (fun p hp => hB0 p (hTI hp)) fun p hp => hB p (hTI hp)
        _ = Cb ^ T.card * ∏ p ∈ T, b p := by rw [prod_mul_distrib, prod_const]
        _ ≤ Cb ^ n * ∏ p ∈ T, b p :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCb hTn) (prod_nonneg fun p _ => hb p)
    have hE2 : ∑ E₂ ∈ (interPairs X).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ p ∈ E₂, B p ≤
        Cb ^ n * h (comps X E₁) * Q :=
      hev.trans (mul_le_mul_of_nonneg_right htree hQ0)
    -- the marks and the odd bonds
    have hmk := prod_marks_le hX (E₁ := E₁) U m hm0 hCm hm
    have hodd : ∏ p ∈ E₁, A p = ∏ Y ∈ comps X E₁, ∏ p ∈ E₁ ∩ interPairs Y, A p :=
      prod_eq_prod_comps hX hE A
    have hAm : (∏ p ∈ E₁, A p) * (∏ i ∈ U ∩ X.biUnion id, m i) ≤
        Cm ^ n * ∏ Y ∈ comps X E₁, w Y (E₁ ∩ interPairs Y) := by
      rw [hodd]
      calc (∏ Y ∈ comps X E₁, ∏ p ∈ E₁ ∩ interPairs Y, A p) * ∏ i ∈ U ∩ X.biUnion id, m i
          ≤ (∏ Y ∈ comps X E₁, ∏ p ∈ E₁ ∩ interPairs Y, A p) *
              (Cm ^ n * ∏ Y ∈ comps X E₁, ∏ i ∈ U ∩ Y.biUnion id, m i) :=
            mul_le_mul_of_nonneg_left hmk
              (prod_nonneg fun Y _ => prod_nonneg fun p _ => hA p)
        _ = Cm ^ n * ∏ Y ∈ comps X E₁, w Y (E₁ ∩ interPairs Y) := by
            rw [hw, prod_mul_distrib]
            ring
    have hS0 : 0 ≤ ∑ E₂ ∈ (interPairs X).powerset.filter
        (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ p ∈ E₂, B p :=
      sum_nonneg fun E₂ hE₂ => prod_nonneg fun p hp =>
        hB0 p (mem_powerset.1 (mem_filter.1 hE₂).1 hp)
    calc (∏ p ∈ E₁, A p) * (∏ i ∈ U ∩ X.biUnion id, m i) *
          ∑ E₂ ∈ (interPairs X).powerset.filter
            (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ p ∈ E₂, B p
        ≤ (Cm ^ n * ∏ Y ∈ comps X E₁, w Y (E₁ ∩ interPairs Y)) *
            (Cb ^ n * h (comps X E₁) * Q) :=
          mul_le_mul hAm hE2 hS0 (mul_nonneg (pow_nonneg hCm0 _)
            (prod_nonneg fun Y _ => hw0 _ _))
      _ = (Cm * Cb) ^ n * Q * ((∏ Y ∈ comps X E₁, w Y (E₁ ∩ interPairs Y)) *
            h (comps X E₁)) := by
          rw [mul_pow]
          ring
  calc _ ≤ ∑ E₁ ∈ markEulerPairs X U, (Cm * Cb) ^ n * Q *
          ((∏ Y ∈ comps X E₁, w Y (E₁ ∩ interPairs Y)) * h (comps X E₁)) := sum_le_sum hone
    _ = (Cm * Cb) ^ n * Q * ∑ E₁ ∈ markEulerPairs X U,
          (∏ Y ∈ comps X E₁, w Y (E₁ ∩ interPairs Y)) * h (comps X E₁) := by
        rw [mul_sum]
    _ ≤ (Cm * Cb) ^ n * Q * ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
          (∏ Y ∈ 𝒱, ∑ E ∈ markEulerConnPairs Y U, w Y E) * h 𝒱 := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg (mul_nonneg hCm0 hCb0) _) hQ0)
        exact sum_le_sum_disjointFamilies hX _ (fun E hE => (mem_markEulerPairs.1 hE).1)
          (fun Y => markEulerConnPairs Y U)
          (fun E hE Y hY => inter_mem_markEulerConnPairs hX hE hY) w hw0 h hh0

end Core

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
