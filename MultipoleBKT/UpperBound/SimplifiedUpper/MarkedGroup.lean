/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.MarkedData

/-!
# Marked Euler groups before exchanging the two tree sums

The paper: Lemma 5.36, and (4.102).

`markedGroupSum_reattach` uses `exists_markedData_sum` to encode the original odd
edge set by its original tree, bridge-cut forest, exceptional edges, pseudoforest
and unused edges. The records reconstruct the original skeleton. Their cost is
at most `4^|V_Y|`. The unused edges are summed into the exponential, and the
pseudoforests into `∏ᵢ(1+∑ⱼḡᵢⱼ)`. The remaining original-tree sum contains its full
replacement-tree family. `RouteLog.Inner.groupSum_route_le` subsequently exchanges
these two sums and obtains the logarithmic predecessor product.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Finset SimpleGraph Multipole Hierarchical SetPartition AbsoluteLower Parity Peeling
  CoreForest Quadratic

/-- The pairs of a subgraph of the graph of `E ⊆ pairsOn U` lie in `E`. -/
theorem edgesOf_subset_of_le_pairGraph {U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ pairsOn U) {G : SimpleGraph U} (h : G ≤ BoundedUpper.pairGraph U E) :
    edgesOf G ⊆ E := by
  intro p hp
  obtain ⟨h1, h2, h12, hadj⟩ := mem_edgesOf.1 hp
  have := (BoundedUpper.pairGraph_adj.1 (h hadj)).2
  rcases this with hp' | hp'
  · exact hp'
  · exact absurd (mem_pairsOn.1 (hE hp')).2.2 (not_lt.2 h12.le)

open scoped Classical in
/-- **The records** (proof of Lemma 5.36): for a relative tree `T ∈ 𝖳^Y`, the pairs
`(Hs, D)` with `Hs ≤ T` and `D` a simple exceptional-edge record for `Hs ∪ ℰ^intra(Y)`
number at most `2^{|T|} 2^{|V_Y|} ≤ 4^{|V_Y|}`. The components of the bridge-cut
forest each supply one optional unordered pair of distinct vertices. -/
theorem sum_records_le {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)
    {T : SimpleGraph (Y.biUnion id)} (hT : IsRelTree Y T) (Hb : SimpleGraph (Y.biUnion id)) :
    ∑ x ∈ (univ : Finset (SimpleGraph (Y.biUnion id))) ×ˢ
        (univ : Finset (Finset (Sym2 (Y.biUnion id)))),
      (if x.1 ≤ T ∧ ValidSimpleExc (x.1 ⊔ Hb) x.2 then (1 : ℝ) else 0) ≤
      (4 : ℝ) ^ (Y.biUnion id).card := by
  have hTcard : T.edgeFinset.card ≤ (Y.biUnion id).card := by
    have h := IsRelTree₀.card_edgeFinset hY (E := T) (Or.inl hT)
    have h' : Y.card ≤ (Y.biUnion id).card := card_le_card_biUnion hY.2 hY.1
    omega
  have hrec : ∀ H : SimpleGraph (Y.biUnion id),
      (((univ : Finset (Finset (Sym2 (Y.biUnion id)))).filter
        (ValidSimpleExc (H ⊔ Hb))).card : ℝ) ≤ 2 ^ (Y.biUnion id).card := by
    intro H
    have h := (card_validSimpleExc_le_prod (H ⊔ Hb)).trans (prod_component_choices_le (H ⊔ Hb))
    rw [Fintype.card_coe] at h
    exact_mod_cast h
  have hcardT : (((univ : Finset (SimpleGraph (Y.biUnion id))).filter (· ≤ T)).card : ℝ) ≤
      2 ^ T.edgeFinset.card := by
    have := card_le_le_pow T ((univ : Finset (SimpleGraph (Y.biUnion id))).filter (· ≤ T))
      fun H hH => (mem_filter.1 hH).2
    exact_mod_cast this
  rw [sum_product]
  calc ∑ H, ∑ D', (if H ≤ T ∧ ValidSimpleExc (H ⊔ Hb) D' then (1 : ℝ) else 0)
      = ∑ H ∈ (univ : Finset (SimpleGraph (Y.biUnion id))).filter (· ≤ T),
          (((univ : Finset (Finset (Sym2 (Y.biUnion id)))).filter
            (ValidSimpleExc (H ⊔ Hb))).card : ℝ) := by
        rw [← sum_filter_add_sum_filter_not univ (· ≤ T)]
        rw [sum_eq_zero (s := (univ : Finset (SimpleGraph (Y.biUnion id))).filter fun H => ¬ H ≤ T)
          fun H hH => sum_eq_zero fun D' _ => by
            rw [ite_eq_right fun h => (mem_filter.1 hH).2 h.1], add_zero]
        refine sum_congr rfl fun H hH => ?_
        rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
        refine sum_congr rfl fun D' _ => ?_
        simp only [(mem_filter.1 hH).2, true_and]
        split_ifs <;> norm_num
    _ ≤ ∑ H ∈ (univ : Finset (SimpleGraph (Y.biUnion id))).filter (· ≤ T),
          ((2 : ℝ) ^ (Y.biUnion id).card) :=
        sum_le_sum fun H _ => hrec H
    _ = (((univ : Finset (SimpleGraph (Y.biUnion id))).filter (· ≤ T)).card : ℝ) *
          2 ^ (Y.biUnion id).card := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ T.edgeFinset.card * 2 ^ (Y.biUnion id).card :=
        mul_le_mul_of_nonneg_right hcardT (pow_nonneg (by norm_num) _)
    _ ≤ (2 : ℝ) ^ (Y.biUnion id).card * 2 ^ (Y.biUnion id).card :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hTcard)
          (pow_nonneg (by norm_num) _)
    _ = 4 ^ (Y.biUnion id).card := by rw [← mul_pow]; norm_num

section Main

variable {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y) {W : Finset ℕ}
  (c : ℕ → ℂ × ℂ) {M lam ε₀ R C₁ C₂ K : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam)
  (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hK : 1 ≤ K)
  (a : ℕ → ℕ → ℝ) (ha0 : ∀ i j, 0 ≤ a i j) (hasymm : ∀ i j, a i j = a j i)
  (ha : ∀ i ∈ Y.biUnion id, ∀ j ∈ Y.biUnion id,
    a i j ≤ C₁ * absOddWeight M lam ε₀ R (c i) (c j))
  (m δ : ℕ → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hm : ∀ i ∈ W, m i ≤ C₂ * (‖(c i).1 - (c i).2‖ / δ i))
  (hδ : ∀ i ∈ Y.biUnion id, 0 < δ i) (hrδ : ∀ i ∈ Y.biUnion id, ‖(c i).1 - (c i).2‖ ≤ δ i)
  (hKE : ∀ i ∈ Y.biUnion id, ∀ j ∈ Y.biUnion id, a i j ≠ 0 → δ j ≤ K * δ i)
  (hKS : ∀ S ∈ Y, ∀ i ∈ S, ∀ j ∈ S, δ j ≤ K * δ i)
include hY hM hlam hC₁ hC₂ hK ha0 hasymm ha hm0 hm hδ hrδ hKE hKS

open scoped Classical in
/-- **Lemma 5.36, the sum over one group with marks** (proof of Lemma 5.36):
see the module docstring. -/
theorem markedGroupSum_reattach (hW : W ⊆ Y.biUnion id) (hWne : W.Nonempty) :
    ∑ E ∈ markEulerConnPairs Y W, (∏ p ∈ E, a p.1 p.2) * ∏ i ∈ W, m i ≤
      (4 * (C₁ ^ 3 * C₂ * K ^ 6)) ^ (Y.biUnion id).card * prodExceptMax c Y *
        (∑ T₀ ∈ relTrees Y, ∑ T ∈ longAgreeingTrees Y
          (fun i : Y.biUnion id => dipoleLength (c i))
          (dipoleDistOn fun i : Y.biUnion id => c i) T₀,
          ∏ e ∈ T.edgeFinset, keptWeight
            (dipoleDistOn fun i : Y.biUnion id => c i)
            (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) e) *
        (∏ p ∈ interPairs Y, Real.exp (C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2))) *
        ∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j) := by
  set V := Y.biUnion id with hVdef
  set n := V.card with hn
  set Kc := C₁ ^ 3 * C₂ * K ^ 6 with hKc
  set d : Sym2 V → ℝ := dipoleDistOn fun i : V => c i with hd_def
  set cc : Sym2 V → ℝ := absIndicator M lam ε₀ R fun i : V => c i with hcc_def
  set g : Sym2 V → ℝ := gbarLift M lam ε₀ R c V with hg_def
  set A : Sym2 V → ℝ := symLift V a hasymm with hA_def
  set aA : ℕ × ℕ → ℝ := fun p => absOddWeight M lam ε₀ R (c p.1) (c p.2) with haA
  set P := prodExceptMax c Y with hP
  set Hb := sameBlockGraph (blockOf hY) with hHb
  set S := markEulerConnPairs Y W with hS
  have hC₁0 : 0 ≤ C₁ := zero_le_one.trans hC₁
  have hKc0 : 0 ≤ Kc := by
    have := zero_le_one.trans hC₂
    have := zero_le_one.trans hK
    positivity
  have hcc : ∀ e, 0 ≤ cc e := absIndicator_nonneg M lam ε₀ R _
  have hg0 : ∀ e, 0 ≤ g e := gbarLift_nonneg M lam ε₀ R c V
  have haA0 : ∀ p, 0 ≤ aA p := fun p => absOddWeight_nonneg _ _ _ _ _ _
  have hP0 : 0 ≤ P := prodExceptMax_nonneg Y
  -- the data of each edge set
  have hex : ∀ E ∈ S, ∃ (T Hs F : SimpleGraph V) (D : Finset (Sym2 V)) (E' : SimpleGraph V),
      IsRelTree Y T ∧ Hs ≤ T ∧ IsPseudoforest F ∧ ValidSimpleExc (Hs ⊔ Hb) D ∧
        E' = T ⊔ F ⊔ fromEdgeSet (D : Set (Sym2 V)) ∧ E' ≤ BoundedUpper.pairGraph V E ∧
        (∏ e ∈ E'.edgeFinset, A e) * ∏ i ∈ W, m i ≤
          Kc ^ n * P * (∑ T' ∈ longAgreeingTrees Y
            (fun i : Y.biUnion id => dipoleLength (c i)) d T,
            ∏ e ∈ T'.edgeFinset, keptWeight d cc e) * ∏ e ∈ F.edgeFinset, g e := by
    intro E hE
    obtain ⟨T, Hs, F, D, E', hT, hHs, hF, hD, hE'eq, hE'le, hwt⟩ :=
      exists_markedData_sum hY c hM hlam hC₁ hC₂ hK a ha0 hasymm ha m δ hm0 hm hδ hrδ hKE
        hKS hW hWne hE
    obtain ⟨hDsimple, hDgraph⟩ := hD.simple_record
    refine ⟨T, Hs, F, simpleExcRecord D, E', hT, hHs, hF, ?_, ?_, hE'le, hwt⟩
    · simpa only [hHb, hVdef] using hDsimple
    · exact hE'eq.trans (congrArg (fun G => T ⊔ F ⊔ G) hDgraph.symm)
  choose! T Hs F D E' hT hHs hF hD hE'eq hE'le hwt using hex
  have hEpairs : ∀ E ∈ S, E ⊆ pairsOn V := fun E hE =>
    (mem_relEdgeSets.1 (mem_markEulerConnPairs.1 hE).1).1.trans interPairs_subset_pairsOn
  have hEinter : ∀ E ∈ S, E ⊆ interPairs Y := fun E hE =>
    (mem_relEdgeSets.1 (mem_markEulerConnPairs.1 hE).1).1
  have hsubE : ∀ E ∈ S, edgesOf (E' E) ⊆ E := fun E hE =>
    edgesOf_subset_of_le_pairGraph (hEpairs E hE) (hE'le E hE)
  -- the encoding
  set f₁ : SimpleGraph V → ℝ := fun T => P * ∑ T' ∈ longAgreeingTrees Y
      (fun i : Y.biUnion id => dipoleLength (c i)) d T,
      ∏ e ∈ T'.edgeFinset, keptWeight d cc e with hf₁
  set ind : SimpleGraph V × (SimpleGraph V × Finset (Sym2 V)) → ℝ :=
    fun x => if x.2.1 ≤ x.1 ∧ ValidSimpleExc (x.2.1 ⊔ Hb) x.2.2 then 1 else 0 with hind
  set f₂ : SimpleGraph V → ℝ := fun F => ∏ e ∈ F.edgeFinset, g e with hf₂
  set f₄ : Finset (ℕ × ℕ) → ℝ := fun R => ∏ p ∈ R, C₁ * aA p with hf₄
  set Ψ : (SimpleGraph V × (SimpleGraph V × Finset (Sym2 V))) ×
      (SimpleGraph V × Finset (ℕ × ℕ)) → ℝ :=
    fun q => (f₁ q.1.1 * ind q.1) * (f₂ q.2.1 * f₄ q.2.2) with hΨ
  set Φ : Finset (ℕ × ℕ) → (SimpleGraph V × (SimpleGraph V × Finset (Sym2 V))) ×
      (SimpleGraph V × Finset (ℕ × ℕ)) :=
    fun E => ((T E, (Hs E, D E)), (F E, E \ edgesOf (E' E))) with hΦ
  set Big := (relTrees Y ×ˢ ((univ : Finset (SimpleGraph V)) ×ˢ
    (univ : Finset (Finset (Sym2 V))))) ×ˢ ((pseudoforests : Finset (SimpleGraph V)) ×ˢ
      (interPairs Y).powerset) with hBig
  have hf₁0 : ∀ T, 0 ≤ f₁ T := fun T =>
    mul_nonneg hP0 (sum_nonneg fun T' _ => prod_nonneg fun e _ => keptWeight_nonneg hcc e)
  have hind0 : ∀ x, 0 ≤ ind x := fun x => by
    simp only [hind]
    split_ifs <;> norm_num
  have hf₂0 : ∀ F, 0 ≤ f₂ F := fun F => prod_nonneg fun e _ => hg0 e
  have hf₄0 : ∀ R, 0 ≤ f₄ R := fun R => prod_nonneg fun p _ => mul_nonneg hC₁0 (haA0 p)
  have hΨ0 : ∀ q, 0 ≤ Ψ q := fun q =>
    mul_nonneg (mul_nonneg (hf₁0 _) (hind0 _)) (mul_nonneg (hf₂0 _) (hf₄0 _))
  -- (i) the bound for one edge set
  have hone : ∀ E ∈ S, (∏ p ∈ E, a p.1 p.2) * ∏ i ∈ W, m i ≤ Kc ^ n * Ψ (Φ E) := by
    intro E hE
    have hsplit := prod_sdiff (hsubE E hE) (f := fun p => a p.1 p.2)
    have hE'prod : ∏ p ∈ edgesOf (E' E), a p.1 p.2 = ∏ e ∈ (E' E).edgeFinset, A e :=
      prod_edgesOf_eq_of _ A (fun p => a p.1 p.2) fun i j => rfl
    have hrest : ∏ p ∈ E \ edgesOf (E' E), a p.1 p.2 ≤ f₄ (E \ edgesOf (E' E)) := by
      refine prod_le_prod₀ (fun p _ => ha0 _ _) fun p hp => ?_
      have hpV := mem_pairsOn.1 (hEpairs E hE (sdiff_subset hp))
      exact ha p.1 hpV.1 p.2 hpV.2.1
    have hindE : ind (T E, (Hs E, D E)) = 1 := by
      simp only [hind]
      rw [ite_eq_left ⟨hHs E hE, hD E hE⟩]
    have hrest0 : 0 ≤ ∏ p ∈ E \ edgesOf (E' E), a p.1 p.2 := prod_nonneg fun p _ => ha0 _ _
    have hm0' : 0 ≤ ∏ i ∈ W, m i := prod_nonneg fun i _ => hm0 i
    calc (∏ p ∈ E, a p.1 p.2) * ∏ i ∈ W, m i
        = ((∏ e ∈ (E' E).edgeFinset, A e) * ∏ i ∈ W, m i) *
            ∏ p ∈ E \ edgesOf (E' E), a p.1 p.2 := by
          rw [← hsplit, hE'prod]
          ring
      _ ≤ (Kc ^ n * P * (∑ T' ∈ longAgreeingTrees Y
            (fun i : Y.biUnion id => dipoleLength (c i)) d (T E),
            ∏ e ∈ T'.edgeFinset, keptWeight d cc e) *
            ∏ e ∈ (F E).edgeFinset, g e) * f₄ (E \ edgesOf (E' E)) :=
          mul_le_mul (hwt E hE) hrest hrest0 (mul_nonneg (mul_nonneg (mul_nonneg
            (pow_nonneg hKc0 _) hP0) (sum_nonneg fun T' _ => prod_nonneg fun e _ => keptWeight_nonneg hcc e))
            (prod_nonneg fun e _ => hg0 e))
      _ = Kc ^ n * Ψ (Φ E) := by
          simp only [hΨ, hΦ, hf₁, hf₂, hindE]
          ring
  -- (ii) the encoding lands in `Big`
  have hmem : ∀ E ∈ S, Φ E ∈ Big := by
    intro E hE
    refine mem_product.2 ⟨mem_product.2 ⟨mem_relTrees.2 (hT E hE), mem_product.2
      ⟨mem_univ _, mem_univ _⟩⟩, mem_product.2 ⟨mem_pseudoforests.2 (hF E hE),
        mem_powerset.2 (sdiff_subset.trans (hEinter E hE))⟩⟩
  -- (iii) injectivity
  have hinj : Set.InjOn Φ S := by
    intro E₁ hE₁ E₂ hE₂ heq
    simp only [hΦ, Prod.mk.injEq] at heq
    obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := heq
    have hE' : E' E₁ = E' E₂ := by rw [hE'eq E₁ hE₁, hE'eq E₂ hE₂, h1, h3, h4]
    rw [← sdiff_union_of_subset (hsubE E₁ hE₁), ← sdiff_union_of_subset (hsubE E₂ hE₂), h5, hE']
  -- (iv) the sum over `Big`
  have hrec : ∀ T ∈ relTrees Y, ∑ x ∈ (univ : Finset (SimpleGraph V)) ×ˢ
      (univ : Finset (Finset (Sym2 V))), ind (T, x) ≤ 4 ^ n := fun T hT' =>
    sum_records_le hY (mem_relTrees.1 hT') Hb
  have hT1 : ∑ x ∈ relTrees Y ×ˢ ((univ : Finset (SimpleGraph V)) ×ˢ
      (univ : Finset (Finset (Sym2 V)))), f₁ x.1 * ind x ≤
      4 ^ n * ∑ T ∈ relTrees Y, f₁ T := by
    rw [sum_product, mul_sum]
    refine sum_le_sum fun T hT' => ?_
    show ∑ y ∈ _, f₁ T * ind (T, y) ≤ _
    rw [← mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (hrec T hT') (hf₁0 T)
  have hT2 : ∑ T ∈ relTrees Y, f₁ T = P * (∑ T₀ ∈ relTrees Y, ∑ T ∈ longAgreeingTrees Y
          (fun i : Y.biUnion id => dipoleLength (c i))
          (dipoleDistOn fun i : Y.biUnion id => c i) T₀,
          ∏ e ∈ T.edgeFinset, keptWeight
            (dipoleDistOn fun i : Y.biUnion id => c i)
            (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) e) := by
    rw [mul_sum]
  have hF2 : ∑ F' ∈ (pseudoforests : Finset (SimpleGraph V)), f₂ F' ≤
      ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j) := by
    refine (sum_pseudoforests_le g hg0).trans_eq ?_
    rw [← prod_coe_sort V]
    refine prod_congr rfl fun i _ => ?_
    rw [← sum_erase_coe V (fun j => gbar M lam ε₀ R c i j) i]
    rfl
  have hR2 : ∑ R' ∈ (interPairs Y).powerset, f₄ R' ≤
      ∏ p ∈ interPairs Y, Real.exp (C₁ * aA p) := by
    rw [hf₄, ← prod_one_add]
    exact prod_le_prod₀ (fun p _ => by have := mul_nonneg hC₁0 (haA0 p); linarith)
      fun p _ => by linarith [Real.add_one_le_exp (C₁ * aA p)]
  have hG0 : 0 ≤ ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j) :=
    prod_nonneg fun i _ => add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _)
  have hBig : ∑ q ∈ Big, Ψ q ≤
      4 ^ n * (P * (∑ T₀ ∈ relTrees Y, ∑ T ∈ longAgreeingTrees Y
          (fun i : Y.biUnion id => dipoleLength (c i))
          (dipoleDistOn fun i : Y.biUnion id => c i) T₀,
          ∏ e ∈ T.edgeFinset, keptWeight
            (dipoleDistOn fun i : Y.biUnion id => c i)
            (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) e)) *
        ((∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j)) *
          ∏ p ∈ interPairs Y, Real.exp (C₁ * aA p)) := by
    have hsplit : ∑ q ∈ Big, Ψ q = (∑ x ∈ relTrees Y ×ˢ ((univ : Finset (SimpleGraph V)) ×ˢ
        (univ : Finset (Finset (Sym2 V)))), f₁ x.1 * ind x) *
        ((∑ F' ∈ (pseudoforests : Finset (SimpleGraph V)), f₂ F') *
          ∑ R' ∈ (interPairs Y).powerset, f₄ R') := by
      rw [hBig, ← sum_product_mul, ← sum_product_mul]
    rw [hsplit, ← hT2]
    refine mul_le_mul hT1 (mul_le_mul hF2 hR2 (sum_nonneg fun R' _ => hf₄0 R') hG0)
      (mul_nonneg (sum_nonneg fun F' _ => hf₂0 F') (sum_nonneg fun R' _ => hf₄0 R'))
      (mul_nonneg (pow_nonneg (by norm_num) n) (sum_nonneg fun T _ => hf₁0 T))
  calc ∑ E ∈ S, (∏ p ∈ E, a p.1 p.2) * ∏ i ∈ W, m i
      ≤ ∑ E ∈ S, Kc ^ n * Ψ (Φ E) := sum_le_sum hone
    _ = Kc ^ n * ∑ q ∈ S.image Φ, Ψ q := by rw [mul_sum, sum_image hinj]
    _ ≤ Kc ^ n * ∑ q ∈ Big, Ψ q := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (fun q hq => ?_)
          fun q _ _ => hΨ0 q) (pow_nonneg hKc0 _)
        obtain ⟨E, hE, rfl⟩ := mem_image.1 hq
        exact hmem E hE
    _ ≤ Kc ^ n * (4 ^ n * (P * (∑ T₀ ∈ relTrees Y, ∑ T ∈ longAgreeingTrees Y
          (fun i : Y.biUnion id => dipoleLength (c i))
          (dipoleDistOn fun i : Y.biUnion id => c i) T₀,
          ∏ e ∈ T.edgeFinset, keptWeight
            (dipoleDistOn fun i : Y.biUnion id => c i)
            (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) e)) *
          ((∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j)) *
            ∏ p ∈ interPairs Y, Real.exp (C₁ * aA p))) :=
        mul_le_mul_of_nonneg_left hBig (pow_nonneg hKc0 _)
    _ = _ := by
        rw [mul_pow]
        ring

end Main

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
