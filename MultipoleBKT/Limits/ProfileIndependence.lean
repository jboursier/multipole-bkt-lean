/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Relabel

/-!
# The multipole activities depend only on the block profile

See Lemma 4.26: the limit (4.54) is
`𝗄^mult((#_k X)_k)`, a function of the profile of `X` only.

Two subpartitions with the same block profile are related by a bijection `e : V_X ≃ V_{X'}` that
maps the blocks of `X` to the blocks of `X'` (`exists_blockEquiv`). The edge sets `𝖤^X` and
`𝖤^{X'}` correspond under `e`, and the box integrals agree (`integral_multBox_relabel`), so
(`multipoleActivity_eq_of_blockProfile_eq`) `𝖪^mult(X) = 𝖪^mult(X')` for every `N ≥ 1`. Hence
(`exists_tendsto_multipoleActivity_blockProfile`) the limit of `N^{|X|-1} 𝖪^mult(X)` is a function
`𝗄^mult_{β,λ}` of the profile, as in Theorem 2 (1).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph Filter Topology
open scoped ENNReal

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

section Bijection

variable {X X' : Finset (Finset ℕ)}

/-- The labels of a block, as a fibre of `blockOf`. -/
def blockFiberEquiv (hX : IsSubpartition X) (S : X) :
    {i : X.biUnion id // blockOf X i = S} ≃ (S : Finset ℕ) where
  toFun i := ⟨i.1.1, (blockOf_eq_iff hX i.1 S).1 i.2⟩
  invFun x := ⟨⟨x.1, mem_biUnion.2 ⟨S, S.2, x.2⟩⟩, (blockOf_eq_iff hX _ S).2 x.2⟩
  left_inv i := by rfl
  right_inv x := by rfl

theorem card_fiber_blockProfile (X : Finset (Finset ℕ)) (n : ℕ) :
    Fintype.card {S : X // (S : Finset ℕ).card = n} = blockProfile X n := by
  rw [blockProfile, Multiset.toFinsupp_apply, Multiset.count_map]
  have h1 : Fintype.card {S : X // (S : Finset ℕ).card = n} =
      (X.filter fun S => S.card = n).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ X)
      (fun S => S.card = n)).trans (Equiv.subtypeEquivRight fun S => by
        simp only [Finset.mem_filter]))
  rw [h1]
  show Multiset.card (Multiset.filter _ X.val) = _
  rw [Multiset.filter_congr fun S _ => eq_comm]

theorem card_eq_of_blockProfile_eq (h : blockProfile X = blockProfile X') : X.card = X'.card := by
  unfold blockProfile at h
  have := congrArg Multiset.card (Multiset.toFinsupp.injective h)
  simpa using this

/-- **A block-preserving bijection.** Subpartitions with the same profile are related by a
bijection of the labels mapping blocks onto blocks of the same size. -/
theorem exists_blockEquiv (hX : IsSubpartition X) (hX' : IsSubpartition X')
    (hprof : blockProfile X = blockProfile X') :
    ∃ (e : X.biUnion id ≃ X'.biUnion id) (σ : X ≃ X'),
      (∀ S, (σ S : Finset ℕ).card = (S : Finset ℕ).card) ∧
      ∀ i, blockOf X' (e i) = σ (blockOf X i) := by
  have hfib : ∀ n, {S : X // (S : Finset ℕ).card = n} ≃ {S : X' // (S : Finset ℕ).card = n} :=
    fun n => Fintype.equivOfCardEq (by
      rw [card_fiber_blockProfile, card_fiber_blockProfile, hprof])
  let σ : X ≃ X' := Equiv.ofFiberEquiv hfib
  have hσ : ∀ S, (σ S : Finset ℕ).card = (S : Finset ℕ).card := fun S =>
    Equiv.ofFiberEquiv_map hfib S
  have hfib' : ∀ S : X, {i : X.biUnion id // blockOf X i = S} ≃
      {i' : X'.biUnion id // σ.symm (blockOf X' i') = S} := fun S =>
    (blockFiberEquiv hX S).trans <|
      (Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hσ])).trans <|
        (blockFiberEquiv hX' (σ S)).symm.trans <|
          Equiv.subtypeEquivRight fun i' => σ.symm_apply_eq.symm
  refine ⟨Equiv.ofFiberEquiv hfib', σ, hσ, fun i => ?_⟩
  exact σ.symm_apply_eq.1 (Equiv.ofFiberEquiv_map hfib' i)

end Bijection

/-! ### The edge sets `𝖤^X` -/

section BlockGraph

/-- The graphs of `𝖤^X`, in terms of a block map: `E` has an edge, every edge joins two different
blocks, and `E` together with the complete graphs on the blocks is connected. -/
def IsBlockGraph {ι κ : Type*} (blk : ι → κ) (E : SimpleGraph ι) : Prop :=
  (∀ i j, E.Adj i j → blk i ≠ blk j) ∧ E.edgeSet.Nonempty ∧
    (E ⊔ SimpleGraph.fromRel fun i j => blk i = blk j).Connected

theorem isBlockGraph_comap {ι ι' κ κ' : Type*} (blk : ι → κ) (blk' : ι' → κ') (e : ι ≃ ι')
    (σ : κ ≃ κ') (hblk : ∀ i, blk' (e i) = σ (blk i)) (E : SimpleGraph ι) :
    IsBlockGraph blk' (E.comap e.symm) ↔ IsBlockGraph blk E := by
  have hblk' : ∀ i', blk' i' = σ (blk (e.symm i')) := fun i' => by
    rw [← hblk, e.apply_symm_apply]
  unfold IsBlockGraph
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro h i j hij
      have := h (e i) (e j) (by simpa using hij)
      rwa [hblk, hblk, σ.injective.ne_iff] at this
    · intro h i' j' hij
      rw [hblk', hblk', σ.injective.ne_iff]
      exact h _ _ hij
  · constructor
    · rintro ⟨x, hx⟩
      induction x using Sym2.ind with
      | h a b => exact ⟨s(e.symm a, e.symm b), hx⟩
    · rintro ⟨x, hx⟩
      induction x using Sym2.ind with
      | h a b => exact ⟨s(e a, e b), by simpa using hx⟩
  · let iso : (E ⊔ SimpleGraph.fromRel fun i j => blk i = blk j) ≃g
        (E.comap e.symm ⊔ SimpleGraph.fromRel fun i j => blk' i = blk' j) :=
      { toEquiv := e
        map_rel_iff' := by
          intro a b
          simp [sup_adj, fromRel_adj, hblk] }
    exact iso.connected_iff.symm

variable {X : Finset (Finset ℕ)}

theorem isBlockGraph_blockOf_iff (hX : IsSubpartition X) (E : SimpleGraph (X.biUnion id)) :
    ((∀ i j : X.biUnion id, E.Adj i j →
        ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
      E.edgeSet.Nonempty ∧
      (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
        ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected) ↔
    IsBlockGraph (blockOf X) E := by
  have hrel : (fun i j : X.biUnion id => ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S) =
      fun i j => blockOf X i = blockOf X j := by
    funext i j
    refine propext ⟨?_, fun h => ⟨_, (blockOf X i).2, mem_blockOf i, by
      rw [h]; exact mem_blockOf j⟩⟩
    rintro ⟨S, hS, hi, hj⟩
    rw [blockOf_eq hX hS hi, blockOf_eq hX hS hj]
  unfold IsBlockGraph
  rw [hrel]
  refine and_congr ⟨adj_blockOf_ne hX, fun h i j hij => ?_⟩ Iff.rfl
  exact ⟨_, (blockOf X i).2, _, (blockOf X j).2, fun h' => h i j hij (Subtype.ext h'),
    mem_blockOf i, mem_blockOf j⟩

end BlockGraph

/-! ### Profile independence -/

open scoped Classical in
/-- **`𝖪^mult(X)` depends only on the profile of `X`** ("by exchangeability", Lemma 4.26). -/
theorem multipoleActivity_eq_of_blockProfile_eq (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hN : 1 ≤ N) {X X' : Finset (Finset ℕ)} (hX : IsSubpartition X) (hX' : IsSubpartition X')
    (hprof : blockProfile X = blockProfile X') :
    multipoleActivity χ N β lam M X = multipoleActivity χ N β lam M X' := by
  obtain ⟨e, σ, hσ, he⟩ := exists_blockEquiv hX hX' hprof
  rw [multipoleActivity_eq_box hχ hlam hN hX, multipoleActivity_eq_box hχ hlam hN hX']
  have hprod : ∏ S ∈ X, multipolePartitionFunction χ N β lam M S =
      ∏ S ∈ X', multipolePartitionFunction χ N β lam M S := by
    rw [← Finset.prod_coe_sort X, ← Finset.prod_coe_sort X']
    exact Fintype.prod_equiv σ _ _ fun S =>
      multipolePartitionFunction_congr_card hχ hlam hN (hσ S).symm
  have hcard : (X.biUnion id).card = (X'.biUnion id).card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe (X'.biUnion id)]
    exact Fintype.card_congr e
  rw [hprod, hcard]
  congr 2
  refine Finset.sum_equiv e.simpleGraph (fun E => ?_) (fun E _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.simpleGraph_apply]
    rw [isBlockGraph_blockOf_iff hX, isBlockGraph_blockOf_iff hX',
      isBlockGraph_comap _ _ e σ he]
  · rw [Equiv.simpleGraph_apply, show E.comap e.symm = E.map e.toEmbedding from comap_symm E e]
    exact (integral_multBox_relabel hχ (blockOf X) (blockOf X') e σ he E).symm

/-! ### The limit `𝗄^mult` as a function of the profile -/

/-- **Lemma 4.26 (𝗄^mult), in the form of Theorem 2 (1).** For `β > 2` and `M ≥ 1` there is
`𝗄^mult : (0, ∞) × (ℕ →₀ ℕ) → ℝ` with `N^{|X|-1} 𝖪^mult_{β,λ}(X) → 𝗄^mult_{β,λ}((#_k X)_k)` for
every `λ > 0` and every subpartition `X` with `∑_{S ∈ X} |S| ≤ p*(β)`. -/
theorem exists_tendsto_multipoleActivity_blockProfile (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) :
    ∃ kmult : ℝ → (ℕ →₀ ℕ) → ℝ, ∀ lam : ℝ, 0 < lam →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
        Tendsto (fun N : ℕ =>
            (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
          (𝓝 (kmult lam (blockProfile X))) := by
  have key : ∀ (lam : ℝ) (P : ℕ →₀ ℕ), ∃ L : ℝ, 0 < lam →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
        blockProfile X = P →
        Tendsto (fun N : ℕ =>
            (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop (𝓝 L) := by
    intro lam P
    by_cases h : 0 < lam ∧ ∃ X₀ : Finset (Finset ℕ), IsSubpartition X₀ ∧
        ((∑ S ∈ X₀, S.card : ℕ) : ℕ∞) ≤ pStar β ∧ blockProfile X₀ = P
    · obtain ⟨hlam, X₀, hX₀, hk₀, hP₀⟩ := h
      obtain ⟨L, hL⟩ := exists_tendsto_multipoleActivity hχ hβ hlam hM hX₀
        (by rwa [card_biUnion_eq_sum hX₀])
      refine ⟨L, fun _ X hX _ hP => ?_⟩
      have hprof : blockProfile X₀ = blockProfile X := hP₀.trans hP.symm
      have hc := card_eq_of_blockProfile_eq hprof
      refine hL.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [hc, multipoleActivity_eq_of_blockProfile_eq hχ hlam hN hX₀ hX hprof]
    · exact ⟨0, fun hlam X hX hk hP => absurd ⟨hlam, X, hX, hk, hP⟩ h⟩
  choose kmult hkmult using key
  exact ⟨kmult, fun lam hlam X hX hk => hkmult lam _ hlam X hX hk rfl⟩

end Limits

end MultipoleBKT

end
