/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Counting
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Separation
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Indicators

/-!
# Raw marked groups and their parity reduction

The paper: Proposition 5.18, and Corollary 5.24.
The hierarchical expansion identifies the nested marked series with the grouped integral. We use
that identification directly, retaining the Mayer groups and separation
edges. Reversal kills the non-parity terms before the odd components are
estimated. No compact connected-graph expansion is used here.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open MeasureTheory Finset Hierarchical Multipole Parity NonEmptyMarks
open scoped Classical

variable {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ L : ℝ}
  {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- The raw nested expansion after the external marks are summed. The
marked grouping identifies it with the activity under its original model. -/
theorem plusActivity_eq_raw (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (h2 : 2 ≤ X.card)
    (hM0 : ∀ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≠ 0) :
    plusActivity χ N p₀ β lam M ε₀ L V Z X =
      ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
            ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
              ∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
                  (extendConfig (X.biUnion id) y) *
                ∏ i ∈ X.biUnion id,
                  (1 + externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i))
                ∂plusModel χ N p₀ β lam M ε₀ L V Z X := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  obtain ⟨hm, hb⟩ := externalBondZ_regular (p₀ := p₀) (β := β)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  have hr := prod_mul_markedSeries_grouped (M := M) (lam := lam) h hX h2
    (m := fun c => ∏ i ∈ X.biUnion id, (1 + externalBondZ χ p₀ β lam ε₀ V Z (c i)))
    (Finset.measurable_prod _ fun i _ => measurable_const.add (hm.comp (measurable_pi_apply i)))
    (BoundedOn.prod _ fun i _ => (BoundedOn.const _ 1).add (BoundedOn.single hb i))
    (by
      intro c c' hcc'
      apply prod_congr rfl
      intro i hi
      rw [hcc' i hi])
  have hg := prod_plusPartitionFunction_mul_plusActivity_grouped
    (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN hX h2
  have heq := mul_left_cancel₀ (prod_ne_zero_iff.2 hM0) (hg.trans hr.symm)
  change plusActivity χ N p₀ β lam M ε₀ L V Z X = _ at heq
  rw [heq]
  apply tsum_eq_sum
  intro n hn
  rw [mem_range, not_lt] at hn
  rw [sum_piFinset_relEdgeSets_eq_zero (by omega), mul_zero]

/-- Even external marks are bounded by their cosh factors. This comparison
retains all odd marks and odd bonds. It is used after raw parity cancellation. -/
theorem abs_markedTerm_le_reduced {X : Finset (Finset ℕ)} {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} {Es : Fin n → Finset (ℕ × ℕ)}
    {F : Finset (ℕ × ℕ)} (hdisj : Disjoint (univ.biUnion Es) F)
    {E₁ : Finset (ℕ × ℕ)} (hE₁ : E₁ ⊆ univ.biUnion Es)
    {U U₁ : Finset ℕ} (hU : U ⊆ X.biUnion id) (c : ℕ → ℂ × ℂ) :
    |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c| ≤
      |reducedTerm χ p₀ β lam M ε₀ V Z X (univ.biUnion Es ∪ F) E₁ U₁ c| := by
  apply (abs_markedTerm_le_core hdisj hE₁ U U₁ c).trans
  have hcosh : (∏ i ∈ U \ U₁, (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) - 1)) ≤
      ∏ i ∈ X.biUnion id \ U₁, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) := by
    calc _ ≤ ∏ i ∈ U \ U₁, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) :=
        prod_le_prod₀ (fun i _ => sub_nonneg.2 (one_le_cosh' _))
          (fun i _ => sub_le_self _ zero_le_one)
      _ ≤ _ := prod_cosh_le_prod_cosh (sdiff_subset_sdiff_left U₁ hU) c
  rw [abs_reducedTerm_eq]
  have h0 : 0 ≤ (∏ p ∈ E₁, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
      (c p.1) (c p.2)|) *
      (∏ p ∈ (univ.biUnion Es ∪ F) \ E₁,
        |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
      ∏ i ∈ U₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| :=
    mul_nonneg (mul_nonneg (prod_nonneg fun _ _ => abs_nonneg _)
      (prod_nonneg fun _ _ => abs_nonneg _)) (prod_nonneg fun _ _ => abs_nonneg _)
  convert mul_le_mul_of_nonneg_left hcosh h0 using 1
  ring

/-- Internal finite-sum adapter. The raw marked expansion is reduced by
Corollary 5.24, then each surviving term is bounded.
The input is a uniform estimate on the reduced terms, not a paper theorem. -/
theorem raw_term_le_of_reduced (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hM : 1 ≤ M)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {k : ℕ}
    (hk : (X.biUnion id).card ≤ k) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hpair : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m))
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l))
    {F : Finset (ℕ × ℕ)} (hF : F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)))
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hterm : ∀ E ∈ relEdgeSets₀ X, ∀ E₁ ∈ E.powerset,
      ∀ U₁ ∈ (X.biUnion id).powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
      ∫ y, (|reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁ (extendConfig (X.biUnion id) y)| *
        oddSeparation M lam X E₁ (extendConfig (X.biUnion id) y))
        ∂plusModel χ N p₀ β lam M ε₀ L V Z X ≤ Q) (U : Finset ℕ) (hU : U ⊆ X.biUnion id) :
    |∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
        (extendConfig (X.biUnion id) y) *
      ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
      ∂plusModel χ N p₀ β lam M ε₀ L V Z X| ≤
      (2 : ℝ) ^ (k * k) * (2 ^ k * Q) := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  have hE := union_mem_relEdgeSets₀ hX hXs hEs hF
  have hEs' : ∀ l, Es l ⊆ interPairs (Xs l) := fun l => (mem_relEdgeSets.1 (hEs l)).1
  have hdisj := disjoint_biUnion_F hEs' (mem_relEdgeSets₀.1 hF).1
  have hFV : ∀ p ∈ F, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := by
    intro p hp
    have hp' := interPairs_subset_pairsOn ((mem_relEdgeSets₀.1 hE).1 (mem_union_right _ hp))
    exact ⟨(mem_pairsOn.1 hp').1, (mem_pairsOn.1 hp').2.1⟩
  apply (abs_integral_clusterTerm_mul_le hχ hlam hε₀ hN hM hX hXs hEs' hFV hU).trans
  have hinner : ∀ E₁ ∈ (univ.biUnion Es).powerset,
      ∑ U₁ ∈ U.powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
        ∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (extendConfig (X.biUnion id) y)|
          ∂plusModel χ N p₀ β lam M ε₀ L V Z X ≤ 2 ^ k * Q := by
    intro E₁ hE₁
    have hle : ∀ U₁ ∈ U.powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
        ∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (extendConfig (X.biUnion id) y)|
          ∂plusModel χ N p₀ β lam M ε₀ L V Z X ≤ Q := by
      intro U₁ hU₁
      obtain ⟨hU₁p, hpar⟩ := mem_filter.1 hU₁
      have hU₁X := (mem_powerset.1 hU₁p).trans hU
      have hint := integrable_abs_reduced_mul_oddSeparation
        (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z)
        hχ hlam hε₀ hN (mem_relEdgeSets₀.1 hE).1
        ((mem_powerset.1 hE₁).trans subset_union_left) hU₁X
      apply (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hint
        (Filter.Eventually.of_forall fun y => by
          let c := extendConfig (X.biUnion id) y
          let sep : ℝ := ∏ Y ∈ oddComponents X E₁, ∏ p ∈ interPairs Y,
            (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1)
          have hs0 : 0 ≤ sep := prod_nonneg fun Y _ => prod_nonneg fun p _ => by
            split_ifs <;> norm_num
          calc _ = |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c| * sep :=
              abs_markedTerm_eq_mul_oddSeparation hX hXs hpair hEs'
                (mem_powerset.1 hE₁) F U U₁ c
            _ ≤ |reducedTerm χ p₀ β lam M ε₀ V Z X (univ.biUnion Es ∪ F) E₁ U₁ c| * sep :=
              mul_le_mul_of_nonneg_right
                (abs_markedTerm_le_reduced hdisj (mem_powerset.1 hE₁) hU c) hs0
            _ = _ := rfl)).trans
      exact hterm _ hE _ (mem_powerset.2 ((mem_powerset.1 hE₁).trans subset_union_left)) _
        (mem_filter.2 ⟨mem_powerset.2 hU₁X, hpar⟩)
    apply (sum_le_card_nsmul _ _ Q hle).trans
    rw [nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hQ
    have hcard : (U.powerset.filter (fun U₁ => IsParityPair X E₁ U₁)).card ≤ 2 ^ k :=
      (card_filter_le _ _).trans ((card_powerset _).le.trans
        (Nat.pow_le_pow_right (by norm_num) ((card_le_card hU).trans hk)))
    exact_mod_cast hcard
  apply (sum_le_card_nsmul _ _ _ hinner).trans
  rw [nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) hQ)
  have hp : (univ.biUnion Es).card ≤ k * k :=
    (card_le_card (subset_union_left.trans ((mem_relEdgeSets₀.1 hE).1.trans interPairs_subset_pairsOn))).trans
      ((card_pairsOn_le _).trans (Nat.mul_le_mul hk hk))
  have hcard : (univ.biUnion Es).powerset.card ≤ 2 ^ (k * k) := by
    rw [card_powerset]
    exact Nat.pow_le_pow_right (by norm_num) hp
  exact_mod_cast hcard

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
