/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Legacy

/-!
# Counting the raw marked expansion

The paper: Proposition 5.18. Start with the raw groups, expand the external marks,
apply reversal and extract odd components and an even tree in each term.
For bounded size, finite budgets replace the paper's maxima by sums.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open MeasureTheory Finset Hierarchical Multipole Parity NonEmptyMarks
open scoped Classical

/-- An explicit budget for the choices of groups, edges, and external marks
in the bounded-size raw expansion. -/
def rawCount (k : ℕ) : ℝ :=
  (k + 1 : ℝ) * 2 ^ (k * k) * 2 ^ (k * k * k) * 2 ^ (k * k) *
    2 ^ k * 2 ^ (k * k) * 2 ^ k

/-- Internal adapter from uniform reduced-term bounds to the raw activity.
The reduced-term bound is supplied by the family estimate and integration. -/
theorem activity_le_of_reduced {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ L : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hM : 1 ≤ M)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card)
    (hM0 : ∀ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≠ 0)
    {k : ℕ} (hk : (X.biUnion id).card ≤ k) {Q : ℝ} (hQ : 0 ≤ Q)
    (hterm : ∀ E ∈ relEdgeSets₀ X, ∀ E₁ ∈ E.powerset,
      ∀ U₁ ∈ (X.biUnion id).powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
      ∫ y, (|reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁ (extendConfig (X.biUnion id) y)| *
        oddSeparation M lam X E₁ (extendConfig (X.biUnion id) y))
        ∂plusModel χ N p₀ β lam M ε₀ L V Z X ≤ Q) :
    |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤ rawCount k * Q := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  have hXk : X.card ≤ k := (card_le_card_biUnion hX.2 hX.1).trans hk
  obtain ⟨hm, hb⟩ := externalBondZ_regular (p₀ := p₀) (β := β)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  let q₁ : ℝ := 2 ^ (k * k) * (2 ^ k * Q)
  let q₂ : ℝ := 2 ^ k * q₁
  let q₃ : ℝ := 2 ^ (k * k) * q₂
  let q₄ : ℝ := 2 ^ (k * k * k) * q₃
  let q₅ : ℝ := 2 ^ (k * k) * q₄
  have hq₁ : 0 ≤ q₁ := by dsimp [q₁]; positivity
  have hq₂ : 0 ≤ q₂ := mul_nonneg (by positivity) hq₁
  have hq₃ : 0 ≤ q₃ := mul_nonneg (by positivity) hq₂
  have hq₄ : 0 ≤ q₄ := mul_nonneg (by positivity) hq₃
  have hq₅ : 0 ≤ q₅ := mul_nonneg (by positivity) hq₄
  rw [plusActivity_eq_raw hχ hlam hε₀ hN hX h2 hM0]
  have houter : ∀ n ∈ range (X.card + 1),
      |1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
            ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
              ∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
                  (extendConfig (X.biUnion id) y) *
                ∏ i ∈ X.biUnion id,
                  (1 + externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i))
                ∂plusModel χ N p₀ β lam M ε₀ L V Z X| ≤ q₅ := by
    intro n hn
    have hnk : n ≤ k := (Nat.le_of_lt_succ (mem_range.1 hn)).trans hXk
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [abs_mul, abs_of_nonneg (one_div_nonneg.2 hfac.le)]
    have hfac1 : 1 / (n.factorial : ℝ) ≤ 1 := by
      rw [div_le_one hfac]
      exact_mod_cast Nat.factorial_pos n
    apply (mul_le_of_le_one_left (abs_nonneg _) hfac1).trans
    have hgroups : (((Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j))).card : ℝ) ≤ 2 ^ (k * k) := by
      exact_mod_cast card_group_tuples_le hXk hnk
    apply abs_sum_le_budget _ _ hgroups hq₄
    intro Xs hXs
    have hXsX : ∀ l, Xs l ⊆ X := fun l =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_filter.1 hXs).1 l)
    have hedges : ((Fintype.piFinset fun l => relEdgeSets (Xs l)).card : ℝ) ≤ 2 ^ (k * k * k) := by
      exact_mod_cast card_edge_tuples_le hk hnk Xs hXsX
    apply abs_sum_le_budget _ _ hedges hq₃
    intro Es hEs
    have hEs' : ∀ l, Es l ∈ relEdgeSets (Xs l) := Fintype.mem_piFinset.1 hEs
    have hEsI : ∀ l, Es l ⊆ interPairs (Xs l) := fun l => (mem_relEdgeSets.1 (hEs' l)).1
    have hCW : (coarsen X (univ.image Xs)).biUnion id = X.biUnion id :=
      biUnion_coarsen fun Y hY => by
        obtain ⟨l, _, rfl⟩ := mem_image.1 hY
        exact hXsX l
    have hsep : ((relEdgeSets₀ (coarsen X (univ.image Xs))).card : ℝ) ≤ 2 ^ (k * k) := by
      exact_mod_cast card_relEdgeSets₀_le (hCW ▸ hk)
    apply abs_sum_le_budget _ _ hsep hq₂
    intro F hF
    have hint : ∀ U ∈ (X.biUnion id).powerset,
        Integrable (fun y => clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
            (extendConfig (X.biUnion id) y) *
          ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i))
          (plusModel χ N p₀ β lam M ε₀ L V Z X) := by
      intro U hU
      have hU' := mem_powerset.1 hU
      apply h.integrable_comp_extendConfig
        ((measurable_clusterTerm β _ M lam h Xs Es F).mul
          (measurable_prod _ fun i _ => hm.comp (measurable_pi_apply i)))
        ((boundedOn_clusterTerm β _ M lam h Xs Es F).mul
          (BoundedOn.prod _ fun i _ => BoundedOn.single hb i))
      intro c c' hcc'
      simp only [Pi.mul_apply, Function.comp_apply]
      rw [dependsOn_clusterTerm β _ M lam hXsX hEsI (mem_relEdgeSets₀.1 hF).1 hcc']
      congr 1
      apply prod_congr rfl
      intro i hi
      rw [hcc' i (hU' hi)]
    simp_rw [Finset.prod_one_add, Finset.mul_sum]
    rw [integral_finsetSum _ hint]
    have hmarks : ((X.biUnion id).powerset.card : ℝ) ≤ 2 ^ k := by
      rw [card_powerset]
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) hk
    apply abs_sum_le_budget _ _ hmarks hq₁
    intro U hU
    exact raw_term_le_of_reduced hχ hlam hε₀ hN hM hX hk hXsX (mem_filter.1 hXs).2 hEs' hF hQ hterm U
      (mem_powerset.1 hU)
  have hncard : ((range (X.card + 1)).card : ℝ) ≤ (k + 1 : ℝ) := by
    rw [card_range]
    exact_mod_cast Nat.add_le_add_right hXk 1
  apply (abs_sum_le_budget _ _ hncard hq₅ houter).trans_eq
  dsimp [q₅, q₄, q₃, q₂, q₁, rawCount]
  ring

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
