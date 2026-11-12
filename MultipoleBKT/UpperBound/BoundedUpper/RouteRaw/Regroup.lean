/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Projection

/-!
# Regrouping after raw parity cancellation

The paper: Corollary 5.24, and Proposition 5.18.
The paper bound keeps the nested groups. The coefficient-one interface
`abs_plusActivity_le` additionally regroups the surviving terms. The
reversal projection stays in place throughout this algebraic adapter.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open MeasureTheory Finset Hierarchical Multipole Parity NonEmptyMarks
open scoped Classical

variable {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ L : ℝ}
  {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- The finite raw integrand before the reversal projection. -/
noncomputable def rawIntegrand (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (X : Finset (Finset ℕ))
    (c : ℕ → ℂ × ℂ) : ℝ :=
  ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
        ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
          clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F c *
            ∏ i ∈ X.biUnion id, (1 + externalBondZ χ p₀ β lam ε₀ V Z (c i))

/-- The nested marked integrand after non-parity terms have been removed. -/
noncomputable def rawProjectedSum (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (X : Finset (Finset ℕ))
    (c : ℕ → ℂ × ℂ) : ℝ :=
  ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
        ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
          rawProjectedTerm χ p₀ β lam M ε₀ V Z X Xs Es F c

/-- Reversal is applied separately to every raw marked term. -/
theorem reversalAverage_rawIntegrand (hM : 1 ≤ M) (X : Finset (Finset ℕ)) :
    reversalAverage (flipOn Prod.swap) X.toList (rawIntegrand χ p₀ β lam M ε₀ V Z X) =
      rawProjectedSum χ p₀ β lam M ε₀ V Z X := by
  unfold rawIntegrand
  simp only [reversalAverage_sum, reversalAverage_mul]
  funext c
  apply sum_congr rfl
  intro n _
  apply congrArg (fun a : ℝ => 1 / (n.factorial : ℝ) * a)
  apply sum_congr rfl
  intro Xs _
  apply sum_congr rfl
  intro Es hEs
  apply sum_congr rfl
  intro F _
  exact congrFun (reversalAverage_raw hM X
    (fun l => (mem_relEdgeSets.1 (Fintype.mem_piFinset.1 hEs l)).1) F) c

/-- Internal algebra for the coefficient-one estimate. This identity is used only
under the reversal projection, after raw parity has been cancelled. -/
theorem regroup_rawIntegrand (hM : 1 ≤ M) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (h2 : 2 ≤ X.card) (c : ℕ → ℂ × ℂ) :
    rawIntegrand χ p₀ β lam M ε₀ V Z X c =
      ∑ E ∈ relEdgeSets₀ X, ∑ E₁ ∈ E.powerset,
        ∑ U₁ ∈ (X.biUnion id).powerset, reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁ c := by
  let f := fun p : ℕ × ℕ => mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c p.1) (c p.2)
  let b := fun p : ℕ × ℕ => if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0
  have hraw : rawIntegrand χ p₀ β lam M ε₀ V Z X c =
      clusterSeries f b X * ∏ i ∈ X.biUnion id,
        (1 + externalBondZ χ p₀ β lam ε₀ V Z (c i)) := by
    rw [clusterSeries, tsum_eq_sum (s := range (X.card + 1)) fun n hn => by
      rw [mem_range, not_lt] at hn
      rw [sum_piFinset_relEdgeSets_eq_zero (by omega), mul_zero]]
    unfold rawIntegrand
    simp_rw [Finset.sum_mul]
    apply sum_congr rfl
    intro n _
    rw [mul_assoc]
    apply congrArg (fun a : ℝ => 1 / (n.factorial : ℝ) * a)
    simp_rw [Finset.sum_mul]
    apply sum_congr rfl
    intro Xs _
    apply sum_congr rfl
    intro Es _
    apply sum_congr rfl
    intro F _
    rw [clusterTerm_eq]
  rw [hraw, clusterSeries_eq_groupWeight hX,
    ← relConnSum_eq_groupWeight hX le_rfl (Finset.card_pos.1 (by omega)),
    relConnSum_eq_sum_relEdgeSets₀, Finset.sum_mul]
  apply sum_congr rfl
  intro E _
  have hu : ∀ p, (1 + f p) * (1 - b p) - 1 =
      unlinkedBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2) := by
    intro p
    unfold unlinkedBondOf f b mayerBondOf stableWeight
    split_ifs <;> ring
  simp_rw [hu, unlinkedBondOf_eq_add hM, one_add_externalBondZ_eq]
  rw [Finset.prod_add, Finset.prod_add, Finset.sum_mul_sum]
  apply sum_congr rfl
  intro E₁ _
  apply sum_congr rfl
  intro U₁ _
  unfold reducedTerm
  ring

/-- Regroup the surviving raw terms while retaining the reversal projection.
Connected reduced terms occur only at this final compatibility step. -/
theorem rawProjectedSum_eq_reduced (hM : 1 ≤ M) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (h2 : 2 ≤ X.card) (c : ℕ → ℂ × ℂ) :
    rawProjectedSum χ p₀ β lam M ε₀ V Z X c =
      ∑ E ∈ relEdgeSets₀ X, ∑ E₁ ∈ E.powerset,
        ∑ U₁ ∈ (X.biUnion id).powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
          reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁ c := by
  rw [← reversalAverage_rawIntegrand hM X]
  have hreg := funext (regroup_rawIntegrand (χ := χ) (p₀ := p₀) (β := β)
    (lam := lam) (ε₀ := ε₀) (V := V) (Z := Z) hM hX h2)
  rw [hreg]
  simp_rw [reversalAverage_sum, reversalAverage_reducedTerm hM]
  apply sum_congr rfl
  intro E _
  apply sum_congr rfl
  intro E₁ _
  simp only [Finset.sum_filter, ite_apply]

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
