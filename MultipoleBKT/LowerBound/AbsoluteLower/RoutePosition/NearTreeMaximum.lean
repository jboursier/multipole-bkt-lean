/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Bridge
public import MultipoleBKT.LowerBound.AbsoluteLower.RoutePosition.NearTrees
public import MultipoleBKT.UpperBound.SimplifiedUpper.Series

/-!
# The paper's fixed-near-tree integral and its maximum

The proof of Lemma 4.58. The connected-block union
bound is integrated over actual near-tree families. Cayley's exact count
then multiplies the maximum of `J₁`, before spatial integration or any
summation over groups and far trees.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RoutePosition

open MeasureTheory Finset SimpleGraph Multipole SetPartition Limits SmallIntegral Parity
open scoped Classical ENNReal

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ C₀ : ℝ} {X : Finset (Finset ℕ)}

/-- The paper's `J₁` at fixed groups, fixed far trees and fixed near trees.
proof of Lemma 4.58. -/
noncomputable def jOne (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ C₀ : ℝ)
    (X : Finset (Finset ℕ)) {κ : Type*} [Fintype κ]
    (G : κ → Finset (Finset ℕ)) (Ta : κ → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (Q : RouteJ.NearTreeFamily (Limits.blockOf X)) : ℝ≥0∞ :=
  ∫⁻ y in boxConfig (X.biUnion id) N,
    ENNReal.ofReal (flatTreeIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Tb Q y)

/-- Measurability permits integration of the finite near-tree union bound. -/
theorem measurable_flatTreeIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    {κ : Type*} [Fintype κ] (G : κ → Finset (Finset ℕ))
    (Ta : κ → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (Q : RouteJ.NearTreeFamily (Limits.blockOf X)) :
    Measurable (flatTreeIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Tb Q) := by
  have hext := measurable_extendConfig (X.biUnion id)
  unfold flatTreeIntegrand
  dsimp only
  apply Measurable.mul
  · apply Measurable.mul
    · exact ((Finset.measurable_prod _ fun p _ =>
        (measurable_pairWeight (measurable_absEvenWeight M lam ε₀ _) p).comp hext).mul
        (Finset.measurable_prod _ fun l _ =>
          (UpperBound.SimplifiedUpper.measurable_prodExceptMax (G l)).comp hext)).mul
        (Finset.measurable_prod _ fun l _ => Finset.measurable_prod _ fun p _ =>
          (UpperBound.SimplifiedUpper.measurable_keptPair M lam ε₀ _ p).comp hext)
    · apply Finset.measurable_prod
      intro e _
      induction e using Sym2.ind with
      | h i j =>
        exact Measurable.ite (measurableSet_setOf_multipoleLinked M lam i j)
          measurable_const measurable_const
  · apply Finset.measurable_prod
    intro i _
    have hr : Measurable (fun c : ℕ → ℂ × ℂ =>
        (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) := by
      fun_prop
    exact (hr.mul ((measurable_cutDens hχ hlam β _).comp (measurable_pi_apply i))).comp hext

/-- Each fibre of the block map has the cardinality of its original block. -/
theorem card_block_fibre (hX : IsSubpartition X) (S : X) :
    Fintype.card {i : X.biUnion id // Limits.blockOf X i = S} = S.val.card := by
  let e : {i : X.biUnion id // Limits.blockOf X i = S} ≃ S.val :=
    { toFun := fun i => ⟨i.val.val, (Limits.blockOf_eq_iff hX i.val S).mp i.property⟩
      invFun := fun j => ⟨⟨j.val, mem_biUnion.mpr ⟨S.val, S.property, j.property⟩⟩,
        Limits.blockOf_eq hX S.property j.property⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe S.val)

/-- The near-tree union bound followed by the exact Cayley count and a maximum.
Groups and both far-tree families are fixed throughout.
proof of Lemma 4.58. -/
theorem lintegral_flatIntegrand_le_cayley_max (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hX : IsSubpartition X) (hh : 0 ≤ ε₀ * truncationScale p₀ β lam) (N : ℕ)
    {κ : Type*} [Fintype κ] (G : κ → Finset (Finset ℕ))
    (Ta : κ → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ)) :
    (∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
      (flatIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Tb (extendConfig (X.biUnion id) y))) ≤
      (∏ S ∈ X, S.card ^ (S.card - 2) : ℕ) *
        ⨆ Q : RouteJ.NearTreeFamily (Limits.blockOf X), jOne χ N p₀ β lam M ε₀ C₀ X G Ta Tb Q := by
  have hn (Q : RouteJ.NearTreeFamily (Limits.blockOf X)) (y : X.biUnion id → ℂ × ℂ) :
      0 ≤ flatTreeIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Tb Q y := by
    unfold flatTreeIntegrand
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (prod_nonneg fun _ _ => absEvenWeight_nonneg _ _ _ _ _ _)
      (prod_nonneg fun _ _ => prodExceptMax_nonneg _))
      (prod_nonneg fun _ _ => prod_nonneg fun _ _ => keptPair_nonneg _))
      (prod_nonneg fun _ _ => linkE_nonneg _ _))
      (prod_nonneg fun _ _ => mul_nonneg
        (Real.rpow_nonneg (div_nonneg hh (norm_nonneg _)) _) (cutDens_nonneg _ _))
  have hcount : (∏ S : X, Fintype.card {i : X.biUnion id // Limits.blockOf X i = S} ^
      (Fintype.card {i : X.biUnion id // Limits.blockOf X i = S} - 2)) =
      ∏ S ∈ X, S.card ^ (S.card - 2) := by
    simp_rw [card_block_fibre hX]
    exact prod_coe_sort X (fun S : Finset ℕ => S.card ^ (S.card - 2))
  calc
    _ ≤ ∫⁻ y in boxConfig (X.biUnion id) N,
        ∑ Q : RouteJ.NearTreeFamily (Limits.blockOf X),
          ENNReal.ofReal (flatTreeIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Tb Q y) := by
      apply lintegral_mono
      intro y
      refine (ENNReal.ofReal_le_ofReal (flatIntegrand_le_sum_nearTree hX hh G Ta Tb y)).trans ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun Q _ => hn Q y)]
    _ = ∑ Q : RouteJ.NearTreeFamily (Limits.blockOf X), jOne χ N p₀ β lam M ε₀ C₀ X G Ta Tb Q :=
      lintegral_finsetSum _ fun Q _ => (measurable_flatTreeIntegrand hχ hlam G Ta Tb Q).ennreal_ofReal
    _ ≤ _ := by
      simpa only [hcount] using sum_nearTreeFamily_le_count_mul_max (Limits.blockOf X)
        (Limits.blockOf_surjective hX) (jOne χ N p₀ β lam M ε₀ C₀ X G Ta Tb)


end MultipoleBKT.AbsoluteLower.RoutePosition

end
