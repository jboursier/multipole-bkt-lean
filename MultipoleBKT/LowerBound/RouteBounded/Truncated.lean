/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.ActivityFromTrees
public import MultipoleBKT.LowerBound.ExpansionErrors.Normalization

/-!
# Finite-cutoff grouped lower activities

The proof of Proposition 4.23. The truncated dipole density supplies the radial cutoff
in the displayed J integral. Its hatted bound applies to the zero model.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical Multipole Parity SetPartition Limits SmallIntegral
open UpperBound.BoundedUpper
open scoped Classical

/-- Internal finite-cutoff consumer of the grouped tree reduction. -/
theorem prod_mul_abs_activity_cut_le {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {N p₀ : ℕ} {β lam M ε₀ : ℝ} (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hM : 1 ≤ M)
    {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
    (h : ModelHyp (cutoffDipoleMeasure χ N p₀ β lam ε₀) β w ψ (cutoffSet N p₀ β lam ε₀))
    (hw₁ : ∀ d e, w d.swap e = -w d e) (hw₂ : ∀ d e, w d e.swap = -w d e)
    (hψ : ∀ d, ψ d.swap = ψ d)
    (hwb : ∃ C, ∀ d ∈ cutoffSet N p₀ β lam ε₀, ∀ e ∈ cutoffSet N p₀ β lam ε₀, |w d e| ≤ C)
    {Wb Ψ Cab : ℝ} (hWb : 1 ≤ Wb) (hΨ : 1 ≤ Ψ) (hCab : 1 ≤ Cab)
    (hstab : ∀ d ∈ cutoffSet N p₀ β lam ε₀, ∀ e ∈ cutoffSet N p₀ β lam ε₀, stableWeight β w d e ≤ Wb)
    (hψb : ∀ d ∈ cutoffSet N p₀ β lam ε₀, ψ d ≤ Ψ)
    (hb : ∀ d ∈ cutoffSet N p₀ β lam ε₀, ∀ e ∈ cutoffSet N p₀ β lam ε₀,
      |oddBondUnlinked β w M lam d e| ≤ Cab * BoundedLowerEps.oddMajP M lam d e ∧
      |evenBondMult β w M lam d e| ≤ Cab * BoundedLowerEps.evenMajP M lam d e)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card) {Ct : ℝ} (hCt : 0 ≤ Ct)
    (hTree : ∀ {n : ℕ} (Ys : Fin n → Finset (Finset ℕ)),
      (∀ l, Ys l ⊆ X) → (∀ l j, l ≠ j → Disjoint (Ys l) (Ys j)) →
      ∀ Ta : ∀ l, SimpleGraph ((Ys l).biUnion id), (∀ l, IsRelTree (Ys l) (Ta l)) →
      ∀ Tb : SimpleGraph ((coarsen X (univ.image Ys)).biUnion id),
        IsRelTree₀ (coarsen X (univ.image Ys)) Tb →
      (∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
        (hatTreeCore M lam X Ys Ta Tb (extendConfig (X.biUnion id) y) *
          (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
          ∏ i, cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (y i))) ≤ ENNReal.ofReal Ct) :
    (∏ S ∈ X, modelPartitionFunction (cutoffDipoleMeasure χ N p₀ β lam ε₀) β w ψ M lam S) *
        |modelActivity (cutoffDipoleMeasure χ N p₀ β lam ε₀) β w ψ M lam X| ≤
      parityCount (X.biUnion id).card *
        ((((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ (X.biUnion id).card) *
          (Wb ^ ((X.biUnion id).card * (X.biUnion id).card) * Ψ ^ (X.biUnion id).card *
            Cab ^ ((X.biUnion id).card * (X.biUnion id).card)) *
          (2 ^ ((X.biUnion id).card * (X.biUnion id).card * (X.biUnion id).card) * Ct)) := by
  apply prod_mul_abs_activity_le hχ h (measurePreserving_swap_cutoffDipoleMeasure hχ N p₀ β lam ε₀)
    hw₁ hw₂ hψ hwb hlam hM hX h2 rfl
    (cutDens χ β lam (ε₀ * truncationScale p₀ β lam)) (measurable_cutDens hχ hlam β _)
    (cutDens_nonneg _) ?_ (natCast_mul_cutoffDipoleNormalization_pos hχ hlam β hε₀ hN)
    ?_ hWb hΨ hCab hstab hψb hb hCt hTree
  · intro y hy hden i
    refine ⟨hy i (Set.mem_univ i), ?_⟩
    by_contra hnorm
    apply hden
    apply prod_eq_zero (mem_univ i)
    unfold cutDens
    rw [Set.indicator_of_notMem (show ‖(y i).1 - (y i).2‖ ∉ Set.Iic (ε₀ * truncationScale p₀ β lam) from hnorm), mul_zero]
  · intro f
    have hπ := ExpansionErrors.integral_pi_cutoffDipoleMeasure (p₀ := p₀) hχ hlam β hε₀ hN f
    rw [Fintype.card_coe] at hπ
    simp_rw [ExpansionErrors.cutoffWeight_eq_indicator, BoundedLowerEps.indicator_exp_eq_cutDens] at hπ
    exact hπ

end MultipoleBKT.LowerBound.RouteBounded

end
