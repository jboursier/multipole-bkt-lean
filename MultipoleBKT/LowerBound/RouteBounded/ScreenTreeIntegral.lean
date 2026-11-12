/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.TreeIntegral
public import MultipoleBKT.UpperBound.BoundedUpper.JMeasurable

/-!
# Integrating the screened separate trees using J

The proof of Proposition 4.23, and Lemma A.4.
Apply Lemma A.4 to the actual separate-tree integrand, with its finite radial cutoff.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open SetPartition MeasureTheory Finset SimpleGraph Hierarchical Multipole Parity Peeling Limits SmallIntegral
open UpperBound.BoundedUpper
open scoped Classical

/-- The screened separate-tree integrand is integrated by `J`. -/
theorem exists_screenTreeIntegral_cut_le {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {β M ε₀ : ℝ} (hβ : 2 < β) (hM : 1 ≤ M) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)) (_hX : IsSubpartition X),
      2 ≤ X.card → (X.biUnion id).card = k →
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l m, l ≠ m → Disjoint (Xs l) (Xs m)) →
      ∀ Ta : ∀ l, SimpleGraph ((Xs l).biUnion id), (∀ l, IsRelTree (Xs l) (Ta l)) →
      ∀ Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id),
        IsRelTree₀ (coarsen X (univ.image Xs)) Tb →
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam ≤ Appendix.lamBound ε₀ k → ∀ N : ℕ,
      (∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
        (jIntegrand M lam ε₀ (truncationScale p₀ β lam) X Xs Ta Tb (extendConfig (X.biUnion id) y) *
          (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
          ∏ i, cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (y i))) ≤
        ENNReal.ofReal (C * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k)) := by
  obtain ⟨C, hC, hbound⟩ := lemma_A6 hχ hβ k hM hε₀ hε₁
  refine ⟨C, hC, ?_⟩
  intro X hX h2 hk n Xs hXs hdisj Ta hTa Tb hTb p₀ lam hlam hlt N
  obtain ⟨hatS, hhat⟩ := exists_hatS hX Xs hXs Ta hTa
  have hW : (coarsen X (univ.image Xs)).biUnion id = X.biUnion id :=
    biUnion_coarsen fun Y hY => by
      obtain ⟨l, _, rfl⟩ := mem_image.1 hY
      exact hXs l
  have hd (y : X.biUnion id → ℂ × ℂ) :
      (jIntegrand M lam ε₀ (truncationScale p₀ β lam) X Xs Ta Tb (extendConfig _ y) *
        (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig _ y) S) then (1 : ℝ) else 0) *
        ∏ i, cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (y i)) =
      jFullIntegrand M lam ε₀ (truncationScale p₀ β lam) χ β X Xs Ta Tb y := by
    unfold jFullIntegrand cutDens pairDensity
    congr 1
    apply prod_congr rfl
    intro i _
    congr 1
    simp only [Set.indicator_apply, Set.mem_Iic, Metric.mem_closedBall, dist_zero_right,
      Pi.one_apply]
  exact (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (by
    rw [hd]
    exact jFullIntegrand_le_integrandJ p₀ hX Xs hXs hdisj Ta Tb hW hatS hhat y)).trans
    (hbound X hX h2 hk Xs hXs hdisj _
      (fun l => mem_image.2 ⟨Ta l, mem_relTrees.2 (hTa l), rfl⟩) _
      (mem_image.2 ⟨Tb, mem_relTrees₀.2 hTb, rfl⟩) hatS hhat p₀ lam hlam hlt N)

end MultipoleBKT.LowerBound.RouteBounded

end
