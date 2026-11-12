/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.ClusterIntegral
public import MultipoleBKT.LowerBound.RouteBounded.GroupedParity

/-!
# Summing fixed expectation differences

The proof of Proposition 4.24. This final counting step is applied after the estimate
of each individual expectation difference.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionErrors

open MeasureTheory Finset Hierarchical Multipole SetPartition LowerBound.RouteBounded
open scoped Classical

/-- Internal final summation of fixed expectation estimates for two
models. The coefficient depends only on the number of labels. -/
theorem internal_activity_diff_of_fixed_expectations
    {ρ₁ ρ₀ : Measure (ℂ × ℂ)} {β M lam : ℝ}
    {w₁ w₀ : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ₁ ψ₀ : ℂ × ℂ → ℝ}
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card)
    {k : ℕ} (hk : (X.biUnion id).card = k) {D : ℝ} (hD : 0 ≤ D)
    (hf : ∀ n (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
        |(∫ y, clusterTerm β w₁ M lam Xs Es F (extendConfig (X.biUnion id) y)
            ∂modelHierarchical ρ₁ β w₁ ψ₁ M lam X) -
          (∫ y, clusterTerm β w₀ M lam Xs Es F (extendConfig (X.biUnion id) y)
            ∂modelHierarchical ρ₀ β w₀ ψ₀ M lam X)| ≤ D) :
    |modelActivity ρ₁ β w₁ ψ₁ M lam X - modelActivity ρ₀ β w₀ ψ₀ M lam X| ≤ countBound k * D := by
  have hsum := abs_clusterSum_le hX hD hf
  have hid₁ : modelActivity ρ₁ β w₁ ψ₁ M lam X = clusterSum X (fun _ Xs Es F =>
      ∫ y, clusterTerm β w₁ M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical ρ₁ β w₁ ψ₁ M lam X) := modelActivity_eq_grouped h2
  have hid₀ : modelActivity ρ₀ β w₀ ψ₀ M lam X = clusterSum X (fun _ Xs Es F =>
      ∫ y, clusterTerm β w₀ M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical ρ₀ β w₀ ψ₀ M lam X) := modelActivity_eq_grouped h2
  rwa [← clusterSum_sub, ← hid₁, ← hid₀, hk] at hsum

end MultipoleBKT.ExpansionErrors

end
