/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ModelBoundary

/-!
# Actual cut-even summands at the spatial integration boundary

See (A.51) and Step 2 of the proof of Lemma A.7. Arbitrary cut-even subsets from the actual cluster expansion
are transported to the original graph. Their original five-subset terms are
then bounded by the complete component and even-tree alternatives.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SimpleGraph Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)}

/-- The actual frozen expansion's integration boundary. The equality in the
conclusion rewrites the odd family back to the original cut-even subset,
so the terms bounded by `MixedBoundary` are precisely the expansion's terms. -/
theorem frozen_actual_mixed_pointwise {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {N p₀ : ℕ} {lam M ε₀ h : ℝ}
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → 1 ≤ M →
      ∀ (Near Far : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (O : Finset (Sym2 (X.biUnion id))),
      (hO : O ⊆ symOf (X.biUnion id) Far) →
      (hcut : CutEven (Sym2.map (Limits.blockOf X)) O) →
      ∀ (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      let hs := actual_source_odd hX hFar hO hcut
      symOf (X.biUnion id) (sourcePairs O) = O ∧
      MixedBoundary hX (hs.1.trans hFar) hs.2.2 χ β lam M h K (Real.exp (β * cbK hχ))
        (routeFrozenInteraction χ p₀ β lam ε₀ V Z) (routeFrozenRadius p₀ β lam ε₀ V Z)
        (routeFrozenQuadratic p₀ β lam ε₀ L V Z) (routeFrozenBad p₀ β lam M ε₀ V Z)
        Near Far Dz c := by
  obtain ⟨K,hK,hb⟩ := frozen_mixed_pointwise (L := L) hχ hβ hX
  refine ⟨K,hK,?_⟩
  intro N p₀ lam M ε₀ h V Z hlam hM Near Far hFar hconn O hO hcut Dz c
  have hs := actual_source_odd hX hFar hO hcut
  exact ⟨hs.2.1,hb (h := h) V Z hlam hM Near Far (sourcePairs O) hFar hconn hs.1 hs.2.2 Dz c⟩

/-- The corresponding entry point for the actual screened mixed terms. -/
theorem screened_actual_mixed_pointwise {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {lam M ε₀ R : ℝ}, 0 < lam → 1 ≤ M → lam ≤ ε₀ * R →
      ∀ (Near Far : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (O : Finset (Sym2 (X.biUnion id))),
      (hO : O ⊆ symOf (X.biUnion id) Far) →
      (hcut : CutEven (Sym2.map (Limits.blockOf X)) O) →
      ∀ (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      let hs := actual_source_odd hX hFar hO hcut
      symOf (X.biUnion id) (sourcePairs O) = O ∧
      MixedBoundary hX (hs.1.trans hFar) hs.2.2 χ β lam M (ε₀ * R) K (Real.exp (β * cbK hχ))
        (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R)
        (fun d => Real.exp (-L * (‖d.1-d.2‖ / (ε₀ * R)) ^ 2) - 1) (fun _ => 0)
        Near Far Dz c := by
  obtain ⟨K,hK,hb⟩ := screened_mixed_pointwise_all (L := L) hχ hβ hX
  refine ⟨K,hK,?_⟩
  intro lam M ε₀ R hlam hM hlh Near Far hFar hconn O hO hcut Dz c
  have hs := actual_source_odd hX hFar hO hcut
  exact ⟨hs.2.1,hb hlam hM hlh Near Far (sourcePairs O) hFar hconn hs.1 hs.2.2 Dz c⟩

end MultipoleBKT.ExpansionK.RouteCases

end
