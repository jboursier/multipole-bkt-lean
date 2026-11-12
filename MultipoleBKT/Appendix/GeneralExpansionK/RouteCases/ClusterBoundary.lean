/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ActualBoundary
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.FrozenModelExpansion

/-!
# Complete pointwise bounds from the original cluster data

See (A.51) and Step 2 of the proof of Lemma A.7. The original near family and the far families supply the
connected original graph. Cut-even subsets and all five correction subsets
stay those of the actual cluster expansion.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SimpleGraph Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)}

/-- All original far families lie in the inter-block original pair family. -/
theorem cluster_far_subset (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
    (hXs : ∀ l, Xs l ⊆ X) (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l)) :
    univ.biUnion Es ⊆ interPairs X := by
  intro p hp
  obtain ⟨l,-,hp⟩ := mem_biUnion.1 hp
  exact interPairs_subset_of_subset hX (hXs l) ((mem_relEdgeSets.1 (hEs l)).1 hp)

/-- the frozen-model entry point on the original `(Dn,Dz,Df)` cluster data.
Connectivity, including the near bonds, is discharged inside this theorem. -/
theorem cluster_frozen_mixed_pointwise {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) (hXne : X.Nonempty) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {N p₀ n : ℕ} {lam M ε₀ h : ℝ}
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → 1 ≤ M →
      ∀ (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (Near : Finset (ℕ × ℕ))
      (hXs : ∀ l, Xs l ⊆ X) (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l)),
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      ∀ (O : Finset (Sym2 (X.biUnion id))) (hO : O ⊆ symOf (X.biUnion id) (univ.biUnion Es))
      (hcut : CutEven (Sym2.map (Limits.blockOf X)) O) (c : ℕ → ℂ × ℂ),
      let Far := univ.biUnion Es
      let hFar := cluster_far_subset hX Xs Es hXs hEs
      let hs := actual_source_odd hX hFar hO hcut
      symOf (X.biUnion id) (sourcePairs O) = O ∧
      MixedBoundary hX (hs.1.trans hFar) hs.2.2 χ β lam M h K (Real.exp (β * cbK hχ))
        (routeFrozenInteraction χ p₀ β lam ε₀ V Z) (routeFrozenRadius p₀ β lam ε₀ V Z)
        (routeFrozenQuadratic p₀ β lam ε₀ L V Z) (routeFrozenBad p₀ β lam M ε₀ V Z)
        Near Far (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ Far)) c := by
  obtain ⟨K,hK,hb⟩ := frozen_actual_mixed_pointwise (L := L) hχ hβ hX
  refine ⟨K,hK,?_⟩
  intro N p₀ n lam M ε₀ h V Z hlam hM Xs Es Near hXs hEs hNear O hO hcut c
  exact hb (h := h) V Z hlam hM Near (univ.biUnion Es) (cluster_far_subset hX Xs Es hXs hEs)
    (source_cluster_graph hX Xs Es Near hXs hEs hNear hXne) O hO hcut _ c

/-- the screened-model entry point on the same original cluster data. -/
theorem cluster_screened_mixed_pointwise {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) (hXne : X.Nonempty) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {n : ℕ} {lam M ε₀ R : ℝ}, 0 < lam → 1 ≤ M → lam ≤ ε₀ * R →
      ∀ (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (Near : Finset (ℕ × ℕ))
      (hXs : ∀ l, Xs l ⊆ X) (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l)),
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      ∀ (O : Finset (Sym2 (X.biUnion id))) (hO : O ⊆ symOf (X.biUnion id) (univ.biUnion Es))
      (hcut : CutEven (Sym2.map (Limits.blockOf X)) O) (c : ℕ → ℂ × ℂ),
      let Far := univ.biUnion Es
      let hFar := cluster_far_subset hX Xs Es hXs hEs
      let hs := actual_source_odd hX hFar hO hcut
      symOf (X.biUnion id) (sourcePairs O) = O ∧
      MixedBoundary hX (hs.1.trans hFar) hs.2.2 χ β lam M (ε₀ * R) K (Real.exp (β * cbK hχ))
        (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R)
        (fun d => Real.exp (-L * (‖d.1-d.2‖ / (ε₀ * R)) ^ 2) - 1) (fun _ => 0)
        Near Far (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ Far)) c := by
  obtain ⟨K,hK,hb⟩ := screened_actual_mixed_pointwise (L := L) hχ hβ hX
  refine ⟨K,hK,?_⟩
  intro n lam M ε₀ R hlam hM hlh Xs Es Near hXs hEs hNear O hO hcut c
  exact hb hlam hM hlh Near (univ.biUnion Es) (cluster_far_subset hX Xs Es hXs hEs)
    (source_cluster_graph hX Xs Es Near hXs hEs hNear hXne) O hO hcut _ c

end MultipoleBKT.ExpansionK.RouteCases

end
