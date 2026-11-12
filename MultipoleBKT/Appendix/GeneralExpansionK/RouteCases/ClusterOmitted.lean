/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ClusterBoundary
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.OmittedBoundary

/-!
# The omitted-integrand entry point on the original cluster data

See Lemma A.7.
Near bonds and the original far families supply connectivity internally.
The returned alternatives bound the actual cut-even parity integrand.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SimpleGraph Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)}

/-- the full omitted-integrand boundary, with the quadratic gain and one global
tail or the retained long even kernel. No support or intermediate estimate
is assumed for the configuration in this entry point. -/
theorem cluster_omitted_pointwise {χ : ℂ → ℝ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) (hXne : X.Nonempty) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {n : ℕ} {lam M h : ℝ}, 0 < lam → 1 ≤ M → lam ≤ h →
      ∀ (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (Near : Finset (ℕ × ℕ))
      (hXs : ∀ l, Xs l ⊆ X) (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l)),
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      ∀ (O : Finset (Sym2 (X.biUnion id))) (hO : O ⊆ symOf (X.biUnion id) (univ.biUnion Es))
      (hcut : CutEven (Sym2.map (Limits.blockOf X)) O) (c : ℕ → ℂ × ℂ),
      let Far := univ.biUnion Es
      let hFar := cluster_far_subset hX Xs Es hXs hEs
      let hs := actual_source_odd hX hFar hO hcut
      symOf (X.biUnion id) (sourcePairs O) = O ∧
      ∃ Tb : SimpleGraph ((coarsen X (oddComponents X (sourcePairs O))).biUnion id),
        IsRelTree₀ (coarsen X (oddComponents X (sourcePairs O))) Tb ∧
        graphPairs Tb ⊆ (Near ∪ Far) \ sourcePairs O ∧
        let cfg := fun i : X.biUnion id => c i
        let Dz := symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ Far)
        let term := omittedParityIntegrand χ β lam M h (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
          (symOf (X.biUnion id) Far) O cfg
        term = 0 ∨ OmittedPointwise hX (hs.1.trans hFar) hs.2.2 lam M (17 * h) c (graphPairs Tb)
          ((Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) *
            K ^ (symOf (X.biUnion id) Far).card) *
            clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz cfg *
            omittedDensity χ β lam h (symOf (X.biUnion id) Far) cfg) term := by
  obtain ⟨K,hK,hb⟩ := baseline_omitted_pointwise_all hχ hβ hX
  refine ⟨K,hK,?_⟩
  intro n lam M h hlam hM hlh Xs Es Near hXs hEs hNear O hO hcut c
  have hFar := cluster_far_subset hX Xs Es hXs hEs
  have hs := actual_source_odd hX hFar hO hcut
  obtain ⟨Tb,hTb,hTE,ht⟩ := hb hlam hM hlh Near (univ.biUnion Es) (sourcePairs O) hFar
    (source_cluster_graph hX Xs Es Near hXs hEs hNear hXne) hs.1 hs.2.2
    (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es)) c
  refine ⟨hs.2.1,Tb,hTb,hTE,?_⟩
  simpa only [hs.2.1] using ht

end MultipoleBKT.ExpansionK.RouteCases

end
