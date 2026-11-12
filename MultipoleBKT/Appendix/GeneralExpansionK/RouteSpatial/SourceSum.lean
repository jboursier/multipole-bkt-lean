/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.FiniteFamilies

/-!
# A fixed finite spatial sum for every actual mixed summand

See Lemma A.7. Both model bounds keep the complete
support and density. The coarse even tree, component trees, component roots,
root gain and even mark are summed before integration.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits RouteCases
open SmallIntegral UpperBound.BoundedUpper
open scoped Classical

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- Sum over the coarse even trees and the separate odd-tree choices.
All original near, far, short and radial support factors are retained. -/
noncomputable def sourceSpatialSum (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (χ : ℂ → ℝ) (β lam M h : ℝ)
    (τ v : ℂ × ℂ → ℝ) (Near Far : Finset (ℕ × ℕ))
    (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ) : ℝ :=
  clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
      (fun i : X.biUnion id => c i) *
    mixedDensity χ β lam h (symOf (X.biUnion id) Far) (fun i : X.biUnion id => c i) *
    ∑ Tb ∈ (univ : Finset (SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))).filter
        (IsRelTree₀ (coarsen X (oddComponents X O))),
      paperSpatialSum hX hOX hpar (fun i => rhoD lam (c i)) (paperDistE c) (farInd M lam c)
        (fun i => τ (c i)) (fun i => v (c i))
        (paperEvenE M lam (fun i : X.biUnion id => c i))
        (markedEvenE lam (fun i : X.biUnion id => c i))
        (symOf (X.biUnion id) (graphPairs Tb)) (maxRad lam (fun i : X.biUnion id => c i))

/-- The fixed finite spatial sum is nonnegative on its full carrier. -/
theorem sourceSpatialSum_nonneg (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (χ : ℂ → ℝ) (β lam M h : ℝ)
    (τ v : ℂ × ℂ → ℝ) (Near Far : Finset (ℕ × ℕ))
    (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ) :
    0 ≤ sourceSpatialSum hX hOX hpar χ β lam M h τ v Near Far Dz c := by
  unfold sourceSpatialSum
  exact mul_nonneg (mul_nonneg (clusterSupport_nonneg _ _ _ _ _ _)
    (mixedDensity_nonneg _ _ _ _ _ _)) (sum_nonneg fun Tb _ =>
      paperSpatialSum_nonneg _ _ _ _ _ _ _ _ _ _ _ _
        (fun e => farInd_nonneg c e) (paperEvenE_nonneg M lam _) (markedEvenE_nonneg lam _))

/-- Internal conversion of the complete pointwise bound into a fixed finite sum.
The concrete model theorems below supply the boundary themselves. -/
theorem internal_mixedBoundary_le_sum {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {χ : ℂ → ℝ} {β lam M h K W : ℝ}
    {w : ℂ × ℂ → ℂ × ℂ → ℝ} {τ u v : ℂ × ℂ → ℝ}
    {Near Far : Finset (ℕ × ℕ)} {Dz : Finset (Sym2 (X.biUnion id))} {c : ℕ → ℂ × ℂ}
    (H : MixedBoundary hX hOX hpar χ β lam M h K W w τ u v Near Far Dz c)
    (hK : 0 ≤ K) (hW : 0 ≤ W)
    (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id))
    (hne : P ≠ (∅,∅,∅,∅,∅))
    (hP : P ∈ fiveSubsets (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) (RouteCases.intraEdges (Limits.blockOf X)) univ) :
    |mixedIntegrand χ β lam M h w u v (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
      (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) (fun i : X.biUnion id => c i) P| ≤
      (W ^ ((X.biUnion id).card * (X.biUnion id).card) *
        K ^ factorCount (symOf (X.biUnion id) O)
          (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) P) *
        sourceSpatialSum hX hOX hpar χ β lam M h τ v Near Far Dz c := by
  obtain ⟨Tb,hTb,-,hb⟩ := H
  let A := W ^ ((X.biUnion id).card * (X.biUnion id).card) *
    K ^ factorCount (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) P
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg hW _) (pow_nonneg hK _)
  have hs0 := clusterSupport_nonneg M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
    (fun i : X.biUnion id => c i)
  have hd0 := mixedDensity_nonneg χ β lam h (symOf (X.biUnion id) Far) (fun i : X.biUnion id => c i)
  rcases hb P hne hP with hz | H
  · rw [hz,abs_zero]
    exact mul_nonneg hA (sourceSpatialSum_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  · have hC : 0 ≤ A * clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
        (fun i : X.biUnion id => c i) * mixedDensity χ β lam h (symOf (X.biUnion id) Far)
        (fun i : X.biUnion id => c i) := mul_nonneg (mul_nonneg hA hs0) hd0
    have hp := internal_paperPointwise_le_sum H hC (fun e => farInd_nonneg c e)
      (paperEvenE_nonneg M lam _) (markedEvenE_nonneg lam _)
    refine hp.trans ?_
    unfold sourceSpatialSum
    have hh := single_le_sum
      (f := fun Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id) =>
        paperSpatialSum hX hOX hpar (fun i => rhoD lam (c i)) (paperDistE c) (farInd M lam c)
          (fun i => τ (c i)) (fun i => v (c i))
          (paperEvenE M lam (fun i : X.biUnion id => c i))
          (markedEvenE lam (fun i : X.biUnion id => c i))
          (symOf (X.biUnion id) (graphPairs Tb)) (maxRad lam (fun i : X.biUnion id => c i)))
      (fun Tb _ => paperSpatialSum_nonneg _ _ _ _ _ _ _ _ _ _ _ _
        (fun e => farInd_nonneg c e) (paperEvenE_nonneg M lam _) (markedEvenE_nonneg lam _))
      (mem_filter.2 ⟨mem_univ Tb,hTb⟩)
    calc
      _ ≤ (A * clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
          (fun i : X.biUnion id => c i) * mixedDensity χ β lam h (symOf (X.biUnion id) Far)
          (fun i : X.biUnion id => c i)) * _ := mul_le_mul_of_nonneg_left hh hC
      _ = _ := by dsimp only [A]; ring

/-- Every actual frozen-model mixed summand is below the fixed finite
tree sum. The coefficient is fixed before lambda and the frozen data. -/
theorem frozen_mixed_source_sum {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) (hXne : X.Nonempty) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {N p₀ n : ℕ} {lam M ε₀ h : ℝ}
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → 1 ≤ M →
      ∀ (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (Near : Finset (ℕ × ℕ))
      (hXs : ∀ l, Xs l ⊆ X) (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l)),
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      ∀ (O : Finset (Sym2 (X.biUnion id))) (hO : O ⊆ symOf (X.biUnion id) (univ.biUnion Es))
      (hcut : CutEven (Sym2.map (Limits.blockOf X)) O) (c : ℕ → ℂ × ℂ),
      let Far := univ.biUnion Es
      let hs := actual_source_odd hX (cluster_far_subset hX Xs Es hXs hEs) hO hcut
      let Dz := symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ Far)
      ∀ P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id),
      P ≠ (∅,∅,∅,∅,∅) → P ∈ fiveSubsets (symOf (X.biUnion id) (sourcePairs O))
        (symOf (X.biUnion id) Far \ symOf (X.biUnion id) (sourcePairs O))
        (RouteCases.intraEdges (Limits.blockOf X)) univ →
      |mixedIntegrand χ β lam M h (routeFrozenInteraction χ p₀ β lam ε₀ V Z)
          (routeFrozenQuadratic p₀ β lam ε₀ L V Z) (routeFrozenBad p₀ β lam M ε₀ V Z)
          (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far)
          (symOf (X.biUnion id) (sourcePairs O)) (fun i : X.biUnion id => c i) P| ≤
        (Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) *
          K ^ factorCount (symOf (X.biUnion id) (sourcePairs O))
            (symOf (X.biUnion id) Far \ symOf (X.biUnion id) (sourcePairs O)) P) *
          sourceSpatialSum hX (hs.1.trans (cluster_far_subset hX Xs Es hXs hEs)) hs.2.2 χ β lam M h
            (routeFrozenRadius p₀ β lam ε₀ V Z) (routeFrozenBad p₀ β lam M ε₀ V Z) Near Far Dz c := by
  obtain ⟨K,hK,hb⟩ := cluster_frozen_mixed_pointwise (L := L) hχ hβ hX hXne
  refine ⟨K,hK,?_⟩
  intro N p₀ n lam M ε₀ h V Z hlam hM Xs Es Near hXs hEs hNear O hO hcut c
  obtain ⟨-,H⟩ := hb (h := h) V Z hlam hM Xs Es Near hXs hEs hNear O hO hcut c
  dsimp only
  intro P hne hP
  exact internal_mixedBoundary_le_sum H (zero_le_one.trans hK) (Real.exp_nonneg _) P hne hP

/-- Every actual screened-model mixed summand has the same fixed finite
tree majorant, with its constant screening radius and zero bad factor. -/
theorem screened_mixed_source_sum {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) (hXne : X.Nonempty) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {n : ℕ} {lam M ε₀ R : ℝ}, 0 < lam → 1 ≤ M → lam ≤ ε₀ * R →
      ∀ (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (Near : Finset (ℕ × ℕ))
      (hXs : ∀ l, Xs l ⊆ X) (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l)),
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      ∀ (O : Finset (Sym2 (X.biUnion id))) (hO : O ⊆ symOf (X.biUnion id) (univ.biUnion Es))
      (hcut : CutEven (Sym2.map (Limits.blockOf X)) O) (c : ℕ → ℂ × ℂ),
      let Far := univ.biUnion Es
      let hs := actual_source_odd hX (cluster_far_subset hX Xs Es hXs hEs) hO hcut
      let Dz := symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ Far)
      ∀ P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id),
      P ≠ (∅,∅,∅,∅,∅) → P ∈ fiveSubsets (symOf (X.biUnion id) (sourcePairs O))
        (symOf (X.biUnion id) Far \ symOf (X.biUnion id) (sourcePairs O))
        (RouteCases.intraEdges (Limits.blockOf X)) univ →
      |mixedIntegrand χ β lam M (ε₀ * R) (upperBoundInteraction χ lam ε₀ R)
          (fun d => Real.exp (-L * (‖d.1-d.2‖ / (ε₀ * R)) ^ 2) - 1) (fun _ => 0)
          (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far)
          (symOf (X.biUnion id) (sourcePairs O)) (fun i : X.biUnion id => c i) P| ≤
        (Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) *
          K ^ factorCount (symOf (X.biUnion id) (sourcePairs O))
            (symOf (X.biUnion id) Far \ symOf (X.biUnion id) (sourcePairs O)) P) *
          sourceSpatialSum hX (hs.1.trans (cluster_far_subset hX Xs Es hXs hEs)) hs.2.2 χ β lam M (ε₀ * R)
            (fun _ => ε₀ * R) (fun _ => 0) Near Far Dz c := by
  obtain ⟨K,hK,hb⟩ := cluster_screened_mixed_pointwise (L := L) hχ hβ hX hXne
  refine ⟨K,hK,?_⟩
  intro n lam M ε₀ R hlam hM hlh Xs Es Near hXs hEs hNear O hO hcut c
  obtain ⟨-,H⟩ := hb hlam hM hlh Xs Es Near hXs hEs hNear O hO hcut c
  dsimp only
  intro P hne hP
  exact internal_mixedBoundary_le_sum H (zero_le_one.trans hK) (Real.exp_nonneg _) P hne hP

end MultipoleBKT.ExpansionK.RouteSpatial

end
