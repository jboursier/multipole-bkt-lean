/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.SourceEnvelope

/-!
# The original omitted-domain integral for both models

See Lemma A.7 and (A.51). On the omitted
domain both model comparisons leave the same baseline parity integrand.
Its bound has its coefficient before epsilon, lambda, volume and frozen data.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

variable {X : Finset (Finset ℕ)}

/-- The actual omitted parity integral on the original near and far families.
The coefficient depends only on the fixed model parameters and label count. -/
theorem omitted_integral {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (_hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → O ⊆ Far → IsParityPair X O ∅ →
      ∀ (Dz : Finset (Sym2 (X.biUnion id))) (n : ℕ),
      (∫⁻ c in boxConfig (X.biUnion id) n,
        ENNReal.ofReal |omittedParityIntegrand χ β lam M (eps*truncationScale p₀ β lam)
          (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
          (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) c|) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*n*lam^((2-β)*(X.biUnion id).card)*
          truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨Q,hQ,hpoint⟩ := omitted_source_envelope hχ (by linarith : 0 ≤ β) k
  obtain ⟨A,hA,hint⟩ := omittedEnvelope_bound hχ hβ hM p₀ hk
  refine ⟨Q*A,mul_pos hQ hA,?_⟩
  intro X hX hXne hcard
  have hnX : Nonempty (X.biUnion id) := by
    obtain ⟨S,hS⟩ := hXne
    obtain ⟨i,hi⟩ := hX.1 S hS
    exact ⟨⟨i,mem_biUnion.2 ⟨S,hS,hi⟩⟩⟩
  intro eps lam hlam hle heps Near Far O hFar hconn hOF hpar Dz n
  let h := eps*truncationScale p₀ β lam
  have heps0 : 0 < eps := hlam.trans_le hle
  have hlh : lam ≤ h := hle.trans (le_mul_of_one_le_right heps0.le
    (Appendix.one_le_truncationScale hβ hlam (hle.trans heps)))
  have hp := hpoint X hX hcard hlam hM hlh Near Far O hFar hconn hOF hpar Dz
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) n, ENNReal.ofReal Q * omittedEnvelope χ β M lam h c :=
      lintegral_mono hp
    _ = ENNReal.ofReal Q * ∫⁻ c in boxConfig (X.biUnion id) n, omittedEnvelope χ β M lam h c :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Q * ENNReal.ofReal (A*eps^(-2:ℝ)*n*lam^((2-β)*(X.biUnion id).card)*
        truncationScale p₀ β lam^(-2:ℝ)) :=
      mul_le_mul' le_rfl (by simpa only [hcard] using hint eps lam hlam hle heps (X.biUnion id) (by rw [Fintype.card_coe,hcard]) n)
    _ = _ := by rw [← ENNReal.ofReal_mul hQ.le]; congr 1; ring

/-- The omitted-domain bound at the original cluster data, common to the
screened and frozen comparisons. No analytic estimate is a hypothesis. -/
theorem cluster_omitted_integral {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
        (Near : Finset (ℕ × ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ l, Es l ∈ relEdgeSets (Xs l)) →
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      ∀ (O : Finset (Sym2 (X.biUnion id))), O ⊆ symOf (X.biUnion id) (univ.biUnion Es) →
      CutEven (Sym2.map (Limits.blockOf X)) O → ∀ N : ℕ,
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |omittedParityIntegrand χ β lam M (eps*truncationScale p₀ β lam)
          (Limits.blockOf X) (symOf (X.biUnion id) Near)
          (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es))
          (symOf (X.biUnion id) (univ.biUnion Es)) O c|) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*N*lam^((2-β)*(X.biUnion id).card)*
          truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := omitted_integral hχ hβ hM p₀ k hk
  refine ⟨C,hC,?_⟩
  intro X hX hXne hcard eps lam hlam hle heps n Xs Es Near hXs hEs hNear O hO hcut N
  have hFar := cluster_far_subset hX Xs Es hXs hEs
  have hs := actual_source_odd hX hFar hO hcut
  have hi := hb X hX hXne hcard eps lam hlam hle heps Near (univ.biUnion Es) (sourcePairs O) hFar
    (source_cluster_graph hX Xs Es Near hXs hEs hNear hXne) hs.1 hs.2.2
    (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es)) N
  simpa only [hs.2.1] using hi

/-- Original parity terms for every positive epsilon, uniformly in `X`. -/
theorem omitted_integral_at {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (k : ℕ) (hk : 1 ≤ k) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (_hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → O ⊆ Far → IsParityPair X O ∅ →
      ∀ (Dz : Finset (Sym2 (X.biUnion id))) (n : ℕ),
      (∫⁻ c in boxConfig (X.biUnion id) n,
        ENNReal.ofReal |omittedParityIntegrand χ β lam M (eps*truncationScale p₀ β lam)
          (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
          (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) c|) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*n*lam^((2-β)*(X.biUnion id).card)*
          truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨Q,hQ,hpoint⟩ := omitted_source_envelope hχ (by linarith : 0 ≤ β) k
  obtain ⟨A,hA,hint⟩ := omittedEnvelope_bound_at hχ hβ hM p₀ hk heps
  refine ⟨Q*A,mul_pos hQ hA,?_⟩
  intro X hX hXne hcard
  have hnX : Nonempty (X.biUnion id) := by
    obtain ⟨S,hS⟩ := hXne
    obtain ⟨i,hi⟩ := hX.1 S hS
    exact ⟨⟨i,mem_biUnion.2 ⟨S,hS,hi⟩⟩⟩
  intro lam hlam hle hlam1 Near Far O hFar hconn hOF hpar Dz n
  let h := eps*truncationScale p₀ β lam
  have heps0 : 0 < eps := hlam.trans_le hle
  have hlh : lam ≤ h := hle.trans (le_mul_of_one_le_right heps0.le
    (Appendix.one_le_truncationScale hβ hlam hlam1))
  have hp := hpoint X hX hcard hlam hM hlh Near Far O hFar hconn hOF hpar Dz
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) n, ENNReal.ofReal Q * omittedEnvelope χ β M lam h c :=
      lintegral_mono hp
    _ = ENNReal.ofReal Q * ∫⁻ c in boxConfig (X.biUnion id) n, omittedEnvelope χ β M lam h c :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Q * ENNReal.ofReal (A*eps^(-2:ℝ)*n*lam^((2-β)*(X.biUnion id).card)*
        truncationScale p₀ β lam^(-2:ℝ)) :=
      mul_le_mul' le_rfl (by simpa only [hcard] using hint lam hlam hle hlam1 (X.biUnion id) (by rw [Fintype.card_coe,hcard]) n)
    _ = _ := by rw [← ENNReal.ofReal_mul hQ.le]; congr 1; ring

/-- The omitted-domain bound at the original cluster data, common to the
screened and frozen comparisons. No analytic estimate is a hypothesis. -/
theorem cluster_omitted_integral_at {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (k : ℕ) (hk : 1 ≤ k) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
        (Near : Finset (ℕ × ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ l, Es l ∈ relEdgeSets (Xs l)) →
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      ∀ (O : Finset (Sym2 (X.biUnion id))), O ⊆ symOf (X.biUnion id) (univ.biUnion Es) →
      CutEven (Sym2.map (Limits.blockOf X)) O → ∀ N : ℕ,
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |omittedParityIntegrand χ β lam M (eps*truncationScale p₀ β lam)
          (Limits.blockOf X) (symOf (X.biUnion id) Near)
          (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es))
          (symOf (X.biUnion id) (univ.biUnion Es)) O c|) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*N*lam^((2-β)*(X.biUnion id).card)*
          truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := omitted_integral_at hχ hβ hM p₀ k hk heps
  refine ⟨C,hC,?_⟩
  intro X hX hXne hcard lam hlam hle hlam1 n Xs Es Near hXs hEs hNear O hO hcut N
  have hFar := cluster_far_subset hX Xs Es hXs hEs
  have hs := actual_source_odd hX hFar hO hcut
  have hi := hb X hX hXne hcard lam hlam hle hlam1 Near (univ.biUnion Es) (sourcePairs O) hFar
    (source_cluster_graph hX Xs Es Near hXs hEs hNear hXne) hs.1 hs.2.2
    (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es)) N
  simpa only [hs.2.1] using hi

end MultipoleBKT.ExpansionK.RouteOmitted

end
