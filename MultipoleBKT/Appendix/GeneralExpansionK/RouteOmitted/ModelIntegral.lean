/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.Average

/-!
# Original omitted integrals for the screened and frozen comparisons

See (A.51) and Lemma A.7. Both model
integrands vanish off the common short-edge domain in the comparison.
The remaining baseline term is the same. Its bound is independent of all
frozen data and supplies the area term of (A.63).
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

variable {X : Finset (Finset ℕ)}

/-- The original screened comparison on the omitted domain, after exact reversal averaging. -/
theorem screened_omitted_integral_small {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
        (Near : Finset (ℕ × ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ l, Es l ∈ relEdgeSets (Xs l)) →
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      ∀ N : ℕ,
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |omittedAverage χ β lam M (eps*truncationScale p₀ β lam)
          (Limits.blockOf X) (symOf (X.biUnion id) Near)
          (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es))
          (symOf (X.biUnion id) (univ.biUnion Es)) c|) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*N*lam^((2-β)*(X.biUnion id).card)*
          truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := averaged_omitted_integral hχ hβ hM p₀ k hk
  refine ⟨C,hC,?_⟩
  intro X hX hXne hcard eps lam hlam hle heps n Xs Es Near hXs hEs hNear N
  exact hb X hX hXne hcard eps lam hlam hle heps Near (univ.biUnion Es)
    (cluster_far_subset hX Xs Es hXs hEs)
    (source_cluster_graph hX Xs Es Near hXs hEs hNear hXne) _ N

/-- The screened omitted bound for every positive epsilon. Lambda is at most one,
as supplied by `min 1 eps` in the original minus caller. -/
theorem screened_omitted_integral {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (k : ℕ) (hk : 1 ≤ k) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
        (Near : Finset (ℕ × ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ l, Es l ∈ relEdgeSets (Xs l)) →
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      ∀ N : ℕ,
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |omittedAverage χ β lam M (eps*truncationScale p₀ β lam)
          (Limits.blockOf X) (symOf (X.biUnion id) Near)
          (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es))
          (symOf (X.biUnion id) (univ.biUnion Es)) c|) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*N*lam^((2-β)*(X.biUnion id).card)*
          truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := averaged_omitted_integral_at hχ hβ hM p₀ k hk heps
  refine ⟨C,hC,?_⟩
  intro X hX hXne hcard lam hlam hle hlam1 n Xs Es Near hXs hEs hNear N
  exact hb X hX hXne hcard lam hlam hle hlam1 Near (univ.biUnion Es)
    (cluster_far_subset hX Xs Es hXs hEs)
    (source_cluster_graph hX Xs Es Near hXs hEs hNear hXne) _ N

/-- The frozen comparison has the same omitted baseline term. Its area bound
is stronger than the full (A.63) bound, uniformly in all frozen data. -/
theorem frozen_omitted_integral {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 → 1 ≤ M →
      ∀ {N : ℕ} (V : Finset (Fin N)) (_Z : Fin N → ℂ × ℂ),
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
        (Near : Finset (ℕ × ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ l, Es l ∈ relEdgeSets (Xs l)) →
      Near ∈ relEdgeSets₀ (coarsen X (univ.image Xs)) →
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |omittedAverage χ β lam M (eps*truncationScale p₀ β lam)
          (Limits.blockOf X) (symOf (X.biUnion id) Near)
          (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es))
          (symOf (X.biUnion id) (univ.biUnion Es)) c|) ≤
        ENNReal.ofReal (lam^((2-β)*(X.biUnion id).card) *
          (C*eps^(-2:ℝ)*N*truncationScale p₀ β lam^(-2:ℝ) +
            C*eps^(alphaExponent β*(X.biUnion id).card)*V.card)) := by
  by_cases hM : 1 ≤ M
  swap
  · exact ⟨1,one_pos,fun _ _ _ _ _ _ _ _ _ hM1 => False.elim (hM hM1)⟩
  obtain ⟨C,hC,hb⟩ := screened_omitted_integral_small hχ hβ hM p₀ k hk
  refine ⟨C,hC,?_⟩
  intro X hX hXne hcard eps lam hlam hle heps _ N V Z n Xs Es Near hXs hEs hNear
  refine (hb X hX hXne hcard eps lam hlam hle heps Xs Es Near hXs hEs hNear N).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have ht := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have heps0 := hlam.trans_le hle
  have he : C*eps^(-2:ℝ)*N*lam^((2-β)*(X.biUnion id).card)*truncationScale p₀ β lam^(-2:ℝ) =
      lam^((2-β)*(X.biUnion id).card)*(C*eps^(-2:ℝ)*N*truncationScale p₀ β lam^(-2:ℝ)) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (Real.rpow_nonneg hlam.le _)

end MultipoleBKT.ExpansionK.RouteOmitted

end
