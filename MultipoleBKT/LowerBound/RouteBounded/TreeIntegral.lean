/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.HatBridge
public import MultipoleBKT.UpperBound.BoundedUpper.JMeasurable

/-!
# Integrating the separate trees using the hatted J bounds

The proof of Proposition 4.23, and Lemma A.4.
Apply Lemma A.4 to the actual separate-tree integrand, with either finite or
infinite radial cutoff.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open SetPartition MeasureTheory Finset SimpleGraph Hierarchical Multipole Parity Peeling Limits SmallIntegral
open UpperBound.BoundedUpper
open scoped Classical

/-- Every odd group admits a selection of a block of maximal radius. -/
theorem exists_hatS {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id)) (hTa : ∀ l, IsRelTree (Xs l) (Ta l)) :
    ∃ hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X,
      ∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧
        ∀ S ∈ (Xs l).subtype (· ∈ X), blockRadius hX (fun i => dipoleLength (z i)) S ≤
          blockRadius hX (fun i => dipoleLength (z i)) (hatS l z) := by
  have hex : ∀ (l : Fin n) (z : X.biUnion id → ℂ × ℂ), ∃ S : X,
      S ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S' ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i => dipoleLength (z i)) S' ≤
          blockRadius hX (fun i => dipoleLength (z i)) S := by
    intro l z
    have hne : ((Xs l).subtype (· ∈ X)).Nonempty := by
      obtain ⟨e, _⟩ := (hTa l).1.2.1
      induction e using Sym2.ind with
      | h i j =>
        obtain ⟨B, hB, _⟩ := mem_biUnion_id.1 i.2
        exact ⟨⟨B, hXs l hB⟩, mem_subtype.2 hB⟩
    obtain ⟨S, hS, hm⟩ := exists_max_image _
      (fun S => blockRadius hX (fun i => dipoleLength (z i)) S) hne
    exact ⟨S, hS, hm⟩
  choose hatS hhat using hex
  exact ⟨hatS, hhat⟩

/-- The finite radial cutoff is integrated by `Ĵ`. -/
theorem exists_hatTreeIntegral_cut_le {χ : ℂ → ℝ} (hχ : IsMollifier χ)
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
        (hatTreeCore M lam X Xs Ta Tb (extendConfig (X.biUnion id) y) *
          (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
          ∏ i, cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (y i))) ≤
        ENNReal.ofReal (C * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k)) := by
  obtain ⟨C, hC, hbound⟩ := lemma_A6_hat hχ hβ k hM hε₀ hε₁
  refine ⟨C, hC, ?_⟩
  intro X hX h2 hk n Xs hXs hdisj Ta hTa Tb hTb p₀ lam hlam hlt N
  obtain ⟨hatS, hhat⟩ := exists_hatS hX Xs hXs Ta hTa
  exact (lintegral_mono fun y => ENNReal.ofReal_le_ofReal
    (hatTreeCore_density_le_cut hlam hX Xs hXs hdisj Ta Tb hatS hhat p₀ y)).trans
    (hbound X hX h2 hk Xs hXs hdisj _
      (fun l => mem_image.2 ⟨Ta l, mem_relTrees.2 (hTa l), rfl⟩) _
      (mem_image.2 ⟨Tb, mem_relTrees₀.2 hTb, rfl⟩) hatS hhat p₀ lam hlam hlt N)

/-- The infinite radial cutoff is integrated by `Ĵ∞`, under the
paper's size condition. The coefficient is chosen before λ. -/
theorem exists_hatTreeIntegral_infinity_le {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {β M : ℝ} (hβ : 2 < β) (hM : 1 ≤ M) (k : ℕ) (hsize : (k : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)) (_hX : IsSubpartition X),
      2 ≤ X.card → (X.biUnion id).card = k →
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l m, l ≠ m → Disjoint (Xs l) (Xs m)) →
      ∀ Ta : ∀ l, SimpleGraph ((Xs l).biUnion id), (∀ l, IsRelTree (Xs l) (Ta l)) →
      ∀ Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id),
        IsRelTree₀ (coarsen X (univ.image Xs)) Tb →
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → ∀ N : ℕ,
      (∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
        (hatTreeCore M lam X Xs Ta Tb (extendConfig (X.biUnion id) y) *
          (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
          ∏ i, pairDensity χ β lam (y i))) ≤
        ENNReal.ofReal (C * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k)) := by
  obtain ⟨C, hC, hbound⟩ := lemma_A6_hat_infinity hχ hβ k hM hsize
  refine ⟨C, hC, ?_⟩
  intro X hX h2 hk n Xs hXs hdisj Ta hTa Tb hTb p₀ lam hlam N
  obtain ⟨hatS, hhat⟩ := exists_hatS hX Xs hXs Ta hTa
  exact (lintegral_mono fun y => ENNReal.ofReal_le_ofReal
    (hatTreeCore_density_le_infinity hlam hX Xs hXs hdisj Ta Tb hatS hhat y)).trans
    (hbound X hX h2 hk Xs hXs hdisj _
      (fun l => mem_image.2 ⟨Ta l, mem_relTrees.2 (hTa l), rfl⟩) _
      (mem_image.2 ⟨Tb, mem_relTrees₀.2 hTb, rfl⟩) hatS hhat p₀ lam hlam N)

end MultipoleBKT.LowerBound.RouteBounded

end
