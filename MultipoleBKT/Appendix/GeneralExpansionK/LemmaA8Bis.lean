/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.CutoffInfrastructure
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.TailAssembly

/-!
# The cutoff-only Lemma A.7 compatibility entry point

See Lemma A.7,
(A.52), (A.64) and Step 5 of the proof of Lemma A.7.
The estimate is also stated in the form used in Section 4.
The cutoff identities and Lemma A.8 estimate are in `RouteAssembly.CutoffInfrastructure`.

The exact nonempty-U₀ and parity expansion is integrated through the
case-F bound. Closed U₀ domains are replaced by strict domains only after
proving the radial boundary null. The singleton extension is separate.
-/


@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph Filter
open Hierarchical Multipole Parity Limits SmallIntegral Appendix

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Lemma A.7, eq. (A.50) -/

open scoped Classical in
/-- **Lemma A.7, eq. (A.50)**: for `β > 2`,
`k ≤ p*(β)`, `M ≥ 1` and `ε₀ > 0` there are `C > 0` and `λ₀ > 0` such that for `0 < λ ≤ λ₀`, every
`N`, every subpartition `X ≠ ∅` with `|V_X| = k`, all `Xₗ ⊆ X`, `Eₗ ∈ 𝖤^{Xₗ}` and
`F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}`: `|I^0_{cl,ε₀} - I^0_{cl,∞}| ≤ C N λ^{(2-β)k} R̄^{-2}`. -/
theorem lemma_A8_bis (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) {k : ℕ}
    (hk : (k : ℕ∞) ≤ pStar β) (hM : 1 ≤ M) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
      ∀ (N : ℕ) (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
        (X.biUnion id).card = k →
        ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
          ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
          ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
            |ExpansionErrors.zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F -
                ExpansionErrors.zeroClusterIntegralInf χ N β lam M X Xs Es F| ≤
              C * N * (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · refine ⟨1, one_pos, 1, one_pos, fun lam _ _ N X hX hXne hV => ?_⟩
    exfalso
    obtain ⟨S, hS⟩ := hXne
    obtain ⟨x, hx⟩ := hX.1 S hS
    have : x ∈ X.biUnion id := mem_biUnion.2 ⟨S, hS, hx⟩
    rw [Finset.card_eq_zero.1 hV] at this
    exact Finset.notMem_empty x this
  obtain ⟨C,hC,hbound⟩ := RouteAssembly.cluster_cutoff_bound_all hχ hβ hM p₀ k hk1 hk ε₀ hε₀
  refine ⟨C,hC,min ε₀ 1,lt_min hε₀ one_pos,?_⟩
  intro lam hlam hlam₀ N X hX hXne hV n Xs hXs Es hEs F hF
  set V := X.biUnion id
  have hEs' : ∀ l, Es l ∈ relEdgeSets (Xs l) := Fintype.mem_piFinset.1 hEs
  have hGX : ∀ Y ∈ Finset.univ.image Xs, Y ⊆ X := by
    intro Y hY
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
    exact hXs l
  have hEI : univ.biUnion Es ⊆ univ.biUnion fun l => interPairs (Xs l) := by
    intro p hp
    obtain ⟨l, -, hpl⟩ := mem_biUnion.1 hp
    exact mem_biUnion.2 ⟨l, mem_univ _, (mem_relEdgeSets.1 (hEs' l)).1 hpl⟩
  have hIX : (univ.biUnion fun l => interPairs (Xs l)) ⊆ interPairs X := by
    intro p hp
    obtain ⟨l, -, hpl⟩ := mem_biUnion.1 hp
    exact interPairs_subset_of_subset hX (hXs l) hpl
  have hI : (univ.biUnion fun l => interPairs (Xs l)) ⊆ pairsOn V :=
    hIX.trans interPairs_subset_pairsOn
  have hFV : F ⊆ pairsOn V := by
    have := (mem_relEdgeSets₀.1 hF).1.trans interPairs_subset_pairsOn
    rwa [biUnion_coarsen hGX] at this
  rw [zeroClusterIntegral_sub hχ hβ0 hlam N p₀ ε₀ hX Xs Es F hEI hI hFV, abs_neg]
  have hh := hbound lam hlam hlam₀ X hX hV F (univ.biUnion Es)
    (RouteCases.cluster_far_subset hX Xs Es hXs hEs')
    (RouteCases.source_cluster_graph hX Xs Es F hXs hEs' hF hXne)
    (symOf V ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es)) N
  have he : (fun c : V → ℂ × ℂ => clusterBox χ β lam M (Limits.blockOf X)
        (symOf V F) (symOf V ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es))
        (symOf V (univ.biUnion Es)) c * (1-cutInd (ε₀*truncationScale p₀ β lam) c)) =
      fun c => -(clusterBox χ β lam M (Limits.blockOf X) (symOf V F)
        (symOf V ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es))
        (symOf V (univ.biUnion Es)) c * (cutInd (ε₀*truncationScale p₀ β lam) c-1)) := by
    funext c
    ring
  rw [he,integral_neg,abs_neg]
  exact hh.trans_eq (by ring)

/-- **Lemma A.7, eq. (A.50)** in the form
`MultipoleBKT.ExpansionErrors.LemmaA8BisStatement` used by Proposition 4.24 (for `M ≥ 1`). -/
theorem lemmaA8Bis_holds (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ}
    (hk : (k : ℕ∞) ≤ pStar β) : ExpansionErrors.LemmaA8BisStatement χ β M p₀ k := by
  intro ε₀ hε₀ _
  obtain ⟨C, hC, lam₀, hlam₀, hA⟩ := lemma_A8_bis hχ hβ p₀ hk hM hε₀
  refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => ⟨0, fun N _ X hX _ hX2 hV n Xs hXs _ Es hEs F
    hF => ?_⟩⟩
  have hXne : X.Nonempty := Finset.card_pos.1 (by omega)
  exact hA lam hlam hlt.le N X hX hXne hV n Xs hXs Es hEs F hF

end ExpansionK

end MultipoleBKT

end
