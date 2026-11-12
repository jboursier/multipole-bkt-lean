/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.FrozenSupport
public import MultipoleBKT.UpperBound.ExpansionPlus.Inputs
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.OmittedSupport

/-!
# Lemma A.7 for the model with frozen bad points

See Lemma A.7,
(A.51), (A.63) and Step 5 of the proof of Lemma A.7.
Split the support D. On D the exact parity and five-subset expansion is
integrated through the cases A–E and the logarithmic bounds. Both error
coefficients are fixed before epsilon and the frozen data.

The omitted baseline is integrated with its quadratic long-edge gain.
The estimate is also stated in the form used in Section 5.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset Metric SimpleGraph Filter
open scoped ENNReal
open TwoComponentCoulomb (box)
open Hierarchical Multipole Parity Limits SmallIntegral UpperBound BoundedUpper MultipoleIntegralZ
  Appendix

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Lemma A.7 for the model `(v^Z, τ^Z)` -/

open scoped Classical in
/-- **Lemma A.7, eq. (A.49)** for
`(w, τ) = (v^Z, τ^Z)`. -/
theorem lemma_A8_plus (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) {k : ℕ}
    (hk : (k : ℕ∞) ≤ pStar β) (M L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ (N : ℕ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → X.Nonempty → (X.biUnion id).card = k →
        ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
          ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
          ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
            |ExpansionPlus.plusClusterIntegral χ N p₀ β lam M ε₀ L V Z X Xs Es F -
                ExpansionErrors.zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F| ≤
              lam ^ ((2 - β) * k) * (Cε * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * V.card) := by
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · refine ⟨1, one_pos, fun ε₀ _ _ => ⟨1, one_pos, 1, one_pos,
      fun lam _ _ _ N V Z _ X hX hXne hV => ?_⟩⟩
    exfalso
    obtain ⟨S, hS⟩ := hXne
    obtain ⟨x, hx⟩ := hX.1 S hS
    have : x ∈ X.biUnion id := mem_biUnion.2 ⟨S, hS, hx⟩
    rw [Finset.card_eq_zero.1 hV] at this
    exact Finset.notMem_empty x this
  obtain ⟨A,hA,hAint⟩ := RouteAssembly.frozen_support_integral (β := β) (L := L) (M := M)
    hχ hβ p₀ k hk1
  obtain ⟨Co, hCo, ho⟩ := RouteOmitted.frozen_omitted_integral (M := M) hχ hβ p₀ k hk1
  refine ⟨A + Co, by positivity, fun ε₀ hε₀ hε1 => ?_⟩
  let Cgood := (A + Co) * ε₀^(-2 : ℝ)
  have hCgood : 0 ≤ Cgood := by positivity
  refine ⟨Cgood+1,by linarith,ε₀,hε₀,fun lam hlam hlε hM3 N V Z hVZ X hX hXne hV n Xs hXs
    Es hEs F hF => ?_⟩
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM3
  have hlam1 : lam ≤ 1 := hlε.trans hε1
  have hR1 := one_le_truncationScale (p₀ := p₀) hβ hlam hlam1
  set R := truncationScale p₀ β lam
  set h := ε₀ * R
  have hlh : lam ≤ h := hlε.trans (le_mul_of_one_le_right hε₀.le hR1)
  have hh0 : 0 < h := hlam.trans_le hlh
  -- the data on the labels
  set Vl := X.biUnion id
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
  have hI : (univ.biUnion fun l => interPairs (Xs l)) ⊆ pairsOn Vl :=
    hIX.trans interPairs_subset_pairsOn
  have hFV : F ⊆ pairsOn Vl := by
    have := (mem_relEdgeSets₀.1 hF).1.trans interPairs_subset_pairsOn
    rwa [biUnion_coarsen hGX] at this
  have hcardV : Fintype.card Vl = k := by rw [Fintype.card_coe, hV]
  have : Nonempty Vl := by
    rw [← Fintype.card_pos_iff, hcardV]
    exact hk1
  set blk := Limits.blockOf X
  set Dn := symOf Vl F
  set Dz := symOf Vl ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es)
  set Df := symOf Vl (univ.biUnion Es)
  have hI1 : ExpansionPlus.plusClusterIntegral χ N p₀ β lam M ε₀ L V Z X Xs Es F =
      ∫ y in boxConfig Vl N, clusterQ β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam blk Dn Dz Df y *
        ((∏ i, pairDensity χ β lam (y i)) * cutInd (ε₀ * truncationScale p₀ β lam) y) := by
    unfold ExpansionPlus.plusClusterIntegral ExpansionErrors.clusterIntegral
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [integrand_eq_clusterQ hX Xs Es F hEI hI hFV y, prod_cutoffWeight]
  have hI0 : ExpansionErrors.zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F =
      ∫ y in boxConfig Vl N, clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df y *
        ((∏ i, pairDensity χ β lam (y i)) * cutInd (ε₀ * truncationScale p₀ β lam) y) := by
    unfold ExpansionErrors.zeroClusterIntegral ExpansionErrors.clusterIntegral
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [integrand_eq_clusterQ hX Xs Es F hEI hI hFV y, prod_cutoffWeight]
  have hsp := plus_split (L := L) (N := N) hχ hβ0 hlam hM1 hlh hM3 hVZ blk Dn Dz Df
  have hFar := RouteCases.cluster_far_subset hX Xs Es hXs hEs'
  have hgraph := RouteCases.source_cluster_graph hX Xs Es F hXs hEs' hF hXne
  have hpI := hAint ε₀ lam hlam hlε hε1 hM3 X hX hXne hV V Z hVZ F (univ.biUnion Es)
    hFar hgraph Dz
  have hII : |∫ y in boxConfig Vl N, clusterQ β (dipoleInteraction χ lam) (fun _ => 1)
      M lam blk Dn Dz Df y * (((∏ i, pairDensity χ β lam (y i)) * cutInd h y) *
        (1-shortInd (17*h) Df y))| ≤
      lam^((2-β)*k)*(Co*ε₀^(-2 : ℝ)*N*R^(-2 : ℝ)+Co*ε₀^(alphaExponent β*k)*V.card) := by
    apply RouteAssembly.internal_abs_integral_omitted_le hχ hβ0 hlam blk Dn Dz Df h
    · positivity
    · simpa only [Vl, R, h, blk, Dn, Dz, Df, hV] using ho X hX hXne hV ε₀ lam hlam hlε hε1 hM1
        V Z Xs Es F hXs hEs' hF
  rw [hI1,hI0,hsp]
  refine (abs_sub _ _).trans ((add_le_add hpI hII).trans ?_)
  have hlp := Real.rpow_nonneg hlam.le ((2-β)*k)
  have hrp := Real.rpow_nonneg (truncationScale_pos (p₀ := p₀) (β := β) hlam).le (-2 : ℝ)
  calc
    _ = lam^((2-β)*k)*(Cgood*N*R^(-2 : ℝ)+(A+Co)*ε₀^(alphaExponent β*k)*V.card) := by
      dsimp only [Cgood]
      ring
    _ ≤ _ := by gcongr; linarith

/-- **Lemma A.7, eq. (A.49), for the model with frozen bad points**, in the form
`MultipoleBKT.UpperBound.ExpansionPlus.LemmaA8PlusStatement` used by Proposition 5.19. -/
theorem lemmaA8Plus_holds (hχ : IsMollifier χ) (hβ : 2 < β) (M L : ℝ) (p₀ : ℕ) {k : ℕ}
    (hk : (k : ℕ∞) ≤ pStar β) : ExpansionPlus.LemmaA8PlusStatement χ β M L p₀ k := by
  obtain ⟨C, hC, hA⟩ := lemma_A8_plus hχ hβ p₀ hk M L
  refine ⟨C, hC, fun ε₀ hε₀ hε1 => ?_⟩
  obtain ⟨Cε, hCε, lam₀, hlam₀, hB⟩ := hA ε₀ hε₀ hε1.le
  refine ⟨Cε, hCε, lam₀, hlam₀, fun lam hlam hlt => ⟨0, fun N _ hM3 V Z hV X hX _ hX2 hk' n Xs
    hXs _ Es hEs F hF => ?_⟩⟩
  have hXne : X.Nonempty := Finset.card_pos.1 (by omega)
  exact hB lam hlam hlt.le hM3 N V Z hV X hX hXne hk' n Xs hXs Es hEs F hF

end ExpansionK

end MultipoleBKT

end
