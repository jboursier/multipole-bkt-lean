/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.ClusterIntegral

/-!
# Lower infrastructure for the two cutoff comparisons

See (A.52)
and Lemma A.8. The cutoff product and
integral difference identities belong below the model expansions.
The unconditional Lemma A.8 estimate is included at this level.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph Filter
open Hierarchical Multipole Parity Limits SmallIntegral Appendix

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### The cutoff weight -/

section CutWeight

variable {ι : Type*} [Fintype ι]

open scoped Classical in
theorem prod_cutoffWeight (h : ℝ) (c : ι → ℂ × ℂ) :
    ∏ i, ExpansionErrors.cutoffWeight χ β lam h (c i) =
      (∏ i, pairDensity χ β lam (c i)) * cutInd h c := by
  unfold cutInd
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  unfold ExpansionErrors.cutoffWeight pairDensity
  congr 1
  by_cases hm : ‖(c i).1 - (c i).2‖ ≤ h
  · rw [indicator_of_mem (by rwa [Metric.mem_closedBall, dist_zero_right]), ite_eq_left hm,
      Pi.one_apply]
  · rw [indicator_of_notMem (by rwa [Metric.mem_closedBall, dist_zero_right]), ite_eq_right hm]

end CutWeight

/-! ### Lemma A.8 in the form of Proposition 4.24 -/

open scoped Classical in
theorem dipoleIntegralCut_eq (N p₀ : ℕ) (ε₀ : ℝ) (V : Finset ℕ) (E : SimpleGraph V) :
    ExpansionErrors.dipoleIntegralCut χ N p₀ β lam ε₀ V E =
      dipoleIntegralCut χ N p₀ β lam ε₀ V E := by
  unfold ExpansionErrors.dipoleIntegralCut dipoleIntegralCut
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only
  rw [prod_cutoffWeight, mul_assoc]

/-- **Lemma A.8** in the form `MultipoleBKT.ExpansionErrors.LemmaI3Statement` used by
Proposition 4.24. -/
theorem lemmaI3_holds (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) {k : ℕ}
    (hk : (k : ℕ∞) ≤ pStar β) : ExpansionErrors.LemmaI3Statement χ β p₀ k := by
  intro ε₀ hε₀ _
  obtain ⟨C, hC, lam₀, hlam₀, hI3⟩ := lemma_I3 hχ hβ p₀ hk hε₀
  refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => ⟨0, fun N _ V _ hV => ?_⟩⟩
  simp_rw [dipoleIntegralCut_eq]
  exact (hI3 lam hlam hlt.le N V hV).trans_eq (by ring)

/-! ### The cutoff difference of a cluster integral -/

open scoped Classical in
/-- `I^0_{cl,ε₀} - I^0_{cl,∞} = -∫ clusterBox (1 - ∏_i 𝟙_{r_i ≤ ε₀ R̄})`. -/
theorem zeroClusterIntegral_sub (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam)
    (N p₀ : ℕ) (ε₀ : ℝ) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ))
    (hEI : univ.biUnion Es ⊆ univ.biUnion fun l => interPairs (Xs l))
    (hI : (univ.biUnion fun l => interPairs (Xs l)) ⊆ pairsOn (X.biUnion id))
    (hF : F ⊆ pairsOn (X.biUnion id)) :
    ExpansionErrors.zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F -
        ExpansionErrors.zeroClusterIntegralInf χ N β lam M X Xs Es F =
      -∫ y in boxConfig (X.biUnion id) N,
        clusterBox χ β lam M (Limits.blockOf X) (symOf (X.biUnion id) F)
          (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es))
          (symOf (X.biUnion id) (univ.biUnion Es)) y *
          (1 - cutInd (ε₀ * truncationScale p₀ β lam) y) := by
  set V := X.biUnion id
  set h := ε₀ * truncationScale p₀ β lam
  set Dn := symOf V F
  set Dz := symOf V ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es)
  set Df := symOf V (univ.biUnion Es)
  have hpt : ∀ y : V → ℂ × ℂ,
      (∏ S ∈ X, blockWeightOf β (dipoleInteraction χ lam) (fun _ => 1) M lam S
        (extendConfig V y)) *
        clusterTerm β (dipoleInteraction χ lam) M lam Xs Es F (extendConfig V y) *
        ∏ i, pairDensity χ β lam (y i) =
      clusterBox χ β lam M (Limits.blockOf X) Dn Dz Df y := by
    intro y
    rw [prod_blockWeightOf_extendConfig_eq hX y, clusterTerm_extendConfig_eq Xs Es F hEI hI hF y]
    unfold clusterBox
    ring
  obtain ⟨B, hB⟩ := exists_abs_clusterBox_le (M := M) hχ hβ0 hlam (Limits.blockOf X) Dn Dz Df
  have hmeas := measurable_clusterBox (β := β) (M := M) hχ hlam (Limits.blockOf X) Dn Dz Df
  have hint1 : IntegrableOn (fun y => clusterBox χ β lam M (Limits.blockOf X) Dn Dz Df y *
      cutInd h y) (boxConfig V N) := by
    refine integrableOn_boxConfig_of_bounded
      (F := fun y => clusterBox χ β lam M (Limits.blockOf X) Dn Dz Df y * cutInd h y)
      (hmeas.mul (measurable_cutInd h)) (B := B) (fun y => ?_) N
    rw [abs_mul, abs_of_nonneg (cutInd_nonneg h y)]
    exact (mul_le_mul (hB y) (cutInd_le_one h y) (cutInd_nonneg h y)
      ((abs_nonneg _).trans (hB y))).trans_eq (mul_one B)
  have hint2 : IntegrableOn (clusterBox χ β lam M (Limits.blockOf X) Dn Dz Df) (boxConfig V N) :=
    integrableOn_boxConfig_of_bounded (F := clusterBox χ β lam M (Limits.blockOf X) Dn Dz Df)
      hmeas hB N
  have h1 : ExpansionErrors.zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F =
      ∫ y in boxConfig V N, clusterBox χ β lam M (Limits.blockOf X) Dn Dz Df y * cutInd h y := by
    unfold ExpansionErrors.zeroClusterIntegral ExpansionErrors.clusterIntegral
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [prod_cutoffWeight, ← mul_assoc, hpt]
  have h2 : ExpansionErrors.zeroClusterIntegralInf χ N β lam M X Xs Es F =
      ∫ y in boxConfig V N, clusterBox χ β lam M (Limits.blockOf X) Dn Dz Df y := by
    unfold ExpansionErrors.zeroClusterIntegralInf ExpansionErrors.clusterIntegral
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact hpt y
  rw [h1, h2, ← integral_sub hint1 hint2, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

end ExpansionK

end MultipoleBKT

end
