/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.FrozenSum
public import MultipoleBKT.Appendix.GeneralExpansionK.ZParts

/-!
# The frozen-model error on the written support

See (A.51),
(A.63) and Step 5 of the proof of Lemma A.7.
The reversal average gives the exact five-subset sum. Its original
mixed integrals are bounded by the cases and the logarithmic integration.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset SimpleGraph Limits Hierarchical Multipole Parity SmallIntegral
open UpperBound BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

/-- Cases A–E assembled for the actual frozen-model difference on D. -/
theorem frozen_support_integral {χ : ℂ → ℝ} {β L M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      (3 : ℝ)^pBeta p₀ β ≤ M → ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      badPointsOn p₀ β lam M eps V Z = V →
      ∀ (Near Far : Finset (ℕ × ℕ)), Far ⊆ interPairs X → Near ∪ Far ∈ relEdgeSets₀ X →
      ∀ Dz : Finset (Sym2 (X.biUnion id)),
      |∫ c in boxConfig (X.biUnion id) N,
        (clusterQ β (interactionGoodZ χ p₀ β lam eps V Z) (dipoleWeightZ p₀ β lam M eps L V Z)
            M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c -
          clusterQ β (dipoleInteraction χ lam) (fun _ => 1)
            M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c) *
          mixedDensity χ β lam (eps*truncationScale p₀ β lam) (symOf (X.biUnion id) Far) c| ≤
        lam^((2-β)*k)*(C*eps^(-2 : ℝ)*N*truncationScale p₀ β lam^(-2 : ℝ)+
          C*eps^(alphaExponent β*k)*V.card) := by
  obtain ⟨C,hC,hbound⟩ := frozen_mixed_sum_bound (β := β) (L := L) (M := M) hχ hβ p₀ k hk
  refine ⟨C,hC,?_⟩
  intro eps lam hlam hle heps hM X hX hXne hcard N V Z hV Near Far hFar hconn Dz
  let I := X.biUnion id
  let blk := Limits.blockOf X
  let Dn := symOf I Near
  let Df := symOf I Far
  let h := eps*truncationScale p₀ β lam
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)).trans hM
  have hlh : lam ≤ h := hle.trans (le_mul_of_one_le_right (hlam.le.trans hle)
    (Appendix.one_le_truncationScale hβ hlam (hle.trans heps)))
  let Q₁ := clusterQ β (interactionGoodZ χ p₀ β lam eps V Z) (dipoleWeightZ p₀ β lam M eps L V Z)
    M lam blk Dn Dz Df
  let Q₀ := clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df
  let F (c : I → ℂ × ℂ) := (Q₁ c-Q₀ c)*mixedDensity χ β lam h Df c
  have hFm : Measurable F := by
    have hqm : Measurable (fun c => Q₁ c-Q₀ c) := (measurable_clusterQ (measurable_interactionGoodZ p₀ β lam eps V Z hχ hlam)
      (measurable_dipoleWeightZ p₀ β lam M eps L V Z) blk Dn Dz Df).sub
        (measurable_clusterQ (measurable_dipoleInteraction hχ hlam) measurable_const blk Dn Dz Df)
    exact hqm.mul (((Finset.measurable_prod _ fun i _ => (measurable_pairDensity hχ hlam β).comp
      (measurable_pi_apply i)).mul (measurable_cutInd h)).mul (measurable_shortInd (17*h) Df))
  obtain ⟨B,hB⟩ := plus_QH_bound (L := L) hχ (by linarith : 0 ≤ β) hlam hlh hM hV blk Dn Dz Df
  have hFb (c : I → ℂ × ℂ) : |F c| ≤ 2*B := by
    have hbs := hB c
    have hs0 := shortInd_nonneg (17*h) Df c
    have hs1 := shortInd_le_one (17*h) Df c
    have he : F c = (Q₁ c*((∏ i, pairDensity χ β lam (c i))*cutInd h c) -
        Q₀ c*((∏ i, pairDensity χ β lam (c i))*cutInd h c))*shortInd (17*h) Df c := by
      unfold F mixedDensity
      ring
    rw [he,abs_mul,abs_of_nonneg hs0]
    calc
      _ ≤ (_+_)*1 := mul_le_mul (abs_sub _ _) hs1 hs0 (add_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ 2*B := by linarith [hbs.1,hbs.2]
  let G (c : I → ℂ × ℂ) :=
    ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
      ∑ P ∈ (fiveSubsets O (Df \ O) (RouteCases.intraEdges blk) univ).erase (∅,∅,∅,∅,∅),
        ENNReal.ofReal |mixedIntegrand χ β lam M h (routeFrozenInteraction χ p₀ β lam eps V Z)
          (routeFrozenQuadratic p₀ β lam eps L V Z) (routeFrozenBad p₀ β lam M eps V Z)
          blk Dn Dz Df O c P|
  apply abs_integral_le_of_avg blk hFm hFb N G
  · intro c
    have hd (A : Finset X) : mixedDensity χ β lam h Df (flipCfg (blockLabels blk A) c) =
        mixedDensity χ β lam h Df c := by
      unfold mixedDensity
      rw [cutInd_flip,shortInd_flip]
      have hp : (∏ i, pairDensity χ β lam (flipCfg (blockLabels blk A) c i)) =
          ∏ i, pairDensity χ β lam (c i) :=
        prod_congr rfl fun i _ => pairDensity_flip hχ _ c i
      rw [hp]
    have hav : (∑ A : Finset X, F (flipCfg (blockLabels blk A) c)) / 2^Fintype.card X =
        ((∑ A : Finset X, (Q₁ (flipCfg (blockLabels blk A) c)-Q₀ (flipCfg (blockLabels blk A) c))) /
          2^Fintype.card X)*mixedDensity χ β lam h Df c := by
      simp only [F,hd,← sum_mul,div_mul_eq_mul_div]
    rw [hav]
    rcases cutInd_eq_one_or h c with ⟨_,hcut⟩ | hz
    · have he := clusterQ_frozen_five_subset_error (L := L) hχ hlam hlh hM hV blk Dn Dz Df c hcut
      have he' : ((∑ A : Finset X, (Q₁ (flipCfg (blockLabels blk A) c)-
          Q₀ (flipCfg (blockLabels blk A) c))) / 2^Fintype.card X) * mixedDensity χ β lam h Df c = ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
        ∑ P ∈ (fiveSubsets O (Df \ O) (RouteCases.intraEdges blk) univ).erase (∅,∅,∅,∅,∅),
          mixedIntegrand χ β lam M h (routeFrozenInteraction χ p₀ β lam eps V Z)
            (routeFrozenQuadratic p₀ β lam eps L V Z) (routeFrozenBad p₀ β lam M eps V Z)
            blk Dn Dz Df O c P := by
        refine he.trans ?_
        apply sum_congr rfl
        intro O _
        apply sum_congr
        · ext P
          simp only [mem_erase]
        · intro P _
          rfl
      rw [he']
      unfold G
      apply (ENNReal.ofReal_le_ofReal ((abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun O _ => abs_sum_le_sum_abs _ _))).trans_eq
      rw [ENNReal.ofReal_sum_of_nonneg (fun O _ => sum_nonneg fun P _ => abs_nonneg _)]
      exact sum_congr rfl fun O _ => ENNReal.ofReal_sum_of_nonneg (fun P _ => abs_nonneg _)
    · have hd0 : mixedDensity χ β lam h Df c = 0 := by unfold mixedDensity; rw [hz,mul_zero,zero_mul]
      rw [hd0,mul_zero,abs_zero,ENNReal.ofReal_zero]
      exact bot_le
  · have he0 := Real.rpow_nonneg (hlam.le.trans hle) (-2 : ℝ)
    have he1 := Real.rpow_nonneg (hlam.le.trans hle) (alphaExponent β*k)
    have hr := Real.rpow_nonneg (Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam).le (-2 : ℝ)
    have hl := Real.rpow_nonneg hlam.le ((2-β)*k)
    positivity
  · exact hbound eps lam hlam hle heps hM X hX hXne hcard V Z hV Near Far hFar hconn Dz

end MultipoleBKT.ExpansionK.RouteAssembly

end
