/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.ScreenedSum
public import MultipoleBKT.Appendix.GeneralExpansionK.ZParts
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ScreenedModelExpansion

/-!
# The screened-model error on the written support

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

/-- Cases A–E assembled for the actual screened-model difference on D. -/
theorem internal_screened_support_integral {χ : ℂ → ℝ} {β L M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ k : ℕ) (hk : 1 ≤ k)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 → ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ N : ℕ,
      ∀ (Near Far : Finset (ℕ × ℕ)), Far ⊆ interPairs X → Near ∪ Far ∈ relEdgeSets₀ X →
      ∀ Dz : Finset (Sym2 (X.biUnion id)),
      ∀ B : ℝ,
      Measurable (fun c : X.biUnion id → ℂ × ℂ =>
        (clusterQ β (upperBoundInteraction χ lam eps (truncationScale p₀ β lam)) (gaussianWeight p₀ β lam eps L)
            M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c -
          clusterQ β (dipoleInteraction χ lam) (fun _ => 1)
            M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c) *
          mixedDensity χ β lam (eps*truncationScale p₀ β lam) (symOf (X.biUnion id) Far) c) →
      (∀ c : X.biUnion id → ℂ × ℂ,
        |(clusterQ β (upperBoundInteraction χ lam eps (truncationScale p₀ β lam)) (gaussianWeight p₀ β lam eps L)
            M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c -
          clusterQ β (dipoleInteraction χ lam) (fun _ => 1)
            M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c) *
          mixedDensity χ β lam (eps*truncationScale p₀ β lam) (symOf (X.biUnion id) Far) c| ≤ B) →
      |∫ c in boxConfig (X.biUnion id) N,
        (clusterQ β (upperBoundInteraction χ lam eps (truncationScale p₀ β lam)) (gaussianWeight p₀ β lam eps L)
            M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c -
          clusterQ β (dipoleInteraction χ lam) (fun _ => 1)
            M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c) *
          mixedDensity χ β lam (eps*truncationScale p₀ β lam) (symOf (X.biUnion id) Far) c| ≤
        C*eps^(-2 : ℝ)*N*lam^((2-β)*k)*truncationScale p₀ β lam^(-2 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := screened_mixed_sum_bound (β := β) (L := L) (M := M) hχ hβ hM p₀ k hk eps heps
  refine ⟨C,hC,?_⟩
  intro lam hlam hle hl1 X hX hXne hcard N Near Far hFar hconn Dz B hFm hFb
  let I := X.biUnion id
  let blk := Limits.blockOf X
  let Dn := symOf I Near
  let Df := symOf I Far
  let h := eps*truncationScale p₀ β lam
  let Q₁ := clusterQ β (upperBoundInteraction χ lam eps (truncationScale p₀ β lam)) (gaussianWeight p₀ β lam eps L)
    M lam blk Dn Dz Df
  let Q₀ := clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df
  let F (c : I → ℂ × ℂ) := (Q₁ c-Q₀ c)*mixedDensity χ β lam h Df c
  let G (c : I → ℂ × ℂ) :=
    ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
      ∑ P ∈ (fiveSubsets O (Df \ O) (RouteCases.intraEdges blk) univ).erase (∅,∅,∅,∅,∅),
        ENNReal.ofReal |mixedIntegrand χ β lam M h (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
          (fun d => Real.exp (-L*(‖d.1-d.2‖ / h)^2)-1) (fun _ => 0)
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
    have he := clusterQ_screened_five_subset_error hχ p₀ β lam M eps L hM blk Dn Dz Df c
    have he' : ((∑ A : Finset X, (Q₁ (flipCfg (blockLabels blk A) c)-
        Q₀ (flipCfg (blockLabels blk A) c))) / 2^Fintype.card X) * mixedDensity χ β lam h Df c = ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
      ∑ P ∈ (fiveSubsets O (Df \ O) (RouteCases.intraEdges blk) univ).erase (∅,∅,∅,∅,∅),
        mixedIntegrand χ β lam M h (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
            (fun d => Real.exp (-L*(‖d.1-d.2‖ / h)^2)-1) (fun _ => 0)
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
  · have he0 := Real.rpow_nonneg (hlam.le.trans hle) (-2 : ℝ)
    have he1 := Real.rpow_nonneg (hlam.le.trans hle) (alphaExponent β*k)
    have hr := Real.rpow_nonneg (Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam).le (-2 : ℝ)
    have hl := Real.rpow_nonneg hlam.le ((2-β)*k)
    positivity
  · exact hbound lam hlam hle hl1 X hX hXne hcard N Near Far hFar hconn Dz

end MultipoleBKT.ExpansionK.RouteAssembly

end
