/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SupportedAssembly

/-!
# Concrete gain-bearing pointwise bounds for spatial integration

See (A.55)–(A.62). Every analytic control is discharged for the admissible
frozen and screened models. The coefficient precedes lambda and frozen data.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SimpleGraph Peeling Multipole Hierarchical SmallIntegral Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)}

/-- Complete pointwise bounds for every nonempty extended frozen mixed term,
with all block, support and density factors and the case-E kernel retained. -/
theorem frozen_mixed_pointwise {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {N p₀ : ℕ} {lam M ε₀ h : ℝ}
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → 1 ≤ M →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
      (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      MixedBoundary hX (hOF.trans hFar) hpar χ β lam M h K (Real.exp (β * cbK hχ))
        (routeFrozenInteraction χ p₀ β lam ε₀ V Z)
        (routeFrozenRadius p₀ β lam ε₀ V Z)
        (routeFrozenQuadratic p₀ β lam ε₀ L V Z)
        (routeFrozenBad p₀ β lam M ε₀ V Z) Near Far Dz c := by
  obtain ⟨K₀,hK₀,hcontrols⟩ := frozen_controls (ι := X.biUnion id) (L := L) hχ hβ
  obtain ⟨Ce,hCe,he⟩ := routeFrozen_interaction_bounds hχ
  obtain ⟨Cv,hCv,hv⟩ := BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ
  obtain ⟨Ke,hKe,href⟩ := internal_refined_even (ι := X.biUnion id) (D := Ce) hβ (add_nonneg hCe.le hCv)
  refine ⟨K₀ + Ke,by linarith,?_⟩
  intro N p₀ lam M ε₀ h V Z hlam hM Near Far O hFar hconn hOF hpar Dz c
  let cfg := fun i : X.biUnion id => c i
  have H := (hcontrols (p₀ := p₀) (ε₀ := ε₀) V Z hlam hM cfg).enlarge (le_add_of_nonneg_right hKe)
  have hpoint := href hlam hM (routeFrozenInteraction χ p₀ β lam ε₀ V Z)
    (routeFrozenRadius p₀ β lam ε₀ V Z ∘ cfg) cfg
    (fun i => hlam.trans_le (routeFrozenRadius_lower p₀ β lam ε₀ V Z (cfg i)).1)
    (fun i j hf => by
      have hw := (he (p₀ := p₀) (β := β) (ε₀ := ε₀) V Z hlam hM (cfg i) (cfg j)).2 hf
      have hw₀ := hv lam hlam M hM (cfg i) (cfg j) hf
      nlinarith)
    (fun i j => (he (p₀ := p₀) (β := β) (ε₀ := ε₀) V Z hlam hM (cfg i) (cfg j)).1)
  apply internal_model_boundary hχ hβ hlam hM hX Near Far hFar hconn hOF hpar Dz c
    (routeFrozenInteraction χ p₀ β lam ε₀ V Z)
    (routeFrozenRadius p₀ β lam ε₀ V Z)
    (routeFrozenQuadratic p₀ β lam ε₀ L V Z)
    (routeFrozenBad p₀ β lam M ε₀ V Z) H
  intro i j
  exact (hpoint i j).trans (mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (markedEvenE_nonneg lam cfg s(i,j))))

/-- Complete pointwise bounds for the screened mixed terms. The Gaussian
correction is literal, and the bad-label correction vanishes identically. -/
theorem screened_mixed_pointwise {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {lam M ε₀ R : ℝ}, 0 < lam → 1 ≤ M → lam ≤ ε₀ * R →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
      (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      (∀ i ∈ X.biUnion id, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      MixedBoundary hX (hOF.trans hFar) hpar χ β lam M (ε₀ * R) K (Real.exp (β * cbK hχ))
        (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R)
        (fun d => Real.exp (-L * (‖d.1 - d.2‖ / (ε₀ * R)) ^ 2) - 1)
        (fun _ => 0) Near Far Dz c := by
  obtain ⟨K₀,hK₀,hcontrols⟩ := screened_controls (ι := X.biUnion id) (L := L) hχ hβ
  obtain ⟨Ke,hKe,href⟩ := internal_refined_even (ι := X.biUnion id) (D := c310 hχ) hβ
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (cA_nonneg hχ))
  refine ⟨K₀ + Ke,by linarith,?_⟩
  intro lam M ε₀ R hlam hM hlh Near Far O hFar hconn hOF hpar Dz c hcut
  let cfg := fun i : X.biUnion id => c i
  have hc : ∀ i, ‖(cfg i).1 - (cfg i).2‖ ≤ ε₀ * R := fun i => hcut i i.property
  have H := (hcontrols (ε₀ := ε₀) (R := R) hlam hM hlh cfg hc).enlarge (le_add_of_nonneg_right hKe)
  have hh : 0 < ε₀ * R := hlam.trans_le hlh
  obtain ⟨hw,hv,-,-⟩ := minus_far_facts hχ hlam hM hlh cfg hc
  have herr : ∀ i j, |upperBoundInteraction χ lam ε₀ R (cfg i) (cfg j) - dipoleInteraction χ lam (cfg i) (cfg j)| ≤
      c310 hχ * (‖(cfg i).1 - (cfg i).2‖ * ‖(cfg j).1 - (cfg j).2‖) / max (ε₀ * R) (ε₀ * R) ^ 2 := by
    intro i j
    have h8 : ∀ i, 8 * max ‖(cfg i).2 - (cfg i).1‖ lam ≤ 8 * ε₀ * R := by
      intro i
      rw [norm_sub_rev,mul_assoc]
      exact mul_le_mul_of_nonneg_left (max_le (hc i) hlh) (by norm_num)
    have hp := ((Classical.choose_spec (lemma_3_10 hχ)).2 lam (8 * ε₀ * R) hlam (cfg i) (cfg j) (h8 i) (h8 j)).1
    change |upperBoundInteraction χ lam ε₀ R (cfg i) (cfg j) - dipoleInteraction χ lam (cfg i) (cfg j)| ≤
      c310 hχ * (‖(cfg i).1 - (cfg i).2‖ * ‖(cfg j).1 - (cfg j).2‖) / (8 * ε₀ * R) ^ 2 at hp
    rw [max_self]
    exact hp.trans (div_le_div_of_nonneg_left
      (mul_nonneg (c310_pos hχ).le (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (pow_pos hh 2) (pow_le_pow_left₀ hh.le (by rw [mul_assoc]; linarith) 2))
  have hpoint := href hlam hM (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R) cfg
    (fun _ => hh) (fun i j hf => by nlinarith [hw i j hf,hv i j hf]) herr
  apply internal_model_boundary hχ hβ hlam hM hX Near Far hFar hconn hOF hpar Dz c
    (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R)
    (fun d => Real.exp (-L * (‖d.1 - d.2‖ / (ε₀ * R)) ^ 2) - 1) (fun _ => 0) H
  intro i j
  exact (hpoint i j).trans (mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (markedEvenE_nonneg lam cfg s(i,j))))

/-- The screened bound on every configuration. Outside the actual radius
cutoff the complete summand vanishes, so the spatial integration needs no pointwise support proof. -/
theorem screened_mixed_pointwise_all {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {lam M ε₀ R : ℝ}, 0 < lam → 1 ≤ M → lam ≤ ε₀ * R →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
      (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      MixedBoundary hX (hOF.trans hFar) hpar χ β lam M (ε₀ * R) K (Real.exp (β * cbK hχ))
        (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R)
        (fun d => Real.exp (-L * (‖d.1 - d.2‖ / (ε₀ * R)) ^ 2) - 1)
        (fun _ => 0) Near Far Dz c := by
  obtain ⟨K,hK,hb⟩ := screened_mixed_pointwise (L := L) hχ hβ hX
  refine ⟨K,hK,?_⟩
  intro lam M ε₀ R hlam hM hlh Near Far O hFar hconn hOF hpar Dz c
  let cfg := fun i : X.biUnion id => c i
  rcases cutInd_eq_one_or (ε₀ * R) cfg with ⟨-,hc⟩ | hz
  · exact hb hlam hM hlh Near Far O hFar hconn hOF hpar Dz c (fun i hi => hc ⟨i,hi⟩)
  · obtain ⟨-,-,Tb,hTb,hTE⟩ := source_skeletons_and_even_tree hX hconn
      (hOF.trans subset_union_right) hpar
    refine ⟨Tb,hTb,hTE,?_⟩
    intro P _ _
    apply Or.inl
    unfold mixedIntegrand mixedDensity
    rw [hz,mul_zero,zero_mul,mul_zero]

end MultipoleBKT.ExpansionK.RouteCases

end
