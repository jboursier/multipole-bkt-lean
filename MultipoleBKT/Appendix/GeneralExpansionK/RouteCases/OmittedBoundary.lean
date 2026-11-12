/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.OmittedIntegrand

/-!
# Omitted-integrand bounds without support hypotheses

See Lemma A.7.
The missing-support branches vanish exactly. Thus the complete pointwise
boundary applies to every configuration of the original parity integrand.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SimpleGraph Peeling Multipole Hierarchical SmallIntegral Parity UpperBound.BoundedUpper

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

/-- A linked far edge annihilates the omitted baseline term too. -/
theorem omittedParity_eq_zero_of_linked (χ : ℂ → ℝ) (β lam M h : ℝ)
    (blk : ι → κ) (Dn Dz Df O : Finset (Sym2 ι)) (c : ι → ℂ × ℂ)
    {e : Sym2 ι} (he : e ∈ Df) (hl : ¬ FarE M lam c e) :
    omittedParityIntegrand χ β lam M h blk Dn Dz Df O c = 0 := by
  unfold omittedParityIntegrand
  by_cases heO : e ∈ O
  · rw [prod_eq_zero heO (gammaW_of_linked c hl),zero_mul,mul_zero,zero_mul]
  · rw [prod_eq_zero (mem_sdiff.2 ⟨he,heO⟩) (alphaW_add_linkIndE_of_linked c hl),
      mul_zero,mul_zero,zero_mul]

section Source

variable {X : Finset (Finset ℕ)}

/-- The full omitted-integrand entry point. Every configuration either has
zero integrand or has the complete quadratic-tail or long-even-edge bound. -/
theorem baseline_omitted_pointwise_all {χ : ℂ → ℝ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {lam M h : ℝ}, 0 < lam → 1 ≤ M → lam ≤ h →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
      (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      ∃ Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id),
        IsRelTree₀ (coarsen X (oddComponents X O)) Tb ∧ graphPairs Tb ⊆ (Near ∪ Far) \ O ∧
        let cfg := fun i : X.biUnion id => c i
        let term := omittedParityIntegrand χ β lam M h (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
          (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) cfg
        term = 0 ∨ OmittedPointwise hX (hOF.trans hFar) hpar lam M (17 * h) c (graphPairs Tb)
          ((Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) *
            K ^ (symOf (X.biUnion id) Far).card) *
            clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz cfg *
            omittedDensity χ β lam h (symOf (X.biUnion id) Far) cfg) term := by
  obtain ⟨K,hK,hb⟩ := baseline_omitted_pointwise hχ hβ hX
  refine ⟨K,hK,?_⟩
  intro lam M h hlam hM hlh Near Far O hFar hconn hOF hpar Dz c
  let cfg := fun i : X.biUnion id => c i
  let Dn := symOf (X.biUnion id) Near
  let Df := symOf (X.biUnion id) Far
  let OS := symOf (X.biUnion id) O
  have hzero : omittedParityIntegrand χ β lam M h (Limits.blockOf X) Dn Dz Df OS cfg = 0 →
      ∃ Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id),
        IsRelTree₀ (coarsen X (oddComponents X O)) Tb ∧ graphPairs Tb ⊆ (Near ∪ Far) \ O ∧
        let term := omittedParityIntegrand χ β lam M h (Limits.blockOf X) Dn Dz Df OS cfg
        term = 0 ∨ OmittedPointwise hX (hOF.trans hFar) hpar lam M (17 * h) c (graphPairs Tb)
          ((Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) * K ^ Df.card) *
            clusterSupport M lam (Limits.blockOf X) Dn Dz cfg * omittedDensity χ β lam h Df cfg) term := by
    intro hz
    obtain ⟨-,-,Tb,hTb,hTE⟩ := source_skeletons_and_even_tree hX hconn (hOF.trans subset_union_right) hpar
    exact ⟨Tb,hTb,hTE,Or.inl hz⟩
  rcases Classical.em (∀ p ∈ Near, MultipoleLinked M lam (c p.1) (c p.2)) with hn | hn
  · rcases Classical.em (∀ p ∈ Far, ¬ MultipoleLinked M lam (c p.1) (c p.2)) with hf | hf
    · rcases Classical.em (∀ i ∈ X.biUnion id, ‖(c i).1 - (c i).2‖ ≤ h) with hc | hc
      · obtain ⟨Tb,hTb,hTE,ht⟩ := hb hlam hM hlh Near Far O hFar hconn hOF hpar Dz c hn hf hc
        exact ⟨Tb,hTb,hTE,Or.inr ht⟩
      · apply hzero
        have hz : cutInd h cfg = 0 := by
          rcases cutInd_eq_one_or h cfg with ⟨-,hcut⟩ | hz
          · exact False.elim (hc fun i hi => hcut ⟨i,hi⟩)
          · exact hz
        unfold omittedParityIntegrand omittedDensity
        rw [hz,mul_zero,zero_mul,mul_zero]
    · push Not at hf
      obtain ⟨p,hp,hl⟩ := hf
      have hv := mem_pairsOn.1 (interPairs_subset_pairsOn (hFar hp))
      let i : X.biUnion id := ⟨p.1,hv.1⟩
      let j : X.biUnion id := ⟨p.2,hv.2.1⟩
      exact hzero (omittedParity_eq_zero_of_linked χ β lam M h (Limits.blockOf X) Dn Dz Df OS cfg
        (e := s(i,j)) (mem_symOf.2 ⟨i,j,hv.2.2,hp,rfl⟩) (not_not_intro hl))
  · push Not at hn
    obtain ⟨p,hp,hl⟩ := hn
    have hNear : Near ⊆ interPairs X := subset_union_left.trans (mem_relEdgeSets₀.1 hconn).1
    have hv := mem_pairsOn.1 (interPairs_subset_pairsOn (hNear hp))
    let i : X.biUnion id := ⟨p.1,hv.1⟩
    let j : X.biUnion id := ⟨p.2,hv.2.1⟩
    have hz := clusterG_eq_zero_of_not_linked β lam M (dipoleInteraction χ lam) (fun _ => 1)
      (Limits.blockOf X) Dn Dz cfg (e := s(i,j)) (mem_symOf.2 ⟨i,j,hv.2.2,hp,rfl⟩) hl
    exact hzero (by unfold omittedParityIntegrand; rw [hz,zero_mul,zero_mul])

end Source

end MultipoleBKT.ExpansionK.RouteCases

end
