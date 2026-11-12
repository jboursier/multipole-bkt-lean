/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SupportBasics

/-!
# Common factors and support in the complete pointwise bound

See (A.55)–(A.62). The original graph includes the actual near bonds. All
block, support, cutoff and density factors remain in the common coefficient.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SimpleGraph Peeling Multipole Hierarchical SmallIntegral Parity UpperBound.BoundedUpper

section Source

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- The exported boundary for a concrete model. Every nonempty actual term has
its whole pointwise estimate, or vanishes on the missing near/far support.
The even tree is selected before the five correction subsets. -/
def MixedBoundary (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (χ : ℂ → ℝ) (β lam M h K W : ℝ)
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) (τ u v : ℂ × ℂ → ℝ)
    (Near Far : Finset (ℕ × ℕ)) (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ) : Prop :=
  ∃ Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id),
    IsRelTree₀ (coarsen X (oddComponents X O)) Tb ∧ graphPairs Tb ⊆ (Near ∪ Far) \ O ∧
    ∀ P, P ≠ (∅,∅,∅,∅,∅) → P ∈ fiveSubsets (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O)
      (intraEdges (Limits.blockOf X)) univ →
      let cfg := fun i : X.biUnion id => c i
      let term := mixedIntegrand χ β lam M h w u v (Limits.blockOf X)
        (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) cfg P
      term = 0 ∨
      PaperPointwise hX hOX hpar (fun i => rhoD lam (c i)) (paperDistE c) (farInd M lam c)
        (τ ∘ cfg) (v ∘ cfg) (paperEvenE M lam cfg) (markedEvenE lam cfg)
        (symOf (X.biUnion id) (graphPairs Tb)) P (maxRad lam cfg)
        ((W ^ ((X.biUnion id).card * (X.biUnion id).card) *
          K ^ factorCount (symOf (X.biUnion id) O)
            (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) P) *
          clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz cfg *
          mixedDensity χ β lam h (symOf (X.biUnion id) Far) cfg) term

/-- Internal transport and assembly for a model whose concrete analytic
controls have already been proved. The model model theorems below
supply these controls with one coefficient before lambda and frozen data. -/
theorem internal_supported_model_boundary {χ : ℂ → ℝ} {β lam M h K : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam) (hM : 1 ≤ M)
    (hX : IsSubpartition X) (Near Far : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X)
    (hconn : Near ∪ Far ∈ relEdgeSets₀ X) (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
    (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ)
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) (τ u v : ℂ × ℂ → ℝ)
    (H : InternalControls K (fun i : X.biUnion id => rhoD lam (c i))
      (fun i : X.biUnion id => τ (c i))
      (mixedOddWeight M lam (fun i : X.biUnion id => c i))
      (mixedEvenWeight M lam (fun i : X.biUnion id => c i))
      (gammaW β w M lam (fun i : X.biUnion id => c i))
      (gammaW β (dipoleInteraction χ lam) M lam (fun i : X.biUnion id => c i))
      (fun e => alphaW β w M lam (fun i : X.biUnion id => c i) e + linkIndE M lam (fun i : X.biUnion id => c i) e)
      (fun e => alphaW β (dipoleInteraction χ lam) M lam (fun i : X.biUnion id => c i) e + linkIndE M lam (fun i : X.biUnion id => c i) e)
      (intraRatio β w (dipoleInteraction χ lam) (fun i : X.biUnion id => c i))
      (fun i : X.biUnion id => u (c i)) (fun i : X.biUnion id => v (c i)))
    (hRef : ∀ i j : X.biUnion id,
      |(alphaW β w M lam (fun i : X.biUnion id => c i) s(i,j) + linkIndE M lam (fun i : X.biUnion id => c i) s(i,j)) -
        (alphaW β (dipoleInteraction χ lam) M lam (fun i : X.biUnion id => c i) s(i,j) + linkIndE M lam (fun i : X.biUnion id => c i) s(i,j))| ≤
      K * ((τ (c i) ^ 2)⁻¹ * markedEvenE lam (fun i : X.biUnion id => c i) s(i,j)))
    (hn : ∀ p ∈ Near, MultipoleLinked M lam (c p.1) (c p.2))
    (hf : ∀ p ∈ Far, ¬ MultipoleLinked M lam (c p.1) (c p.2)) :
    MixedBoundary hX (hOF.trans hFar) hpar χ β lam M h K (Real.exp (β * cbK hχ)) w τ u v Near Far Dz c := by
  let cfg := fun i : X.biUnion id => c i
  let Dn := symOf (X.biUnion id) Near
  let Df := symOf (X.biUnion id) Far
  let OS := symOf (X.biUnion id) O
  let r := fun i => rhoD lam (c i)
  let d := paperDistE c
  let g := farInd M lam c
  have hr : ∀ i, 0 ≤ r i := fun _ => (norm_nonneg _).trans (le_max_left _ _)
  have hd : ∀ e, 0 ≤ d e := by
    intro e
    induction e using Sym2.ind with
    | h i j => exact dipoleDist_nonneg _ _
  have hg : ∀ e, 0 ≤ g e := fun e => farInd_nonneg c e
  have hg1 : ∀ e, g e ≤ 1 := fun e => farInd_le_one c e
  have hb0 := paperEvenE_nonneg M lam cfg
  have hb1 := paperEven_le_one hlam hM cfg
  have hj0 := markedEvenE_nonneg lam cfg
  have Hgeom := H.mono (A' := componentEdge (absWeight r d g)) (B' := paperEvenE M lam cfg)
    (fun e => (mixedOdd_le_absWeight hlam hM cfg e).trans_eq (by
      induction e using Sym2.ind with | h i j => rfl))
    (mixedEven_le_paperEven cfg)
  obtain ⟨-,-,Tb,hTb,hTbE⟩ := source_skeletons_and_even_tree hX hconn
    (hOF.trans subset_union_right) hpar
  refine ⟨Tb,hTb,hTbE,?_⟩
  intro P hne hP
  dsimp only
  have hPbase := hP
  have hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2) := by
    intro p hp
    have hp' := (far_facts hlam hM (hf p (hOF hp))).2.1
    have hmin : 0 ≤ min (r p.1) (r p.2) := le_min (hr _) (hr _)
    exact (le_mul_of_one_le_left hmin hM).trans hp'.le
  have hnear : ∀ e ∈ Dn, paperEvenE M lam cfg e = 1 := by
    intro e he
    obtain ⟨i,j,-,hp,rfl⟩ := mem_symOf.1 he
    exact ite_eq_left (hn _ hp)
  have ht : symOf (X.biUnion id) (graphPairs Tb) ⊆ Dn ∪ symOf (X.biUnion id) (Far \ O) := by
    rw [← symOf_union]
    apply symOf_mono
    intro p hp
    have hh := mem_sdiff.1 (hTbE hp)
    rcases mem_union.1 hh.1 with hn | hf
    · exact mem_union_left _ hn
    · exact mem_union_right _ (mem_sdiff.2 ⟨hf,hh.2⟩)
  let G := clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam (Limits.blockOf X) Dn Dz cfg *
    mixedDensity χ β lam h Df cfg
  have hp' : P ≠ (∅,∅,∅,∅,∅) ∧ P ∈ fiveSubsets OS (symOf (X.biUnion id) (Far \ O))
      (intraEdges (Limits.blockOf X)) univ := by
    exact ⟨hne,by simpa only [OS,symOf_sdiff] using hP⟩
  have hb := internal_pointwise_cases hX (hOF.trans hFar) hpar r d g hr hd hg hg1 hfar
    (fun i hi => rhoD_le_maxRad lam cfg ⟨i,hi⟩)
    (symOf (X.biUnion id) (graphPairs Tb)) (intraEdges (Limits.blockOf X))
    (paperEvenE M lam cfg) (markedEvenE lam cfg) hb0 hb1 hj0 ht hnear Hgeom hRef P (by simpa only [mem_erase] using hp') G
  have hcommon := internal_common_factor (M := M) hχ hβ hlam (zero_le_one.trans H.coefficient)
    (mixedDensity_nonneg χ β lam h Df cfg) (Limits.blockOf X) Dn Dz cfg
    (factorCount OS (symOf (X.biUnion id) (Far \ O)) P)
  simp only [Fintype.card_coe] at hcommon
  have hres := hb.mono_common hcommon hg hb0 hj0
  apply Or.inr
  simpa only [mixedIntegrand_eq_reordered,OS,Df,Dn,cfg,r,d,g,G,Function.comp_def,symOf_sdiff] using hres
theorem internal_model_boundary {χ : ℂ → ℝ} {β lam M h K : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam) (hM : 1 ≤ M)
    (hX : IsSubpartition X) (Near Far : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X)
    (hconn : Near ∪ Far ∈ relEdgeSets₀ X) (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
    (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ)
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) (τ u v : ℂ × ℂ → ℝ)
    (H : InternalControls K (fun i : X.biUnion id => rhoD lam (c i))
      (fun i : X.biUnion id => τ (c i))
      (mixedOddWeight M lam (fun i : X.biUnion id => c i))
      (mixedEvenWeight M lam (fun i : X.biUnion id => c i))
      (gammaW β w M lam (fun i : X.biUnion id => c i))
      (gammaW β (dipoleInteraction χ lam) M lam (fun i : X.biUnion id => c i))
      (fun e => alphaW β w M lam (fun i : X.biUnion id => c i) e + linkIndE M lam (fun i : X.biUnion id => c i) e)
      (fun e => alphaW β (dipoleInteraction χ lam) M lam (fun i : X.biUnion id => c i) e + linkIndE M lam (fun i : X.biUnion id => c i) e)
      (intraRatio β w (dipoleInteraction χ lam) (fun i : X.biUnion id => c i))
      (fun i : X.biUnion id => u (c i)) (fun i : X.biUnion id => v (c i)))
    (hRef : ∀ i j : X.biUnion id,
      |(alphaW β w M lam (fun i : X.biUnion id => c i) s(i,j) + linkIndE M lam (fun i : X.biUnion id => c i) s(i,j)) -
        (alphaW β (dipoleInteraction χ lam) M lam (fun i : X.biUnion id => c i) s(i,j) + linkIndE M lam (fun i : X.biUnion id => c i) s(i,j))| ≤
      K * ((τ (c i) ^ 2)⁻¹ * markedEvenE lam (fun i : X.biUnion id => c i) s(i,j))) :
    MixedBoundary hX (hOF.trans hFar) hpar χ β lam M h K (Real.exp (β * cbK hχ)) w τ u v Near Far Dz c := by
  let cfg := fun i : X.biUnion id => c i
  let Dn := symOf (X.biUnion id) Near
  let Df := symOf (X.biUnion id) Far
  let OS := symOf (X.biUnion id) O
  rcases Classical.em (∀ p ∈ Near, MultipoleLinked M lam (c p.1) (c p.2)) with hn | hn
  · rcases Classical.em (∀ p ∈ Far, ¬ MultipoleLinked M lam (c p.1) (c p.2)) with hf | hf
    · exact internal_supported_model_boundary hχ hβ hlam hM hX Near Far hFar hconn hOF hpar Dz c w τ u v H hRef hn hf
    · obtain ⟨-,-,Tb,hTb,hTbE⟩ := source_skeletons_and_even_tree hX hconn
        (hOF.trans subset_union_right) hpar
      refine ⟨Tb,hTb,hTbE,?_⟩
      intro P hne hP
      dsimp only
      have hPbase := hP
      push Not at hf
      obtain ⟨p,hp,hl⟩ := hf
      have hpV := mem_pairsOn.1 (interPairs_subset_pairsOn (hFar hp))
      let i : X.biUnion id := ⟨p.1,hpV.1⟩
      let j : X.biUnion id := ⟨p.2,hpV.2.1⟩
      exact Or.inl (mixedIntegrand_eq_zero_of_linked χ β lam M h w u v (Limits.blockOf X) Dn Dz Df OS cfg P (e := s(i,j))
        (by simpa only [OS,Df,fiveSubsets] using hPbase) (mem_symOf.2 ⟨i,j,hpV.2.2,hp,rfl⟩) (show ¬ FarE M lam cfg s(i,j) from not_not_intro hl))
  · obtain ⟨-,-,Tb,hTb,hTbE⟩ := source_skeletons_and_even_tree hX hconn
      (hOF.trans subset_union_right) hpar
    refine ⟨Tb,hTb,hTbE,?_⟩
    intro P hne hP
    dsimp only
    have hPbase := hP
    push Not at hn
    obtain ⟨p,hp,hl⟩ := hn
    have hNear : Near ⊆ interPairs X := subset_union_left.trans (mem_relEdgeSets₀.1 hconn).1
    have hpV := mem_pairsOn.1 (interPairs_subset_pairsOn (hNear hp))
    let i : X.biUnion id := ⟨p.1,hpV.1⟩
    let j : X.biUnion id := ⟨p.2,hpV.2.1⟩
    have hz := clusterG_eq_zero_of_not_linked β lam M (dipoleInteraction χ lam) (fun _ => 1)
      (Limits.blockOf X) Dn Dz cfg (mem_symOf.2 ⟨i,j,hpV.2.2,hp,rfl⟩) hl
    exact Or.inl (by unfold mixedIntegrand; rw [hz,zero_mul,zero_mul])

end Source

end MultipoleBKT.ExpansionK.RouteCases

end
