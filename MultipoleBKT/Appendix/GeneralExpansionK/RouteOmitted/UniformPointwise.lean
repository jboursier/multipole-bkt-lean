/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.OmittedBoundary

/-!
# The omitted pointwise coefficient before the subpartition

See Lemma A.7. The bond coefficient is
`partConst β Cv`, where `Cv` bounds the model interaction uniformly.
Replaying the same two alternatives exposes this coefficient before `X`.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open Finset Limits SimpleGraph Peeling Multipole Hierarchical SmallIntegral Parity UpperBound.BoundedUpper
open RouteCases
open scoped Classical

/-- The supported omitted alternatives with the bond coefficient chosen before `X`. -/
theorem internal_baseline_pointwise_uniform {χ : ℂ → ℝ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (X : Finset (Finset ℕ)) (hX : IsSubpartition X),
      ∀ {lam M h : ℝ}, 0 < lam → 1 ≤ M → lam ≤ h →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
      (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      (∀ p ∈ Near, MultipoleLinked M lam (c p.1) (c p.2)) →
      (∀ p ∈ Far, ¬ MultipoleLinked M lam (c p.1) (c p.2)) →
      (∀ i ∈ X.biUnion id, ‖(c i).1 - (c i).2‖ ≤ h) →
      ∃ Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id),
        IsRelTree₀ (coarsen X (oddComponents X O)) Tb ∧ graphPairs Tb ⊆ (Near ∪ Far) \ O ∧
        OmittedPointwise hX (hOF.trans hFar) hpar lam M (17 * h) c (graphPairs Tb)
          ((Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) *
            K ^ (symOf (X.biUnion id) Far).card) *
            clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (fun i : X.biUnion id => c i) *
            omittedDensity χ β lam h (symOf (X.biUnion id) Far) (fun i : X.biUnion id => c i))
          (omittedParityIntegrand χ β lam M h (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
            (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) (fun i : X.biUnion id => c i)) := by
  obtain ⟨Cv,hCv,hv⟩ := BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ
  let K := partConst β Cv
  have hK := one_le_partConst hβ hCv
  refine ⟨K,hK,?_⟩
  intro X hX lam M h hlam hM hlh Near Far O hFar hconn hOF hpar Dz c hnear hfar hcut
  let cfg := fun i : X.biUnion id => c i
  let Dn := symOf (X.biUnion id) Near
  let Df := symOf (X.biUnion id) Far
  let OS := symOf (X.biUnion id) O
  let r := fun i => rhoD lam (c i)
  let d := paperDistE c
  let g := farInd M lam c
  let b := fun p : ℕ × ℕ => paperEvenE M lam c s(p.1,p.2)
  let R := maxRad lam cfg
  let Den := omittedDensity χ β lam h Df cfg
  let G := clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam (Limits.blockOf X) Dn Dz cfg * Den
  let C := (Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) * K ^ Df.card) *
    clusterSupport M lam (Limits.blockOf X) Dn Dz cfg * Den
  have hDen := omittedDensity_nonneg χ β lam h Df cfg
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _)
    (pow_nonneg (zero_le_one.trans hK) _)) (clusterSupport_nonneg _ _ _ _ _ _)) hDen
  have hr : ∀ i, 0 ≤ r i := fun _ => (norm_nonneg _).trans (le_max_left _ _)
  have hd : ∀ e, 0 ≤ d e := by intro e; induction e using Sym2.ind with | h i j => exact dipoleDist_nonneg _ _
  have hg := farInd_nonneg (M := M) (lam := lam) c
  have hg1 := farInd_le_one (M := M) (lam := lam) c
  have hOgeom : (∏ e ∈ OS, absWeight (fun i => rhoD lam (cfg i)) (paperDistE cfg) (farInd M lam cfg) e) =
      ∏ p ∈ O, absWeight r d g s(p.1,p.2) := by
    rw [← source_product (hOF.trans (hFar.trans interPairs_subset_pairsOn)) (absWeight r d g)]
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with | h i j => rfl
  have hBgeom : (∏ e ∈ Df \ OS, paperEvenE M lam cfg e) = ∏ p ∈ Far \ O, b p := by
    rw [← symOf_sdiff]
    symm
    exact prod_symOf ((sdiff_subset.trans hFar).trans interPairs_subset_pairsOn) b (paperEvenE M lam cfg)
      (fun i j _ => rfl)
  have hraw := internal_baseline_product hβ hCv hlam hM (K := K) le_rfl (zero_le_one.trans hK) cfg
    (fun i j hf => hv lam hlam M hM (cfg i) (cfg j) hf) Df OS (symOf_mono hOF) G
  rw [hOgeom,hBgeom] at hraw
  have hcommon := internal_common_factor (M := M) hχ hβ hlam (zero_le_one.trans hK) hDen
    (Limits.blockOf X) Dn Dz cfg Df.card
  simp only [Fintype.card_coe] at hcommon
  have hprod0 : 0 ≤ (∏ p ∈ O, absWeight r d g s(p.1,p.2)) * ∏ p ∈ Far \ O, b p :=
    mul_nonneg (prod_nonneg fun _ _ => absWeight_nonneg hr hd hg _)
      (prod_nonneg fun _ _ => paperEvenE_nonneg _ _ _ _)
  have ht : omittedParityIntegrand χ β lam M h (Limits.blockOf X) Dn Dz Df OS cfg =
      G * ((∏ e ∈ OS, gammaW β (dipoleInteraction χ lam) M lam cfg e) *
        ∏ e ∈ Df \ OS, (alphaW β (dipoleInteraction χ lam) M lam cfg e + linkIndE M lam cfg e)) := by
    unfold omittedParityIntegrand
    dsimp only [G,Den]
    ring
  have hbase : |omittedParityIntegrand χ β lam M h (Limits.blockOf X) Dn Dz Df OS cfg| ≤
      C * ((∏ p ∈ O, absWeight r d g s(p.1,p.2)) * ∏ p ∈ Far \ O, b p) := by
    rw [ht]
    exact hraw.trans (mul_le_mul_of_nonneg_right hcommon hprod0)
  obtain ⟨-,-,Tb,hTb,hTbE⟩ := source_skeletons_and_even_tree hX hconn (hOF.trans subset_union_right) hpar
  refine ⟨Tb,hTb,hTbE,?_⟩
  change OmittedPointwise hX (hOF.trans hFar) hpar lam M (17 * h) c (graphPairs Tb) C _
  rcases shortInd_eq_one_or (17 * h) Df cfg with ⟨hshort,-⟩ | ⟨-,e,he,hlong⟩
  · obtain ⟨F,-⟩ := source_skeleton_family hX (hOF.trans hFar) hpar r d g hr hd hg hg1
    apply Or.inl
    refine ⟨F,?_⟩
    have hz : Den = 0 := by dsimp only [Den,omittedDensity]; rw [hshort,sub_self,mul_zero]
    have hzC : C = 0 := by dsimp only [C]; rw [hz,mul_zero]
    have hzt : omittedParityIntegrand χ β lam M h (Limits.blockOf X) Dn Dz Df OS cfg = 0 := by
      unfold omittedParityIntegrand
      change _ * Den = 0
      rw [hz,mul_zero]
    rw [hzt,abs_zero,hzC,zero_mul,zero_mul,zero_mul]
  · obtain ⟨i,j,-,hp,rfl⟩ := mem_symOf.1 he
    have hh : 0 < h := hlam.trans_le hlh
    have hH : 0 < 17 * h := mul_pos (by norm_num) hh
    have hR : ∀ i ∈ X.biUnion id, r i ≤ R := fun i hi => rhoD_le_maxRad lam cfg ⟨i,hi⟩
    have hRH : R ≤ 17 * h := (maxRad_le_of_cut hlh cfg (fun i => hcut i i.property)).trans (by linarith)
    have hfg : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2) := by
      intro p hp
      exact (le_mul_of_one_le_left (le_min (hr _) (hr _)) hM).trans (far_facts hlam hM (hfar p (hOF hp))).2.1.le
    have hpos : ∀ p ∈ O, 0 < d s(p.1,p.2) := fun p hp => hlam.trans (far_facts hlam hM (hfar p (hOF hp))).1
    have hT : graphPairs Tb ⊆ Near ∪ (Far \ O) := by
      intro p hp
      have hs := mem_sdiff.1 (hTbE hp)
      rcases mem_union.1 hs.1 with hn | hf
      · exact mem_union_left _ hn
      · exact mem_union_right _ (mem_sdiff.2 ⟨hf,hs.2⟩)
    have hbp := long_even_pointwise hlam hM (c i) (c j) (hfar _ hp) hH hlong.le
      (rhoD_le_maxRad lam cfg i) (rhoD_le_maxRad lam cfg j)
    have hbp' : b (i.val,j.val) ≤ R ^ 2 / (17 * h) ^ 2 ∧
        b (i.val,j.val) ≤ r i ^ 2 * r j ^ 2 / d s(i.val,j.val) ^ 4 := by
      simpa only [b,r,d,R,cfg,paperEvenE,paperDistE,symmLift_mk,Matrix.cons_val_zero,Matrix.cons_val_one,ite_eq_right (hfar _ hp)] using hbp
    obtain ⟨F,hsp | ⟨hpT,hsp⟩⟩ := internal_omitted_source_product hX (hOF.trans hFar) hpar r d g hr hd hg hg1 hfg hpos
      Near Far (graphPairs Tb) (hFar.trans interPairs_subset_pairsOn) hOF hT b
      (fun _ => paperEvenE_nonneg _ _ _ _) (fun _ => paperEven_le_one hlam hM c _)
      (fun p hp => ite_eq_left (hnear p hp)) hR hH hRH hp hlong.le hbp'.1 hbp'.2
    · exact Or.inl ⟨F,(hbase.trans (mul_le_mul_of_nonneg_left hsp hC)).trans_eq (by ring)⟩
    · exact Or.inr ⟨F,(i.val,j.val),hpT,hlong,(hbase.trans (mul_le_mul_of_nonneg_left hsp hC)).trans_eq (by ring)⟩


/-- The same coefficient also covers every zero-support branch. -/
theorem internal_baseline_pointwise_all_uniform {χ : ℂ → ℝ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (X : Finset (Finset ℕ)) (hX : IsSubpartition X),
      ∀ {lam M h : ℝ}, 0 < lam → 1 ≤ M → lam ≤ h →
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
  obtain ⟨K,hK,hb⟩ := internal_baseline_pointwise_uniform hχ hβ
  refine ⟨K,hK,?_⟩
  intro X hX lam M h hlam hM hlh Near Far O hFar hconn hOF hpar Dz c
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
      · obtain ⟨Tb,hTb,hTE,ht⟩ := hb X hX hlam hM hlh Near Far O hFar hconn hOF hpar Dz c hn hf hc
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


end MultipoleBKT.ExpansionK.RouteOmitted

end
