/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.API

/-!
# The actual baseline parity term with its full original forest

See (A.53)
and Step 4 of the proof of Lemma A.7.
The baseline parity integrand is reduced by the separate original peelings.
The global odd tail is retained through the radius allocation.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases
open RouteSpatial
open scoped Classical ENNReal

/-- The actual baseline term is below one normalized unbounded tree.
All near, far and block support branches are handled on the full carrier. -/
theorem internal_baseline_source_uniform {χ : ℂ → ℝ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (X : Finset (Finset ℕ)) (_hX : IsSubpartition X)
      [Nonempty (X.biUnion id)] {lam M : ℝ}, 0 < lam → 1 ≤ M →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (_hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (_hOF : O ⊆ Far) (_hpar : IsParityPair X O ∅)
        (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      let cfg := fun i : X.biUnion id => c i
      baselineParityIntegrand χ β lam M (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
        (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) cfg = 0 ∨
      ∃ (T : SimpleGraph (X.biUnion id)), T.IsTree ∧
        ∃ (A E N : Finset (Sym2 (X.biUnion id))), A ∪ (E ∪ N) = T.edgeFinset ∧
          Disjoint A (E ∪ N) ∧ Disjoint E N ∧
          ENNReal.ofReal |baselineParityIntegrand χ β lam M (Limits.blockOf X)
            (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) cfg| ≤
            ENNReal.ofReal (Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) *
              K ^ (symOf (X.biUnion id) Far).card) * jointTreeDensity χ β M lam A E N cfg := by
  obtain ⟨Cv,hCv,hv⟩ := BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ
  let K := partConst β Cv
  have hK : 1 ≤ K := one_le_partConst hβ hCv
  refine ⟨K,hK,?_⟩
  intro X hX _ lam M hlam hM Near Far O hFar hconn hOF hpar Dz c
  let cfg := fun i : X.biUnion id => c i
  let Dn := symOf (X.biUnion id) Near
  let Df := symOf (X.biUnion id) Far
  let OS := symOf (X.biUnion id) O
  let S := clusterSupport M lam (Limits.blockOf X) Dn Dz cfg
  let G := clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam (Limits.blockOf X) Dn Dz cfg
  let r := fun i => rhoD lam (c i)
  let d := paperDistE c
  let g := farInd M lam c
  have hG := clusterG_baseline_common (M := M) hχ hβ hlam (Limits.blockOf X) Dn Dz cfg
  by_cases hS : S = 0
  · apply Or.inl
    have hG' : |G| ≤ Real.exp (β * cbK hχ) ^ (Fintype.card (X.biUnion id) * Fintype.card (X.biUnion id)) * S := hG
    rw [hS,mul_zero] at hG'
    have hz : G = 0 := abs_nonpos_iff.1 hG'
    change G * _ * _ = 0
    rw [hz,zero_mul,zero_mul]
  by_cases hfar : ∀ e ∈ Df, FarE M lam cfg e
  swap
  · push Not at hfar
    obtain ⟨e,he,hl⟩ := hfar
    exact Or.inl (baselineParity_zero_linked χ β lam M _ _ _ _ _ cfg he hl)
  apply Or.inr
  obtain ⟨Q,hnear⟩ := exists_linked_nearTreeFamily (Limits.blockOf X) M lam cfg
    (connected_of_clusterSupport_ne_zero M lam (Limits.blockOf X) Dn Dz cfg hS)
  have hnearDn : ∀ p ∈ Near, MultipoleLinked M lam (c p.1) (c p.2) := by
    intro p hp
    by_contra hl
    have hh : S = 0 := by
      unfold S clusterSupport
      have hz : linkIndE M lam cfg (s(⟨p.1,(mem_pairsOn.1 (interPairs_subset_pairsOn ((mem_relEdgeSets₀.1 hconn).1 (mem_union_left _ hp)))).1⟩,
          ⟨p.2,(mem_pairsOn.1 (interPairs_subset_pairsOn ((mem_relEdgeSets₀.1 hconn).1 (mem_union_left _ hp)))).2.1⟩)) = 0 := ite_eq_right hl
      rw [prod_eq_zero (mem_symOf.2 ⟨_,_,(mem_pairsOn.1 (interPairs_subset_pairsOn ((mem_relEdgeSets₀.1 hconn).1 (mem_union_left _ hp)))).2.2,hp,rfl⟩) hz,mul_zero]
    exact hS hh
  have hfarp : ∀ p ∈ Far, ¬ MultipoleLinked M lam (c p.1) (c p.2) := by
    intro p hp
    have hs := mem_pairsOn.1 (interPairs_subset_pairsOn (hFar hp))
    exact hfar _ (mem_symOf.2 ⟨⟨p.1,hs.1⟩,⟨p.2,hs.2.1⟩,hs.2.2,hp,rfl⟩)
  have hr : ∀ i, 0 ≤ r i := fun i => (rhoD_pos hlam (c i)).le
  have hd : ∀ e, 0 ≤ d e := by intro e; induction e using Sym2.ind with | h i j => exact dipoleDist_nonneg _ _
  have hg := farInd_nonneg (M := M) (lam := lam) c
  have hg1 := farInd_le_one (M := M) (lam := lam) c
  have hmin : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2) := by
    intro p hp
    exact (le_mul_of_one_le_left (le_min (hr _) (hr _)) hM).trans (lt_of_not_ge (hfarp p (hOF hp))).le
  have hpos : ∀ p ∈ O, 0 < d s(p.1,p.2) := fun p hp =>
    hlam.trans (far_facts hlam hM (hfarp p (hOF hp))).1
  obtain ⟨P⟩ := exists_source_peeling hX (hOF.trans hFar) hpar r d
  let F := P.family
  have hodd := (source_odd_skeleton_drop hX (hOF.trans hFar) hpar r d g hr hd hg hg1 hmin).trans
    (SourcePeeling.family_tail hX (hOF.trans hFar) hpar r d g hr hd hg hg1 hpos P
      (fun i hi => rhoD_le_maxRad lam cfg ⟨i,hi⟩))
  obtain ⟨-,-,Tb,hTb,hTE⟩ := source_skeletons_and_even_tree hX hconn (hOF.trans subset_union_right) hpar
  let E := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
  let N := nearForest (Limits.blockOf X) (fun S => (Q S).val)
  let A := oddEdges F
  let T : SimpleGraph (X.biUnion id) := fromEdgeSet ((N ∪ (A ∪ E) : Finset _) : Set _)
  obtain ⟨hT,hTedges,hNA,hAE,-⟩ := source_family_structure hX (hOF.trans hFar) hpar r F Tb hTb Q
  refine ⟨T,hT,A,E,N,?_,Finset.disjoint_union_right.2 ⟨hAE,(Finset.disjoint_union_right.1 hNA).1.symm⟩,
    (Finset.disjoint_union_right.1 hNA).2.symm,?_⟩
  · ext e
    have hh : e ∈ T.edgeSet ↔ e ∈ N ∨ e ∈ A ∨ e ∈ E := by
      simpa only [T,N,A,E,mem_edgeFinset,Finset.mem_union] using Finset.ext_iff.mp hTedges e
    simp only [mem_edgeFinset,Finset.mem_union]
    tauto

  have hraw := internal_baseline_product hβ hCv hlam hM (K := K) le_rfl (zero_le_one.trans hK) cfg
    (fun i j hf => hv lam hlam M hM (cfg i) (cfg j) hf) Df OS (symOf_mono hOF) G
  have heven := internal_even_drop_near (Far \ O) Near (graphPairs Tb) (by
    intro p hp
    have hs := mem_sdiff.1 (hTE hp)
    rcases mem_union.1 hs.1 with hn | hf
    · exact mem_union_left _ hn
    · exact mem_union_right _ (mem_sdiff.2 ⟨hf,hs.2⟩))
    (fun p : ℕ × ℕ => paperEvenE M lam c s(p.1,p.2))
    (fun _ => paperEvenE_nonneg _ _ _ _) (fun _ => paperEven_le_one hlam hM c _)
    (fun p hp => ite_eq_left (hnearDn p hp))
  have ho : (∏ e ∈ OS, absWeight (fun i => rhoD lam (cfg i)) (paperDistE cfg) (farInd M lam cfg) e) =
      ∏ p ∈ O, absWeight r d g s(p.1,p.2) := by
    rw [← source_product ((hOF.trans hFar).trans interPairs_subset_pairsOn) (absWeight r d g)]
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with | h i j => rfl
  have hb : (∏ e ∈ Df \ OS, paperEvenE M lam cfg e) = ∏ p ∈ Far \ O, paperEvenE M lam c s(p.1,p.2) := by
    rw [← symOf_sdiff]
    exact (prod_symOf ((Finset.sdiff_subset.trans hFar).trans interPairs_subset_pairsOn) _ _ (fun _ _ _ => rfl)).symm
  have hEb : (∏ p ∈ graphPairs Tb, paperEvenE M lam c s(p.1,p.2)) = ∏ e ∈ E, paperEvenE M lam cfg e := by
    rw [graphPairs_eq_edgesOf]
    exact UpperBound.BoundedUpper.prod_pairs_eq_prod_edgeFinset (by
      exact (edgesOf_subset_pairsOn Tb).trans (pairsOn_mono (by
        rw [biUnion_coarsen (fun Y hY => subset_of_mem_relComponents (oddComponents_subset O hY))]))) (fun i j : ℕ => paperEvenE M lam c s(i,j))
        (fun i j => congrArg (paperEvenE M lam c) Sym2.eq_swap)
  rw [ho,hb] at hraw
  rw [hEb] at heven
  have hn := uncut_family_normalized hX (hOF.trans hFar) hpar hlam hM c F Tb hTb Q hnear
  let C := Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) * K ^ Df.card
  have hC : 0 ≤ C := mul_nonneg (pow_nonneg (Real.exp_nonneg _) _) (pow_nonneg (zero_le_one.trans hK) _)
  have hbase : |baselineParityIntegrand χ β lam M (Limits.blockOf X) Dn Dz Df OS cfg| ≤
      C * S * (F.weight d g * globalTail (maxRad lam cfg) d F.edges * ∏ e ∈ E, paperEvenE M lam cfg e) *
        ∏ i, pairDensity χ β lam (cfg i) := by
    unfold baselineParityIntegrand
    rw [abs_mul,abs_of_nonneg (prod_nonneg fun _ _ => (pairDensity_pos _ _ _ _).le)]
    apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _ => (pairDensity_pos _ _ _ _).le)
    refine hraw.trans ?_
    have hodd0 : 0 ≤ F.weight d g * globalTail (maxRad lam cfg) d F.edges :=
      mul_nonneg (F.weight_nonneg _ _ hg) (globalTail_nonneg _ _ _)
    have heven0 : 0 ≤ ∏ p ∈ Far \ O, paperEvenE M lam c s(p.1,p.2) := prod_nonneg fun _ _ => paperEvenE_nonneg _ _ _ _
    have hm := mul_le_mul hodd heven heven0 hodd0
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right hG (pow_nonneg (zero_le_one.trans hK) Df.card)) hm
      (mul_nonneg (prod_nonneg fun _ _ => absWeight_nonneg hr hd hg _) heven0)
      (mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_nonneg _) _) (clusterSupport_nonneg _ _ _ _ _ _))
        (pow_nonneg (zero_le_one.trans hK) Df.card))
    simp only [Fintype.card_coe] at hh
    convert hh using 1
    dsimp only [C]
    ring
  have hremove : |baselineParityIntegrand χ β lam M (Limits.blockOf X) Dn Dz Df OS cfg| ≤
      C * (F.weight d g * globalTail (maxRad lam cfg) d F.edges * ∏ e ∈ E, paperEvenE M lam cfg e) *
        ∏ i, pairDensity χ β lam (cfg i) := by
    refine hbase.trans ?_
    have hS1 := clusterSupport_le_one M lam (Limits.blockOf X) Dn Dz cfg
    have hp0 : 0 ≤ F.weight d g * globalTail (maxRad lam cfg) d F.edges * ∏ e ∈ E, paperEvenE M lam cfg e :=
      mul_nonneg (mul_nonneg (F.weight_nonneg _ _ hg) (globalTail_nonneg _ _ _)) (prod_nonneg fun _ _ => paperEvenE_nonneg _ _ _ _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hS1 hC) hp0)
      (prod_nonneg fun _ _ => (pairDensity_pos _ _ _ _).le)
  refine (ENNReal.ofReal_le_ofReal hremove).trans ?_
  rw [ENNReal.ofReal_mul' (prod_nonneg fun _ _ => (pairDensity_pos _ _ _ _).le),ENNReal.ofReal_mul hC]
  calc
    _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal (radialFactor lam cfg) * treeProfile M lam A E N cfg)) *
        ENNReal.ofReal (∏ i, pairDensity χ β lam (cfg i)) :=
      mul_le_mul' (mul_le_mul' (le_refl (ENNReal.ofReal C)) hn) le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => (pairDensity_pos _ _ _ _).le)]
      unfold jointTreeDensity
      ring

/-- (A.64) for the actual baseline parity term. This is the common
baseline of both concrete models. The coefficient precedes lambda and all
original near and far graph choices. -/
theorem caseF_baseline_integral_uniform {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ k : ℕ)
    (hkp : ((k+2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (X : Finset (Finset ℕ)) (_hX : IsSubpartition X),
      (X.biUnion id).card = k+2 → ∀ lam : ℝ, 0 < lam → lam ≤ eps →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (_hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (_hOF : O ⊆ Far) (_hpar : IsParityPair X O ∅)
        (Dz : Finset (Sym2 (X.biUnion id))) (n : ℕ),
      (∫⁻ c in boxConfig (X.biUnion id) n ∩
          {c : X.biUnion id → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
        ENNReal.ofReal |baselineParityIntegrand χ β lam M (Limits.blockOf X)
          (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) c|) ≤
        ENNReal.ofReal (C * n * lam ^ ((2-β)*(k+2)) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  obtain ⟨K,hK,hpoint⟩ := internal_baseline_source_uniform hχ (by linarith : 0 ≤ β)
  let Q := mixedCoefficient (Real.exp (β * cbK hχ)) K (k+2)
  have hQ : 0 < Q := mul_pos (pow_pos (Real.exp_pos _) _) (pow_pos (lt_of_lt_of_le zero_lt_one hK) _)
  intro eps heps heps1
  obtain ⟨A,hA,hbound⟩ := caseF_jointEnvelope_bound hχ hβ hM p₀ k hkp eps heps heps1
  refine ⟨Q*A,mul_pos hQ hA,?_⟩
  intro X hX hcard lam hlam hle Near Far O hFar hconn hOF hpar Dz n
  have hnX : Nonempty (X.biUnion id) := Fintype.card_pos_iff.1 (by rw [Fintype.card_coe,hcard]; omega)
  have hp (c : X.biUnion id → ℂ × ℂ) :
      ENNReal.ofReal |baselineParityIntegrand χ β lam M (Limits.blockOf X)
        (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) c| ≤
        ENNReal.ofReal Q * jointEnvelope χ β M lam c := by
    let ext := extendConfig (X.biUnion id) c
    have he : (fun i : X.biUnion id => ext i) = c := by funext i; exact extendConfig_coe c i
    have hh := hpoint X hX hlam hM Near Far O hFar hconn hOF hpar Dz ext
    rw [he] at hh
    rcases hh with hz | ⟨T,hT,Ao,E,N,hpart,hdis,hEN,hh⟩
    · rw [hz,abs_zero,ENNReal.ofReal_zero]
      exact bot_le
    · let s : JointShape (X.biUnion id) := ⟨T,Ao,E,N,hT,hpart,hdis,hEN⟩
      have hcoef : Real.exp (β * cbK hχ) ^ ((X.biUnion id).card * (X.biUnion id).card) *
          K ^ (symOf (X.biUnion id) Far).card ≤ Q := by
        dsimp only [Q,mixedCoefficient]
        rw [hcard]
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.exp_nonneg _) _)
        apply pow_le_pow_right₀ hK
        have hc := card_le_univ (symOf (X.biUnion id) Far)
        rw [Sym2.card,Fintype.card_coe,hcard] at hc
        omega
      exact hh.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) (le_jointEnvelope χ β M lam s c))
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) n ∩
        {c : X.biUnion id → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
          ENNReal.ofReal Q * jointEnvelope χ β M lam c := lintegral_mono hp
    _ = ENNReal.ofReal Q * ∫⁻ c in boxConfig (X.biUnion id) n ∩
        {c : X.biUnion id → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
          jointEnvelope χ β M lam c := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Q * ENNReal.ofReal (A * n * lam ^ ((2-β)*(k+2)) * truncationScale p₀ β lam ^ (-2 : ℝ)) :=
      mul_le_mul' le_rfl (hbound lam hlam hle (X.biUnion id) (by rw [Fintype.card_coe,hcard]) n)
    _ = _ := by rw [← ENNReal.ofReal_mul hQ.le]; congr 1; ring

end MultipoleBKT.ExpansionK.RouteAssembly

end
