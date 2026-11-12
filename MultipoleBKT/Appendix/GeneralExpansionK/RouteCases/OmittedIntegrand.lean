/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SupportBasics
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.OmittedGeometry

/-!
# The whole baseline integrand outside the short-edge domain

See Lemma A.7.
The baseline parity term keeps its common block, support and density factors.
The long-edge alternatives retain a quadratic minimum with one global odd
tail, or the distinguished even quartic kernel for the exterior integral.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SimpleGraph Peeling Multipole Hierarchical SmallIntegral Parity UpperBound.BoundedUpper

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

/-- The dipole density on the omitted short-edge domain. -/
noncomputable def omittedDensity (χ : ℂ → ℝ) (β lam h : ℝ) (Df : Finset (Sym2 ι))
    (c : ι → ℂ × ℂ) : ℝ :=
  (∏ i, pairDensity χ β lam (c i)) * cutInd h c * (1 - shortInd (17 * h) Df c)

/-- The literal baseline parity integrand omitted by the short-edge restriction. -/
noncomputable def omittedParityIntegrand (χ : ℂ → ℝ) (β lam M h : ℝ)
    (blk : ι → κ) (Dn Dz Df O : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) : ℝ :=
  clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c *
    ((∏ e ∈ O, gammaW β (dipoleInteraction χ lam) M lam c e) *
      ∏ e ∈ Df \ O, (alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)) *
    omittedDensity χ β lam h Df c

omit [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ] in
/-- The omitted density is nonnegative on its whole carrier. -/
theorem omittedDensity_nonneg (χ : ℂ → ℝ) (β lam h : ℝ) (Df : Finset (Sym2 ι))
    (c : ι → ℂ × ℂ) : 0 ≤ omittedDensity χ β lam h Df c :=
  mul_nonneg (mul_nonneg (prod_nonneg fun _ _ => (pairDensity_pos _ _ _ _).le) (cutInd_nonneg _ _))
    (sub_nonneg.2 (shortInd_le_one _ _ _))

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ] in
/-- The far even weight on a long edge retains its quartic kernel and also
admits the surplus-edge quadratic gain. -/
theorem long_even_pointwise {lam M R H : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (a b : ℂ × ℂ) (hf : ¬ MultipoleLinked M lam a b)
    (hH : 0 < H) (hd : H ≤ dipoleDist a b)
    (haR : rhoD lam a ≤ R) (hbR : rhoD lam b ≤ R) :
    ahat a b ^ 2 ≤ R ^ 2 / H ^ 2 ∧
      ahat a b ^ 2 ≤
        rhoD lam a ^ 2 * rhoD lam b ^ 2 / dipoleDist a b ^ 4 := by
  have hdist : 0 < dipoleDist a b := hH.trans_le hd
  have hden : 0 < dipoleDist a b * max (dipoleDist a b) (max ‖a.1-a.2‖ ‖b.1-b.2‖) :=
    mul_pos hdist (hdist.trans_le (le_max_left _ _))
  have hr0a : 0 ≤ rhoD lam a := (norm_nonneg _).trans (le_max_left _ _)
  have hr0b : 0 ≤ rhoD lam b := (norm_nonneg _).trans (le_max_left _ _)
  have hprod : ‖a.1-a.2‖ * ‖b.1-b.2‖ ≤ rhoD lam a * rhoD lam b :=
    mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) hr0a
  have hsq : dipoleDist a b ^ 2 ≤ dipoleDist a b * max (dipoleDist a b) (max ‖a.1-a.2‖ ‖b.1-b.2‖) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hdist.le
  have hA : ahat a b ≤ rhoD lam a * rhoD lam b / dipoleDist a b ^ 2 :=
    div_le_div₀ (mul_nonneg hr0a hr0b) hprod (pow_pos hdist 2) hsq
  have hRprod : rhoD lam a * rhoD lam b ≤ R ^ 2 := by
    rw [sq]
    exact mul_le_mul haR hbR hr0b (hr0a.trans haR)
  have hq : ahat a b ≤ R ^ 2 / H ^ 2 := hA.trans
    (div_le_div₀ (sq_nonneg R) hRprod (pow_pos hH 2) (pow_le_pow_left₀ hH.le hd 2))
  have hA0 := ahat_nonneg a b
  have hA1 := (far_facts hlam hM hf).2.2
  refine ⟨(by nlinarith : ahat a b ^ 2 ≤ ahat a b).trans hq,?_⟩
  have hh := pow_le_pow_left₀ hA0 hA 2
  convert hh using 1
  ring

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- Internal baseline bond comparison, before the original geometry is reduced. -/
theorem internal_baseline_product {χ : ℂ → ℝ} {β lam M K C : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hlam : 0 < lam) (hM : 1 ≤ M)
    (hK : partConst β C ≤ K) (hK0 : 0 ≤ K) (c : ι → ℂ × ℂ)
    (hw : ∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
      |dipoleInteraction χ lam (c i) (c j)| ≤ C * ahat (c i) (c j))
    (Df O : Finset (Sym2 ι)) (hO : O ⊆ Df) (G : ℝ) :
    |G * ((∏ e ∈ O, gammaW β (dipoleInteraction χ lam) M lam c e) *
      ∏ e ∈ Df \ O, (alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e))| ≤
      |G| * K ^ Df.card *
        ((∏ e ∈ O, absWeight (fun i => rhoD lam (c i)) (paperDistE c) (farInd M lam c) e) *
          ∏ e ∈ Df \ O, paperEvenE M lam c e) := by
  have hp := internal_bond_parts_geometric hβ hC hlam hM c hw
  have ha := internal_prod_bound O (gammaW β (dipoleInteraction χ lam) M lam c)
    (fun e => absWeight (fun i => rhoD lam (c i)) (paperDistE c) (farInd M lam c) e) (K := K)
    (fun e _ => ((hp e).1).trans ((mul_le_mul_of_nonneg_left (mixedOdd_le_absWeight hlam hM c e)
      (zero_le_one.trans (one_le_partConst hβ hC))).trans
      (mul_le_mul_of_nonneg_right hK (absWeight_nonneg
        (fun i => (norm_nonneg _).trans (le_max_left _ _))
        (fun e => by induction e using Sym2.ind with | h i j => exact dipoleDist_nonneg _ _)
        (farInd_nonneg c) e))))
  have hb := internal_prod_bound (Df \ O)
    (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
    (paperEvenE M lam c) (K := K) (fun e _ => ((hp e).2).trans
      ((mul_le_mul_of_nonneg_left (mixedEven_le_paperEven c e)
        (zero_le_one.trans (one_le_partConst hβ hC))).trans
        (mul_le_mul_of_nonneg_right hK (paperEvenE_nonneg _ _ _ _))))
  rw [abs_mul,abs_mul,abs_prod,abs_prod]
  calc _ ≤ |G| * ((K ^ O.card * ∏ e ∈ O, absWeight (fun i => rhoD lam (c i)) (paperDistE c) (farInd M lam c) e) *
      (K ^ (Df \ O).card * ∏ e ∈ Df \ O, paperEvenE M lam c e)) := by
        have h1 : 0 ≤ ∏ e ∈ O, absWeight (fun i => rhoD lam (c i)) (paperDistE c) (farInd M lam c) e := by
          apply prod_nonneg
          intro e _
          exact absWeight_nonneg (fun i => (norm_nonneg _).trans (le_max_left _ _))
            (fun e => by induction e using Sym2.ind with | h i j => exact dipoleDist_nonneg _ _) (farInd_nonneg c) e
        have h2 : 0 ≤ ∏ e ∈ Df \ O, paperEvenE M lam c e := prod_nonneg fun e _ => paperEvenE_nonneg _ _ _ _
        gcongr
       _ = _ := by
         rw [← card_sdiff_add_card_eq_card hO, pow_add]
         ring

section Source

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- The omitted integrand's spatial boundary. The even alternative keeps its
original long edge and quartic kernel, for the exterior integration. -/
def OmittedPointwise (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (lam M H : ℝ) (c : ℕ → ℂ × ℂ)
    (T : Finset (ℕ × ℕ)) (common term : ℝ) : Prop :=
  let cfg := fun i : X.biUnion id => c i
  let R := maxRad lam cfg
  let r := fun i => rhoD lam (c i)
  let d := paperDistE c
  let g := farInd M lam c
  let b := fun p : ℕ × ℕ => paperEvenE M lam c s(p.1,p.2)
  (∃ F : OddFamily hX hOX hpar r,
    |term| ≤ common * F.weight d g * min (R ^ 2 / H ^ 2) (globalTail R d F.edges) * ∏ p ∈ T, b p) ∨
  (∃ (F : OddFamily hX hOX hpar r) (p : ℕ × ℕ), p ∈ T ∧ H < d s(p.1,p.2) ∧
    |term| ≤ common * F.weight d g * globalTail R d F.edges *
      (r p.1 ^ 2 * r p.2 ^ 2 / d s(p.1,p.2) ^ 4) * ∏ q ∈ T.erase p, b q)

/-- Complete pointwise bound for the actual omitted baseline parity term on
its near, far and radial support. The separate vanishing identities remove
these support hypotheses when using the bound under the integral. -/
theorem baseline_omitted_pointwise {χ : ℂ → ℝ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hX : IsSubpartition X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {lam M h : ℝ}, 0 < lam → 1 ≤ M → lam ≤ h →
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
  intro lam M h hlam hM hlh Near Far O hFar hconn hOF hpar Dz c hnear hfar hcut
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

end Source

end MultipoleBKT.ExpansionK.RouteCases

end
