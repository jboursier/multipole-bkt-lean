/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.API

/-!
# Uniformity in the original cluster labels

See (A.63). Restrict the model controls on natural labels before
selecting a subpartition. This puts the coefficient before the original cluster data, as required by the statement of Lemma A.7.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

/-- Internal restriction of the frozen controls to the original finite labels. -/
theorem internal_frozen_controls_uniform {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (S : Finset ℕ) {N p₀ : ℕ} {lam M eps : ℝ}
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → 1 ≤ M →
      ∀ c : ℕ → ℂ × ℂ,
      InternalControls K (fun i : S => rhoD lam (c i))
        (fun i : S => routeFrozenRadius p₀ β lam eps V Z (c i))
        (mixedOddWeight M lam (fun i : S => c i)) (mixedEvenWeight M lam (fun i : S => c i))
        (gammaW β (routeFrozenInteraction χ p₀ β lam eps V Z) M lam (fun i : S => c i))
        (gammaW β (dipoleInteraction χ lam) M lam (fun i : S => c i))
        (fun e => alphaW β (routeFrozenInteraction χ p₀ β lam eps V Z) M lam (fun i : S => c i) e +
          linkIndE M lam (fun i : S => c i) e)
        (fun e => alphaW β (dipoleInteraction χ lam) M lam (fun i : S => c i) e +
          linkIndE M lam (fun i : S => c i) e)
        (intraRatio β (routeFrozenInteraction χ p₀ β lam eps V Z) (dipoleInteraction χ lam) (fun i : S => c i))
        (fun i : S => routeFrozenQuadratic p₀ β lam eps L V Z (c i))
        (fun i : S => routeFrozenBad p₀ β lam M eps V Z (c i)) := by
  obtain ⟨K,hK,hb⟩ := frozen_controls (ι := ℕ) (L := L) hχ hβ
  refine ⟨K,hK,?_⟩
  intro S N p₀ lam M eps V Z hlam hM c
  have H := hb (p₀ := p₀) (ε₀ := eps) V Z hlam hM c
  refine ⟨H.coefficient,fun i => H.radius_nonneg i,fun i => H.screening_pos i,?_,?_,?_,
    fun i => H.quadratic i,fun i => H.bad i,?_,?_,?_,fun i => H.quadratic_error i⟩
  · intro e
    induction e using Sym2.ind with
    | h i j => simpa only [gammaW,mixedOddWeight,ahatE,farInd,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.odd s(i.val,j.val)
  · intro e
    induction e using Sym2.ind with
    | h i j => simpa only [alphaW,linkIndE,mixedEvenWeight,ahatE,farInd,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.even s(i.val,j.val)
  · intro e
    induction e using Sym2.ind with
    | h i j => simpa only [intraRatio,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.intra s(i.val,j.val)
  · intro i j
    simpa only [gammaW,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.odd_error i.val j.val
  · intro i j
    simpa only [alphaW,linkIndE,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.even_error i.val j.val
  · intro i j
    simpa only [intraRatio,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.intra_error i.val j.val

/-- the complete frozen mixed boundary with its coefficient chosen before X. -/
theorem internal_frozen_boundary_uniform {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
      {N p₀ : ℕ} {lam M eps h : ℝ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      0 < lam → 1 ≤ M → ∀ (Near Far O : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
      (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      MixedBoundary hX (hOF.trans hFar) hpar χ β lam M h K (Real.exp (β * cbK hχ))
        (routeFrozenInteraction χ p₀ β lam eps V Z) (routeFrozenRadius p₀ β lam eps V Z)
        (routeFrozenQuadratic p₀ β lam eps L V Z) (routeFrozenBad p₀ β lam M eps V Z)
        Near Far Dz c := by
  obtain ⟨K₀,hK₀,hcontrols⟩ := internal_frozen_controls_uniform (L := L) hχ hβ
  obtain ⟨Ce,hCe,he⟩ := routeFrozen_interaction_bounds hχ
  obtain ⟨Cv,hCv,hv⟩ := BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ
  obtain ⟨Ke,hKe,href⟩ := internal_refined_even (ι := ℕ) (D := Ce) hβ (add_nonneg hCe.le hCv)
  refine ⟨K₀+Ke,by linarith,?_⟩
  intro X hX N p₀ lam M eps h V Z hlam hM Near Far O hFar hconn hOF hpar Dz c
  have H := (hcontrols (X.biUnion id) (p₀ := p₀) (eps := eps) V Z hlam hM c).enlarge
    (le_add_of_nonneg_right hKe)
  have hpoint := href hlam hM (routeFrozenInteraction χ p₀ β lam eps V Z)
    (routeFrozenRadius p₀ β lam eps V Z ∘ c) c
    (fun i => hlam.trans_le (routeFrozenRadius_lower p₀ β lam eps V Z (c i)).1)
    (fun i j hf => by
      have hw := (he (p₀ := p₀) (β := β) (ε₀ := eps) V Z hlam hM (c i) (c j)).2 hf
      have hw₀ := hv lam hlam M hM (c i) (c j) hf
      nlinarith)
    (fun i j => (he (p₀ := p₀) (β := β) (ε₀ := eps) V Z hlam hM (c i) (c j)).1)
  apply internal_model_boundary hχ hβ hlam hM hX Near Far hFar hconn hOF hpar Dz c
    (routeFrozenInteraction χ p₀ β lam eps V Z) (routeFrozenRadius p₀ β lam eps V Z)
    (routeFrozenQuadratic p₀ β lam eps L V Z) (routeFrozenBad p₀ β lam M eps V Z) H
  intro i j
  have hp := hpoint i.val j.val
  simp only [alphaW,linkIndE,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] at hp ⊢
  exact hp.trans (mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (markedEvenE_nonneg lam (fun i : X.biUnion id => c i) s(i,j))))

/-- (A.63) for every actual frozen mixed term, with the bad-point coefficient
fixed before epsilon and the frozen data. Both ordinary and marked trees enter. -/
theorem frozen_mixed_integral_uniform {χ : ℂ → ℝ} {β L M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ (X : Finset (Finset ℕ)) (_hX : IsSubpartition X) (_hXne : X.Nonempty),
      (X.biUnion id).card = k → ∀ {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      UpperBound.badPointsOn p₀ β lam M eps V Z = V →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (_hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (_hOF : O ⊆ Far) (_hpar : IsParityPair X O ∅)
        (Dz : Finset (Sym2 (X.biUnion id))) (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id)),
      P ≠ (∅,∅,∅,∅,∅) → P ∈ fiveSubsets (symOf (X.biUnion id) O)
        (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) (RouteCases.intraEdges (Limits.blockOf X)) univ →
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |mixedIntegrand χ β lam M (eps * truncationScale p₀ β lam)
          (routeFrozenInteraction χ p₀ β lam eps V Z) (routeFrozenQuadratic p₀ β lam eps L V Z)
          (routeFrozenBad p₀ β lam M eps V Z) (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
          (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) c P|) ≤
        ENNReal.ofReal (lam ^ ((2-β)*(X.biUnion id).card) *
          (C * eps ^ (-2 : ℝ) * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * eps ^ (alphaExponent β * (X.biUnion id).card) * V.card)) := by
  obtain ⟨K,hK,hpoint⟩ := internal_frozen_boundary_uniform (L := L) hχ (by linarith : 0 ≤ β)
  obtain ⟨A,hA,hint⟩ := frozen_spatialEnvelope_bound (M := M) hχ hβ p₀ hk
  let Q := mixedCoefficient (Real.exp (β * cbK hχ)) K k
  have hQ : 0 < Q := mul_pos (pow_pos (Real.exp_pos _) _) (pow_pos (lt_of_lt_of_le zero_lt_one hK) _)
  refine ⟨(Q*17)*A,by positivity,?_⟩
  intro eps lam hlam hle heps hM3 X hX hXne hcard N V Z hV Near Far O hFar hconn hOF hpar Dz P hne hP
  have hnX : Nonempty (X.biUnion id) := by
    apply Fintype.card_pos_iff.mp
    rw [Fintype.card_coe,hcard]
    omega
  have hM : 1 ≤ M := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)).trans hM3
  let h := eps * truncationScale p₀ β lam
  let F (c : X.biUnion id → ℂ × ℂ) (i : X.biUnion id) := ENNReal.ofReal ((rhoD lam (c i) ^ 2)⁻¹) *
    rootM p₀ β lam M eps V Z ((c i).1-(c i).2) (c i).2
  have hp (c : X.biUnion id → ℂ × ℂ) (hc : c ∈ boxConfig (X.biUnion id) N) :
      ENNReal.ofReal |mixedIntegrand χ β lam M h (routeFrozenInteraction χ p₀ β lam eps V Z)
        (routeFrozenQuadratic p₀ β lam eps L V Z) (routeFrozenBad p₀ β lam M eps V Z)
        (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far)
        (symOf (X.biUnion id) O) c P| ≤
        (ENNReal.ofReal Q * 17) * spatialEnvelope χ β M lam h F c := by
    let ext := extendConfig (X.biUnion id) c
    have he : (fun i : X.biUnion id => ext i) = c := by funext i; exact extendConfig_coe c i
    have H := hpoint hX (p₀ := p₀) (eps := eps) (h := h) V Z hlam hM Near Far O hFar hconn hOF hpar Dz ext
    have hb := internal_boundary_envelope hlam hM (zero_le_one.trans hK) (Real.exp_nonneg _)
      hOF H P hne hP F 17 (fun i => by
        have hr := frozen_sourceRoot_le (p₀ := p₀) (β := β) (M := M) (eps := eps)
          V Z (c i) hlam (rhoD_le_maxRad lam c i)
        rw [indicator_of_mem (((Set.mem_univ_pi.mp hc) i).2),Pi.one_apply,one_mul] at hr
        simpa only [he,show ext i = c i from extendConfig_coe c i] using hr)
    rw [he] at hb
    exact hb.trans (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (by
      simpa only [Fintype.card_coe,hcard] using mixedCoefficient_le (Real.exp_nonneg _) hK
        (symOf (X.biUnion id) O) (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) P)) le_rfl) le_rfl)
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) N, (ENNReal.ofReal Q * 17) * spatialEnvelope χ β M lam h F c :=
      setLIntegral_mono' (measurableSet_boxConfig N) hp
    _ ≤ ∫⁻ c, (ENNReal.ofReal Q * 17) * spatialEnvelope χ β M lam h F c := setLIntegral_le_lintegral _ _
    _ = (ENNReal.ofReal Q * 17) * ∫⁻ c, spatialEnvelope χ β M lam h F c :=
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
    _ ≤ (ENNReal.ofReal Q * 17) * ENNReal.ofReal (lam ^ ((2-β)*k) *
        (A * eps ^ (-2 : ℝ) * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
          A * eps ^ (alphaExponent β * k) * V.card)) :=
      mul_le_mul' le_rfl (hint eps lam hlam hle heps hM3 (X.biUnion id)
        (by rw [Fintype.card_coe,hcard]) V Z hV)
    _ = _ := by
      rw [hcard]
      rw [show (17 : ℝ≥0∞) = ENNReal.ofReal (17 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul hQ.le,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end MultipoleBKT.ExpansionK.RouteAssembly

end
