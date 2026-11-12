/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.Integral

/-!
# Omitted integration after reversal averaging

See (A.51) and Lemma A.7.
The original averaged baseline term expands over the cut-even odd subsets.
Every such subset has the same finite omitted envelope.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

/-- The original averaged cluster term with its omitted-domain density. -/
noncomputable def omittedAverage {W B : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]
    [Fintype B] [DecidableEq B] (χ : ℂ → ℝ) (β lam M h : ℝ) (blk : W → B)
    (Dn Dz Df : Finset (Sym2 W)) (c : W → ℂ × ℂ) : ℝ :=
  ((∑ A : Finset B, clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df
    (flipCfg (blockLabels blk A) c)) / 2^Fintype.card B) * omittedDensity χ β lam h Df c

/-- Exact reversal cancellation on the omitted domain. Every retained odd subset
has coefficient one, as in the written parity expansion. -/
theorem omittedAverage_eq {W B : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]
    [Fintype B] [DecidableEq B] {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    (β lam h : ℝ) {M : ℝ} (hM : 1 ≤ M) (blk : W → B)
    (Dn Dz Df : Finset (Sym2 W)) (c : W → ℂ × ℂ) :
    omittedAverage χ β lam M h blk Dn Dz Df c =
      ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
        omittedParityIntegrand χ β lam M h blk Dn Dz Df O c := by
  unfold omittedAverage
  simp_rw [clusterQ_flip (ψ := fun _ => 1) hM (fun d e => Limits.dipoleInteraction_swap_left d e hχ lam)
    (fun d e => Limits.dipoleInteraction_swap_right d e hχ lam) (fun _ => rfl)]
  rw [← mul_sum,mul_div_assoc,avg_product_eq_cutEven,mul_sum,sum_mul]
  apply sum_congr rfl
  intro O _
  rfl

variable {X : Finset (Finset ℕ)}

/-- The averaged original omitted cluster integrand has its full configuration
bound after the parity sum. The coefficient precedes epsilon and lambda. -/
theorem averaged_omitted_integral {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ (Near Far : Finset (ℕ × ℕ)), Far ⊆ interPairs X → Near ∪ Far ∈ relEdgeSets₀ X →
      ∀ (Dz : Finset (Sym2 (X.biUnion id))) (N : ℕ),
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |omittedAverage χ β lam M (eps*truncationScale p₀ β lam)
          (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c|) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*N*lam^((2-β)*(X.biUnion id).card)*
          truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨Q,hQ,hpoint⟩ := omitted_source_envelope hχ (by linarith : 0 ≤ β) k
  obtain ⟨A,hA,hint⟩ := omittedEnvelope_bound hχ hβ hM p₀ hk
  let D : ℝ := (2 : ℝ)^((k+1).choose 2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*Q*A,by positivity,?_⟩
  intro X hX hXne hcard
  have hnX : Nonempty (X.biUnion id) := by
    obtain ⟨S,hS⟩ := hXne
    obtain ⟨i,hi⟩ := hX.1 S hS
    exact ⟨⟨i,mem_biUnion.2 ⟨S,hS,hi⟩⟩⟩
  intro eps lam hlam hle heps Near Far hFar hconn Dz N
  let h := eps*truncationScale p₀ β lam
  have heps0 : 0 < eps := hlam.trans_le hle
  have hlh : lam ≤ h := hle.trans (le_mul_of_one_le_right heps0.le
    (Appendix.one_le_truncationScale hβ hlam (hle.trans heps)))
  let S := (symOf (X.biUnion id) Far).powerset.filter (CutEven (Sym2.map (Limits.blockOf X)))
  have hc : (S.card : ℝ) ≤ D := by
    have hh : S.card ≤ Fintype.card (Finset (Sym2 (X.biUnion id))) := card_le_univ S
    rw [Fintype.card_finset,Sym2.card,Fintype.card_coe] at hh
    dsimp only [D]
    rw [hcard] at hh
    exact_mod_cast hh
  have hp (c : X.biUnion id → ℂ × ℂ) :
      ENNReal.ofReal |omittedAverage χ β lam M h (Limits.blockOf X)
        (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c| ≤
        ENNReal.ofReal (D*Q) * omittedEnvelope χ β M lam h c := by
    rw [omittedAverage_eq hχ β lam h hM]
    refine (ENNReal.ofReal_le_ofReal (abs_sum_le_sum_abs _ _)).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
    have hterm (O : Finset (Sym2 (X.biUnion id))) (hO : O ∈ S) :
        ENNReal.ofReal |omittedParityIntegrand χ β lam M h (Limits.blockOf X)
          (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) O c| ≤
          ENNReal.ofReal Q * omittedEnvelope χ β M lam h c := by
      have hs := actual_source_odd hX hFar (mem_powerset.1 (mem_filter.1 hO).1) (mem_filter.1 hO).2
      have ht := hpoint X hX hcard hlam hM hlh Near Far (sourcePairs O) hFar hconn hs.1 hs.2.2 Dz c
      simpa only [hs.2.1] using ht
    calc
      _ ≤ ∑ _O ∈ S, ENNReal.ofReal Q * omittedEnvelope χ β M lam h c := sum_le_sum hterm
      _ = (S.card : ℝ≥0∞) * (ENNReal.ofReal Q * omittedEnvelope χ β M lam h c) := by
        rw [sum_const,nsmul_eq_mul]
      _ ≤ ENNReal.ofReal D * (ENNReal.ofReal Q * omittedEnvelope χ β M lam h c) :=
        mul_le_mul' (by rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hc) le_rfl
      _ = _ := by rw [ENNReal.ofReal_mul hD.le,mul_assoc]
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) N, ENNReal.ofReal (D*Q) * omittedEnvelope χ β M lam h c :=
      lintegral_mono hp
    _ = ENNReal.ofReal (D*Q) * ∫⁻ c in boxConfig (X.biUnion id) N, omittedEnvelope χ β M lam h c :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (D*Q) * ENNReal.ofReal (A*eps^(-2:ℝ)*N*lam^((2-β)*(X.biUnion id).card)*
        truncationScale p₀ β lam^(-2:ℝ)) :=
      mul_le_mul' le_rfl (by simpa only [hcard] using hint eps lam hlam hle heps (X.biUnion id) (by rw [Fintype.card_coe,hcard]) N)
    _ = _ := by rw [← ENNReal.ofReal_mul (mul_nonneg hD.le hQ.le)]; congr 1; ring

/-- Exact reversal sum for arbitrary fixed positive epsilon, with a coefficient before `X`. -/
theorem averaged_omitted_integral_at {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (k : ℕ) (hk : 1 ≤ k) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ (Near Far : Finset (ℕ × ℕ)), Far ⊆ interPairs X → Near ∪ Far ∈ relEdgeSets₀ X →
      ∀ (Dz : Finset (Sym2 (X.biUnion id))) (N : ℕ),
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |omittedAverage χ β lam M (eps*truncationScale p₀ β lam)
          (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c|) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*N*lam^((2-β)*(X.biUnion id).card)*
          truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨Q,hQ,hpoint⟩ := omitted_source_envelope hχ (by linarith : 0 ≤ β) k
  obtain ⟨A,hA,hint⟩ := omittedEnvelope_bound_at hχ hβ hM p₀ hk heps
  let D : ℝ := (2 : ℝ)^((k+1).choose 2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*Q*A,by positivity,?_⟩
  intro X hX hXne hcard
  have hnX : Nonempty (X.biUnion id) := by
    obtain ⟨S,hS⟩ := hXne
    obtain ⟨i,hi⟩ := hX.1 S hS
    exact ⟨⟨i,mem_biUnion.2 ⟨S,hS,hi⟩⟩⟩
  intro lam hlam hle hlam1 Near Far hFar hconn Dz N
  let h := eps*truncationScale p₀ β lam
  have heps0 : 0 < eps := hlam.trans_le hle
  have hlh : lam ≤ h := hle.trans (le_mul_of_one_le_right heps0.le
    (Appendix.one_le_truncationScale hβ hlam hlam1))
  let S := (symOf (X.biUnion id) Far).powerset.filter (CutEven (Sym2.map (Limits.blockOf X)))
  have hc : (S.card : ℝ) ≤ D := by
    have hh : S.card ≤ Fintype.card (Finset (Sym2 (X.biUnion id))) := card_le_univ S
    rw [Fintype.card_finset,Sym2.card,Fintype.card_coe] at hh
    dsimp only [D]
    rw [hcard] at hh
    exact_mod_cast hh
  have hp (c : X.biUnion id → ℂ × ℂ) :
      ENNReal.ofReal |omittedAverage χ β lam M h (Limits.blockOf X)
        (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c| ≤
        ENNReal.ofReal (D*Q) * omittedEnvelope χ β M lam h c := by
    rw [omittedAverage_eq hχ β lam h hM]
    refine (ENNReal.ofReal_le_ofReal (abs_sum_le_sum_abs _ _)).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
    have hterm (O : Finset (Sym2 (X.biUnion id))) (hO : O ∈ S) :
        ENNReal.ofReal |omittedParityIntegrand χ β lam M h (Limits.blockOf X)
          (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) O c| ≤
          ENNReal.ofReal Q * omittedEnvelope χ β M lam h c := by
      have hs := actual_source_odd hX hFar (mem_powerset.1 (mem_filter.1 hO).1) (mem_filter.1 hO).2
      have ht := hpoint X hX hcard hlam hM hlh Near Far (sourcePairs O) hFar hconn hs.1 hs.2.2 Dz c
      simpa only [hs.2.1] using ht
    calc
      _ ≤ ∑ _O ∈ S, ENNReal.ofReal Q * omittedEnvelope χ β M lam h c := sum_le_sum hterm
      _ = (S.card : ℝ≥0∞) * (ENNReal.ofReal Q * omittedEnvelope χ β M lam h c) := by
        rw [sum_const,nsmul_eq_mul]
      _ ≤ ENNReal.ofReal D * (ENNReal.ofReal Q * omittedEnvelope χ β M lam h c) :=
        mul_le_mul' (by rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hc) le_rfl
      _ = _ := by rw [ENNReal.ofReal_mul hD.le,mul_assoc]
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) N, ENNReal.ofReal (D*Q) * omittedEnvelope χ β M lam h c :=
      lintegral_mono hp
    _ = ENNReal.ofReal (D*Q) * ∫⁻ c in boxConfig (X.biUnion id) N, omittedEnvelope χ β M lam h c :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (D*Q) * ENNReal.ofReal (A*eps^(-2:ℝ)*N*lam^((2-β)*(X.biUnion id).card)*
        truncationScale p₀ β lam^(-2:ℝ)) :=
      mul_le_mul' le_rfl (by simpa only [hcard] using hint lam hlam hle hlam1 (X.biUnion id) (by rw [Fintype.card_coe,hcard]) N)
    _ = _ := by rw [← ENNReal.ofReal_mul (mul_nonneg hD.le hQ.le)]; congr 1; ring

end MultipoleBKT.ExpansionK.RouteOmitted

end
