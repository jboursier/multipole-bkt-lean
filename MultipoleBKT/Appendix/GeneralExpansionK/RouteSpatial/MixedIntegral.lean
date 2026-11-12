/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.BoundaryEnvelope

/-!
# The actual mixed-term integral, (A.63)

See Step 3 of
the proof of Lemma A.7. The pointwise expansion supplies the complete mixed
alternatives. Their selected trees enter the finite logarithmic envelope.
The radial gain is absorbed only after the actual root integral.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases
open TwoComponentCoulomb (box)
open scoped Classical ENNReal

/-- The uniform factor coefficient after bounding the number of mixed factors. -/
noncomputable def mixedCoefficient (W K : ℝ) (k : ℕ) : ℝ :=
  W ^ (k * k) * K ^ (3 * (k + 1).choose 2 + 2 * k)

/-- The original factor coefficient is bounded using only the label count. -/
theorem mixedCoefficient_le {V : Type*} [Fintype V] {W K : ℝ} (hW : 0 ≤ W) (hK : 1 ≤ K)
    (A B : Finset (Sym2 V)) (P : FiveSubsets (Sym2 V) V) :
    W ^ (Fintype.card V * Fintype.card V) * K ^ factorCount A B P ≤
      mixedCoefficient W K (Fintype.card V) := by
  unfold mixedCoefficient
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hW _)
  apply pow_le_pow_right₀ hK
  simpa only [Sym2.card] using factorCount_le_label_count A B P

variable {X : Finset (Finset ℕ)}

/-- (A.63) for every actual screened mixed term on its original graph.
The statement assumes original graph data and parameter ranges only. -/
theorem screened_mixed_integral {χ : ℂ → ℝ} {β L M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (hX : IsSubpartition X) (hXne : X.Nonempty) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (_hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (_hOF : O ⊆ Far) (_hpar : IsParityPair X O ∅)
        (Dz : Finset (Sym2 (X.biUnion id))) (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id)),
      P ≠ (∅,∅,∅,∅,∅) → P ∈ fiveSubsets (symOf (X.biUnion id) O)
        (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) (RouteCases.intraEdges (Limits.blockOf X)) univ →
      ∀ N : ℕ, (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |mixedIntegrand χ β lam M (eps * truncationScale p₀ β lam)
          (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
          (fun d => Real.exp (-L * (‖d.1-d.2‖ / (eps * truncationScale p₀ β lam)) ^ 2) - 1)
          (fun _ => 0) (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far)
          (symOf (X.biUnion id) O) c P|) ≤
        ENNReal.ofReal (C * eps ^ (-2 : ℝ) * N * lam ^ ((2-β)*(X.biUnion id).card) *
          truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  have hnX : Nonempty (X.biUnion id) := by
    obtain ⟨S,hS⟩ := hXne
    obtain ⟨i,hi⟩ := hX.1 S hS
    exact ⟨⟨i,mem_biUnion.2 ⟨S,hS,hi⟩⟩⟩
  have hk : 1 ≤ (X.biUnion id).card := by
    have := Fintype.card_pos (α := X.biUnion id)
    exact Nat.succ_le_iff.2 (by simpa only [Fintype.card_coe] using this)
  obtain ⟨K,hK,hpoint⟩ := screened_mixed_pointwise_all (L := L) hχ (by linarith : 0 ≤ β) hX
  obtain ⟨A,hA,hint⟩ := screened_spatialEnvelope_bound hχ hβ hM p₀ hk
  let Q := mixedCoefficient (Real.exp (β * cbK hχ)) K (X.biUnion id).card
  have hQ : 0 < Q := mul_pos (pow_pos (Real.exp_pos _) _) (pow_pos (lt_of_lt_of_le zero_lt_one hK) _)
  refine ⟨Q*A,mul_pos hQ hA,?_⟩
  intro eps lam hlam hle heps Near Far O hFar hconn hOF hpar Dz P hne hP N
  let h := eps * truncationScale p₀ β lam
  have heps0 : 0 < eps := hlam.trans_le hle
  have hlh : lam ≤ h := hle.trans (le_mul_of_one_le_right heps0.le
    (Appendix.one_le_truncationScale hβ hlam (hle.trans heps)))
  let F (c : X.biUnion id → ℂ × ℂ) (i : X.biUnion id) :=
    (box N).indicator (1 : ℂ → ℝ≥0∞) (c i).2 * ENNReal.ofReal ((h ^ 2)⁻¹)
  have hp (c : X.biUnion id → ℂ × ℂ) (hc : c ∈ boxConfig (X.biUnion id) N) :
      ENNReal.ofReal |mixedIntegrand χ β lam M h (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
        (fun d => Real.exp (-L * (‖d.1-d.2‖ / h) ^ 2) - 1) (fun _ => 0)
        (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far)
        (symOf (X.biUnion id) O) c P| ≤ ENNReal.ofReal Q * spatialEnvelope χ β M lam h F c := by
    let ext := extendConfig (X.biUnion id) c
    have he : (fun i : X.biUnion id => ext i) = c := by funext i; exact extendConfig_coe c i
    have H := hpoint hlam hM hlh Near Far O hFar hconn hOF hpar Dz ext
    have hb := internal_boundary_envelope hlam hM (zero_le_one.trans hK) (Real.exp_nonneg _)
      hOF H P hne hP F 1 (fun i => by
        rw [he]
        rw [abs_zero,zero_div,add_zero,one_mul]
        dsimp only [F]
        rw [indicator_of_mem (((Set.mem_univ_pi.mp hc) i).2),Pi.one_apply,one_mul])
    rw [he,mul_one] at hb
    exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by
      simpa only [Fintype.card_coe] using mixedCoefficient_le (Real.exp_nonneg _) hK
        (symOf (X.biUnion id) O) (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) P)) le_rfl)
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) N, ENNReal.ofReal Q * spatialEnvelope χ β M lam h F c :=
      setLIntegral_mono' (measurableSet_boxConfig N) hp
    _ ≤ ∫⁻ c, ENNReal.ofReal Q * spatialEnvelope χ β M lam h F c := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal Q * ∫⁻ c, spatialEnvelope χ β M lam h F c :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Q * ENNReal.ofReal (A * eps ^ (-2 : ℝ) * N *
        lam ^ ((2-β)*(X.biUnion id).card) * truncationScale p₀ β lam ^ (-2 : ℝ)) :=
      mul_le_mul' le_rfl (hint eps lam hlam hle heps (X.biUnion id) (by rw [Fintype.card_coe]) N)
    _ = _ := by rw [← ENNReal.ofReal_mul hQ.le]; congr 1; ring

/-- (A.63) for every actual frozen mixed term, with the bad-point coefficient
fixed before epsilon and the frozen data. Both ordinary and marked trees enter. -/
theorem frozen_mixed_integral {χ : ℂ → ℝ} {β L M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ)
    (hX : IsSubpartition X) (hXne : X.Nonempty) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
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
  have hnX : Nonempty (X.biUnion id) := by
    obtain ⟨S,hS⟩ := hXne
    obtain ⟨i,hi⟩ := hX.1 S hS
    exact ⟨⟨i,mem_biUnion.2 ⟨S,hS,hi⟩⟩⟩
  have hk : 1 ≤ (X.biUnion id).card := by
    have := Fintype.card_pos (α := X.biUnion id)
    exact Nat.succ_le_iff.2 (by simpa only [Fintype.card_coe] using this)
  obtain ⟨K,hK,hpoint⟩ := frozen_mixed_pointwise (L := L) hχ (by linarith : 0 ≤ β) hX
  obtain ⟨A,hA,hint⟩ := frozen_spatialEnvelope_bound (M := M) hχ hβ p₀ hk
  let Q := mixedCoefficient (Real.exp (β * cbK hχ)) K (X.biUnion id).card
  have hQ : 0 < Q := mul_pos (pow_pos (Real.exp_pos _) _) (pow_pos (lt_of_lt_of_le zero_lt_one hK) _)
  refine ⟨(Q*17)*A,by positivity,?_⟩
  intro eps lam hlam hle heps hM3 N V Z hV Near Far O hFar hconn hOF hpar Dz P hne hP
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
    have H := hpoint (p₀ := p₀) (ε₀ := eps) (h := h) V Z hlam hM Near Far O hFar hconn hOF hpar Dz ext
    have hb := internal_boundary_envelope hlam hM (zero_le_one.trans hK) (Real.exp_nonneg _)
      hOF H P hne hP F 17 (fun i => by
        have hr := frozen_sourceRoot_le (p₀ := p₀) (β := β) (M := M) (eps := eps)
          V Z (c i) hlam (rhoD_le_maxRad lam c i)
        rw [indicator_of_mem (((Set.mem_univ_pi.mp hc) i).2),Pi.one_apply,one_mul] at hr
        simpa only [he,show ext i = c i from extendConfig_coe c i] using hr)
    rw [he] at hb
    exact hb.trans (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (by
      simpa only [Fintype.card_coe] using mixedCoefficient_le (Real.exp_nonneg _) hK
        (symOf (X.biUnion id) O) (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) P)) le_rfl) le_rfl)
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) N, (ENNReal.ofReal Q * 17) * spatialEnvelope χ β M lam h F c :=
      setLIntegral_mono' (measurableSet_boxConfig N) hp
    _ ≤ ∫⁻ c, (ENNReal.ofReal Q * 17) * spatialEnvelope χ β M lam h F c := setLIntegral_le_lintegral _ _
    _ = (ENNReal.ofReal Q * 17) * ∫⁻ c, spatialEnvelope χ β M lam h F c :=
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
    _ ≤ (ENNReal.ofReal Q * 17) * ENNReal.ofReal (lam ^ ((2-β)*(X.biUnion id).card) *
        (A * eps ^ (-2 : ℝ) * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
          A * eps ^ (alphaExponent β * (X.biUnion id).card) * V.card)) :=
      mul_le_mul' le_rfl (hint eps lam hlam hle heps hM3 (X.biUnion id)
        (by rw [Fintype.card_coe]) V Z hV)
    _ = _ := by
      rw [show (17 : ℝ≥0∞) = ENNReal.ofReal (17 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul hQ.le,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end MultipoleBKT.ExpansionK.RouteSpatial

end
