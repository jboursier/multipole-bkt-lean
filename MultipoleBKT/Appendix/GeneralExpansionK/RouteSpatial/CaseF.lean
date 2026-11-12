/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.JointEnvelope

/-!
# Case F for the original baseline parity integral

See (A.64). The original parity term is compared with the finite
tree envelope on every configuration. Integrating that envelope
uses the unordered logarithmic vector displays and their three regimes.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases
open scoped Classical ENNReal

variable {X : Finset (Finset ℕ)}

/-- (A.64) for the actual baseline parity term. This is the common
baseline of both concrete models. The coefficient precedes lambda and all
original near and far graph choices. -/
theorem caseF_baseline_integral {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ k : ℕ)
    (hkp : ((k+2 : ℕ) : ℕ∞) ≤ pStar β) (hX : IsSubpartition X)
    (hcard : (X.biUnion id).card = k+2) :
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ eps →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (_hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (_hOF : O ⊆ Far) (_hpar : IsParityPair X O ∅)
        (Dz : Finset (Sym2 (X.biUnion id))) (n : ℕ),
      (∫⁻ c in boxConfig (X.biUnion id) n ∩
          {c : X.biUnion id → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
        ENNReal.ofReal |baselineParityIntegrand χ β lam M (Limits.blockOf X)
          (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) c|) ≤
        ENNReal.ofReal (C * n * lam ^ ((2-β)*(k+2)) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  have hnX : Nonempty (X.biUnion id) := Fintype.card_pos_iff.1 (by
    rw [Fintype.card_coe,hcard]
    omega)
  obtain ⟨K,hK,hpoint⟩ := baseline_source_normalized hχ (by linarith : 0 ≤ β) hX
  let Q := mixedCoefficient (Real.exp (β * cbK hχ)) K (k+2)
  have hQ : 0 < Q := mul_pos (pow_pos (Real.exp_pos _) _) (pow_pos (lt_of_lt_of_le zero_lt_one hK) _)
  intro eps heps heps1
  obtain ⟨A,hA,hbound⟩ := caseF_jointEnvelope_bound hχ hβ hM p₀ k hkp eps heps heps1
  refine ⟨Q*A,mul_pos hQ hA,?_⟩
  intro lam hlam hle Near Far O hFar hconn hOF hpar Dz n
  have hp (c : X.biUnion id → ℂ × ℂ) :
      ENNReal.ofReal |baselineParityIntegrand χ β lam M (Limits.blockOf X)
        (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) c| ≤
        ENNReal.ofReal Q * jointEnvelope χ β M lam c := by
    let ext := extendConfig (X.biUnion id) c
    have he : (fun i : X.biUnion id => ext i) = c := by funext i; exact extendConfig_coe c i
    have hh := hpoint hlam hM Near Far O hFar hconn hOF hpar Dz ext
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

end MultipoleBKT.ExpansionK.RouteSpatial

end
