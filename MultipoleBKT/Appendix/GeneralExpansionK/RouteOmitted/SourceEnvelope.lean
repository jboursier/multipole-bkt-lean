/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.SourceNormalization
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.UniformPointwise

/-!
# Uniform envelope for every original omitted parity term

See Lemma A.7. The coefficient is fixed before
all original choices and all configuration variables.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

variable {X : Finset (Finset ℕ)}

/-- Original near and far families enter one common envelope, uniformly in the odd subset. -/
theorem omitted_source_envelope {χ : ℂ → ℝ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (k : ℕ) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ (X : Finset (Finset ℕ)), IsSubpartition X →
      (X.biUnion id).card = k → ∀ [Nonempty (X.biUnion id)] {lam M h : ℝ}, 0 < lam → 1 ≤ M → lam ≤ h →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (_hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → O ⊆ Far → IsParityPair X O ∅ →
      ∀ (Dz : Finset (Sym2 (X.biUnion id))) (c : X.biUnion id → ℂ × ℂ),
      ENNReal.ofReal |omittedParityIntegrand χ β lam M h (Limits.blockOf X)
        (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O) c| ≤
        ENNReal.ofReal Q * omittedEnvelope χ β M lam h c := by
  obtain ⟨K,hK,hpoint⟩ := internal_baseline_pointwise_all_uniform hχ hβ
  let Q := mixedCoefficient (Real.exp (β*cbK hχ)) K k
  have hQ : 0 < Q := mul_pos (pow_pos (Real.exp_pos _) _) (pow_pos (lt_of_lt_of_le zero_lt_one hK) _)
  refine ⟨Q,hQ,?_⟩
  intro X hX hcard _ lam M h hlam hM hlh Near Far O hFar hconn hOF hpar Dz c
  let ext := extendConfig (X.biUnion id) c
  have he : (fun i : X.biUnion id => ext i) = c := by funext i; exact extendConfig_coe c i
  obtain ⟨Tb,hTb,-,hz | H⟩ := hpoint X hX hlam hM hlh Near Far O hFar hconn hOF hpar Dz ext
  · rw [he] at hz
    rw [hz,abs_zero,ENNReal.ofReal_zero]
    exact bot_le
  · have hcoef : Real.exp (β*cbK hχ)^((X.biUnion id).card*(X.biUnion id).card)*
        K^(symOf (X.biUnion id) Far).card ≤ Q := by
      have hh := mixedCoefficient_le (Real.exp_nonneg (β*cbK hχ)) hK
        (∅ : Finset (Sym2 (X.biUnion id))) (symOf (X.biUnion id) Far) (∅,∅,∅,∅,∅)
      simpa only [factorCount,Finset.card_empty,zero_add,add_zero,Fintype.card_coe,hcard] using hh
    have hb := internal_boundary_envelope hX (hOF.trans hFar) hpar hlam hM hlh
      (mul_nonneg (pow_nonneg (Real.exp_nonneg _) _) (pow_nonneg (zero_le_one.trans hK) _))
      Near Far Dz ext Tb hTb H
    rw [he] at hb
    exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)

end MultipoleBKT.ExpansionK.RouteOmitted

end
