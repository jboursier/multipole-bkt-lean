/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.OmittedOdd
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.EndpointIntegration

/-!
# The quadratic gain in a mixed omitted-edge tree

See Step 3 of
the proof of Lemma A.7. The same global odd tail is
integrated together with all near and even coordinates. Its quadratic
cutoff factor is retained outside every coordinate integration.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SmallIntegral.RouteJ
open scoped Classical ENNReal

/-- The normalized mixed-coordinate integrand on the omitted-edge domain. -/
noncomputable def omittedMixed {I : Type*} [Fintype I] (odd : I → Prop) [DecidablePred odd]
    (even : {i // ¬odd i} → Bool) (s t : {i // ¬odd i} → ℝ) (M a R H : ℝ) (z : I → ℂ) : ℝ≥0∞ :=
  omittedOdd a R H (fun i : {i // odd i} => z i) *
    ∏ i : {i // ¬odd i}, ENNReal.ofReal (spatialProfile (even i) M (s i) (t i) ‖z i‖ / s i ^ 2)

/-- All non-odd coordinates retain their individual near/even profiles.
The odd coordinates have one tail at scale `H`, with the prefactor `R²/H²`. -/
theorem omittedMixed_eq {I : Type*} [Fintype I] (odd : I → Prop) [DecidablePred odd]
    (even : {i // ¬odd i} → Bool) (s t : {i // ¬odd i} → ℝ) (M a R H : ℝ)
    (ha : 0 < a) (hH : 0 < H) (z : I → ℂ) :
    omittedMixed odd even s t M a R H z = ENNReal.ofReal (R ^ 2 / H ^ 2) *
      (jointOdd a H (fun i : {i // odd i} => z i) *
        ∏ i : {i // ¬odd i}, ENNReal.ofReal (spatialProfile (even i) M (s i) (t i) ‖z i‖ / s i ^ 2)) := by
  unfold omittedMixed
  rw [omittedOdd_eq ha hH R, mul_assoc]

/-- The complete normalized omitted-tree coordinate integral, with the
quadratic gain and the actual logarithmic factor left intact. -/
theorem lintegral_omittedMixed {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I], Fintype.card I ≤ k →
      ∀ (odd : I → Prop) [DecidablePred odd] (even : {i // ¬odd i} → Bool)
        (s t : {i // ¬odd i} → ℝ) (a R H : ℝ),
      0 < a → a ≤ H → (∀ i, a ≤ s i ∧ s i ≤ t i ∧ t i ≤ H) →
      (∫⁻ z : I → ℂ, omittedMixed odd even s t M a R H z) ≤
        ENNReal.ofReal (C * (R ^ 2 / H ^ 2) * (1 + Real.log (H / a)) ^ k) := by
  obtain ⟨C,hC,hb⟩ := lintegral_normalized_mixed_profiles hM k
  refine ⟨C,hC,fun I _ hI odd _ even s t a R H ha haH hst => ?_⟩
  simp_rw [omittedMixed_eq odd even s t M a R H ha (ha.trans_le haH)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl (hb I hI odd even s t a H ha haH hst)).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end MultipoleBKT.ExpansionK.RouteSpatial

end
