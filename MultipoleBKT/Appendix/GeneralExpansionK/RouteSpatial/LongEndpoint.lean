/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.CoupledTree
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.LongEvenTree

/-!
# The exterior even mark with all endpoint sectors and one odd tail

See omitted-domain
long-even display, the proof of Lemma A.7. All other odd edges are unbounded.
The exterior integral supplies its quadratic inverse cutoff before any
radial absorption.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral SmallIntegral.RouteJ
open TwoComponentCoulomb (box)
open scoped Classical ENNReal

/-- Endpoint-sector integration with a distinguished exterior even edge.
The remaining edge family contains one coupled odd maximum tail. -/
theorem lintegral_long_endpoint_tree {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Type*) [Fintype W] [DecidableEq W], Fintype.card W ≤ k+1 →
      ∀ (T : SimpleGraph W) (_hT : T.IsTree) (root : W) (u : W → ℂ) (mark : T.edgeFinset),
      let I := {e : T.edgeFinset // e ≠ mark}
      ∀ (odd : I → Prop) [DecidablePred odd] (even : {i // ¬odd i} → Bool)
        (s t : {i // ¬odd i} → ℝ) (a R H : ℝ),
      0 < a → a ≤ R → 0 < H → (∀ i, a ≤ s i ∧ s i ≤ t i ∧ t i ≤ R) → ∀ n : ℕ,
      (∫⁻ x : W → ℂ, (box n).indicator (1 : ℂ → ℝ≥0∞) (x root) *
        (mixedDistanceProfile odd even s t M a R
          (fun i => dipoleDistOn (ofPosVec x u) i.val) *
            longEvenProfile 1 1 H (dipoleDistOn (ofPosVec x u) mark))) ≤
        ENNReal.ofReal (C * n / H ^ 2 * (1 + Real.log (R / a)) ^ k) := by
  obtain ⟨C,hC,hb⟩ := lintegral_normalized_mixed_profiles hM k
  refine ⟨4 ^ k * C * Real.pi,by positivity,?_⟩
  intro W _ _ hW T hT root u mark I odd _ even s t a R H ha haR hH hst n
  let Ψ := mixedDistanceProfile odd even s t M a R
  have hΨ : Measurable Ψ := measurable_mixedDistanceProfile odd even s t M a R
  let Φ (d : T.edgeFinset → ℝ) := Ψ (fun i : I => d i.val) * longEvenProfile 1 1 H (d mark)
  have hΦ : Measurable Φ := (hΨ.comp (show Measurable (fun d : T.edgeFinset → ℝ => fun i : I => d i.val) by fun_prop)).mul
    ((measurable_longEvenProfile 1 1 H).comp (measurable_pi_apply mark))
  have hs := lintegral_coupled_tree_le T hT root u ((box n).indicator (1 : ℂ → ℝ≥0∞))
    (measurable_const.indicator (TwoComponentCoulomb.measurableSet_box n)) Φ hΦ
  have hnorm : Measurable (fun z : I → ℂ => Ψ (fun i => ‖z i‖)) := hΨ.comp (show Measurable (fun z : I → ℂ => fun i : I => ‖z i‖) by fun_prop)
  have hlong : Measurable (fun z : ℂ => longEvenProfile 1 1 H ‖z‖) :=
    (measurable_longEvenProfile 1 1 H).comp measurable_norm
  have he : (∫⁻ z : T.edgeFinset → ℂ, Φ (fun e => ‖z e‖)) =
      (∫⁻ z : ℂ, longEvenProfile 1 1 H ‖z‖) * ∫⁻ z : I → ℂ, Ψ (fun i => ‖z i‖) := by
    have hr := lintegral_root_coordinates mark _ hlong _ hnorm
    convert hr using 1
    apply lintegral_congr
    intro z
    exact mul_comm _ _
  have hI : Fintype.card I ≤ k := by
    have hc := hT.card_edgeFinset
    have hcard : Fintype.card I = Fintype.card T.edgeFinset - 1 := by
      rw [Fintype.card_subtype_compl]
      simp only [Fintype.card_subtype_eq]
    rw [hcard,Fintype.card_coe]
    omega
  have hi : (∫⁻ z : I → ℂ, Ψ (fun i => ‖z i‖)) ≤
      ENNReal.ofReal (C * (1 + Real.log (R/a)) ^ k) := by
    dsimp only [Ψ]
    simp_rw [mixedDistanceProfile_norm]
    exact hb I hI odd even s t a R ha haR hst
  rw [he,lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box n),TwoComponentCoulomb.volume_box] at hs
  have hn : Fintype.card W - 1 ≤ k := by omega
  refine hs.trans ((mul_le_mul'
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 4) hn)
    (mul_le_mul' le_rfl (mul_le_mul' (lintegral_longEvenProfile (s := 1) (t := 1) hH) hi))).trans_eq ?_)
  rw [show (4 : ℝ≥0∞) ^ k = ENNReal.ofReal ((4 : ℝ)^k) by
      rw [ENNReal.ofReal_pow (by norm_num)]; norm_num,
    ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end MultipoleBKT.ExpansionK.RouteSpatial

end
