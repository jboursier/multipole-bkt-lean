/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Sectors
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.MixedSpatial

/-!
# Simultaneous endpoint and mixed-edge integration

See Lemma A.4. Sum over the four endpoint sectors,
use the tree-coordinate identity, integrate the root over its box, and
integrate all odd coordinates as one family.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Limits TwoComponentCoulomb
open scoped Classical ENNReal

/-- The mixed profile as a function of the selected tree-edge distances.
Complex real coordinates encode nonnegative distances in the joint odd profile. -/
noncomputable def mixedDistanceProfile {I : Type*} [Fintype I]
    (odd : I → Prop) [DecidablePred odd] (even : {i // ¬odd i} → Bool)
    (s t : {i // ¬odd i} → ℝ) (M a R : ℝ) (d : I → ℝ) : ℝ≥0∞ :=
  jointOdd a R (fun i : {i // odd i} => (d i : ℂ)) *
    ∏ i : {i // ¬odd i}, ENNReal.ofReal (spatialProfile (even i) M (s i) (t i) (d i) / s i ^ 2)

/-- Measurability of the full mixed profile, including the shared maximum. -/
theorem measurable_mixedDistanceProfile {I : Type*} [Fintype I]
    (odd : I → Prop) [DecidablePred odd] (even : {i // ¬odd i} → Bool)
    (s t : {i // ¬odd i} → ℝ) (M a R : ℝ) :
    Measurable (mixedDistanceProfile odd even s t M a R) := by
  unfold mixedDistanceProfile
  apply Measurable.mul ((measurable_jointOdd a R).comp (by fun_prop))
  apply Finset.measurable_prod
  intro i _
  apply Measurable.ennreal_ofReal
  apply Measurable.div_const
  have hnear : MeasurableSet {d : I → ℝ | d i ≤ M * s i} :=
    measurableSet_le (measurable_pi_apply i.val) measurable_const
  unfold spatialProfile MultipoleBKT.RouteLog.evenEdgeProfile
  split_ifs <;> first
    | fun_prop
    | exact Measurable.ite hnear measurable_const (by fun_prop)

/-- Evaluate the distance profile on independent planar coordinates. -/
theorem mixedDistanceProfile_norm {I : Type*} [Fintype I]
    (odd : I → Prop) [DecidablePred odd] (even : {i // ¬odd i} → Bool)
    (s t : {i // ¬odd i} → ℝ) (M a R : ℝ) (z : I → ℂ) :
    mixedDistanceProfile odd even s t M a R (fun i => ‖z i‖) =
      jointOdd a R (fun i : {i // odd i} => z i) *
        ∏ i : {i // ¬odd i}, ENNReal.ofReal (spatialProfile (even i) M (s i) (t i) ‖z i‖ / s i ^ 2) := by
  unfold mixedDistanceProfile
  congr 1
  exact jointOdd_congr_norm a R _ _ (fun i => by simp)

/-- The complete spatial integration of a retained oriented tree profile.
All endpoint assignments use `lintegral_treeCoordinates`. The root costs `N`
and the odd maximum tail is integrated once.
See the proof of Lemma A.4. -/
theorem lintegral_endpoint_mixed_profiles {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (root : V) (par : V → V) (depth : V → ℕ),
      (∀ i, i ≠ root → depth (par i) < depth i) → Fintype.card {i // i ≠ root} ≤ k →
      ∀ (u : V → ℂ) (odd : {i // i ≠ root} → Prop) [DecidablePred odd]
        (even : {i : {i // i ≠ root} // ¬odd i} → Bool)
        (s t : {i : {i // i ≠ root} // ¬odd i} → ℝ) (a R : ℝ),
      0 < a → a ≤ R → (∀ i, a ≤ s i ∧ s i ≤ t i ∧ t i ≤ R) → ∀ N : ℕ,
      (∫⁻ x : V → ℂ, (box N).indicator (1 : ℂ → ℝ≥0∞) (x root) *
        mixedDistanceProfile odd even s t M a R
          (fun i => dipoleDist (ofPosVec x u i) (ofPosVec x u (par i)))) ≤
        ENNReal.ofReal (C * N * (1 + Real.log (R / a)) ^ k) := by
  obtain ⟨C, hC, hb⟩ := lintegral_normalized_mixed_profiles hM k
  refine ⟨4 ^ k * C, by positivity,
    fun V _ _ root par depth hdepth hV u odd _ even s t a R ha haR hst N => ?_⟩
  let Φ := mixedDistanceProfile odd even s t M a R
  have hΦ : Measurable Φ := measurable_mixedDistanceProfile odd even s t M a R
  have hh : Measurable ((box N).indicator (1 : ℂ → ℝ≥0∞)) :=
    measurable_const.indicator (measurableSet_box N)
  have hs := lintegral_endpoint_sectors root par depth hdepth u _ hh Φ hΦ
  have hp : (∫⁻ z : V → ℂ, (box N).indicator (1 : ℂ → ℝ≥0∞) (z root) *
      Φ (fun i => ‖z i‖)) = N *
        ∫⁻ z : {i // i ≠ root} → ℂ, Φ (fun i => ‖z i‖) := by
    have hF : Measurable (fun z : {i // i ≠ root} → ℂ => Φ (fun i => ‖z i‖)) :=
      hΦ.comp (show Measurable (fun z : {i // i ≠ root} → ℂ => fun i => ‖z i‖) by fun_prop)
    have hr := lintegral_root_coordinates root _ hh
      (fun z : {i // i ≠ root} → ℂ => Φ (fun i => ‖z i‖)) hF
    rw [lintegral_indicator_one (measurableSet_box N), volume_box] at hr
    exact hr
  rw [hp] at hs
  have hi : (∫⁻ z : {i // i ≠ root} → ℂ, Φ (fun i => ‖z i‖)) ≤
      ENNReal.ofReal (C * (1 + Real.log (R / a)) ^ k) := by
    dsimp only [Φ]
    simp_rw [mixedDistanceProfile_norm]
    exact hb _ hV odd even s t a R ha haR hst
  refine hs.trans ((mul_le_mul' (pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 4) hV)
    (mul_le_mul_right hi _)).trans_eq ?_)
  rw [show (4 : ℝ≥0∞) ^ k = ENNReal.ofReal ((4 : ℝ) ^ k) by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num,
    show (N : ℝ≥0∞) = ENNReal.ofReal N by rw [ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end MultipoleBKT.SmallIntegral.RouteJ

end
