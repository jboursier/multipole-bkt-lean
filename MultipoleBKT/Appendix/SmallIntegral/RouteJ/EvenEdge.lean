/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.EvenEdge
public import MultipoleBKT.Appendix.SmallIntegral.JCore

/-!
# The logarithmic integral of an actual hatted even edge

See Lemma A.4. Compare the hatted weight to the regularized radial profile.
The four possible closest endpoints cost a factor of four when the distance
partition is summed.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory
open Limits MultipoleBKT.RouteLog
open scoped ENNReal

open scoped Classical in
/-- The hatted even weight is bounded by the even-edge profile with
`s = min(ρ_i,ρ_j)` and `t = max(ρ_i,ρ_j)`.
See the proof of Lemma A.4. -/
theorem hatEven_le_profile {M lam : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) (a b : ℂ × ℂ) :
    (if MultipoleLinked M lam a b then 1 else ahat a b ^ 2) ≤
      evenEdgeProfile M (min (rhoD lam a) (rhoD lam b))
        (max (rhoD lam a) (rhoD lam b)) (dipoleDist a b) := by
  classical
  let s := min (rhoD lam a) (rhoD lam b)
  let t := max (rhoD lam a) (rhoD lam b)
  have hs : 0 < s := lt_min (rhoD_pos hlam _) (rhoD_pos hlam _)
  have hsM : s ≤ M * s := le_mul_of_one_le_left hs.le hM
  have hlink : MultipoleLinked M lam a b ↔ dipoleDist a b ≤ M * s := Iff.rfl
  unfold evenEdgeProfile
  rw [hlink]
  split_ifs with hnear
  · exact le_rfl
  · have hd : 0 < dipoleDist a b := hs.trans_le (hsM.trans (lt_of_not_ge hnear).le)
    have hlamd : lam ≤ dipoleDist a b :=
      (le_min (le_max_right _ _) (le_max_right _ _)).trans (hsM.trans (lt_of_not_ge hnear).le)
    have hden : max (dipoleDist a b) (max ‖a.1 - a.2‖ ‖b.1 - b.2‖) =
        max (dipoleDist a b) t := by
      dsimp only [t, rhoD]
      conv_rhs => rw [max_max_max_comm, max_self, ← max_assoc]
      exact (max_eq_left (hlamd.trans (le_max_left _ _))).symm
    have hnum : ‖a.1 - a.2‖ * ‖b.1 - b.2‖ ≤ s * t := by
      calc
        _ ≤ rhoD lam a * rhoD lam b :=
          mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) (rhoD_pos hlam _).le
        _ = _ := (min_mul_max _ _).symm
    apply pow_le_pow_left₀ (ahat_nonneg _ _)
    unfold ahat
    rw [hden]
    exact div_le_div_of_nonneg_right hnum
      (mul_nonneg hd.le (hd.le.trans (le_max_left _ _)))

private theorem lintegral_profile_dipoleDist_le (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (u : ℂ) (b : ℂ × ℂ) :
    ∫⁻ x : ℂ, φ (dipoleDist (x, x + u) b) ≤ 4 * ∫⁻ z : ℂ, φ ‖z‖ := by
  have hpt (x : ℂ) : φ (dipoleDist (x, x + u) b) ≤
      φ ‖x - b.1‖ + φ ‖x - b.2‖ + φ ‖x - (b.1 - u)‖ + φ ‖x - (b.2 - u)‖ := by
    rw [dipoleDist_eq_min]
    simp only [min_def]
    split_ifs <;> first
      | exact le_add_right (le_add_right (le_add_right le_rfl))
      | exact le_add_right (le_add_right (le_add_left le_rfl))
      | exact le_add_right (le_add_left le_rfl)
      | exact le_add_left le_rfl
  have htr (p : ℂ) : (∫⁻ x : ℂ, φ ‖x - p‖) = ∫⁻ z : ℂ, φ ‖z‖ :=
    lintegral_sub_right_eq_self (fun z => φ ‖z‖) p
  have hm (p : ℂ) : Measurable fun x : ℂ => φ ‖x - p‖ := by fun_prop
  have hm2 : Measurable fun x : ℂ => φ ‖x - b.1‖ + φ ‖x - b.2‖ := (hm _).add (hm _)
  have hm3 : Measurable fun x : ℂ => φ ‖x - b.1‖ + φ ‖x - b.2‖ + φ ‖x - (b.1 - u)‖ :=
    hm2.add (hm _)
  calc
    _ ≤ ∫⁻ x : ℂ, (φ ‖x - b.1‖ + φ ‖x - b.2‖ + φ ‖x - (b.1 - u)‖ + φ ‖x - (b.2 - u)‖) :=
      lintegral_mono hpt
    _ = _ := by
      rw [lintegral_add_left hm3,
        lintegral_add_left hm2, lintegral_add_left (hm _), htr, htr, htr, htr]
      ring

open scoped Classical in
/-- Integrating a hatted even edge in one endpoint position gives the written
logarithm of the ratio of its two radii. Summing the four closest-endpoint
regions gives the explicit coefficient `4π(M²+3)`.
See the proof of Lemma A.4. -/
theorem lintegral_hatEven_le {M lam : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam)
    (u : ℂ) (b : ℂ × ℂ) :
    (∫⁻ x : ℂ, ENNReal.ofReal
      (if MultipoleLinked M lam (x, x + u) b then 1 else ahat (x, x + u) b ^ 2)) ≤
      ENNReal.ofReal (4 * Real.pi * (M ^ 2 + 3) *
        min (rho lam u) (rhoD lam b) ^ 2 *
          (1 + Real.log (max (rho lam u) (rhoD lam b) / min (rho lam u) (rhoD lam b)))) := by
  classical
  let s := min (rho lam u) (rhoD lam b)
  let t := max (rho lam u) (rhoD lam b)
  have hs : 0 < s := lt_min (rho_pos hlam _) (rhoD_pos hlam _)
  let φ : ℝ → ℝ≥0∞ := fun d => ENNReal.ofReal (evenEdgeProfile M s t d)
  have hm : Measurable φ := by
    unfold φ evenEdgeProfile
    apply Measurable.ennreal_ofReal
    exact Measurable.ite measurableSet_Iic measurable_const (by fun_prop)
  calc
    _ ≤ ∫⁻ x : ℂ, φ (dipoleDist (x, x + u) b) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (by simpa only [rhoD_mk] using hatEven_le_profile hM hlam (x, x + u) b)
    _ ≤ 4 * ∫⁻ z : ℂ, φ ‖z‖ := lintegral_profile_dipoleDist_le φ hm u b
    _ ≤ 4 * ENNReal.ofReal (Real.pi * (M ^ 2 + 3) * s ^ 2 * (1 + Real.log (t / s))) := by
      gcongr
      exact lintegral_evenEdgeProfile_le hM hs (min_le_max)
    _ = _ := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp only [s, t]
      ring

end MultipoleBKT.SmallIntegral.RouteJ

end
