/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Profiles
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.EdgeProfiles

/-!
# Integrating each cutoff tree edge

See Lemma A.4. Near edges give disc areas.
Even edges and the cutoff odd edges retain their annular logarithms.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJext

open MeasureTheory Set Finset Limits Peeling RouteJ
open scoped Classical ENNReal

/-- The normalized near or even profile has a common logarithmic bound. -/
theorem lintegral_normalized_spatialProfile_le (even : Bool) {M a s t h : ℝ}
    (hM : 1 ≤ M) (ha : 0 < a) (has : a ≤ s) (hst : s ≤ t) (hth : t ≤ h) :
    (∫⁻ z : ℂ, ENNReal.ofReal (spatialProfile even M s t ‖z‖ / s ^ 2)) ≤
      ENNReal.ofReal (Real.pi * (M ^ 2 + 3) * (1 + Real.log (17 * h / a))) := by
  have hs : 0 < s := ha.trans_le has
  have hh : 0 < h := hs.trans_le (hst.trans hth)
  have hL : 1 ≤ 1 + Real.log (17 * h / a) := by
    have := Real.log_nonneg ((one_le_div ha).2 (show a ≤ 17 * h by linarith))
    linarith
  have hp : (fun z : ℂ => ENNReal.ofReal (spatialProfile even M s t ‖z‖ / s ^ 2)) =
      fun z => ENNReal.ofReal ((s ^ 2)⁻¹) * ENNReal.ofReal (spatialProfile even M s t ‖z‖) := by
    funext z
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hp, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_right (lintegral_spatialProfile_le even hM hs hst) _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : (s ^ 2)⁻¹ * (Real.pi * (M ^ 2 + 3) * s ^ 2 *
      (if even then 1 + Real.log (t / s) else 1)) =
      Real.pi * (M ^ 2 + 3) * (if even then 1 + Real.log (t / s) else 1) := by
    field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  cases even with
  | false => exact hL
  | true =>
    simp only [ite_true]
    apply add_le_add le_rfl
    apply Real.log_le_log (div_pos (hs.trans_le hst) hs)
    exact div_le_div₀ (by linarith) (by linarith) ha has

/-- The scalar profile selected by the original odd and even edge families. -/
noncomputable def cutProfile {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A E : Finset (Sym2 V)) (M lam h : ℝ) (u : V → ℂ) (e : Sym2 V) (d : ℝ) : ℝ :=
  if e ∈ A then oddProfile (minRho lam u) h d else
    spatialProfile (e ∈ E) M (edgeMin id (fun i => rho lam (u i)) e)
      (radMax (fun i => rho lam (u i)) e) d /
        edgeMin id (fun i => rho lam (u i)) e ^ 2

theorem measurable_cutProfile {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A E : Finset (Sym2 V)) (M lam h : ℝ) (u : V → ℂ) (e : Sym2 V) :
    Measurable (cutProfile A E M lam h u e) := by
  unfold cutProfile
  split_ifs
  · exact measurable_oddProfile _ _
  · unfold spatialProfile MultipoleBKT.RouteLog.evenEdgeProfile
    split_ifs <;> exact Measurable.div_const
      (Measurable.ite measurableSet_Iic measurable_const (by fun_prop)) _

/-- All edge factors have one uniform logarithmic coefficient at fixed vectors. -/
theorem lintegral_cutProfile_le {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A E : Finset (Sym2 V)) {M lam h : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam)
    (u : V → ℂ) (hu : ∀ i, rho lam (u i) ≤ h) (e : Sym2 V) :
    (∫⁻ z : ℂ, ENNReal.ofReal (cutProfile A E M lam h u e ‖z‖)) ≤
      ENNReal.ofReal (Real.pi * (M ^ 2 + 5) *
        (1 + Real.log (17 * h / minRho lam u))) := by
  have ha := minRho_pos hlam u
  obtain ⟨i⟩ := ‹Nonempty V›
  have hah := (minRho_le_rho lam u i).trans (hu i)
  have hlog := Real.log_nonneg ((one_le_div ha).2 (show minRho lam u ≤ 17 * h by linarith))
  unfold cutProfile
  split_ifs with he
  · rw [lintegral_oddProfile ha hah]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg M, Real.pi_pos, mul_nonneg (sq_nonneg M) hlog]
  · have hs : minRho lam u ≤ edgeMin id (fun i => rho lam (u i)) e ∧
        edgeMin id (fun i => rho lam (u i)) e ≤ radMax (fun i => rho lam (u i)) e ∧
        radMax (fun i => rho lam (u i)) e ≤ h := by
      induction e using Sym2.ind with
      | h i j => exact ⟨le_min (minRho_le_rho lam u i) (minRho_le_rho lam u j), min_le_max,
          max_le (hu i) (hu j)⟩
    refine (lintegral_normalized_spatialProfile_le _ hM ha hs.1 hs.2.1 hs.2.2).trans ?_
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.pi_pos]

end MultipoleBKT.SmallIntegral.RouteJext

end
