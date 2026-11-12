/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.EvenEdge
public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Spatial

/-!
# The marked even edge in the cutoff tree

See (A.62) and Step 3 of the proof of Lemma A.7. Normalize the marked edge by
both endpoint squares. Its integral is logarithmic. The squares remain
outside the spatial integral for the two-sided radius allocation.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset Limits Peeling SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext
open scoped Classical ENNReal

/-- The case-E edge divided by its two endpoint squares, on the written disc. -/
noncomputable def markedProfile (s t h d : ℝ) : ℝ :=
  (Iic (17 * h)).indicator
    (fun d => RouteCases.markedEvenKernel s t d / (s ^ 2 * t ^ 2)) d

theorem measurable_markedProfile (s t h : ℝ) : Measurable (markedProfile s t h) := by
  unfold markedProfile RouteCases.markedEvenKernel
  exact Measurable.indicator (by fun_prop) measurableSet_Iic

/-- The two endpoint squares can be restored exactly before tree ordering. -/
theorem markedProfile_restore {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h d : ℝ) :
    s ^ 2 * t ^ 2 * markedProfile s t h d =
      (Iic (17 * h)).indicator (RouteCases.markedEvenKernel s t) d := by
  unfold markedProfile
  by_cases hd : d ∈ Iic (17 * h)
  · rw [indicator_of_mem hd, indicator_of_mem hd]
    field_simp
  · rw [indicator_of_notMem hd, indicator_of_notMem hd, mul_zero]

/-- The literal marked-edge logarithm after dividing by both endpoint squares. -/
theorem lintegral_markedProfile {s t h : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hsh : s ≤ h) (hth : t ≤ h) :
    (∫⁻ z : ℂ, ENNReal.ofReal (markedProfile s t h ‖z‖)) =
      ENNReal.ofReal (2 * Real.pi * (1 + Real.log (17 * h / max s t))) := by
  have hset : MeasurableSet {z : ℂ | ‖z‖ ≤ 17 * h} :=
    measurableSet_le (by fun_prop) measurable_const
  have heq (z : ℂ) : ENNReal.ofReal (markedProfile s t h ‖z‖) =
      ENNReal.ofReal ((s ^ 2 * t ^ 2)⁻¹) *
        {z : ℂ | ‖z‖ ≤ 17 * h}.indicator
          (fun z => ENNReal.ofReal (RouteCases.markedEvenKernel s t ‖z‖)) z := by
    unfold markedProfile
    by_cases hz : ‖z‖ ≤ 17 * h
    · rw [indicator_of_mem (show ‖z‖ ∈ Iic (17 * h) from hz),
        indicator_of_mem (show z ∈ {z : ℂ | ‖z‖ ≤ 17 * h} from hz), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    · rw [indicator_of_notMem (show ‖z‖ ∉ Iic (17 * h) from hz),
        indicator_of_notMem (show z ∉ {z : ℂ | ‖z‖ ≤ 17 * h} from hz), ENNReal.ofReal_zero, mul_zero]
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hset,
    RouteCases.lintegral_marked_even hs ht (by
      have hh : 0 ≤ h := hs.le.trans hsh
      exact (max_le hsh hth).trans (by nlinarith)),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- One marked edge has the same uniform logarithmic coefficient as the
other cutoff-tree edges. This estimate is applied after its exact integral. -/
theorem lintegral_markedProfile_le {M a s t h : ℝ} (_hM : 1 ≤ M) (ha : 0 < a)
    (has : a ≤ s) (hat : a ≤ t) (hsh : s ≤ h) (hth : t ≤ h) :
    (∫⁻ z : ℂ, ENNReal.ofReal (markedProfile s t h ‖z‖)) ≤
      ENNReal.ofReal (Real.pi * (M ^ 2 + 5) * (1 + Real.log (17 * h / a))) := by
  have hs := ha.trans_le has
  have ht := ha.trans_le hat
  have hh := hs.trans_le hsh
  rw [lintegral_markedProfile hs ht hsh hth]
  apply ENNReal.ofReal_le_ofReal
  have hlog := Real.log_le_log (by positivity : 0 < 17 * h / max s t)
    (div_le_div_of_nonneg_left (by positivity) ha (has.trans (le_max_left _ _)))
  have hL : 0 ≤ 1 + Real.log (17 * h / a) := by
    have := Real.log_nonneg ((one_le_div ha).2 (show a ≤ 17 * h by linarith))
    linarith
  nlinarith [Real.pi_pos, mul_nonneg (sq_nonneg M) hL]

/-- The normalized tree with one distinguished even edge. The ordinary
odd and even families are still the separate original families. -/
noncomputable def markedCutProfile {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A E : Finset (Sym2 V)) (mark : Sym2 V) (M lam h : ℝ) (u : V → ℂ)
    (e : Sym2 V) (d : ℝ) : ℝ :=
  if e = mark then
    markedProfile (edgeMin id (fun i => rho lam (u i)) e)
      (radMax (fun i => rho lam (u i)) e) h d
  else cutProfile A E M lam h u e d

theorem measurable_markedCutProfile {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A E : Finset (Sym2 V)) (mark : Sym2 V) (M lam h : ℝ) (u : V → ℂ) (e : Sym2 V) :
    Measurable (markedCutProfile A E mark M lam h u e) := by
  unfold markedCutProfile
  split_ifs
  · exact measurable_markedProfile _ _ _
  · exact measurable_cutProfile A E M lam h u e

theorem lintegral_markedCutProfile_le {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A E : Finset (Sym2 V)) (mark : Sym2 V) {M lam h : ℝ}
    (hM : 1 ≤ M) (hlam : 0 < lam) (u : V → ℂ) (hu : ∀ i, rho lam (u i) ≤ h)
    (e : Sym2 V) :
    (∫⁻ z : ℂ, ENNReal.ofReal (markedCutProfile A E mark M lam h u e ‖z‖)) ≤
      ENNReal.ofReal (Real.pi * (M ^ 2 + 5) * (1 + Real.log (17 * h / minRho lam u))) := by
  unfold markedCutProfile
  split_ifs
  · induction e using Sym2.ind with
    | h i j =>
      exact lintegral_markedProfile_le hM (minRho_pos hlam u)
        (le_min (minRho_le_rho lam u i) (minRho_le_rho lam u j))
        ((minRho_le_rho lam u i).trans (le_max_left _ _))
        ((min_le_left _ _).trans (hu i)) (max_le (hu i) (hu j))
  · exact lintegral_cutProfile_le A E hM hlam u hu e

end MultipoleBKT.ExpansionK.RouteSpatial

end
