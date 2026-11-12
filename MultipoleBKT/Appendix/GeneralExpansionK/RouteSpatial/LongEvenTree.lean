/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TreeIntegral
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.MixedSpatial

/-!
# The retained long even edge in a spatial tree

See omitted-integral
display in Step 3 of the proof of Lemma A.7. The marked
exterior kernel is quartic. Its integral leaves `s² t²/H²`, so the
two endpoint squares are available to the two-sided tree ordering.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral
open SmallIntegral.RouteJ SmallIntegral.RouteJext
open scoped Classical ENNReal

/-- The quartic exterior kernel of a retained long even edge. -/
noncomputable def longEvenProfile (s t H d : ℝ) : ℝ≥0∞ :=
  (Ioi H).indicator (fun d => ENNReal.ofReal (s ^ 2 * t ^ 2 * d ^ (-4 : ℝ))) d

theorem measurable_longEvenProfile (s t H : ℝ) : Measurable (longEvenProfile s t H) := by
  unfold longEvenProfile
  exact Measurable.indicator (by fun_prop) measurableSet_Ioi

/-- Use the exterior integral before any radius allocation. -/
theorem lintegral_longEvenProfile {s t H : ℝ} (hH : 0 < H) :
    (∫⁻ z : ℂ, longEvenProfile s t H ‖z‖) ≤
      ENNReal.ofReal (Real.pi * s ^ 2 * t ^ 2 / H ^ 2) := by
  have heq (z : ℂ) : longEvenProfile s t H ‖z‖ =
      {z : ℂ | H < ‖z‖}.indicator (fun z => ENNReal.ofReal (s ^ 2 * t ^ 2 * ‖z‖ ^ (-4 : ℝ))) z := rfl
  simp_rw [heq]
  rw [lintegral_indicator (measurableSet_lt measurable_const (by fun_prop))]
  refine (RouteCases.long_even_edge_integral (s := s) (t := t) hH).trans_eq ?_
  congr 1
  rw [mul_assoc Real.pi, ← mul_pow, min_mul_max]
  ring

/-- All other tree edges are integrated with their logarithmic profiles.
The exterior mark retains its endpoint squares and the exponent two in `H`. -/
theorem lintegral_long_even_tree_le {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {M lam h H s t : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) (hH : 0 < H) (u : W → ℂ)
    (hu : ∀ i, rho lam (u i) ≤ h) (T : SimpleGraph W) [DecidableRel T.Adj] (hT : T.IsTree)
    (A E : Finset (Sym2 W)) (mark : Sym2 W) (hmark : mark ∈ T.edgeFinset)
    (root : W) (G : ℂ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x : W → ℂ, G (x root) * ∏ e ∈ T.edgeFinset,
      (if e = mark then longEvenProfile s t H (dipoleDistOn (ofPosVec x u) e)
        else ENNReal.ofReal (cutProfile A E M lam h u e (dipoleDistOn (ofPosVec x u) e)))) ≤
      (4 : ℝ≥0∞) ^ (Fintype.card W - 1) * ((∫⁻ y, G y) *
        (ENNReal.ofReal (Real.pi * s ^ 2 * t ^ 2 / H ^ 2) *
          ENNReal.ofReal (Real.pi * (M ^ 2 + 5) *
            (1 + Real.log (17 * h / minRho lam u))) ^ (Fintype.card W - 2))) := by
  let f (e : Sym2 W) (d : ℝ) := if e = mark then longEvenProfile s t H d
    else ENNReal.ofReal (cutProfile A E M lam h u e d)
  have hf (e : Sym2 W) : Measurable (f e) := by
    unfold f
    split_ifs
    · exact measurable_longEvenProfile s t H
    · exact (measurable_cutProfile A E M lam h u e).ennreal_ofReal
  have hb := lintegral_tree_product_le T hT root u G hG f hf
  refine hb.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_))
  rw [← mul_prod_erase T.edgeFinset (fun e => ∫⁻ z : ℂ, f e ‖z‖) hmark]
  have hm : (∫⁻ z : ℂ, f mark ‖z‖) ≤ ENNReal.ofReal (Real.pi * s ^ 2 * t ^ 2 / H ^ 2) := by
    simp only [f, ite_true]
    exact lintegral_longEvenProfile hH
  have hr : (∏ e ∈ T.edgeFinset.erase mark, ∫⁻ z : ℂ, f e ‖z‖) ≤
      ENNReal.ofReal (Real.pi * (M ^ 2 + 5) * (1 + Real.log (17 * h / minRho lam u))) ^
        (Fintype.card W - 2) := by
    calc
      _ ≤ ∏ _e ∈ T.edgeFinset.erase mark,
          ENNReal.ofReal (Real.pi * (M ^ 2 + 5) * (1 + Real.log (17 * h / minRho lam u))) := by
        apply prod_le_prod
        intro e he
        simp only [f, ite_eq_right (mem_erase.mp he).1]
        exact lintegral_cutProfile_le A E hM hlam u hu e
      _ = _ := by
        rw [prod_const, card_erase_of_mem hmark]
        congr 1
        have := hT.card_edgeFinset
        omega
  exact mul_le_mul' hm hr

/-- The complete joint odd-family integral with a retained long even mark in
independent tree coordinates. Odd edges are unbounded and keep their shared
maximum tail. The marked edge keeps both endpoint squares and `H⁻²`. -/
theorem lintegral_joint_long_even_coordinates {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I], Fintype.card I ≤ k →
      ∀ (odd : I → Prop) [DecidablePred odd] (even : {i // ¬odd i} → Bool)
        (s t : {i // ¬odd i} → ℝ) (a R H sm tm : ℝ),
      0 < a → a ≤ R → 0 < H → (∀ i, a ≤ s i ∧ s i ≤ t i ∧ t i ≤ R) →
      (∫⁻ z : (I → ℂ) × ℂ,
        (jointOdd a R (fun i : {i // odd i} => z.1 i) *
          ∏ i : {i // ¬odd i}, ENNReal.ofReal
            (spatialProfile (even i) M (s i) (t i) ‖z.1 i‖ / s i ^ 2)) *
          longEvenProfile sm tm H ‖z.2‖) ≤
        ENNReal.ofReal (C * Real.pi * sm ^ 2 * tm ^ 2 / H ^ 2 *
          (1 + Real.log (R / a)) ^ k) := by
  obtain ⟨C,hC,hb⟩ := lintegral_normalized_mixed_profiles hM k
  refine ⟨C,hC,?_⟩
  intro I _ hI odd _ even s t a R H sm tm ha haR hH hst
  let f (x : I → ℂ) := jointOdd a R (fun i : {i // odd i} => x i) *
    ∏ i : {i // ¬odd i}, ENNReal.ofReal
      (spatialProfile (even i) M (s i) (t i) ‖x i‖ / s i ^ 2)
  have hf : Measurable f := by
    apply Measurable.mul ((measurable_jointOdd a R).comp (by fun_prop))
    apply Finset.measurable_prod
    intro i _
    unfold spatialProfile MultipoleBKT.RouteLog.evenEdgeProfile
    have hnear : MeasurableSet {x : I → ℂ | ‖x i‖ ≤ M * s i} :=
      measurableSet_le (by fun_prop) measurable_const
    split_ifs <;> first
      | fun_prop
      | exact Measurable.ennreal_ofReal ((Measurable.ite hnear measurable_const (by fun_prop)).div_const _)
  have hg : Measurable (fun z : ℂ => longEvenProfile sm tm H ‖z‖) :=
    (measurable_longEvenProfile sm tm H).comp measurable_norm
  have hprod : (∫⁻ z : (I → ℂ) × ℂ, f z.1 * longEvenProfile sm tm H ‖z.2‖) =
      (∫⁻ x : I → ℂ, f x) * (∫⁻ z : ℂ, longEvenProfile sm tm H ‖z‖) := by
    rw [Measure.volume_eq_prod]
    exact lintegral_prod_mul hf.aemeasurable hg.aemeasurable
  change (∫⁻ z : (I → ℂ) × ℂ, f z.1 * longEvenProfile sm tm H ‖z.2‖) ≤ _
  rw [hprod]
  refine (mul_le_mul' (hb I hI odd even s t a R ha haR hst) (lintegral_longEvenProfile hH)).trans_eq ?_
  rw [← ENNReal.ofReal_mul (mul_nonneg hC.le (by
    apply pow_nonneg
    have := Real.log_nonneg ((one_le_div ha).2 haR)
    linarith))]
  congr 1
  ring

end MultipoleBKT.ExpansionK.RouteSpatial

end
