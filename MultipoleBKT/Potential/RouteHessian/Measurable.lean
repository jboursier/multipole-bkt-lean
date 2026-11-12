/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.Polar

/-!
# Measurability and local integrability of the radial Hessian

See Lemma 3.1 of the paper. The radial tensor is measurable for bounded measurable sources.
Its operator bound gives local integrability on the whole plane, including zero.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace ENNReal

namespace MultipoleBKT.RouteHessian

open RouteFlux

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- Measurability of the radial tensor requires no continuity of the density. -/
theorem measurable_radialHessian (hχ : IsMollifier χ) :
    Measurable (radialHessian χ lam) := by
  have hm := (massProfile_mono hχ lam).measurable
  have hd : Measurable (massDensity χ lam) := by
    unfold massDensity density
    exact (measurable_const.mul measurable_id).mul
      (measurable_const.mul (hχ.measurable.comp
        (Complex.continuous_ofReal.div_const _).measurable))
  have ha : Measurable (fun x : ℂ => tangentialCoefficient χ lam ‖x‖) :=
    (hm.comp measurable_norm).div (measurable_norm.pow_const 2)
  have hb : Measurable (fun x : ℂ => densityCoefficient χ lam ‖x‖) :=
    (hd.comp measurable_norm).div measurable_norm
  have hu : Measurable (fun x : ℂ => ‖x‖⁻¹ • x) :=
    measurable_norm.inv.smul measurable_id
  have hp : Measurable (fun x : ℂ =>
      (innerSL ℝ (‖x‖⁻¹ • x)).smulRight (‖x‖⁻¹ • x)) := by
    exact (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := ℂ) (F := ℂ)).continuous.measurable.comp
      (((innerSL ℝ).continuous.measurable.comp hu).prodMk hu)
  exact ha.neg.smul measurable_const |>.add ((ha.const_mul 2 |>.sub hb).smul hp)

/-- The tensor is locally integrable even on compact sets containing the origin. -/
theorem locallyIntegrable_radialHessian (hχ : IsMollifier χ) (hlam : 0 < lam) :
    LocallyIntegrable (radialHessian χ lam) volume := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact IntegrableOn.of_bound hK.measure_lt_top
    (measurable_radialHessian hχ).aestronglyMeasurable _
    (Eventually.of_forall (norm_radialHessian_le hχ hM hlam))

/-- The explicit operator bound is also an essential bound on the plane. -/
theorem ae_norm_radialHessian_le (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam) :
    ∀ᵐ x : ℂ, ‖radialHessian χ lam x‖ ≤ 3 * (Real.pi * M / lam ^ 2) :=
  Eventually.of_forall (norm_radialHessian_le hχ hM hlam)

/-- The radial weak-Hessian tensor belongs to `L∞` on the whole plane. -/
theorem memLp_radialHessian_top (hχ : IsMollifier χ) (hlam : 0 < lam) :
    MemLp (radialHessian χ lam) ∞ volume := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  exact memLp_top_of_bound (measurable_radialHessian hχ).aestronglyMeasurable
    (3 * (Real.pi * M / lam ^ 2)) (ae_norm_radialHessian_le hχ hM hlam)

end MultipoleBKT.RouteHessian

end
