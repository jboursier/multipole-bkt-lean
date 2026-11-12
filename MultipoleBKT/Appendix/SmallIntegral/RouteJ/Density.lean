/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.CoreMajorant
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.RadialRelabel

/-!
# The kernel-density comparison in the logarithmic radial integral

See Lemma A.4. Replace each density by the
regularized inverse power only after the spatial logarithms have been retained.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Set Limits
open scoped ENNReal

/-- The radial weight left after integrating the positions, with the original
single-dipole densities. -/
noncomputable def logDensityWeight {I : Type*} [Fintype I] [Nonempty I]
    (χ : ℂ → ℝ) (β lam : ℝ) (q : ℕ) (u : I → ℂ) : ℝ :=
  (1 + Real.log (maxRho lam u / minRho lam u)) ^ q *
    radialFactor lam (ofPosVec (fun _ => 0) u) *
      ∏ i, Real.exp (β * smearedKernel χ lam (u i))

/-- The logarithmic factor is nonnegative. -/
theorem logRatio_nonneg {I : Type*} [Fintype I] [Nonempty I] {lam : ℝ}
    (hlam : 0 < lam) (u : I → ℂ) : 0 ≤ 1 + Real.log (maxRho lam u / minRho lam u) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  have hm := (minRho_le_rho lam u i).trans (rho_le_maxRho lam u i)
  have h := Real.log_nonneg ((one_le_div (minRho_pos hlam u)).mpr hm)
  linarith

/-- The product kernel bound in (A.26), uniform in the finite carrier and λ. -/
theorem exists_logDensityWeight_le {χ : ℂ → ℝ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ (I : Type*) [Fintype I] [Nonempty I]
      (lam : ℝ), 0 < lam → ∀ (q : ℕ) (u : I → ℂ),
      logDensityWeight χ β lam q u ≤ Cg ^ Fintype.card I * logRadialWeight β lam q u := by
  obtain ⟨Cg, hCg, hexp⟩ := exists_exp_smearedKernel_le hχ hβ
  refine ⟨Cg, hCg, fun I _ _ lam hlam q u => ?_⟩
  have hp : (∏ i, Real.exp (β * smearedKernel χ lam (u i))) ≤
      Cg ^ Fintype.card I * ∏ i, rho lam (u i) ^ (-β) := by
    calc
      _ ≤ ∏ i, (Cg * rho lam (u i) ^ (-β)) :=
        prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun i _ => hexp lam hlam (u i)
      _ = _ := by rw [prod_mul_distrib]; simp
  have hrad0 : 0 ≤ radialFactor lam (ofPosVec (fun _ : I => 0) u) := by
    unfold radialFactor
    exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
      (Real.rpow_nonneg (hlam.le.trans (lam_le_maxRad lam _)) _)
  have hr : radialFactor lam (ofPosVec (fun _ : I => 0) u) *
      (∏ i, rho lam (u i) ^ (-β)) =
        maxRho lam u ^ (-2 : ℝ) * ∏ i, rho lam (u i) ^ (2 - β) := by
    unfold radialFactor
    simp only [rhoD_mk, ofPosVec_apply, maxRad_ofPosVec_eq]
    rw [mul_right_comm, ← prod_mul_distrib, mul_comm]
    congr 1
    apply prod_congr rfl
    intro i _
    rw [← Real.rpow_two, ← Real.rpow_add (rho_pos hlam _)]
    congr 1
  unfold logDensityWeight logRadialWeight
  calc
    _ ≤ (1 + Real.log (maxRho lam u / minRho lam u)) ^ q *
        radialFactor lam (ofPosVec (fun _ => 0) u) *
          (Cg ^ Fintype.card I * ∏ i, rho lam (u i) ^ (-β)) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (pow_nonneg (logRatio_nonneg hlam u) _) hrad0)
    _ = Cg ^ Fintype.card I * ((1 + Real.log (maxRho lam u / minRho lam u)) ^ q *
        (radialFactor lam (ofPosVec (fun _ => 0) u) * ∏ i, rho lam (u i) ^ (-β))) := by ring
    _ = _ := by rw [hr]

/-- A pair density restricted to a measurable set of lengths. The finite
and infinite hatted integrals use `Iic h` and `univ`, respectively. -/
noncomputable def restrictedPairDensity (χ : ℂ → ℝ) (β lam : ℝ) (D : Set ℝ)
    (c : ℂ × ℂ) : ℝ := pairDensity χ β lam c * D.indicator 1 ‖c.1 - c.2‖

theorem measurable_restrictedPairDensity {χ : ℂ → ℝ} {lam : ℝ} (hχ : IsMollifier χ)
    (hlam : 0 < lam) (β : ℝ) (D : Set ℝ) (hD : MeasurableSet D) :
    Measurable (restrictedPairDensity χ β lam D) := by
  unfold restrictedPairDensity
  exact (measurable_pairDensity hχ hlam β).mul
    ((measurable_const.indicator hD).comp (by fun_prop))

/-- At fixed vectors the restricted densities are independent of all positions. -/
theorem restrictedPairDensity_ofPosVec {I : Type*} {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    (β lam : ℝ) (D : Set ℝ) (x u : I → ℂ) (i : I) :
    restrictedPairDensity χ β lam D (ofPosVec x u i) =
      Real.exp (β * smearedKernel χ lam (u i)) * D.indicator 1 ‖u i‖ := by
  unfold restrictedPairDensity
  rw [pairDensity_ofPosVec hχ, norm_ofPosVec_sub]

end MultipoleBKT.SmallIntegral.RouteJ

end
