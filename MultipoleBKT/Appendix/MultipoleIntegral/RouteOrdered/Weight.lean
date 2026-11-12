/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.Basic

/-!
# The connected configuration weight

See upper-bound reduction
before (A.6). Keep the box restriction, the connected
linking graph, and the smoothed one-dipole weights.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {ι : Type*} [Fintype ι]
variable {χ : ℂ → ℝ} {lam β M : ℝ}

/-- The integrand `𝟙_{(Λ²)^ι} 𝟙_{𝓑} ∏ e^{β g_λ(x_i - y_i)}` of the upper bound (after the bond
bound). -/
noncomputable def connectedWeight (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ) (c : ι → ℂ × ℂ) : ℝ≥0∞ := by
  classical
  exact (Set.univ.pi fun _ : ι => box N ×ˢ box N).indicator (fun c =>
    (if (SimpleGraph.fromRel fun i j => MultipoleLinked M lam (c i) (c j)).Connected then 1 else 0) *
      ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c

theorem measurable_connectedWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (N : ℕ) (β M : ℝ) :
    Measurable (connectedWeight (ι := ι) χ N β lam M) := by
  classical
  unfold connectedWeight
  refine Measurable.indicator ?_ (measurableSet_pi_box_prod N)
  refine Measurable.mul (Measurable.ite
    (measurableSet_setOf_fromRel_multipoleLinked M lam (fun G => G.Connected))
    measurable_const measurable_const) ?_
  exact Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
    ((continuous_exp_smearedKernel_sub hχ hlam β).measurable.comp (measurable_pi_apply i))

end MultipoleBKT.MultipoleIntegral

end
