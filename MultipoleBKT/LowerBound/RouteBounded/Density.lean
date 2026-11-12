/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.ExpE11

/-!
# Finite density of a hierarchical expectation

(4.74),
proof of Proposition 4.23. Keep both the product of block normalizers and the
product dipole measure visible before integrating the tree expression.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical
open scoped Classical

/-- The hierarchical expectation as a finite product-measure integral.
This identity also covers a vanishing block normalizer. -/
theorem integral_model_eq_finite {ρ : Measure (ℂ × ℂ)} {β M lam : ℝ}
    {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)}
    (h : ModelHyp ρ β w ψ K) (X : Finset (Finset ℕ)) (f : (X.biUnion id → ℂ × ℂ) → ℝ) :
    ∫ y, f y ∂modelHierarchical ρ β w ψ M lam X =
      (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
        ∫ y, (∏ S ∈ X, blockWeightOf β w ψ M lam S (Multipole.extendConfig (X.biUnion id) y)) * f y
          ∂Measure.pi (fun _ : X.biUnion id => ρ) := by
  have hd := h.measurable_modelHierarchicalDensity (M := M) (lam := lam) X
  rw [modelHierarchical_eq, integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall fun y => ENNReal.prod_lt_top fun S _ => ENNReal.ofReal_lt_top)]
  have hden (y : X.biUnion id → ℂ × ℂ) :
      (∏ S ∈ X, ENNReal.ofReal ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
        hierBlockWeight β w ψ M lam X S y)).toReal =
        (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
          ∏ S ∈ X, blockWeightOf β w ψ M lam S (Multipole.extendConfig (X.biUnion id) y) := by
    rw [ENNReal.toReal_prod]
    simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 (h.modelPartitionFunction_nonneg M lam _))
      (hierBlockWeight_nonneg M lam h.nonneg_ψ X _ y))]
    rw [prod_mul_distrib, ← prod_inv_distrib]
    congr 1
    apply prod_congr rfl
    intro S hS
    have hr : (X.biUnion id).restrict (Multipole.extendConfig (X.biUnion id) y) = y := by
      funext i
      simp [Multipole.extendConfig, Finset.restrict, i.2]
    conv_lhs => rw [← hr]
    exact hierBlockWeight_restrict β w ψ M lam hS _
  simp_rw [hden, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

end MultipoleBKT.LowerBound.RouteBounded

end
