/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.FrozenBounds
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Geometry
public import MultipoleBKT.Limits.Radial
public import MultipoleBKT.Appendix.GeneralExpansion.FrozenRoot

/-!
# The regularized root defect for the activity error

See Lemma A.7,
Step 3 of the proof of Lemma A.7. The root carries its screening defect or its
bad-point indicator. The numerator is the regularized root radius squared.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK

open MeasureTheory Set Finset Metric Function
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral UpperBound MultipoleIntegralZ GeneralExpansion Limits

variable {N p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

open scoped Classical in
/-- The root weight at the dipole `(y + w, y)`:
`𝟙_Λ(y) ((max(|w|, λ)/τ^Z)² 𝟙_{good} + 𝟙_{bad})`. -/
noncomputable def rootM (p₀ : ℕ) (β lam M ε₀ : ℝ) {N : ℕ} (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (w y : ℂ) : ℝ≥0∞ :=
  (box N).indicator 1 y *
    ((if IsGoodZ p₀ β lam M ε₀ V Z (y + w, y) then
        ENNReal.ofReal ((max ‖w‖ lam / goodRadiusZ p₀ β lam ε₀ V Z (y + w, y)) ^ 2) else 0) +
      (if IsGoodZ p₀ β lam M ε₀ V Z (y + w, y) then 0 else 1))

theorem measurable_rootM (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    Measurable (uncurry (rootM p₀ β lam M ε₀ V Z)) := by
  classical
  have he : Measurable fun q : ℂ × ℂ => (q.2 + q.1, q.2) := by fun_prop
  have hgood : MeasurableSet {q : ℂ × ℂ | IsGoodZ p₀ β lam M ε₀ V Z (q.2 + q.1, q.2)} :=
    he (measurableSet_isGoodZ p₀ β lam M ε₀ V Z)
  have hτ := (continuous_goodRadiusZ p₀ β lam ε₀ V Z).measurable.comp he
  unfold rootM
  refine ((measurable_one.indicator (TwoComponentCoulomb.measurableSet_box N)).comp
    measurable_snd).mul (Measurable.add ?_ ?_)
  · exact Measurable.ite hgood (ENNReal.measurable_ofReal.comp
      (((measurable_fst.norm.max measurable_const).div hτ).pow_const 2)) measurable_const
  · exact Measurable.ite hgood measurable_const measurable_const

end MultipoleBKT.ExpansionK

end
