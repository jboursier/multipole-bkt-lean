/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RootBound
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Geometry
public import MultipoleBKT.UpperBound.Hierarchical.FrozenBounds
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Frozen-root geometry and compatibility declarations

See (A.40) and
(A.41). `rootZ` is the actual defect of the
root dipole, with its box indicator. `rootCentre` gives the four translated
bad endpoints. Its logarithmic integration is in `RouteLog/RootGeometry`.

The power declarations retained here are consumed by the external-gain and
cluster-error modules. They do not enter the multipole-error root estimate.
-/

@[expose] public section

namespace MultipoleBKT

namespace GeneralExpansion

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral UpperBound MultipoleIntegralZ

/-! ### The exponent `η` -/

/-- The compatibility exponent for the external-gain integration: `(4 - β)/2` for `β < 4`
and `1/(2(2p₀ + 1))` for `β ≥ 4`. -/
noncomputable def rootEta (p₀ : ℕ) (β : ℝ) : ℝ :=
  if β < 4 then (4 - β) / 2 else 1 / (2 * (2 * p₀ + 1))

theorem zero_lt_rootEta {p₀ : ℕ} {β : ℝ} : 0 < rootEta p₀ β := by
  unfold rootEta
  by_cases hβ : β < 4
  · rw [ite_eq_left hβ]; linarith
  · rw [ite_eq_right hβ]; positivity

theorem rootEta_le_two {p₀ : ℕ} {β : ℝ} (hβ : 2 < β) : rootEta p₀ β ≤ 2 := by
  unfold rootEta
  by_cases hβ4 : β < 4
  · rw [ite_eq_left hβ4]; linarith
  · rw [ite_eq_right hβ4]
    have : (1 : ℝ) ≤ 2 * (2 * p₀ + 1) := by
      have := (Nat.cast_nonneg p₀ : (0 : ℝ) ≤ p₀); linarith
    rw [div_le_iff₀ (by positivity)]
    linarith

/-! ### The charges of a bad dipole seen from the root -/

/-- The four points `x_j - w, y_j - w, x_j, y_j`: for the dipole `(y + w, y)`, the distances to the
charges of `z = (x_j, y_j)` are the distances from `y` to these points. -/
def rootCentre (z : ℂ × ℂ) (w : ℂ) : Fin 4 → ℂ :=
  ![z.1 - w, z.2 - w, z.1, z.2]

theorem exists_dipoleDist_root_eq (z : ℂ × ℂ) (w y : ℂ) :
    ∃ l : Fin 4, dipoleDist (y + w, y) z = ‖y - rootCentre z w l‖ := by
  unfold dipoleDist rootCentre
  simp only [Fin.exists_fin_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.exists_fin_zero, or_false]
  rw [show y - (z.1 - w) = y + w - z.1 by ring, show y - (z.2 - w) = y + w - z.2 by ring]
  rcases min_choice (min ‖y + w - z.1‖ ‖y + w - z.2‖) (min ‖y - z.1‖ ‖y - z.2‖) with h | h <;>
    rw [h]
  · rcases min_choice ‖y + w - z.1‖ ‖y + w - z.2‖ with h' | h' <;> rw [h']
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases min_choice ‖y - z.1‖ ‖y - z.2‖ with h' | h' <;> rw [h']
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (by simp)))

/-- `m²/max(m, d)² ≤ m^{2-η} d^{η-2}` for `m, d > 0` and `0 ≤ η ≤ 2`. -/
theorem sq_div_max_sq_le {m d η : ℝ} (hm : 0 < m) (hd : 0 < d) (hη0 : 0 ≤ η) (hη2 : η ≤ 2) :
    m ^ 2 / max m d ^ 2 ≤ m ^ (2 - η) * d ^ (η - 2) := by
  rcases le_total d m with hdm | hmd
  · rw [max_eq_left hdm, div_self (by positivity)]
    have h1 : d ^ (2 - η) ≤ m ^ (2 - η) := Real.rpow_le_rpow hd.le hdm (by linarith)
    have h2 : d ^ (2 - η) * d ^ (η - 2) = 1 := by
      rw [← Real.rpow_add hd]; simp
    have h3 : 0 ≤ d ^ (η - 2) := Real.rpow_nonneg hd.le _
    nlinarith
  · rw [max_eq_right hmd, div_le_iff₀ (by positivity)]
    have h1 : m ^ η ≤ d ^ η := Real.rpow_le_rpow hm.le hmd hη0
    have e1 : m ^ 2 = m ^ (2 - η) * m ^ η := by
      rw [← Real.rpow_add hm]; norm_num
    have e2 : d ^ (η - 2) * d ^ 2 = d ^ η := by
      rw [← Real.rpow_natCast d 2, ← Real.rpow_add hd]; norm_num
    rw [e1, mul_assoc, e2]
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hm.le _)

/-! ### The weight of the root dipole -/

section Root

variable {N p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

open scoped Classical in
/-- **The defect of the root dipole** `e = (y + w, y)` (eqs. (A.36) and (A.40)), with the
indicator of `y ∈ Λ`: `𝟙_Λ(y) ((|w|/τ_e^Z)² 𝟙_{e ∈ I_good^Z} + 𝟙_{e ∉ I_good^Z})`. -/
noncomputable def rootZ (p₀ : ℕ) (β lam M ε₀ : ℝ) {N : ℕ} (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (w y : ℂ) : ℝ≥0∞ :=
  (box N).indicator 1 y *
    ((if IsGoodZ p₀ β lam M ε₀ V Z (y + w, y) then
        ENNReal.ofReal ((‖w‖ / goodRadiusZ p₀ β lam ε₀ V Z (y + w, y)) ^ 2) else 0) +
      (if IsGoodZ p₀ β lam M ε₀ V Z (y + w, y) then 0 else 1))

theorem measurable_rootZ (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    Measurable (Function.uncurry (rootZ p₀ β lam M ε₀ V Z)) := by
  classical
  have he : Measurable fun q : ℂ × ℂ => (q.2 + q.1, q.2) := by fun_prop
  have hgood : MeasurableSet {q : ℂ × ℂ | IsGoodZ p₀ β lam M ε₀ V Z (q.2 + q.1, q.2)} :=
    he (measurableSet_isGoodZ p₀ β lam M ε₀ V Z)
  have hτ := (continuous_goodRadiusZ p₀ β lam ε₀ V Z).measurable.comp he
  unfold rootZ
  refine ((measurable_one.indicator (TwoComponentCoulomb.measurableSet_box N)).comp
    measurable_snd).mul (Measurable.add ?_ ?_)
  · exact Measurable.ite hgood (ENNReal.measurable_ofReal.comp
      ((measurable_fst.norm.div hτ).pow_const 2)) measurable_const
  · exact Measurable.ite hgood measurable_const measurable_const


end Root

/-- `R̄^y = λ^{-2p₀ y}` for `β ≥ 4`. -/
theorem truncationScale_rpow_of_ge {p₀ : ℕ} {β lam : ℝ} (hβ4 : 4 ≤ β) (hlam : 0 < lam) (y : ℝ) :
    truncationScale p₀ β lam ^ y = lam ^ (-(2 * (p₀ : ℝ)) * y) := by
  rw [Appendix.truncationScale_of_ge hβ4, ← Real.rpow_intCast, ← Real.rpow_mul hlam.le]
  congr 1
  push_cast
  ring


end GeneralExpansion

end MultipoleBKT

end
