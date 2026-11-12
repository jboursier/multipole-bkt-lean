/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.Basic
import MultipoleBKT.Potential.Regularity
import MultipoleBKT.Potential.DipoleInteraction

/-!
# The lower event and its Hessian interaction estimate

See Lemma A.3. The event uses the path in the prescribed label order.
The mixed Hessian integral is bounded by the global classical Hessian bound
supplied by the interaction Hessian estimate.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral.RouteChain

open MeasureTheory Set Finset

/-- The event `𝒞`: radii in `(λ,2λ)` and consecutive dipole distances in `(2λ,4λ)`. -/
def Event {ι : Type*} {k : ℕ} (lam : ℝ) (σ : ι ≃ Fin k) (c : ι → ℂ × ℂ) : Prop :=
  (∀ i, lam < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ < 2 * lam) ∧
    ∀ i j, (σ j : ℕ) = σ i + 1 →
      2 * lam < dipoleDist (c i) (c j) ∧ dipoleDist (c i) (c j) < 4 * lam

/-- The global Hessian estimate for the true dipole interaction. No separation
hypothesis is needed for the smoothed kernel. Integrate the classical Hessian
bound in (3.38) over the unit square, as in
Lemma A.3. -/
theorem abs_dipoleInteraction_hessian {χ : ℂ → ℝ} (hχ : IsMollifier χ) {B lam : ℝ}
    (hB : ∀ x, χ x ≤ B) (hlam : 0 < lam) (d e : ℂ × ℂ) :
    |dipoleInteraction χ lam d e| ≤
      (3 * (Real.pi * B / lam ^ 2)) * ‖d.1 - d.2‖ * ‖e.1 - e.2‖ := by
  rw [dipoleInteraction_eq_integral_hessian hχ hlam, abs_neg, ← Real.norm_eq_abs]
  apply RouteMixed.norm_integral_integral_le
  intro s _ t _
  let x := (1 / 2 : ℝ) • (e.1 + e.2 - d.1 - d.2) + s • (d.2 - d.1) + t • (e.2 - e.1)
  have hb : ‖fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) x‖ ≤
      3 * (Real.pi * B / lam ^ 2) := by
    rw [← twoRadiusKernel_self]
    exact norm_fderiv_fderiv_twoRadiusKernel_le hχ hB hlam hlam x
  calc _ ≤ ‖fderiv ℝ (fderiv ℝ (smearedKernel χ lam)) x‖ * ‖d.2 - d.1‖ * ‖e.2 - e.1‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ (3 * (Real.pi * B / lam ^ 2)) * ‖d.2 - d.1‖ * ‖e.2 - e.1‖ := by gcongr
    _ = _ := by rw [norm_sub_rev d.2, norm_sub_rev e.2]

/-- The interaction is uniformly bounded throughout `𝒞`, as asserted before
(A.15). The bound is independent of the number and separation of the dipoles. -/
theorem Event.abs_interaction_le {ι : Type*} {k : ℕ} {χ : ℂ → ℝ}
    (hχ : IsMollifier χ) {B lam : ℝ} (hB : ∀ x, χ x ≤ B) (hlam : 0 < lam)
    {σ : ι ≃ Fin k} {c : ι → ℂ × ℂ} (hc : Event lam σ c) (i j : ι) :
    |dipoleInteraction χ lam (c i) (c j)| ≤ 12 * Real.pi * B := by
  have hB0 := hχ.nonneg_of_le hB
  have h := abs_dipoleInteraction_hessian hχ hB hlam (c i) (c j)
  have hp := mul_le_mul (hc.1 i).2.le (hc.1 j).2.le (norm_nonneg _) (by positivity : 0 ≤ 2 * lam)
  have hL : 0 ≤ 3 * (Real.pi * B / lam ^ 2) := by positivity
  calc _ ≤ (3 * (Real.pi * B / lam ^ 2)) * ‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖ := h
    _ ≤ (3 * (Real.pi * B / lam ^ 2)) * ((2 * lam) * (2 * lam)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hp hL
    _ = _ := by field_simp; ring

/-- Summing the Hessian interaction bound on `𝒞`, before (A.15) in the
paper. The explicit bound uses `k²` pairs. -/
theorem Event.abs_sum_interaction_le {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
    {χ : ℂ → ℝ} (hχ : IsMollifier χ) {B lam : ℝ} (hB : ∀ x, χ x ≤ B) (hlam : 0 < lam)
    {σ : ι ≃ Fin k} {c : ι → ℂ × ℂ} (hc : Event lam σ c) :
    |∑ i : ι, ∑ j : ι, if i < j then dipoleInteraction χ lam (c i) (c j) else 0| ≤
      (Fintype.card ι : ℝ) ^ 2 * (12 * Real.pi * B) := by
  classical
  have hB0 := hχ.nonneg_of_le hB
  calc _ ≤ ∑ i : ι, |∑ j : ι, if i < j then dipoleInteraction χ lam (c i) (c j) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ∑ _j : ι, (12 * Real.pi * B) := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · exact hc.abs_interaction_le hχ hB hlam i j
      · rw [abs_zero]; positivity
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

end MultipoleBKT.MultipoleIntegral.RouteChain

end
