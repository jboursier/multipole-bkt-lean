/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.TreeIntegral
public import MultipoleBKT.Limits.Radial

/-!
# Extremal radii

See Lemma A.4 and Lemma A.6. The maximum and minimum regularized radii are shared by
the logarithmic integrals and the activity-error integration.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open MeasureTheory Set Finset Filter Metric
open scoped ENNReal
open Limits

variable {χ : ℂ → ℝ} {β lam : ℝ}

/-! ### The largest and smallest radii -/

section Radii

variable {ι : Type*} [Fintype ι]

/-- The largest radius `R = max_i max(|u_i|, λ)` (at least `λ`). -/
noncomputable def maxRho (lam : ℝ) (u : ι → ℂ) : ℝ := univ.fold max lam fun i => rho lam (u i)

theorem rho_le_maxRho (lam : ℝ) (u : ι → ℂ) (i : ι) : rho lam (u i) ≤ maxRho lam u :=
  (Finset.le_fold_max (rho lam (u i))).2 (Or.inr ⟨i, mem_univ _, le_rfl⟩)

theorem lam_le_maxRho (lam : ℝ) (u : ι → ℂ) : lam ≤ maxRho lam u :=
  (Finset.le_fold_max lam).2 (Or.inl le_rfl)

theorem maxRho_pos (hlam : 0 < lam) (u : ι → ℂ) : 0 < maxRho lam u :=
  hlam.trans_le (lam_le_maxRho lam u)

theorem measurable_maxRho (lam : ℝ) : Measurable (maxRho (ι := ι) lam) := by
  classical
  unfold maxRho
  induction (univ : Finset ι) using Finset.induction_on with
  | empty => simp only [fold_empty]; exact measurable_const
  | insert a s ha ih =>
    simp only [fold_insert ha]
    exact ((measurable_rho lam).comp (measurable_pi_apply a)).max ih

variable [Nonempty ι]

/-- The smallest radius `ρ_* = min_i max(|u_i|, λ)`. -/
noncomputable def minRho (lam : ℝ) (u : ι → ℂ) : ℝ := univ.inf' univ_nonempty fun i => rho lam (u i)

theorem minRho_le_rho (lam : ℝ) (u : ι → ℂ) (i : ι) : minRho lam u ≤ rho lam (u i) :=
  inf'_le _ (mem_univ i)

theorem exists_minRho_eq (lam : ℝ) (u : ι → ℂ) : ∃ j, minRho lam u = rho lam (u j) := by
  obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' (univ_nonempty (α := ι)) fun i => rho lam (u i)
  exact ⟨j, hj⟩

theorem lam_le_minRho (lam : ℝ) (u : ι → ℂ) : lam ≤ minRho lam u :=
  (le_inf'_iff _ _).2 fun _ _ => lam_le_rho lam _

theorem minRho_pos (hlam : 0 < lam) (u : ι → ℂ) : 0 < minRho lam u :=
  hlam.trans_le (lam_le_minRho lam u)

theorem measurable_minRho (lam : ℝ) : Measurable (minRho (ι := ι) lam) := by
  have : minRho (ι := ι) lam =
      univ.inf' univ_nonempty (fun i => fun u : ι → ℂ => rho lam (u i)) := by
    funext u
    simp only [minRho, Finset.inf'_apply]
  rw [this]
  exact Finset.inf'_induction univ_nonempty _ (fun f hf g hg => hf.inf hg) fun i _ =>
    (measurable_rho lam).comp (measurable_pi_apply i)

end Radii

end SmallIntegral

end MultipoleBKT

end
