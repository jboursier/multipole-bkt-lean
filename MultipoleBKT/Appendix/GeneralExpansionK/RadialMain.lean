/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.TreeSharp

/-!
# The smallest regularized radius

See Lemma A.7. On a nonempty finite carrier the smallest regularized radius is
attained, is bounded below by lambda and is positive for positive lambda.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset Function
open scoped ENNReal
open Limits

variable {lam : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The smallest radius -/

section MinRho

variable [Nonempty ι]

/-- The smallest radius `m(u) = min_j ρ(u_j)`. -/
noncomputable def minRho (lam : ℝ) (u : ι → ℂ) : ℝ := univ.inf' univ_nonempty fun j => rho lam (u j)

omit [DecidableEq ι] in
theorem minRho_le_rho (lam : ℝ) (u : ι → ℂ) (j : ι) : minRho lam u ≤ rho lam (u j) :=
  inf'_le _ (mem_univ j)

omit [DecidableEq ι] in
theorem exists_minRho_eq (lam : ℝ) (u : ι → ℂ) : ∃ j, minRho lam u = rho lam (u j) := by
  obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' (univ_nonempty (α := ι)) fun j => rho lam (u j)
  exact ⟨j, hj⟩

omit [DecidableEq ι] in
theorem lam_le_minRho (lam : ℝ) (u : ι → ℂ) : lam ≤ minRho lam u := by
  obtain ⟨j, hj⟩ := exists_minRho_eq lam u
  rw [hj]
  exact lam_le_rho lam _

omit [DecidableEq ι] in
theorem minRho_pos (hlam : 0 < lam) (u : ι → ℂ) : 0 < minRho lam u :=
  hlam.trans_le (lam_le_minRho lam u)

end MinRho

end ExpansionK

end MultipoleBKT

end
