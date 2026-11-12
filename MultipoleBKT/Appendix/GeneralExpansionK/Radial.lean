/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.TreeIntegral
public import MultipoleBKT.Limits.Radial
public import MultipoleBKT.Limits.Kernels
public import MultipoleBKT.Appendix.RadialIntegral
public import TwoComponentCoulomb.LowerBound.PolarPi

/-!
# The largest regularized radius

See Lemma A.7. The largest regularized radius is defined on every finite carrier,
including the empty carrier. Its elementary bounds are shared by the
logarithmic radial calculations.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset Function
open scoped ENNReal
open Limits

variable {lam : ℝ}

/-! ### Several variables -/

section Several

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The largest radius `R(u) = max(λ, max_j ρ(u_j)) = max_j max(|u_j|, λ)`. -/
noncomputable def maxRho (lam : ℝ) (u : ι → ℂ) : ℝ := univ.fold max lam fun j => rho lam (u j)

omit [DecidableEq ι] in
theorem rho_le_maxRho (lam : ℝ) (u : ι → ℂ) (j : ι) : rho lam (u j) ≤ maxRho lam u :=
  (Finset.le_fold_max (rho lam (u j))).2 (Or.inr ⟨j, mem_univ _, le_rfl⟩)

omit [DecidableEq ι] in
theorem lam_le_maxRho (lam : ℝ) (u : ι → ℂ) : lam ≤ maxRho lam u :=
  (Finset.le_fold_max lam).2 (Or.inl le_rfl)

omit [DecidableEq ι] in
theorem maxRho_pos (hlam : 0 < lam) (u : ι → ℂ) : 0 < maxRho lam u :=
  hlam.trans_le (lam_le_maxRho lam u)

end Several

end ExpansionK

end MultipoleBKT

end
