/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.ParityMajorant
public import MultipoleBKT.Appendix.GeneralExpansionK.RadialMain

/-!
# Uniform bounds on the dipole density

See Lemma A.7. The dipole density is bounded by a mollifier-dependent constant
times the negative beta power of the regularized radius. The model
assemblies use this elementary bound to justify finite-box integration.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset Function SimpleGraph
open scoped ENNReal
open Limits

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Densities -/

/-- The constant `C_g` with `e^{β g_λ(u)} ≤ C_g ρ_λ(u)^{-β}`
(`MultipoleBKT.Limits.exists_exp_smearedKernel_le`). -/
noncomputable def densConst (hχ : IsMollifier χ) (hβ : 0 ≤ β) : ℝ :=
  Classical.choose (exists_exp_smearedKernel_le hχ hβ)

theorem densConst_pos (hχ : IsMollifier χ) (hβ : 0 ≤ β) : 0 < densConst hχ hβ :=
  (Classical.choose_spec (exists_exp_smearedKernel_le hχ hβ)).1

theorem exp_le_densConst (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam) (u : ℂ) :
    Real.exp (β * smearedKernel χ lam u) ≤ densConst hχ hβ * rho lam u ^ (-β) :=
  (Classical.choose_spec (exists_exp_smearedKernel_le hχ hβ)).2 lam hlam u

/-! ### Constants depending only on the number of labels -/

section Consts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_simpleGraph_le : Fintype.card (SimpleGraph ι) ≤ 2 ^ (Fintype.card ι * Fintype.card ι) := by
  classical
  have h1 : Fintype.card (SimpleGraph ι) ≤ Fintype.card (Set (Sym2 ι)) :=
    Fintype.card_le_of_injective (fun G => G.edgeSet) SimpleGraph.edgeSet_injective
  rw [Fintype.card_set] at h1
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) card_sym2_le)

end Consts

end ExpansionK

end MultipoleBKT

end
