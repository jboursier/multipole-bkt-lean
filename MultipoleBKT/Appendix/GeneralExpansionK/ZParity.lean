/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.ZPointwise

/-!
# Vanishing of a frozen-model cluster at a bad label

See Lemma A.7, support restriction D.
The finite parity and five-subset assembly is in `RouteAssembly`.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK

open Finset Limits Hierarchical SmallIntegral

variable {χ : ℂ → ℝ} {β lam M : ℝ}
variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

theorem clusterQ_eq_zero_of {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ} (blk : ι → β')
    (Dn Dz Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) {i₀ : ι} (h0 : ψ (c i₀) = 0) :
    clusterQ β w ψ M lam blk Dn Dz Df c = 0 := by
  classical
  unfold clusterQ clusterG
  refine mul_eq_zero_of_left (mul_eq_zero_of_left (mul_eq_zero_of_left
    (prod_eq_zero (mem_univ (blk i₀)) ?_) _) _) _
  unfold blockWW
  exact mul_eq_zero_of_right _ (prod_eq_zero (mem_univ i₀) (by rw [ite_eq_left rfl, h0]))

end MultipoleBKT.ExpansionK

end
