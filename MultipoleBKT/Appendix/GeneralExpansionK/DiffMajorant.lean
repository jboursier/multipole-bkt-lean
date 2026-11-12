/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.GeneralModel
public import MultipoleBKT.Appendix.GeneralExpansionK.DfMajorant
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ParityExpansion

/-!
# Cancellation of linked far bonds

See Lemma A.7. A linked pair annihilates the far odd and even bonds. These support
identities are used before the separate graph estimates.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph
open Hierarchical Multipole Parity Limits SmallIntegral

variable {β lam M : ℝ}

/-! ### The pointwise majorants -/

section Pointwise

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

omit [Fintype ι] [DecidableEq ι] in
/-- On a linked pair, the even part plus the indicator vanishes. -/
theorem alphaW_add_linkIndE_of_linked {w : ℂ × ℂ → ℂ × ℂ → ℝ} (c : ι → ℂ × ℂ) {e : Sym2 ι}
    (he : ¬ FarE M lam c e) : alphaW β w M lam c e + linkIndE M lam c e = 0 := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    have hl : MultipoleLinked M lam (c i) (c j) := not_not.1 he
    simp only [alphaW, linkIndE, symmLift_mk, linkInd, ite_eq_left hl]
    norm_num

omit [Fintype ι] [DecidableEq ι] in
theorem gammaW_of_linked {w : ℂ × ℂ → ℂ × ℂ → ℝ} (c : ι → ℂ × ℂ) {e : Sym2 ι}
    (he : ¬ FarE M lam c e) : gammaW β w M lam c e = 0 := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    have hl : MultipoleLinked M lam (c i) (c j) := not_not.1 he
    simp only [gammaW, symmLift_mk, ite_eq_left hl]

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem linkIndE_of_far (c : ι → ℂ × ℂ) {e : Sym2 ι} (he : FarE M lam c e) :
    linkIndE M lam c e = 0 := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    have hl : ¬ MultipoleLinked M lam (c i) (c j) := he
    simp only [linkIndE, symmLift_mk, linkInd, ite_eq_right hl]

variable {w₁ w₀ : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ₁ ψ₀ : ℂ × ℂ → ℝ}

end Pointwise

end ExpansionK

end MultipoleBKT

end
