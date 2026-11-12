/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.Majorant
public import MultipoleBKT.Limits.Reversal

/-!
# The far-pair indicator

See Lemma A.7. The far-pair indicator is nonnegative and measurable. The elementary
unordered-pair count bounds the finite expansions.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open Finset SimpleGraph
open Limits

variable {χ : ℂ → ℝ} {β lam M : ℝ}

section Def

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [Fintype β'] [DecidableEq β']

open scoped Classical in
/-- The indicator `𝟙_{𝓑_ij^c}` of a far pair. -/
noncomputable def farInd (M lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => if MultipoleLinked M lam (c i) (c j) then 0 else 1) fun _ _ =>
    if_congr multipoleLinked_comm rfl rfl

omit [Fintype ι] [DecidableEq ι] in
theorem farInd_nonneg (c : ι → ℂ × ℂ) (e : Sym2 ι) : 0 ≤ farInd M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show 0 ≤ (if MultipoleLinked M lam (c i) (c j) then (0 : ℝ) else 1)
    split_ifs <;> norm_num

end Def

/-! ### The pointwise bound -/

section Pointwise

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [Fintype β'] [DecidableEq β']

omit [DecidableEq ι] in
theorem card_sym2_le : Fintype.card (Sym2 ι) ≤ Fintype.card ι * Fintype.card ι := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_surjective _ Sym2.mk_surjective

end Pointwise

/-! ### Measurability -/

section Meas

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [Fintype β'] [DecidableEq β']

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_farInd (M lam : ℝ) (e : Sym2 ι) :
    Measurable fun c : ι → ℂ × ℂ => farInd M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show Measurable fun c : ι → ℂ × ℂ =>
      (if MultipoleLinked M lam (c i) (c j) then (0 : ℝ) else 1)
    exact Measurable.ite (measurableSet_setOf_multipoleLinked M lam i j) measurable_const
      measurable_const

end Meas

end ExpansionK

end MultipoleBKT

end
