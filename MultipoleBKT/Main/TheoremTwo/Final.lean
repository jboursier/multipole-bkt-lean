/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.Assembly
public import MultipoleBKT.Limits.DipoleLimit

/-!
# Theorem 2 from the gates: the limiting activities discharged

`MultipoleBKT.TheoremTwo.limitingActivitiesExist` proves the input `LimitingActivitiesExist` of
the conditional assembly from Lemma 4.26, in the form
`MultipoleBKT.Limits.exists_limits_multipole` (any `M ≥ 1` works; the threshold is taken to be `1`).

`MultipoleBKT.TheoremTwo.theorem_2_of_gates'` is then Theorem 2 from the three gate statements alone: the frozen statements of
Propositions 4.23, 4.62 and 5.43 (`Prop423Statement`, `Prop462Statement`, `Prop543Statement`).
The three gates are proved, and the provider of the frozen Theorem 2
(`MultipoleBKT.Main.theorem_2`) is `theorem_2_of_gates'` applied to `proposition_4_23`,
`proposition_4_62` and `proposition_5_43`.
-/

@[expose] public section

namespace MultipoleBKT

namespace TheoremTwo

/-- **Existence of the limiting activities** `𝗆`, `𝗄^mult` (eqs. (2.45), (2.46); Lemma 4.26): the input `LimitingActivitiesExist` of `theorem_2_of_gates`, proved from
`MultipoleBKT.Limits.exists_limits_multipole`. -/
theorem limitingActivitiesExist : LimitingActivitiesExist := by
  intro χ hχ β hβ
  refine ⟨1, fun M hM => ?_⟩
  obtain ⟨msf, kmult, h⟩ := Limits.exists_limits_multipole hχ hβ hM
  exact ⟨msf, kmult, fun lam h0 _ => h lam h0⟩

/-- **Theorem 2** from the frozen
statements of the three gates, Propositions 4.23, 4.62 and 5.43, alone. The conclusion is the
type of the frozen statement `MultipoleBKT.theorem_2`. -/
theorem theorem_2_of_gates' (h423 : Prop423Statement) (h462 : Prop462Statement)
    (h543 : Prop543Statement) : Theorem2Statement :=
  theorem_2_of_gates h423 h462 h543 limitingActivitiesExist

end TheoremTwo

end MultipoleBKT

end
