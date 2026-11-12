/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremOne.Assembly
public import MultipoleBKT.Limits.DipoleLimit

/-!
# Theorem 1 from the gates: the dipole limits discharged

`MultipoleBKT.TheoremOne.dipoleLimitsExist` proves the input `DipoleLimitsExist` of the
conditional assembly from Lemma 4.26, eq. (2.34), in the form `MultipoleBKT.Limits.exists_tendsto_dipoleActivity`.

`MultipoleBKT.TheoremOne.theorem_1_of_gates'` is then Theorem 1 from the two gate statements alone: the frozen statements of
Proposition 4.23 (`MultipoleBKT.TheoremTwo.Prop423Statement`) and Proposition 5.45
(`Prop545Statement`). Both gates are proved, and the provider of the frozen Theorem 1
(`MultipoleBKT.Main.theorem_1`) is `theorem_1_of_gates'` applied to `proposition_4_23` and
`proposition_5_45`.
-/

@[expose] public section

namespace MultipoleBKT

namespace TheoremOne

/-- **Existence of the limits `𝗄^dip`** (eq. (2.34); Lemma 4.26): the input
`DipoleLimitsExist` of `theorem_1_of_gates`, proved from
`MultipoleBKT.Limits.exists_tendsto_dipoleActivity`. -/
theorem dipoleLimitsExist : DipoleLimitsExist := by
  intro χ hχ β hβ
  obtain ⟨kdip, h⟩ := Limits.exists_tendsto_dipoleActivity hχ hβ
  exact ⟨kdip, fun lam h0 _ k hk hkp V hV => (h lam h0).2.2 k hk hkp V hV⟩

/-- **Theorem 1** from the frozen
statements of Propositions 4.23 and 5.45 alone. The conclusion is the type of the frozen statement
`MultipoleBKT.theorem_1`. -/
theorem theorem_1_of_gates' (h423 : TheoremTwo.Prop423Statement) (h545 : Prop545Statement) :
    Theorem1Statement :=
  theorem_1_of_gates h423 h545 dipoleLimitsExist

end TheoremOne

end MultipoleBKT

end
