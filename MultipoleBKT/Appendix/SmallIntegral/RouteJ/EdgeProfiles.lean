/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.CoreMajorant
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.ProfileReindex

/-!
# Comparing the actual edges with the normalized radial profiles

See Lemma A.4. The near indicator gives a disc
profile. The actual hatted even weight is bounded by its logarithmic profile.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Limits
open scoped Classical

/-- The normalized near or even radial profile of an unordered edge. -/
noncomputable def edgeProfile {V : Type*} (even : Bool) (M lam : ℝ)
    (c : V → ℂ × ℂ) : Sym2 V → ℝ :=
  symmLift (fun i j =>
    spatialProfile even M (min (rhoD lam (c i)) (rhoD lam (c j)))
      (max (rhoD lam (c i)) (rhoD lam (c j))) (dipoleDist (c i) (c j)) /
        min (rhoD lam (c i)) (rhoD lam (c j)) ^ 2)
    (fun i j => by rw [min_comm, max_comm, dipoleDist_comm])

theorem edgeProfile_mk {V : Type*} (even : Bool) (M lam : ℝ)
    (c : V → ℂ × ℂ) (i j : V) :
    edgeProfile even M lam c s(i, j) =
      spatialProfile even M (min (rhoD lam (c i)) (rhoD lam (c j)))
        (max (rhoD lam (c i)) (rhoD lam (c j))) (dipoleDist (c i) (c j)) /
          min (rhoD lam (c i)) (rhoD lam (c j)) ^ 2 := rfl

/-- The near weight equals its normalized disc profile. -/
theorem nearE_eq_edgeProfile {V : Type*} (M lam : ℝ) (c : V → ℂ × ℂ) (e : Sym2 V) :
    nearE M lam c e = edgeProfile false M lam c e := by
  induction e using Sym2.ind with
  | h i j => rfl

/-- The normalized actual hatted even edge is bounded by its radial profile. -/
theorem normalizedEven_le_edgeProfile {V : Type*} {M lam : ℝ}
    (hM : 1 ≤ M) (hlam : 0 < lam) (c : V → ℂ × ℂ) (e : Sym2 V) :
    normalizedEven M lam c e ≤ edgeProfile true M lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    unfold normalizedEven
    rw [minSq_mk, edgeProfile_mk]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have heq : aSqE M lam c s(i, j) + linkE M lam c s(i, j) =
        if MultipoleLinked M lam (c i) (c j) then 1 else ahat (c i) (c j) ^ 2 := by
      change (if MultipoleLinked M lam (c i) (c j) then 0 else ahat (c i) (c j) ^ 2) +
        (if MultipoleLinked M lam (c i) (c j) then 1 else 0) = _
      split_ifs <;> ring
    rw [heq]
    exact hatEven_le_profile hM hlam _ _

end MultipoleBKT.SmallIntegral.RouteJ

end
