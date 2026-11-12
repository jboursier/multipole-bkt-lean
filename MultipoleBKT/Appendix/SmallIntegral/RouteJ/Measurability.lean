/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.ConfigurationMajorant

/-!
# Measurability of the retained-tree majorant

See Lemma A.4. The majorant is measurable even
when the original selection of a largest block is given without measurability.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Limits Peeling
open scoped Classical ENNReal

variable {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B] [Nonempty V]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
private theorem measurable_minSq (lam : ℝ) (e : Sym2 V) : Measurable fun c => minSq lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [minSq_mk]
    have hi : Measurable (fun c : V → ℂ × ℂ => rhoD lam (c i)) :=
      (measurable_rhoD lam).comp (measurable_pi_apply i)
    have hj : Measurable (fun c : V → ℂ × ℂ => rhoD lam (c j)) :=
      (measurable_rhoD lam).comp (measurable_pi_apply j)
    exact (hi.min hj).pow_const 2

omit [Fintype V] [DecidableEq V] [Nonempty V] in
/-- Measurability of the normalized actual hatted even edge. -/
theorem measurable_normalizedEven (M lam : ℝ) (e : Sym2 V) :
    Measurable fun c : V → ℂ × ℂ => normalizedEven M lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    have hA : Measurable fun c : V → ℂ × ℂ => ahat (c i) (c j) := by
      unfold ahat
      have hd : Measurable (fun c : V → ℂ × ℂ => dipoleDist (c i) (c j)) :=
        measurable_dipoleDist.comp (show Measurable (fun c : V → ℂ × ℂ => (c i, c j)) by fun_prop)
      fun_prop
    have hset := measurableSet_setOf_multipoleLinked M lam i j
    apply Measurable.div _ (measurable_minSq lam s(i, j))
    exact (Measurable.ite hset measurable_const (hA.pow_const 2)).add
      (Measurable.ite hset measurable_const measurable_const)

/-- Measurability of a whole retained-tree term, including its coupled tail. -/
theorem measurable_retainedTreeTerm (blk : V → B) (M lam : ℝ)
    (A E : Finset (Sym2 V)) (R : NearTreeFamily blk) :
    Measurable (retainedTreeTerm blk M lam A E R) := by
  have hd (e : Sym2 V) : Measurable fun c : V → ℂ × ℂ => (dipoleDistOn c e : ℂ) := by
    induction e using Sym2.ind with
    | h i j =>
      simp only [dipoleDistOn_mk]
      have hm : Measurable (fun c : V → ℂ × ℂ => dipoleDist (c i) (c j)) :=
        measurable_dipoleDist.comp (show Measurable (fun c : V → ℂ × ℂ => (c i, c j)) by fun_prop)
      exact Complex.measurable_ofReal.comp hm
  have hrad : Measurable (radialFactor (V := V) lam) := by
    unfold radialFactor
    exact (Finset.measurable_prod _ fun i _ =>
      ((measurable_rhoD lam).comp (measurable_pi_apply i)).pow_const 2).mul
        ((measurable_maxRad lam).pow_const (-2 : ℝ))
  unfold retainedTreeTerm
  exact (measurable_jointOdd_comp _ _ _ (measurable_minRad lam) (measurable_maxRad lam)
    (measurable_pi_iff.mpr fun e : A => hd e.val)).mul
      (hrad.ennreal_ofReal.mul
        ((Finset.measurable_prod E fun e _ => (measurable_normalizedEven M lam e).ennreal_ofReal).mul
          (Finset.measurable_prod (nearForest blk (fun b => (R b).val)) fun e _ => (measurable_nearE M lam e).ennreal_ofReal)))

end MultipoleBKT.SmallIntegral.RouteJ

end
