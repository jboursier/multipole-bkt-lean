/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.JIntegral
public import MultipoleBKT.Main.TheoremTwo.MeasurableClustering

/-!
# Measurability of the integrand of `J`

The integrand of `J` (eq. (A.17)) is a Borel function of the configuration: `jIntegrand` and the
separation indicators `∏_{S ∈ X} 𝟙_{𝓑_S}` (`measurable_jIntegrand`,
`measurable_prod_connOn_indicator`), hence `jFullIntegrand` (`measurable_jFullIntegrand`). This is
used to integrate the pointwise bound of `MultipoleBKT.UpperBound.BoundedUpper.Pointwise` term by
term.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Parity Quadratic Peeling Multipole

section Measurability

theorem measurable_finset_sup_nnreal {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    {f : ι → α → ℝ≥0} (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun x => s.sup fun i => f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty]
    exact measurable_const
  | insert a s ha ih =>
    simp only [Finset.sup_insert]
    exact (hf a (mem_insert_self a s)).sup (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem measurable_dipoleDist_apply (i j : ℕ) :
    Measurable fun c : ℕ → ℂ × ℂ => dipoleDist (c i) (c j) := by
  unfold dipoleDist
  fun_prop

theorem measurable_blockRad (S : Finset ℕ) : Measurable fun c : ℕ → ℂ × ℂ => blockRad c S := by
  unfold blockRad
  refine measurable_coe_nnreal_real.comp (measurable_finset_sup_nnreal S fun i _ => ?_)
  exact (((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd).nnnorm)

theorem measurable_radialExceptMax (Y : Finset (Finset ℕ)) :
    Measurable fun c : ℕ → ℂ × ℂ => radialExceptMax c Y := by
  unfold radialExceptMax
  exact (Finset.measurable_prod _ fun S _ => (measurable_blockRad S).pow_const 2).div
    ((measurable_blockRad _).pow_const 2)

theorem measurable_distOn {W : Finset ℕ} (e : Sym2 W) :
    Measurable fun c : ℕ → ℂ × ℂ => distOn (fun i : W => c i) e := by
  induction e using Sym2.ind with
  | h i j => exact measurable_dipoleDist_apply i j

theorem measurable_cutOn {W : Finset ℕ} (M lam ε₀ R : ℝ) (e : Sym2 W) :
    Measurable fun c : ℕ → ℂ × ℂ => cutOn M lam ε₀ R (fun i : W => c i) e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [cutOn, Sym2.lift_mk]
    refine Measurable.mul ?_ ?_
    · exact Measurable.ite (measurableSet_setOf_multipoleLinked M lam (i : ℕ) (j : ℕ))
        measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le (measurable_dipoleDist_apply i j) measurable_const)
        measurable_const measurable_const

theorem measurable_keptLift {W : Finset ℕ} (M lam ε₀ R : ℝ) (e : Sym2 W) :
    Measurable fun c : ℕ → ℂ × ℂ => keptLift M lam ε₀ R c e := by
  unfold keptLift keptWeight
  exact (measurable_cutOn M lam ε₀ R e).div ((measurable_distOn e).pow_const 2)

theorem measurable_absOddWeight' (M lam ε₀ R : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => absOddWeight M lam ε₀ R q.1 q.2 := by
  classical
  unfold absOddWeight
  have hd : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => dipoleDist q.1 q.2 := by
    unfold dipoleDist
    fun_prop
  refine ((Measurable.div (by fun_prop) (hd.mul (hd.max (by fun_prop)))).mul ?_).mul ?_
  · exact Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const
  · exact Measurable.ite (measurableSet_le hd measurable_const) measurable_const measurable_const

theorem measurable_absEvenWeight' (M lam ε₀ R : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => absEvenWeight M lam ε₀ R q.1 q.2 := by
  classical
  unfold absEvenWeight
  exact ((measurable_absOddWeight' M lam ε₀ R).pow_const 2).add
    (Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const)

theorem measurable_absEvenLift {W : Finset ℕ} (M lam ε₀ R : ℝ) (e : Sym2 W) :
    Measurable fun c : ℕ → ℂ × ℂ => absEvenLift M lam ε₀ R c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [absEvenLift, Sym2.lift_mk]
    have h : Measurable fun c : ℕ → ℂ × ℂ => ((c i, c j) : (ℂ × ℂ) × (ℂ × ℂ)) :=
      (measurable_pi_apply (i : ℕ)).prodMk (measurable_pi_apply (j : ℕ))
    have hc := (measurable_absEvenWeight' M lam ε₀ R).comp h
    exact hc

theorem measurable_maxEdgeDist {W : Finset ℕ} (T : SimpleGraph W) [DecidableRel T.Adj] :
    Measurable fun c : ℕ → ℂ × ℂ => maxEdgeDist c T := by
  unfold maxEdgeDist
  exact measurable_finset_sup_nnreal _ fun e _ => measurable_real_toNNReal.comp
    (measurable_distOn e)

open scoped Classical in
theorem measurable_jTail (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id)) :
    Measurable fun c : ℕ → ℂ × ℂ => jTail c X Xs Ta := by
  unfold jTail
  refine ((measurable_blockRad _).div ((measurable_coe_nnreal_real.comp
    (measurable_finset_sup_nnreal _ fun l _ => measurable_maxEdgeDist (Ta l))).max
      (measurable_blockRad _))).pow_const 2

open scoped Classical in
theorem measurable_jIntegrand (M lam ε₀ R : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) :
    Measurable (jIntegrand M lam ε₀ R X Xs Ta Tb) := by
  unfold jIntegrand
  refine (((measurable_jTail X Xs Ta).mul ?_).mul ?_).mul ?_
  · exact Finset.measurable_prod _ fun l _ => measurable_radialExceptMax _
  · exact Finset.measurable_prod _ fun l _ => Finset.measurable_prod _ fun e _ =>
      measurable_keptLift M lam ε₀ R e
  · exact Finset.measurable_prod _ fun e _ => measurable_absEvenLift M lam ε₀ R e

open scoped Classical in
theorem measurableSet_connOn_linkedPairs (M lam : ℝ) (S : Finset ℕ) :
    MeasurableSet {c : ℕ → ℂ × ℂ | ConnOn S (linkedPairs M lam c S)} := by
  have h : TheoremTwo.FiberMeasurable fun c : ℕ → ℂ × ℂ => linkedPairs M lam c S := by
    have := TheoremTwo.fiberMeasurable_filter (α := ℕ → ℂ × ℂ) (pairsOn S)
      (P := fun c q => MultipoleLinked M lam (c q.1) (c q.2))
      fun q => measurableSet_setOf_multipoleLinked M lam q.1 q.2
    convert this using 2 with c
    ext q
    rw [mem_linkedPairs, Finset.mem_filter]
  exact h.measurableSet (fun E => ConnOn S E)

open scoped Classical in
theorem measurable_prod_connOn_indicator (M lam : ℝ) (X : Finset (Finset ℕ)) :
    Measurable fun c : ℕ → ℂ × ℂ =>
      ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) :=
  Finset.measurable_prod _ fun S _ =>
    Measurable.ite (measurableSet_connOn_linkedPairs M lam S) measurable_const measurable_const

theorem measurable_jFullIntegrand {χ : ℂ → ℝ} (hχ : IsMollifier χ) {lam : ℝ} (hlam : 0 < lam)
    (M ε₀ R β : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) :
    Measurable (jFullIntegrand M lam ε₀ R χ β X Xs Ta Tb) := by
  classical
  unfold jFullIntegrand
  refine (((measurable_jIntegrand M lam ε₀ R X Xs Ta Tb).comp (measurable_extendConfig _)).mul
    ((measurable_prod_connOn_indicator M lam X).comp (measurable_extendConfig _))).mul ?_
  refine Finset.measurable_prod _ fun i _ => ?_
  have hsub : Measurable fun y : X.biUnion id → ℂ × ℂ => (y i).1 - (y i).2 :=
    (measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd
  refine ((measurable_exp_smearedKernel hχ hlam β).comp hsub).mul ?_
  exact (measurable_const.indicator Metric.isClosed_closedBall.measurableSet).comp hsub

end Measurability

end BoundedUpper

end UpperBound

end MultipoleBKT

end
