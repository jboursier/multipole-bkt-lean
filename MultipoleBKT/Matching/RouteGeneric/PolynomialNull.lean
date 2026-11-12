/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Null zero sets of real polynomials

The polynomial argument in Section 4.1 of the paper. Induction on the number of real coordinates reduces to finitely many roots
in one variable, outside the null zero set of a nonzero coefficient.
-/

@[expose] public section

open MeasureTheory MvPolynomial

namespace MultipoleBKT.RouteGeneric

private theorem ae_eval_ne_zero_fin : ∀ n (p : MvPolynomial (Fin n) ℝ), p ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), eval x p ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    refine Filter.Eventually.of_forall fun x hx => hp ?_
    have he : eval x p = p.coeff 0 := by
      conv_lhs => rw [eq_C_of_isEmpty p]
      exact eval_C _
    rw [eq_C_of_isEmpty p, ← he, hx, C_0]
  | succ n ih =>
    intro p hp
    let P := finSuccEquiv ℝ n p
    have hP : P ≠ 0 := fun h => hp ((finSuccEquiv ℝ n).injective (h.trans (map_zero _).symm))
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have ha : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        ∀ᵐ t ∂(volume : Measure ℝ), eval (Fin.cons t x) p ≠ 0 := by
      filter_upwards [ih (P.coeff k) hk] with x hx
      have hmap : P.map (eval x) ≠ 0 := by
        intro h
        have := congrArg (fun Q : Polynomial ℝ => Q.coeff k) h
        exact hx (by simpa using this)
      have hf := (Polynomial.finite_setOfPred_isRoot hmap).measure_zero volume
      apply ae_iff.2
      simpa only [not_not, eval_eq_eval_mv_eval', Polynomial.IsRoot] using hf
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hmeas : MeasurableSet {v : ℝ × (Fin n → ℝ) | eval (e.symm v) p ≠ 0} := by
      exact ((continuous_eval p).measurable.comp e.symm.measurable)
        (measurableSet_singleton 0).compl
    have hprod : ∀ᵐ v ∂(volume : Measure (ℝ × (Fin n → ℝ))), eval (e.symm v) p ≠ 0 := by
      rw [Measure.volume_eq_prod]
      apply (Measure.ae_prod_iff_ae_ae hmeas).2
      apply (Measure.ae_ae_comm hmeas).2
      simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero] using ha
    simpa only [e, MeasurableEquiv.symm_apply_apply] using he.quasiMeasurePreserving.ae hprod

/-- A nonzero real polynomial in finitely many variables has a null zero set.
This is the exceptional-set argument of Section 4.1. -/
theorem volume_polynomial_zero {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    volume {x : ι → ℝ | eval x p = 0} = 0 := by
  let e := Fintype.equivFin ι
  have h := ae_eval_ne_zero_fin (Fintype.card ι) (rename e p)
    (by intro h; exact hp ((rename_injective e e.injective) (h.trans (map_zero _).symm)))
  have he := volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e.symm
  have h' := he.symm.quasiMeasurePreserving.ae h
  have ha : ∀ᵐ x ∂(volume : Measure (ι → ℝ)), eval x p ≠ 0 := by
    simpa [MeasurableEquiv.piCongrLeft, eval_rename, Function.comp_def, e] using h'
  simpa only [not_not] using ae_iff.1 ha

end MultipoleBKT.RouteGeneric

end
