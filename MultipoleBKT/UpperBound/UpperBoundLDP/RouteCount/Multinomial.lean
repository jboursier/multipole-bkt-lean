/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.Split
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Complex.Exponential

/-!
# Class counts in Proposition 5.38

The paper: Proposition 5.38. Labellings are grouped by their class counts before applying
the factorial entropy estimate. Zero class counts use `0 ^ 0 = 1`.
-/

@[expose] public section

namespace MultipoleBKT.UpperBoundLDP.RouteCount

open Finset

/-- The class counts of a labelling. -/
def counts {m K : ℕ} (f : Fin m → Fin K) : Fin K → ℕ := fun j => (fiber f j).card

/-- The exact number of labellings with prescribed class counts. -/
theorem card_counts {m K : ℕ} (n : Fin K → ℕ) (hn : ∑ j, n j = m) :
    (univ.filter fun f : Fin m → Fin K => counts f = n).card = Nat.multinomial univ n := by
  classical
  let d : (Fin K → ℕ) → (Fin K →₀ ℕ) := fun n => Finsupp.equivFunOnFinite.symm n
  have hd : Function.Injective d := Finsupp.equivFunOnFinite.symm.injective
  have hmon (n : Fin K → ℕ) :
      (∏ j, (MvPolynomial.X j : MvPolynomial (Fin K) ℕ) ^ n j) =
        MvPolynomial.monomial (d n) 1 := by
    rw [MvPolynomial.prod_X_pow]
    have he : Finsupp.indicator univ (fun i _ => n i) = d n := by
      ext j
      simp [d, Finsupp.indicator_apply]
    rw [he]
  have hpoly :
      (∑ j, (MvPolynomial.X j : MvPolynomial (Fin K) ℕ)) ^ m =
        ∑ f : Fin m → Fin K, MvPolynomial.monomial (d (counts f)) 1 := by
    rw [show (∑ j, (MvPolynomial.X j : MvPolynomial (Fin K) ℕ)) ^ m =
      ∏ _a : Fin m, ∑ j, (MvPolynomial.X j : MvPolynomial (Fin K) ℕ) by simp]
    rw [Fintype.prod_sum]
    apply sum_congr rfl
    intro f _
    rw [← prod_pow_card_fiber f, hmon]
    rfl
  have hm := Finset.sum_pow_eq_sum_piAntidiag univ
    (fun j => (MvPolynomial.X j : MvPolynomial (Fin K) ℕ)) m
  have hcoeff := congrArg (fun p : MvPolynomial (Fin K) ℕ => p.coeff (d n)) (hpoly.symm.trans hm)
  simp_rw [MvPolynomial.coeff_sum, hmon, ← map_natCast MvPolynomial.C, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_monomial] at hcoeff
  have he (q : Fin K → ℕ) : d q = d n ↔ q = n := hd.eq_iff
  simp only [he, mul_ite, mul_one, mul_zero] at hcoeff
  have hnmem : n ∈ piAntidiag (univ : Finset (Fin K)) m := by simp [hn]
  simpa only [sum_boole, sum_ite_eq', hnmem, ite_true, Nat.cast_id] using hcoeff

/-- Group the sum over labellings by the vector of class counts. -/
theorem sum_counts {m K : ℕ} {R : Type*} [CommSemiring R] (F : (Fin K → ℕ) → R) :
    ∑ f : Fin m → Fin K, F (counts f) =
      ∑ n ∈ piAntidiag (univ : Finset (Fin K)) m, (Nat.multinomial univ n : R) * F n := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := counts)
    (t := piAntidiag (univ : Finset (Fin K)) m) (fun f _ => by
      exact mem_piAntidiag.2 ⟨sum_card_fiber f, fun j _ => mem_univ j⟩)]
  apply sum_congr rfl
  intro n hn
  rw [sum_congr rfl (fun f hf => congrArg F (mem_filter.1 hf).2), sum_const,
    nsmul_eq_mul, card_counts n (mem_piAntidiag.1 hn).1]

end MultipoleBKT.UpperBoundLDP.RouteCount

end
