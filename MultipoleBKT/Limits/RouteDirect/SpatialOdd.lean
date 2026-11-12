/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.Radius
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.EndpointIntegration
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.ProfileReindex

/-!
# The retained odd tail in the limiting integrals

See (A.30) and
Lemma 4.26. The single maximum tail
is passed to the joint logarithmic integral without splitting it over edges.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph
open SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

variable {V : Type*} [Fintype V] [Nonempty V]

/-- The odd-tree factor is bounded by the joint spatial profile. -/
theorem globalTail_paperOdd_le {M lam : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam)
    (c : V → ℂ × ℂ) (A : Finset (Sym2 V)) :
    ENNReal.ofReal (globalTail (maxRad lam c) (paperDistE c) A *
      ∏ e ∈ A, paperOddE M lam c e) ≤
        jointOdd (minRad lam c) (maxRad lam c) (fun e : A => (paperDistE c e : ℂ)) := by
  by_cases hA : A.Nonempty
  · have : Nonempty A := hA.to_subtype
    by_cases hz : ∃ e ∈ A, paperOddE M lam c e = 0
    · obtain ⟨e, he, hz⟩ := hz
      rw [prod_eq_zero he hz, mul_zero, ENNReal.ofReal_zero]
      exact bot_le
    push Not at hz
    have hfar (e : Sym2 V) (he : e ∈ A) :
        minRad lam c < paperDistE c e ∧ paperOddE M lam c e = (paperDistE c e ^ 2)⁻¹ := by
      induction e using Sym2.ind with
      | h i j =>
        have hn : ¬MultipoleLinked M lam (c i) (c j) := by
          intro hn
          exact hz s(i, j) he (by change ite _ _ _ = 0; rw [ite_eq_left hn])
        have hs : minRad lam c ≤ min (rhoD lam (c i)) (rhoD lam (c j)) :=
          le_min (minRad_le lam c i) (minRad_le lam c j)
        have hdist : M * min (rhoD lam (c i)) (rhoD lam (c j)) < dipoleDist (c i) (c j) :=
          lt_of_not_ge hn
        have hmult : min (rhoD lam (c i)) (rhoD lam (c j)) ≤
            M * min (rhoD lam (c i)) (rhoD lam (c j)) :=
          le_mul_of_one_le_left (le_min (rhoD_pos hlam _).le (rhoD_pos hlam _).le) hM
        exact ⟨hs.trans_lt (hmult.trans_lt hdist), by change ite _ _ _ = _; rw [ite_eq_right hn]; rfl⟩
    have hd (e : Sym2 V) (he : e ∈ A) : 0 < paperDistE c e :=
      (minRad_pos hlam c).trans (hfar e he).1
    obtain ⟨e₀, he₀, hmax⟩ := exists_max_image A (paperDistE c) hA
    have hnorm (e : A) : ‖(paperDistE c e : ℂ)‖ = paperDistE c e :=
      by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd e e.property)]
    have hsup : univ.sup' univ_nonempty (fun e : A => ‖(paperDistE c e : ℂ)‖) =
        paperDistE c e₀ := by
      simp_rw [hnorm]
      apply le_antisymm
      · exact (sup'_le_iff _ _).mpr fun e _ => hmax e e.property
      · exact le_sup' (fun e : A => paperDistE c e) (mem_univ ⟨e₀, he₀⟩)
    unfold jointOdd
    rw [dite_eq_left ‹Nonempty A›, Set.indicator_of_mem (show
      (fun e : A => (paperDistE c e : ℂ)) ∈ {z : A → ℂ | ∀ e, minRad lam c < ‖z e‖} by
        intro e; rw [hnorm]; exact (hfar e e.property).1), hsup]
    rw [globalTail_eq_of_max he₀ hd hmax, ENNReal.ofReal_mul (by positivity)]
    simp_rw [div_pow]
    apply le_of_eq
    congr 1
    rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => paperOddE_nonneg M lam c e)]
    rw [← Finset.prod_coe_sort A]
    apply prod_congr rfl
    intro e _
    rw [hnorm, (hfar e e.property).2]
  · have hempty : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    have hi : IsEmpty A := ⟨fun e => hA ⟨e, e.property⟩⟩
    subst A
    unfold globalTail jointOdd
    simp only [fold_empty, Finset.prod_empty, mul_one, ENNReal.ofReal_one,
      dite_eq_right (not_nonempty_iff.mpr hi), le_refl]

end MultipoleBKT.Limits.RouteDirect

end
