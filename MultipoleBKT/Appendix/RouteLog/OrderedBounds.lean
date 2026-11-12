/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Ordered

/-!
# Uniform ordered radial bounds at and above the critical temperature

See the proof of Lemma A.4.
We scale the outer integral by `λ` and integrate its logarithmic moment.
The critical and supercritical inner moments remain separate until this step.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set Finset
open scoped ENNReal

private theorem ordered_bound_from_inner {β : ℝ} (hβ : 2 < β) (k q l : ℕ) (A σ : ℝ)
    (hA : 0 < A) (hσ : σ + (2 - β) = (4 - β) * (k + 2) - 2)
    (hinner : ∀ lam u : ℝ, 0 < lam → lam ≤ u →
      (∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 u),
        ENNReal.ofReal ((1 + Real.log (u / minimumRadius lam r)) ^ q) *
          ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β))) ≤
        ENNReal.ofReal (A * lam ^ σ * (1 + Real.log (u / lam)) ^ l)) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedLogIntegral β lam h k q ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  have hp : 0 < β - 2 := by linarith
  let C := 1 + A * momentConstant (β - 2) l
  have hC : 0 < C := by
    dsimp only [C]
    have := momentConstant_pos hp l
    positivity
  refine ⟨C, hC, fun lam h hlam _ => ?_⟩
  let E := (4 - β) * ((k : ℝ) + 2) - 2
  have htail : (∫⁻ u in Ioi lam,
      ENNReal.ofReal (u ^ (1 - β) * (1 + Real.log (u / lam)) ^ l)) ≤
      ENNReal.ofReal (lam ^ (2 - β) * momentConstant (β - 2) l) := by
    have he : 2 - β - 1 = 1 - β := by ring
    have he' : -(β - 2) = 2 - β := by ring
    simpa only [he, he'] using lintegral_logarithmic_tail_scaled hp hlam l
  have houter : (∫⁻ u in Ioc lam h, ENNReal.ofReal (u ^ (1 - β)) *
      ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 u),
        ENNReal.ofReal ((1 + Real.log (u / minimumRadius lam r)) ^ q) *
          ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β))) ≤
      ENNReal.ofReal (A * momentConstant (β - 2) l * lam ^ E) := by
    calc
      _ ≤ ∫⁻ u in Ioc lam h, ENNReal.ofReal (A * lam ^ σ) *
          ENNReal.ofReal (u ^ (1 - β) * (1 + Real.log (u / lam)) ^ l) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro u hu
        have hu0 : 0 < u := hlam.trans hu.1
        calc
          _ ≤ ENNReal.ofReal (u ^ (1 - β)) *
              ENNReal.ofReal (A * lam ^ σ * (1 + Real.log (u / lam)) ^ l) := by
            gcongr
            exact hinner lam u hlam hu.1.le
          _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _),
              ← ENNReal.ofReal_mul (mul_nonneg hA.le (Real.rpow_nonneg hlam.le _))]
            congr 1
            ring
      _ ≤ ∫⁻ u in Ioi lam, ENNReal.ofReal (A * lam ^ σ) *
          ENNReal.ofReal (u ^ (1 - β) * (1 + Real.log (u / lam)) ^ l) :=
        lintegral_mono_set Ioc_subset_Ioi_self
      _ = ENNReal.ofReal (A * lam ^ σ) *
          ∫⁻ u in Ioi lam, ENNReal.ofReal (u ^ (1 - β) * (1 + Real.log (u / lam)) ^ l) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (A * lam ^ σ) *
          ENNReal.ofReal (lam ^ (2 - β) * momentConstant (β - 2) l) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hA.le (Real.rpow_nonneg hlam.le _))]
        congr 1
        calc
          _ = A * momentConstant (β - 2) l * (lam ^ σ * lam ^ (2 - β)) := by ring
          _ = _ := by rw [← Real.rpow_add hlam, hσ]
  unfold orderedLogIntegral
  calc
    _ ≤ ENNReal.ofReal (lam ^ E) +
        ENNReal.ofReal (A * momentConstant (β - 2) l * lam ^ E) := add_le_add_right houter _
    _ = _ := by
      rw [← ENNReal.ofReal_add (Real.rpow_nonneg hlam.le _) (by
        exact mul_nonneg (mul_nonneg hA.le (momentConstant_pos hp l).le)
          (Real.rpow_nonneg hlam.le _))]
      congr 1
      dsimp only [C, E]
      ring

/-- The uniform ordered logarithmic radial estimate for `β ≥ 4`.
It includes the critical case without changing the temperature exponent. -/
theorem ordered_radial_ge_four_bound {β : ℝ} (hβ : 4 ≤ β) (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedLogIntegral β lam h k q ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  by_cases heq : β = 4
  · subst β
    let A := ((k : ℝ) + 1) * (1 / 2 + 1 / ((q : ℝ) + 1)) * (3 / 2 : ℝ) ^ k
    apply ordered_bound_from_inner (by norm_num) k q (k + 1 + q) A 0
      (by dsimp only [A]; positivity) (by ring)
    intro lam u hlam hlu
    have hb := lintegral_minimum_log_le_zero (k := k) q hlam hlu
    have hL : 0 ≤ 1 + Real.log (u / lam) := by
      have := Real.log_nonneg ((one_le_div hlam).2 hlu)
      linarith
    convert hb using 1
    · norm_num
    · dsimp only [A]
      simp (disch := positivity) only [Real.rpow_zero, mul_one, ENNReal.ofReal_mul,
        ENNReal.ofReal_pow, ENNReal.ofReal_add, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  · have hgt : 4 < β := lt_of_le_of_ne hβ (Ne.symm heq)
    let a := 4 - β
    have ha : a < 0 := by dsimp only [a]; linarith
    let c := 1 / 2 + 1 / (-a)
    have hc : 0 < c := by dsimp only [c]; have : 0 < -a := neg_pos.mpr ha; positivity
    let A := ((k : ℝ) + 1) * c ^ (k + 1)
    apply ordered_bound_from_inner (by linarith) k q q A (a * (k + 1))
      (by dsimp only [A]; positivity) (by dsimp only [a]; ring)
    intro lam u hlam hlu
    have hb := lintegral_minimum_log_le_of_neg (k := k) ha q hlam hlu
    have hL : 0 ≤ 1 + Real.log (u / lam) := by
      have := Real.log_nonneg ((one_le_div hlam).2 hlu)
      linarith
    have he : a - 2 = 2 - β := by dsimp only [a]; ring
    rw [he] at hb
    refine hb.trans (le_of_eq ?_)
    have hpow : lam ^ (a * (k + 1)) = (lam ^ a) ^ (k + 1) := by
      rw [Real.rpow_mul hlam.le,
        show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
    rw [hpow]
    dsimp only [A, c]
    simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_add, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

end MultipoleBKT.RouteLog

end
