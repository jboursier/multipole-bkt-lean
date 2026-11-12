/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.SquareMoment
public import MultipoleBKT.Appendix.RouteLog.Ordered
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Radial
import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Polar

/-!
# The three cutoff-tail integrations

See Step 3 of
the proof of Lemma A.6. Retain the ordered inner radial
integral, then integrate its power, logarithm or constant in the three
regimes. No temperature exponent is changed before the integration.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set
open scoped ENNReal
open MultipoleIntegral

/-- The ordered tail in the plane is the literal nested radial integral,
including its angular factor. -/
theorem lintegral_ordered_tail_profile {β lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h) (n : ℕ) :
    ∫⁻ z : ℂ, {z : ℂ | h < ‖z‖}.indicator
        (fun z => ENNReal.ofReal (max ‖z‖ lam ^ (-β)) * orderedInner β lam ‖z‖ ^ n) z =
      ENNReal.ofReal (2 * Real.pi) * orderedRadial β lam (Ioi h) n := by
  let f (r : ℝ) := (Ioi h).indicator
    (fun r => ENNReal.ofReal (max r lam ^ (-β)) * orderedInner β lam r ^ n) r
  have hf : Measurable f := by
    refine Measurable.indicator ?_ measurableSet_Ioi
    exact (ENNReal.measurable_ofReal.comp
      ((continuous_id.max continuous_const).rpow_const
        (fun r => Or.inl (lt_max_of_lt_right hlam).ne')).measurable).fun_mul
      ((orderedInner_mono β lam).measurable.pow_const n)
  have he : (fun z : ℂ => {z : ℂ | h < ‖z‖}.indicator
      (fun z => ENNReal.ofReal (max ‖z‖ lam ^ (-β)) * orderedInner β lam ‖z‖ ^ n) z) =
      fun z : ℂ => f ‖z‖ := by
    funext z
    rfl
  rw [he, lintegral_norm_eq f hf]
  congr 1
  have hp : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * f r =
      (Ioi h).indicator
        (fun r => ENNReal.ofReal (r * max r lam ^ (-β)) * orderedInner β lam r ^ n) r := by
    intro r hr
    by_cases hhr : h < r
    · dsimp only [f]
      rw [indicator_of_mem (s := Ioi h) hhr, indicator_of_mem (s := Ioi h) hhr, ← mul_assoc, ← ENNReal.ofReal_mul hr.le]
    · simp [f, hhr]
  rw [setLIntegral_congr_fun measurableSet_Ioi hp, setLIntegral_indicator measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hh.le)]
  rfl

/-- Internal evaluation of a logarithmic tail after the inner radii have
been integrated. The hypotheses concern the scalar inner profile only. -/
theorem internal_ordered_tail_log_le {β lam h A s : ℝ} {n q : ℕ}
    (hlam : 0 < lam) (hlh : lam ≤ h) (hA : 0 ≤ A) (hp : 0 < β - s - 2)
    (hinner : ∀ r : ℝ, h < r → orderedInner β lam r ^ n ≤
      ENNReal.ofReal (A * r ^ s * (1 + Real.log (r / lam)) ^ q)) :
    orderedRadial β lam (Ioi h) n ≤ ENNReal.ofReal
      (A * RouteLog.momentConstant (β - s - 2) q * h ^ (-(β - s - 2)) *
        (1 + Real.log (h / lam)) ^ q) := by
  have hh : 0 < h := hlam.trans_le hlh
  let p := β - s - 2
  have hL : 0 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  have hpt : ∀ r ∈ Ioi h,
      ENNReal.ofReal (r * max r lam ^ (-β)) * orderedInner β lam r ^ n ≤
        ENNReal.ofReal (A * (1 + Real.log (h / lam)) ^ q) *
          ENNReal.ofReal (r ^ (-p - 1) * (1 + Real.log (r / h)) ^ q) := by
    intro r hr
    have hr0 : 0 < r := hh.trans hr
    have hrl : lam ≤ r := hlh.trans hr.le
    have hlogh : 0 ≤ Real.log (h / lam) := Real.log_nonneg ((one_le_div hlam).2 hlh)
    have hlogr : 0 ≤ Real.log (r / h) := Real.log_nonneg ((one_le_div hh).2 hr.le)
    have he : Real.log (r / lam) = Real.log (r / h) + Real.log (h / lam) := by
      rw [← Real.log_mul (div_pos hr0 hh).ne' (div_pos hh hlam).ne']
      congr 1
      field_simp
    have hlog : (1 + Real.log (r / lam)) ^ q ≤
        ((1 + Real.log (h / lam)) * (1 + Real.log (r / h))) ^ q := by
      apply pow_le_pow_left₀ (by rw [he]; positivity)
      rw [he]
      nlinarith
    calc
      _ ≤ ENNReal.ofReal (r * r ^ (-β)) *
          ENNReal.ofReal (A * r ^ s * (1 + Real.log (r / lam)) ^ q) := by
        rw [max_eq_left hrl]
        exact mul_le_mul' le_rfl (hinner r hr)
      _ ≤ ENNReal.ofReal (r * r ^ (-β)) *
          ENNReal.ofReal (A * r ^ s *
            ((1 + Real.log (h / lam)) * (1 + Real.log (r / h))) ^ q) := by
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have he : r * r ^ (-β) * r ^ s = r ^ (-p - 1) := by
          rw [mul_comm r, ← Real.rpow_add_one hr0.ne', ← Real.rpow_add hr0]
          congr 1
          dsimp only [p]
          ring
        rw [mul_pow]
        calc
          _ = A * (r * r ^ (-β) * r ^ s) * (1 + Real.log (h / lam)) ^ q *
              (1 + Real.log (r / h)) ^ q := by ring
          _ = _ := by rw [he]; ring
  unfold orderedRadial
  calc
    _ ≤ ∫⁻ r in Ioi h, ENNReal.ofReal (A * (1 + Real.log (h / lam)) ^ q) *
        ENNReal.ofReal (r ^ (-p - 1) * (1 + Real.log (r / h)) ^ q) :=
      setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (A * (1 + Real.log (h / lam)) ^ q) *
        ∫⁻ r in Ioi h, ENNReal.ofReal (r ^ (-p - 1) * (1 + Real.log (r / h)) ^ q) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (A * (1 + Real.log (h / lam)) ^ q) *
        ENNReal.ofReal (h ^ (-p) * RouteLog.momentConstant p q) := by
      gcongr
      exact RouteLog.lintegral_logarithmic_tail_scaled hp hh q
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Below four the ordered tail is a single convergent power integral. -/
theorem ordered_tail_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4)
    {k : ℕ} (hk : 1 ≤ k) (hkp : (4 - β) * k - 2 < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedRadial β lam (Ioi h) (k - 1) ≤
        ENNReal.ofReal (C * h ^ ((4 - β) * k - 2)) := by
  let a := 4 - β
  let n := k - 1
  let s := a * (n : ℝ)
  let A := RouteLog.momentConstant a 0 ^ n
  have ha : 0 < a := by dsimp only [a]; linarith
  have ha2 : a ≤ 2 := by dsimp only [a]; linarith
  have hA : 0 < A := pow_pos (RouteLog.momentConstant_pos ha 0) _
  have he : -(β - s - 2) = (4 - β) * k - 2 := by
    dsimp only [s, a, n]
    rw [Nat.cast_sub hk, Nat.cast_one]
    ring
  have hp : 0 < β - s - 2 := by linarith
  refine ⟨A * RouteLog.momentConstant (β - s - 2) 0,
    mul_pos hA (RouteLog.momentConstant_pos hp 0), fun lam h hlam hlh => ?_⟩
  have hb := internal_ordered_tail_log_le (β := β) (s := s) (n := n) (q := 0) hlam hlh hA.le hp (fun r hr => ?_)
  · simpa only [pow_zero, mul_one, he] using hb
  · have hrl : lam ≤ r := hlh.trans hr.le
    rw [orderedInner_eq_moment hlam hrl]
    have hm := radialLogMoment_nonneg a 0 hlam hrl
    have hmle := RouteLog.radialLogMoment_le_of_pos ha ha2 0 hlam hrl
    rw [← ENNReal.ofReal_pow hm]
    apply ENNReal.ofReal_le_ofReal
    simp only [pow_zero, mul_one]
    calc
      _ ≤ (RouteLog.momentConstant a 0 * r ^ a) ^ n := pow_le_pow_left₀ hm hmle _
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (r ^ a) n, ← Real.rpow_mul (hlam.trans_le hrl).le]

/-- At four the tail retains `k-1` logarithms and the factor `h^(-2)`. -/
theorem ordered_tail_four {k : ℕ} (_hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedRadial 4 lam (Ioi h) (k - 1) ≤
        ENNReal.ofReal (C * h ^ (-2 : ℝ) * (1 + Real.log (h / lam)) ^ (k - 1)) := by
  let n := k - 1
  let A := (3 / 2 : ℝ) ^ n
  refine ⟨A * RouteLog.momentConstant 2 n, by
    exact mul_pos (pow_pos (by norm_num) _) (RouteLog.momentConstant_pos (by norm_num) _),
    fun lam h hlam hlh => ?_⟩
  have hb := internal_ordered_tail_log_le (β := 4) (s := 0) (n := n) (q := n)
    hlam hlh (show 0 ≤ A by dsimp only [A]; positivity) (by norm_num) (fun r hr => ?_)
  · simpa only [sub_zero, show (4 : ℝ) - 2 = 2 by norm_num] using hb
  · have hrl : lam ≤ r := hlh.trans hr.le
    rw [orderedInner_eq_moment hlam hrl]
    norm_num only [show (4 : ℝ) - 4 = 0 by norm_num]
    have hm := radialLogMoment_nonneg 0 0 hlam hrl
    have hmle : RouteLog.radialLogMoment 0 lam r 0 ≤ 3 / 2 * (1 + Real.log (r / lam)) := by
      convert RouteLog.radialLogMoment_le_zero 0 hlam hrl using 1
      norm_num
    rw [← ENNReal.ofReal_pow hm]
    apply ENNReal.ofReal_le_ofReal
    simp only [Real.rpow_zero, mul_one]
    calc
      _ ≤ (3 / 2 * (1 + Real.log (r / lam))) ^ n := pow_le_pow_left₀ hm hmle _
      _ = _ := mul_pow _ _ _

/-- Above four the inner moment contributes only its lower-cutoff power. -/
theorem ordered_tail_gt_four {β : ℝ} (hβ : 4 < β) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedRadial β lam (Ioi h) (k - 1) ≤ ENNReal.ofReal
        (C * h ^ (2 - β) * lam ^ ((4 - β) * ((k : ℝ) - 1))) := by
  let a := 4 - β
  let c := 1 / 2 + 1 / (-a)
  have ha : a < 0 := by dsimp only [a]; linarith
  have hc : 0 < c := by
    have : 0 < -a := neg_pos.mpr ha
    dsimp only [c]
    positivity
  let n := k - 1
  refine ⟨c ^ n * RouteLog.momentConstant (β - 2) 0,
    mul_pos (pow_pos hc _) (RouteLog.momentConstant_pos (by linarith) _),
    fun lam h hlam hlh => ?_⟩
  let A := c ^ n * lam ^ (a * n)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hb := internal_ordered_tail_log_le (β := β) (s := 0) (n := n) (q := 0)
    hlam hlh hA (by linarith) (fun r hr => ?_)
  · simp only [sub_zero, pow_zero, mul_one] at hb
    refine hb.trans (le_of_eq ?_)
    congr 1
    dsimp only [A, a, n]
    rw [Nat.cast_sub hk, Nat.cast_one]
    rw [show -(β - 2) = 2 - β by ring]
    ring
  · have hrl : lam ≤ r := hlh.trans hr.le
    rw [orderedInner_eq_moment hlam hrl]
    have hm := radialLogMoment_nonneg a 0 hlam hrl
    have hmle : RouteLog.radialLogMoment a lam r 0 ≤ c * lam ^ a := by
      simpa only [pow_zero, mul_one] using RouteLog.radialLogMoment_le_of_neg ha 0 hlam hrl
    rw [← ENNReal.ofReal_pow hm]
    apply ENNReal.ofReal_le_ofReal
    simp only [Real.rpow_zero, pow_zero, mul_one]
    calc
      _ ≤ (c * lam ^ a) ^ n := pow_le_pow_left₀ hm hmle _
      _ = A := by
        rw [mul_pow, ← Real.rpow_natCast (lam ^ a) n, ← Real.rpow_mul hlam.le]

/-- Express the three evaluated tails as power bounds.
The positive exponent occurs only after the tail integrations. -/
theorem ordered_tail_compat {β σ : ℝ} (hβ : 2 < β) (hσ : 0 < σ)
    (hσβ : 4 - β ≤ σ) {k : ℕ} (hk : 1 ≤ k) (hkp : (4 - β) * k - 2 < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedRadial β lam (Ioi h) (k - 1) ≤ ENNReal.ofReal
        (C * lam ^ ((4 - β - σ) * ((k : ℝ) - 1)) *
          h ^ (σ * ((k : ℝ) - 1) - β + 2)) := by
  let n : ℝ := (k : ℝ) - 1
  have hn : 0 ≤ n := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp only [n]
    linarith
  by_cases hlt : β < 4
  · obtain ⟨C, hC, hbound⟩ := ordered_tail_lt_four hβ hlt hk hkp
    refine ⟨C, hC, fun lam h hlam hlh => (hbound lam h hlam hlh).trans ?_⟩
    apply ENNReal.ofReal_le_ofReal
    have hh : 0 < h := hlam.trans_le hlh
    have he : (4 - β) * k - 2 = (4 - β - σ) * n + (σ * n - β + 2) := by
      dsimp only [n]
      ring
    rw [he, Real.rpow_add hh]
    have hp := Real.rpow_le_rpow_of_nonpos hlam hlh
      (show (4 - β - σ) * n ≤ 0 from mul_nonpos_of_nonpos_of_nonneg (by linarith) hn)
    calc
      _ ≤ C * (lam ^ ((4 - β - σ) * n) * h ^ (σ * n - β + 2)) := by gcongr
      _ = _ := by ring
  · by_cases heq : β = 4
    · subst β
      obtain ⟨C, hC, hbound⟩ := ordered_tail_four hk
      refine ⟨C * (1 + 1 / σ) ^ (k - 1), by positivity, fun lam h hlam hlh => ?_⟩
      refine (hbound lam h hlam hlh).trans (ENNReal.ofReal_le_ofReal ?_)
      have hh : 0 < h := hlam.trans_le hlh
      have hL : 0 ≤ 1 + Real.log (h / lam) := by
        have := Real.log_nonneg ((one_le_div hlam).2 hlh)
        linarith
      have hp := pow_le_pow_left₀ hL (log_growth_le ((one_le_div hlam).2 hlh) hσ) (k - 1)
      have he : h ^ (-2 : ℝ) * ((h / lam) ^ σ) ^ (k - 1) =
          lam ^ ((4 - 4 - σ) * n) * h ^ (σ * n - 4 + 2) := by
        rw [← Real.rpow_natCast ((h / lam) ^ σ) (k - 1),
          ← Real.rpow_mul (div_pos hh hlam).le, Nat.cast_sub hk, Nat.cast_one,
          Real.div_rpow hh.le hlam.le, div_eq_mul_inv, ← Real.rpow_neg hlam.le,
          ← mul_assoc, ← Real.rpow_add hh, mul_comm]
        congr 1 <;> dsimp only [n] <;> ring_nf
      calc
        _ ≤ C * h ^ (-2 : ℝ) * ((1 + 1 / σ) * (h / lam) ^ σ) ^ (k - 1) := by gcongr
        _ = (C * (1 + 1 / σ) ^ (k - 1)) *
            (h ^ (-2 : ℝ) * ((h / lam) ^ σ) ^ (k - 1)) := by rw [mul_pow]; ring
        _ = _ := by rw [he]; ring
    · have hgt : 4 < β := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      obtain ⟨C, hC, hbound⟩ := ordered_tail_gt_four hgt hk
      refine ⟨C, hC, fun lam h hlam hlh => (hbound lam h hlam hlh).trans ?_⟩
      apply ENNReal.ofReal_le_ofReal
      have hh : 0 < h := hlam.trans_le hlh
      have hp := Real.rpow_le_rpow hlam.le hlh (mul_nonneg hσ.le hn)
      have he : lam ^ ((4 - β) * n) = lam ^ ((4 - β - σ) * n) * lam ^ (σ * n) := by
        rw [← Real.rpow_add hlam]
        congr 1
        ring
      rw [he]
      calc
        _ ≤ C * h ^ (2 - β) * (lam ^ ((4 - β - σ) * n) * h ^ (σ * n)) := by gcongr
        _ = C * lam ^ ((4 - β - σ) * n) * (h ^ (2 - β) * h ^ (σ * n)) := by ring
        _ = _ := by rw [← Real.rpow_add hh]; congr 2; dsimp only [n]; ring

end MultipoleBKT.GeneralExpansion

end
