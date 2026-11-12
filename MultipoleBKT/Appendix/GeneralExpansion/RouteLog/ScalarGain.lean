/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.ScalarBasic
public import MultipoleBKT.Appendix.GeneralExpansion.FrozenRoot
public import MultipoleBKT.Appendix.RouteLog.Absorption

/-!
# Final absorption of the root logarithmic moments

See (A.42). The three radial regimes are
applied before absorbing logarithms. The compatibility interfaces quantify
all `λ ≤ ε₀`, so the final absorption uses a uniform finite coefficient.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set
open scoped ENNReal

/-- The product of one marked logarithmic radial moment and `k-1`
zeroth moments, below four. No auxiliary temperature exponent is used. -/
theorem moment_product_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4)
    {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      RouteLog.radialLogMoment (4 - β) lam h q *
          RouteLog.radialLogMoment (4 - β) lam h 0 ^ (k - 1) ≤
        C * h ^ ((4 - β) * k) := by
  let a := 4 - β
  have ha : 0 < a := by dsimp only [a]; linarith
  have ha2 : a ≤ 2 := by dsimp only [a]; linarith
  let C := RouteLog.momentConstant a q * RouteLog.momentConstant a 0 ^ (k - 1)
  refine ⟨C, mul_pos (RouteLog.momentConstant_pos ha q)
    (pow_pos (RouteLog.momentConstant_pos ha 0) _), fun lam h hlam hlh => ?_⟩
  calc
    _ ≤ (RouteLog.momentConstant a q * h ^ a) *
        (RouteLog.momentConstant a 0 * h ^ a) ^ (k - 1) :=
      mul_le_mul (RouteLog.radialLogMoment_le_of_pos ha ha2 q hlam hlh)
        (pow_le_pow_left₀ (radialLogMoment_nonneg a 0 hlam hlh)
          (RouteLog.radialLogMoment_le_of_pos ha ha2 0 hlam hlh) _)
        (pow_nonneg (radialLogMoment_nonneg a 0 hlam hlh) _)
        (mul_nonneg (RouteLog.momentConstant_pos ha q).le (Real.rpow_nonneg (hlam.trans_le hlh).le _))
    _ = C * h ^ (a * k) := by
      rw [mul_pow]
      calc
        _ = C * (h ^ a * (h ^ a) ^ (k - 1)) := by ring
        _ = _ := by rw [rpow_mul_pow_pred (hlam.trans_le hlh) a hk]

/-- Critical moments retain exactly `k+q` logarithms. -/
theorem moment_product_four {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      RouteLog.radialLogMoment 0 lam h q * RouteLog.radialLogMoment 0 lam h 0 ^ (k - 1) ≤
        C * (1 + Real.log (h / lam)) ^ (k + q) := by
  let c := 1 / 2 + 1 / ((q : ℝ) + 1)
  let C := c * (3 / 2 : ℝ) ^ (k - 1)
  refine ⟨C, by dsimp only [C, c]; positivity, fun lam h hlam hlh => ?_⟩
  have hL : 0 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  have h0 : RouteLog.radialLogMoment 0 lam h 0 ≤ 3 / 2 * (1 + Real.log (h / lam)) := by
    convert RouteLog.radialLogMoment_le_zero 0 hlam hlh using 1
    norm_num
  calc
    _ ≤ (c * (1 + Real.log (h / lam)) ^ (q + 1)) *
        (3 / 2 * (1 + Real.log (h / lam))) ^ (k - 1) :=
      mul_le_mul (RouteLog.radialLogMoment_le_zero q hlam hlh)
        (pow_le_pow_left₀ (radialLogMoment_nonneg 0 0 hlam hlh) h0 _)
        (pow_nonneg (radialLogMoment_nonneg 0 0 hlam hlh) _) (by dsimp only [c]; positivity)
    _ = _ := by
      rw [mul_pow]
      have hn : k + q = (q + 1) + (k - 1) := by omega
      rw [hn, pow_add]
      dsimp only [C]
      ring

/-- Supercritical moments retain exactly `q` logarithms. -/
theorem moment_product_gt_four {β : ℝ} (hβ : 4 < β) {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      RouteLog.radialLogMoment (4 - β) lam h q *
          RouteLog.radialLogMoment (4 - β) lam h 0 ^ (k - 1) ≤
        C * lam ^ ((4 - β) * k) * (1 + Real.log (h / lam)) ^ q := by
  let a := 4 - β
  have ha : a < 0 := by dsimp only [a]; linarith
  let c := 1 / 2 + 1 / (-a)
  have hc : 0 < c := by
    have hna : 0 < -a := neg_pos.mpr ha
    dsimp only [c]
    positivity
  let C := c ^ k
  refine ⟨C, pow_pos hc _, fun lam h hlam hlh => ?_⟩
  have hL : 0 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  have h0 : RouteLog.radialLogMoment a lam h 0 ≤ c * lam ^ a := by
    simpa only [pow_zero, mul_one] using RouteLog.radialLogMoment_le_of_neg ha 0 hlam hlh
  calc
    _ ≤ (c * lam ^ a * (1 + Real.log (h / lam)) ^ q) * (c * lam ^ a) ^ (k - 1) :=
      mul_le_mul (RouteLog.radialLogMoment_le_of_neg ha q hlam hlh)
        (pow_le_pow_left₀ (radialLogMoment_nonneg a 0 hlam hlh) h0 _)
        (pow_nonneg (radialLogMoment_nonneg a 0 hlam hlh) _) (by positivity)
    _ = _ := by
      rw [mul_pow]
      have he := rpow_mul_pow_pred hlam a hk
      have hc' : c * c ^ (k - 1) = c ^ k := by rw [← pow_succ', Nat.sub_add_cancel hk]
      calc
        _ = (c * c ^ (k - 1)) * (lam ^ a * (lam ^ a) ^ (k - 1)) *
            (1 + Real.log (h / lam)) ^ q := by ring
        _ = _ := by rw [he, hc']

/-- After the separate critical and supercritical integrations, the remaining
logarithmic polynomial is absorbed by the surplus `λ^k`. -/
theorem moment_product_ge_four_absorb {β : ℝ} (hβ : 4 ≤ β) (p₀ : ℕ)
    {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      RouteLog.radialLogMoment (4 - β) lam (eps * truncationScale p₀ β lam) q *
          RouteLog.radialLogMoment (4 - β) lam (eps * truncationScale p₀ β lam) 0 ^ (k - 1) ≤
        C * lam ^ ((3 - β) * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hreg : ∃ A : ℝ, 0 < A ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      RouteLog.radialLogMoment (4 - β) lam h q *
          RouteLog.radialLogMoment (4 - β) lam h 0 ^ (k - 1) ≤
        A * lam ^ ((4 - β) * k) * (1 + Real.log (h / lam)) ^ (k + q) := by
    by_cases heq : β = 4
    · subst β
      obtain ⟨A, hA, hbound⟩ := moment_product_four hk q
      refine ⟨A, hA, fun lam h hlam hlh => ?_⟩
      simpa only [sub_self, zero_mul, Real.rpow_zero, mul_one] using hbound lam h hlam hlh
    · obtain ⟨A, hA, hbound⟩ := moment_product_gt_four (lt_of_le_of_ne hβ (Ne.symm heq)) hk q
      refine ⟨A, hA, fun lam h hlam hlh => (hbound lam h hlam hlh).trans ?_⟩
      have hL : 1 ≤ 1 + Real.log (h / lam) := by
        have := Real.log_nonneg ((one_le_div hlam).2 hlh)
        linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (Nat.le_add_left q k)) (by positivity)
  obtain ⟨A, hA, hbound⟩ := hreg
  obtain ⟨B, hB, hlog⟩ := power_log_uniform hk0
    (show (0 : ℝ) ≤ 2 * p₀ + 1 by positivity) (k + q)
  refine ⟨A * B, mul_pos hA hB, fun eps lam hlam hle heps1 => ?_⟩
  have heps : 0 < eps := hlam.trans_le hle
  have hlam1 := hle.trans heps1
  have hlh : lam ≤ eps * truncationScale p₀ β lam := hle.trans
    (le_mul_of_one_le_right heps.le
      (Appendix.one_le_truncationScale (by linarith) hlam hlam1))
  have hL : 0 ≤ 1 + Real.log (eps * truncationScale p₀ β lam / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  have hp := pow_le_pow_left₀ hL
    (add_le_add_right (RouteLog.log_cutoff_le hβ hlam hlam1 heps heps1) 1) (k + q)
  have hl := (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hlam.le (k : ℝ))).trans
    (hlog lam hlam hlam1)
  have he : lam ^ ((4 - β) * k) = lam ^ ((3 - β) * k) * lam ^ (k : ℝ) := by
    rw [← Real.rpow_add hlam]
    congr 1
    ring
  calc
    _ ≤ A * lam ^ ((4 - β) * k) *
        (1 + Real.log (eps * truncationScale p₀ β lam / lam)) ^ (k + q) :=
      hbound lam _ hlam hlh
    _ = A * lam ^ ((3 - β) * k) * (lam ^ (k : ℝ) *
        (1 + Real.log (eps * truncationScale p₀ β lam / lam)) ^ (k + q)) := by rw [he]; ring
    _ ≤ A * lam ^ ((3 - β) * k) * B :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by ring

/-- Internal scalar compatibility with any exponent permitted by the two
cutoff scalings. The moment integration itself is unconditional. -/
theorem internal_moment_product_cutoff_le {β d : ℝ} (hβ : 2 < β) (p₀ : ℕ)
    {k : ℕ} (hk : 1 ≤ k) (q : ℕ)
    (hdlt : β < 4 → d ≤ (4 - β) * k) (hdge : 4 ≤ β → d ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      RouteLog.radialLogMoment (4 - β) lam (eps * truncationScale p₀ β lam) q *
          RouteLog.radialLogMoment (4 - β) lam (eps * truncationScale p₀ β lam) 0 ^ (k - 1) ≤
        C * eps ^ d * lam ^ ((2 - β) * k) := by
  by_cases hβ4 : β < 4
  · obtain ⟨C, hC, hbound⟩ := moment_product_lt_four hβ hβ4 hk q
    refine ⟨C, hC, fun eps lam hlam hle heps1 => ?_⟩
    have heps : 0 < eps := hlam.trans_le hle
    have hlh : lam ≤ eps * truncationScale p₀ β lam := hle.trans
      (le_mul_of_one_le_right heps.le (Appendix.one_le_truncationScale hβ hlam (hle.trans heps1)))
    refine (hbound lam _ hlam hlh).trans ?_
    rw [Real.mul_rpow heps.le (Appendix.truncationScale_pos hlam).le,
      Appendix.rpow_truncationScale_mul_of_lt hlam hβ4]
    have hp := Real.rpow_le_rpow_of_exponent_ge heps heps1 (hdlt hβ4)
    calc
      _ ≤ C * (eps ^ d * lam ^ ((2 - β) * k)) := by gcongr
      _ = _ := by ring
  · have hge : 4 ≤ β := le_of_not_gt hβ4
    obtain ⟨C, hC, hbound⟩ := moment_product_ge_four_absorb hge p₀ hk q
    refine ⟨C, hC, fun eps lam hlam hle heps1 => ?_⟩
    have heps : 0 < eps := hlam.trans_le hle
    have hp : lam ^ (k : ℝ) ≤ eps ^ d :=
      (Real.rpow_le_rpow hlam.le hle (Nat.cast_nonneg k)).trans
        (Real.rpow_le_rpow_of_exponent_ge heps heps1 (hdge hge))
    have he : lam ^ ((3 - β) * k) = lam ^ (k : ℝ) * lam ^ ((2 - β) * k) := by
      rw [← Real.rpow_add hlam]
      congr 1
      ring
    refine (hbound eps lam hlam hle heps1).trans ?_
    rw [he]
    calc
      _ ≤ C * (eps ^ d * lam ^ ((2 - β) * k)) := by gcongr
      _ = _ := by ring

/-- The cap contribution has the required compatibility exponent. -/
theorem moment_product_cap_le {β : ℝ} (hβ : 2 < β) (p₀ : ℕ)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      RouteLog.radialLogMoment (4 - β) lam (eps * truncationScale p₀ β lam) 0 ^ k ≤
        C * eps ^ (tailSigma p₀ β k * k) * lam ^ ((2 - β) * k) := by
  obtain ⟨C, hC, hbound⟩ := internal_moment_product_cutoff_le hβ p₀ hk 0
    (d := tailSigma p₀ β k * k)
    (by intro hlt; simp only [tailSigma, ite_eq_left hlt]; exact le_rfl)
    (by
      intro hge
      have hp : (1 : ℝ) ≤ 2 * p₀ + 1 := by have := (Nat.cast_nonneg p₀ : (0 : ℝ) ≤ p₀); linarith
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      rw [tailSigma, ite_eq_right (not_lt.mpr hge)]
      have hσ : 1 / ((k : ℝ) * (2 * p₀ + 1)) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]
        simp only [one_mul]
        nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast hk]
      exact mul_le_of_le_one_left hk0.le hσ)
  refine ⟨C, hC, fun eps lam hlam hle heps => ?_⟩
  have hb := hbound eps lam hlam hle heps
  rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk] at hb
  exact hb

/-- The bad-root terms gain `ε₀^(α k)` with an independent coefficient,
after their logarithmic integrations. -/
theorem moment_product_bad_le {β : ℝ} (hβ : 2 < β) (p₀ : ℕ)
    {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      RouteLog.radialLogMoment (4 - β) lam (eps * truncationScale p₀ β lam) q *
          RouteLog.radialLogMoment (4 - β) lam (eps * truncationScale p₀ β lam) 0 ^ (k - 1) ≤
        C * eps ^ (alphaExponent β * k) * lam ^ ((2 - β) * k) := by
  apply internal_moment_product_cutoff_le hβ p₀ hk q
  · intro hlt
    rw [alphaExponent, ite_eq_left hlt]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  · intro hge
    rw [alphaExponent, ite_eq_right (not_lt.mpr hge)]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

/-- The cutoff cap converts the scalar gain to the normalization in (A.44). -/
theorem cutoff_cap_scaling {p₀ : ℕ} {β lam eps d : ℝ} (hlam : 0 < lam) (heps : 0 < eps) :
    eps ^ d / (eps * truncationScale p₀ β lam) ^ 2 =
      eps ^ (d - 2) * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  rw [mul_pow, Real.rpow_sub heps, Real.rpow_two, Real.rpow_neg hR.le, Real.rpow_two]
  ring

end MultipoleBKT.GeneralExpansion

end
