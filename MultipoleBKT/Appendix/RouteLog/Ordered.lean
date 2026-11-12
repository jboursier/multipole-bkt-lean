/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Products
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Ordered radial logarithmic integrations

See the proof of Lemma A.4. The inner radii are integrated below the largest radius.
For `β < 4` this leaves the single power integral displayed after (A.26).
For `β ≥ 4`, the rescaled outer integral converges with the logarithms retained.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set Finset
open scoped ENNReal

/-- A logarithmic moment on the unbounded radial interval. This is the
inverted form of the moment on `(0,1]`, with the same explicit constant. -/
theorem lintegral_logarithmic_tail {p : ℝ} (hp : 0 < p) (q : ℕ) :
    ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-p - 1) * (1 + Real.log t) ^ q) ≤
      ENNReal.ofReal (momentConstant p q) := by
  have himage : (fun t : ℝ => t⁻¹) '' Ioi (1 : ℝ) = Ioo (0 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨inv_pos.mpr (zero_lt_one.trans hs), inv_lt_one_of_one_lt₀ hs⟩
    · intro ht
      refine ⟨t⁻¹, one_lt_inv₀ ht.1 |>.mpr ht.2, inv_inv t⟩
  have he := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun t ht => (hasDerivAt_inv (zero_lt_one.trans ht).ne').hasDerivWithinAt)
    inv_injective.injOn (fun s : ℝ => ENNReal.ofReal (s ^ (p - 1) * (1 + Real.log (1 / s)) ^ q))
  rw [himage] at he
  have hpoint : ∀ t ∈ Ioi (1 : ℝ), ENNReal.ofReal |-(t ^ 2)⁻¹| *
      ENNReal.ofReal (t⁻¹ ^ (p - 1) * (1 + Real.log (1 / t⁻¹)) ^ q) =
      ENNReal.ofReal (t ^ (-p - 1) * (1 + Real.log t) ^ q) := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [abs_neg, abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_div, inv_inv]
    have hpow : (t ^ 2)⁻¹ * t⁻¹ ^ (p - 1) = t ^ (-p - 1) := by
      rw [Real.inv_rpow ht0.le, show (t ^ 2)⁻¹ = t ^ (-2 : ℝ) by
        rw [Real.rpow_neg ht0.le, Real.rpow_two], ← Real.rpow_neg ht0.le,
        ← Real.rpow_add ht0]
      congr 1
      ring
    rw [← mul_assoc, hpow]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpoint] at he
  rw [← he, restrict_Ioo_eq_restrict_Ioc]
  simpa only [one_div, Real.one_rpow, mul_one] using
    lintegral_power_log_moment hp (show (0 : ℝ) < 1 by norm_num) q

/-- Scaling the unbounded logarithmic radial moment by its lower cutoff. -/
theorem lintegral_logarithmic_tail_scaled {p lam : ℝ} (hp : 0 < p)
    (hlam : 0 < lam) (q : ℕ) :
    ∫⁻ t in Ioi lam, ENNReal.ofReal (t ^ (-p - 1) * (1 + Real.log (t / lam)) ^ q) ≤
      ENNReal.ofReal (lam ^ (-p) * momentConstant p q) := by
  have himage : (fun t : ℝ => lam * t) '' Ioi (1 : ℝ) = Ioi lam := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      change lam < lam * s
      calc lam = lam * 1 := by ring
           _ < lam * s := mul_lt_mul_of_pos_left hs hlam
    · intro ht
      exact ⟨t / lam, (one_lt_div hlam).2 ht, mul_div_cancel₀ t hlam.ne'⟩
  have he := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (1 : ℝ)) measurableSet_Ioi
    (fun t _ => ((hasDerivAt_id t).const_mul lam).hasDerivWithinAt)
    (mul_right_injective₀ hlam.ne').injOn
    (fun t : ℝ => ENNReal.ofReal (t ^ (-p - 1) * (1 + Real.log (t / lam)) ^ q))
  simp only [mul_one, id_eq] at he
  rw [himage] at he
  have hpoint : ∀ t ∈ Ioi (1 : ℝ), ENNReal.ofReal |lam| *
      ENNReal.ofReal ((lam * t) ^ (-p - 1) * (1 + Real.log (lam * t / lam)) ^ q) =
      ENNReal.ofReal (lam ^ (-p)) * ENNReal.ofReal (t ^ (-p - 1) * (1 + Real.log t) ^ q) := by
    intro t ht
    have ht0 := zero_lt_one.trans ht
    rw [abs_of_pos hlam, mul_div_cancel_left₀ t hlam.ne',
      Real.mul_rpow hlam.le ht0.le, ← ENNReal.ofReal_mul hlam.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)]
    congr 1
    have hpw : lam * lam ^ (-p - 1) = lam ^ (-p) := by
      rw [mul_comm, ← Real.rpow_add_one hlam.ne']
      congr 1
      ring
    calc
      _ = (lam * lam ^ (-p - 1)) * (t ^ (-p - 1) * (1 + Real.log t) ^ q) := by ring
      _ = _ := by rw [hpw]
  rw [he, setLIntegral_congr_fun measurableSet_Ioi hpoint,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (lam ^ (-p)) * ENNReal.ofReal (momentConstant p q) := by
      gcongr
      exact lintegral_logarithmic_tail hp q
    _ = _ := (ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)).symm

/-- Inner ordered-radius integration for `β < 4`, with the full logarithmic
moment at the smallest radius. -/
theorem ordered_inner_log_moment {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4)
    (k q : ℕ) {lam u : ℝ} (hlam : 0 < lam) (hlu : lam ≤ u) :
    ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 u),
      ENNReal.ofReal ((1 + Real.log (u / minimumRadius lam r)) ^ q) *
        ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β)) ≤
      ENNReal.ofReal (((k : ℝ) + 1) * momentConstant (4 - β) q *
        momentConstant (4 - β) 0 ^ k * u ^ ((4 - β) * (k + 1))) := by
  have ha : 0 < 4 - β := by linarith
  have ha2 : 4 - β ≤ 2 := by linarith
  have he : 2 - β = (4 - β) - 2 := by ring
  rw [he]
  refine (lintegral_minimum_log_le_of_pos ha ha2 q hlam hlu).trans (le_of_eq ?_)
  have hu : 0 < u := hlam.trans_le hlu
  have hp : u ^ ((4 - β) * (k + 1)) = u ^ (4 - β) * (u ^ (4 - β)) ^ k := by
    rw [mul_add, mul_one, Real.rpow_add hu, Real.rpow_mul hu.le, Real.rpow_natCast]
    ring
  rw [hp]
  have hCq := (momentConstant_pos ha q).le
  have hC0 := (momentConstant_pos ha 0).le
  simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    ENNReal.ofReal_natCast, ENNReal.ofReal_add, ENNReal.ofReal_one]
  ring

/-- Ordered radial integration below the largest radius, after separating
its core at `λ`. The number of radii is `k+2`. -/
noncomputable def orderedLogIntegral (β lam h : ℝ) (k q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (lam ^ ((4 - β) * (k + 2) - 2)) +
    ∫⁻ u in Ioc lam h, ENNReal.ofReal (u ^ (1 - β)) *
      ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 u),
        ENNReal.ofReal ((1 + Real.log (u / minimumRadius lam r)) ^ q) *
          ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β))

/-- The ordered logarithmic radial moment reduces to the single power integral
in the proof of Lemma A.4. This constant is uniform in both radial cutoffs. -/
theorem ordered_radial_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4) (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedLogIntegral β lam h k q ≤
        ENNReal.ofReal (C * (lam ^ ((4 - β) * (k + 2) - 2) +
          ∫ u in lam..h, u ^ ((4 - β) * (k + 2) - 3))) := by
  have ha : 0 < 4 - β := by linarith
  let D := ((k : ℝ) + 1) * momentConstant (4 - β) q * momentConstant (4 - β) 0 ^ k
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (mul_pos (by positivity) (momentConstant_pos ha q))
      (pow_pos (momentConstant_pos ha 0) k)
  refine ⟨max 1 D, lt_max_of_lt_left zero_lt_one, fun lam h hlam hlh => ?_⟩
  have hh : 0 < h := hlam.trans_le hlh
  have hset (e : ℝ) : ContinuousOn (fun u : ℝ => u ^ e) (Icc lam h) :=
    continuousOn_id.rpow_const fun u hu => Or.inl (hlam.trans_le hu.1).ne'
  have hp : ∫⁻ u in Ioc lam h, ENNReal.ofReal (u ^ ((4 - β) * (k + 2) - 3)) =
      ENNReal.ofReal (∫ u in lam..h, u ^ ((4 - β) * (k + 2) - 3)) := by
    rw [intervalIntegral.integral_of_le hlh,
      ofReal_integral_eq_lintegral_ofReal ((hset _).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
          Real.rpow_nonneg (hlam.trans hu.1).le _))]
  have hinner : (∫⁻ u in Ioc lam h, ENNReal.ofReal (u ^ (1 - β)) *
      ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 u),
        ENNReal.ofReal ((1 + Real.log (u / minimumRadius lam r)) ^ q) *
          ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β))) ≤
      ENNReal.ofReal D * ENNReal.ofReal (∫ u in lam..h, u ^ ((4 - β) * (k + 2) - 3)) := by
    calc
      _ ≤ ∫⁻ u in Ioc lam h, ENNReal.ofReal D *
          ENNReal.ofReal (u ^ ((4 - β) * (k + 2) - 3)) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro u hu
        have hu0 : 0 < u := hlam.trans hu.1
        calc
          _ ≤ ENNReal.ofReal (u ^ (1 - β)) *
              ENNReal.ofReal (D * u ^ ((4 - β) * (k + 1))) := by
            gcongr
            exact ordered_inner_log_moment hβ hβ4 k q hlam hu.1.le
          _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _),
              ← ENNReal.ofReal_mul hD.le]
            congr 1
            rw [show u ^ (1 - β) * (D * u ^ ((4 - β) * (k + 1))) =
                D * (u ^ (1 - β) * u ^ ((4 - β) * (k + 1))) by ring,
              ← Real.rpow_add hu0]
            congr 2
            ring
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hp]
  have hint0 : 0 ≤ ∫ u in lam..h, u ^ ((4 - β) * (k + 2) - 3) :=
    intervalIntegral.integral_nonneg hlh fun u hu =>
      Real.rpow_nonneg (hlam.trans_le hu.1).le _
  unfold orderedLogIntegral
  calc
    _ ≤ ENNReal.ofReal (lam ^ ((4 - β) * (k + 2) - 2)) +
        ENNReal.ofReal D * ENNReal.ofReal (∫ u in lam..h, u ^ ((4 - β) * (k + 2) - 3)) :=
      add_le_add_right hinner _
    _ = ENNReal.ofReal (lam ^ ((4 - β) * (k + 2) - 2) +
        D * ∫ u in lam..h, u ^ ((4 - β) * (k + 2) - 3)) := by
      rw [← ENNReal.ofReal_mul hD.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hcore := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) D)
        (Real.rpow_nonneg hlam.le ((4 - β) * (k + 2) - 2))
      have htail := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) D) hint0
      nlinarith

private theorem inner_power_le_log {β u : ℝ} (hβ : 4 ≤ β) (hu : 1 ≤ u) :
    0 ≤ (∫ t in (1 : ℝ)..u, t ^ (3 - β)) ∧
      (∫ t in (1 : ℝ)..u, t ^ (3 - β)) ≤ Real.log u := by
  have hc : ContinuousOn (fun t : ℝ => t ^ (3 - β)) (uIcc 1 u) := by
    refine continuousOn_id.rpow_const fun t ht => Or.inl ?_
    rw [uIcc_of_le hu] at ht
    change t ≠ 0
    exact (zero_lt_one.trans_le ht.1).ne'
  have hi : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc 1 u) := by
    apply continuousOn_id.inv₀
    intro t ht
    rw [uIcc_of_le hu] at ht
    change t ≠ 0
    exact (zero_lt_one.trans_le ht.1).ne'
  refine ⟨intervalIntegral.integral_nonneg hu (fun t ht => Real.rpow_nonneg (by linarith [ht.1]) _), ?_⟩
  have hbound := intervalIntegral.integral_mono_on hu (hc.intervalIntegrable (μ := volume)) (hi.intervalIntegrable (μ := volume))
    (fun t ht => by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le ht.1 (by linarith))
  rw [integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hu), div_one] at hbound
  exact hbound

/-- The rescaled ordered radial moment appearing in the proof of Lemma A.4 converges for
`β ≥ 4`, including the critical logarithmic case. -/
theorem ordered_radial_ge_four {β : ℝ} (hβ : 4 ≤ β) (k : ℕ) :
    ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal
      (u ^ (1 - β) * Real.log (2 * u) ^ (k + 1) *
        (1 + ∫ t in (1 : ℝ)..u, t ^ (3 - β)) ^ k) < ⊤ := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  calc
    _ ≤ ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (u ^ (-3 : ℝ) *
        (1 + Real.log u) ^ (2 * k + 1)) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro u hu
      have hu0 : 0 < u := zero_lt_one.trans hu
      have hlog : 0 ≤ Real.log u := Real.log_nonneg hu.le
      have hlog2u : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by
        have hu1 : 1 < u := hu
        linarith)
      have hi := inner_power_le_log hβ hu.le
      have hinner := hi.2
      have hinner0 : 0 ≤ 1 + ∫ t in (1 : ℝ)..u, t ^ (3 - β) := by linarith [hi.1]
      apply ENNReal.ofReal_le_ofReal
      have hp : u ^ (1 - β) ≤ u ^ (-3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hu.le (by linarith)
      have hl : Real.log (2 * u) ≤ 1 + Real.log u := by
        rw [Real.log_mul (by norm_num) hu0.ne']
        linarith
      calc
        _ ≤ u ^ (-3 : ℝ) * (1 + Real.log u) ^ (k + 1) * (1 + Real.log u) ^ k := by
          gcongr
        _ = _ := by rw [mul_assoc, ← pow_add]; congr 2; omega
    _ ≤ ENNReal.ofReal (momentConstant 2 (2 * k + 1)) := by
      convert lintegral_logarithmic_tail (show (0 : ℝ) < 2 by norm_num) (2 * k + 1) using 1
      norm_num
    _ < ⊤ := ENNReal.ofReal_lt_top

end MultipoleBKT.RouteLog

end
