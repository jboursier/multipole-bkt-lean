/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Radial
public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.ScalarGain

/-!
# Case F with its logarithmic radial displays

See Step 4 of
the proof of Lemma A.7. The largest radius is at least
`h`. The inner radii retain their logarithmic moments. At and above
four those moments are split at lambda before integrating the largest
radius. No effective temperature is introduced.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset MultipoleBKT.RouteLog
open scoped ENNReal

/-- The literal ordered tail with `k+2` radii and logarithmic order `q`.
Its inner integral includes every regularized core below lambda. -/
noncomputable def orderedTail (β lam h : ℝ) (k q : ℕ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi h, ENNReal.ofReal (u ^ (1 - β)) * SmallIntegral.RouteJ.innerRadial β lam k q u

/-- The outer logarithmic tail, retaining the logarithm at its lower endpoint. -/
theorem lintegral_shifted_log_tail {p lam h : ℝ} (hp : 0 < p)
    (hlam : 0 < lam) (hlh : lam ≤ h) (q : ℕ) :
    (∫⁻ u in Ioi h, ENNReal.ofReal (u ^ (-p - 1) * (1 + Real.log (u / lam)) ^ q)) ≤
      ENNReal.ofReal (h ^ (-p) * momentConstant p q * (1 + Real.log (h / lam)) ^ q) := by
  have hh : 0 < h := hlam.trans_le hlh
  have hL : 0 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  have hb (u : ℝ) (hu : u ∈ Ioi h) :
      ENNReal.ofReal (u ^ (-p - 1) * (1 + Real.log (u / lam)) ^ q) ≤
        ENNReal.ofReal ((1 + Real.log (h / lam)) ^ q) *
          ENNReal.ofReal (u ^ (-p - 1) * (1 + Real.log (u / h)) ^ q) := by
    have hu0 := hh.trans hu
    have hlogh : 0 ≤ Real.log (h / lam) := Real.log_nonneg ((one_le_div hlam).2 hlh)
    have hlogu : 0 ≤ Real.log (u / h) := Real.log_nonneg ((one_le_div hh).2 hu.le)
    have he : Real.log (u / lam) = Real.log (u / h) + Real.log (h / lam) := by
      rw [← Real.log_mul (div_pos hu0 hh).ne' (div_pos hh hlam).ne']
      congr 1
      field_simp
    rw [← ENNReal.ofReal_mul (pow_nonneg hL q)]
    apply ENNReal.ofReal_le_ofReal
    have hs : (1 + Real.log (u / lam)) ^ q ≤
        ((1 + Real.log (h / lam)) * (1 + Real.log (u / h))) ^ q := by
      apply pow_le_pow_left₀ (by rw [he]; positivity)
      rw [he]
      nlinarith
    calc
      _ ≤ u ^ (-p - 1) * ((1 + Real.log (h / lam)) * (1 + Real.log (u / h))) ^ q :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hu0.le _)
      _ = _ := by rw [mul_pow]; ring
  calc
    _ ≤ ∫⁻ u in Ioi h, ENNReal.ofReal ((1 + Real.log (h / lam)) ^ q) *
        ENNReal.ofReal (u ^ (-p - 1) * (1 + Real.log (u / h)) ^ q) :=
      setLIntegral_mono' measurableSet_Ioi hb
    _ = ENNReal.ofReal ((1 + Real.log (h / lam)) ^ q) *
        ∫⁻ u in Ioi h, ENNReal.ofReal (u ^ (-p - 1) * (1 + Real.log (u / h)) ^ q) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((1 + Real.log (h / lam)) ^ q) *
        ENNReal.ofReal (h ^ (-p) * momentConstant p q) :=
      mul_le_mul' le_rfl (lintegral_logarithmic_tail_scaled hp hh q)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (pow_nonneg hL q)]
      congr 1
      ring

/-- Internal outer integration after the inner logarithmic moments.
The concrete regime theorems discharge its scalar inner estimate. -/
theorem internal_orderedTail_le {β σ τ A lam h : ℝ} (k q l : ℕ)
    (hlam : 0 < lam) (hlh : lam ≤ h) (hA : 0 ≤ A) (hp : 0 < β - 2 - τ)
    (hinner : ∀ u : ℝ, h < u → SmallIntegral.RouteJ.innerRadial β lam k q u ≤
      ENNReal.ofReal (A * lam ^ σ * u ^ τ * (1 + Real.log (u / lam)) ^ l)) :
    orderedTail β lam h k q ≤ ENNReal.ofReal
      (A * momentConstant (β - 2 - τ) l * lam ^ σ * h ^ (-(β - 2 - τ)) *
        (1 + Real.log (h / lam)) ^ l) := by
  have hh := hlam.trans_le hlh
  have hpt (u : ℝ) (hu : u ∈ Ioi h) :
      ENNReal.ofReal (u ^ (1 - β)) * SmallIntegral.RouteJ.innerRadial β lam k q u ≤
        ENNReal.ofReal (A * lam ^ σ) *
          ENNReal.ofReal (u ^ (-(β - 2 - τ) - 1) * (1 + Real.log (u / lam)) ^ l) := by
    have hu0 := hh.trans hu
    refine (mul_le_mul' le_rfl (hinner u hu)).trans_eq ?_
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _),
      ← ENNReal.ofReal_mul (mul_nonneg hA (Real.rpow_nonneg hlam.le _))]
    congr 1
    have he : u ^ (1 - β) * u ^ τ = u ^ (-(β - 2 - τ) - 1) := by
      rw [← Real.rpow_add hu0]
      congr 1
      ring
    calc
      _ = A * lam ^ σ * (u ^ (1 - β) * u ^ τ) * (1 + Real.log (u / lam)) ^ l := by ring
      _ = _ := by rw [he]; ring
  unfold orderedTail
  calc
    _ ≤ ∫⁻ u in Ioi h, ENNReal.ofReal (A * lam ^ σ) *
        ENNReal.ofReal (u ^ (-(β - 2 - τ) - 1) * (1 + Real.log (u / lam)) ^ l) :=
      setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (A * lam ^ σ) *
        ∫⁻ u in Ioi h, ENNReal.ofReal (u ^ (-(β - 2 - τ) - 1) * (1 + Real.log (u / lam)) ^ l) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (A * lam ^ σ) * ENNReal.ofReal
        (h ^ (-(β - 2 - τ)) * momentConstant (β - 2 - τ) l * (1 + Real.log (h / lam)) ^ l) :=
      mul_le_mul' le_rfl (lintegral_shifted_log_tail hp hlam hlh l)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.rpow_nonneg hlam.le _))]
      congr 1
      ring

/-- Below four, integrating the inner logarithmic moments gives exactly
the power `h^((4-beta)(k+2)-2)` in the written case-F display. -/
theorem orderedTail_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4) (k q : ℕ)
    (hsize : (4 - β) * (k + 2) < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedTail β lam h k q ≤ ENNReal.ofReal (C * h ^ ((4 - β) * (k + 2) - 2)) := by
  let A := ((k : ℝ) + 1) * momentConstant (4 - β) q * momentConstant (4 - β) 0 ^ k
  let τ := (4 - β) * ((k : ℝ) + 1)
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos (by positivity) (momentConstant_pos (by linarith) q))
      (pow_pos (momentConstant_pos (by linarith) 0) k)
  have hp : 0 < β - 2 - τ := by dsimp only [τ]; nlinarith
  refine ⟨A * momentConstant (β - 2 - τ) 0, mul_pos hA (momentConstant_pos hp 0),
    fun lam h hlam hlh => ?_⟩
  have hb := internal_orderedTail_le (σ := 0) k q 0 hlam hlh hA.le hp (fun u hu => ?_)
  · have he : -(β - 2 - τ) = (4 - β) * (k + 2) - 2 := by dsimp only [τ]; ring
    simpa only [Real.rpow_zero, mul_one, pow_zero, he] using hb
  · unfold SmallIntegral.RouteJ.innerRadial
    rw [max_eq_left (hlh.trans hu.le)]
    simpa only [A, τ, Real.rpow_zero, mul_one, pow_zero] using
      ordered_inner_log_moment hβ hβ4 k q hlam (hlh.trans hu.le)

/-- At four, the inner radial integral contributes `k+1+q` logarithms. -/
theorem orderedTail_four (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedTail 4 lam h k q ≤ ENNReal.ofReal
        (C * h ^ (-2 : ℝ) * (1 + Real.log (h / lam)) ^ (k + 1 + q)) := by
  let A := ((k : ℝ) + 1) * (1 / 2 + 1 / ((q : ℝ) + 1)) * (3 / 2 : ℝ) ^ k
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A * momentConstant 2 (k + 1 + q), mul_pos hA (momentConstant_pos (by norm_num) _),
    fun lam h hlam hlh => ?_⟩
  have hb := internal_orderedTail_le (β := 4) (σ := 0) (τ := 0) k q (k + 1 + q)
    hlam hlh hA.le (by norm_num) (fun u hu => ?_)
  · simpa only [Real.rpow_zero, mul_one, sub_zero, show (4 : ℝ) - 2 = 2 by norm_num] using hb
  · unfold SmallIntegral.RouteJ.innerRadial
    rw [max_eq_left (hlh.trans hu.le)]
    have hm := lintegral_minimum_log_le_zero (k := k) q hlam (hlh.trans hu.le)
    simp only [show (2 : ℝ) - 4 = -2 by norm_num]
    refine hm.trans_eq ?_
    have hL : 0 ≤ 1 + Real.log (u / lam) := by
      have := Real.log_nonneg ((one_le_div hlam).2 (hlh.trans hu.le))
      linarith
    simp only [Real.rpow_zero, mul_one]
    dsimp only [A]
    simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_add, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

/-- Above four, split at lambda. The lower-cutoff power and the `q`
logarithms remain visible before final absorption. -/
theorem orderedTail_gt_four {β : ℝ} (hβ : 4 < β) (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedTail β lam h k q ≤ ENNReal.ofReal
        (C * h ^ (2 - β) * lam ^ ((4 - β) * (k + 1)) * (1 + Real.log (h / lam)) ^ q) := by
  let c := 1 / 2 + 1 / (β - 4)
  let A := ((k : ℝ) + 1) * c ^ (k + 1)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hA : 0 < A := mul_pos (by positivity) (pow_pos hc _)
  refine ⟨A * momentConstant (β - 2) q, mul_pos hA (momentConstant_pos (by linarith) _),
    fun lam h hlam hlh => ?_⟩
  have hb := internal_orderedTail_le (β := β) (σ := (4 - β) * (k + 1)) (τ := 0) k q q
    hlam hlh hA.le (by linarith) (fun u hu => ?_)
  · simp only [sub_zero, show -(β - 2) = 2 - β by ring] at hb
    refine hb.trans_eq ?_
    congr 1
    ring
  · unfold SmallIntegral.RouteJ.innerRadial
    rw [max_eq_left (hlh.trans hu.le)]
    have hm := lintegral_minimum_log_le_of_neg (k := k) (show 4 - β < 0 by linarith)
      q hlam (hlh.trans hu.le)
    rw [show 4 - β - 2 = 2 - β by ring, show -(4 - β) = β - 4 by ring] at hm
    refine hm.trans_eq ?_
    have hL : 0 ≤ 1 + Real.log (u / lam) := by
      have := Real.log_nonneg ((one_le_div hlam).2 (hlh.trans hu.le))
      linarith
    simp only [Real.rpow_zero, mul_one]
    rw [show lam ^ ((4 - β) * (k + 1)) = (lam ^ (4 - β)) ^ (k + 1) by
      rw [Real.rpow_mul hlam.le, ← Nat.cast_add_one, Real.rpow_natCast]]
    simp only [A, c]
    simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_add, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

end MultipoleBKT.ExpansionK.RouteSpatial

end
