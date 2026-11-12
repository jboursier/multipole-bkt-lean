/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.CutoffGain

/-!
# Absorbing the logarithms at the final cutoff step

See (A.42). Only here are logarithmic moments absorbed by small powers of
`λ`. The threshold may depend on `ε₀`, while the coefficient does not.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set Filter Topology
open scoped ENNReal

private theorem tendsto_power_log_moment {θ : ℝ} (hθ : 0 < θ) (B : ℝ) (q : ℕ) :
    Tendsto (fun lam : ℝ => lam ^ θ * (1 + B * |Real.log lam|) ^ q)
      (𝓝[>] 0) (𝓝 0) := by
  let r := θ / ((q : ℝ) + 1)
  have hr : 0 < r := div_pos hθ (by positivity)
  have ht : Tendsto (fun lam : ℝ => lam ^ r) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hr.ne'] using
      ((Real.continuous_rpow_const hr.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun lam : ℝ => |Real.log lam| * lam ^ r) (𝓝[>] 0) (𝓝 0) := by
    have he := (tendsto_log_mul_rpow_nhdsGT_zero hr).abs
    simp only [abs_zero] at he
    apply he.congr'
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hlam) r)]
  have hi : Tendsto (fun lam : ℝ => lam ^ r * (1 + B * |Real.log lam|))
      (𝓝[>] 0) (𝓝 0) := by
    convert ht.add (hl.const_mul B) using 1
    · funext lam
      ring
    · simp
  have he := ht.mul (hi.pow q)
  simp only [zero_mul] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  have hlam0 : 0 < lam := hlam
  have hp : lam ^ r * (lam ^ r * (1 + B * |Real.log lam|)) ^ q =
      lam ^ θ * (1 + B * |Real.log lam|) ^ q := by
    rw [mul_pow, ← mul_assoc, ← pow_succ', ← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]
    have heq : r * ((q + 1 : ℕ) : ℝ) = θ := by
      dsimp [r]
      push_cast
      field_simp
    rw [heq]
  exact hp

private theorem small_power_log_moment {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (B : ℝ) (q : ℕ) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
      lam ^ θ * (1 + B * |Real.log lam|) ^ q ≤ δ := by
  have he := (tendsto_power_log_moment hθ B q).eventually_lt_const hδ
  obtain ⟨lam₀, hlam₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  exact ⟨lam₀, hlam₀, fun lam hlam hl => (hsub ⟨hlam, hl⟩).le⟩

/-- The paper's logarithmic cutoff comparison for `β ≥ 4`. -/
theorem log_cutoff_le {β lam eps : ℝ} {p₀ : ℕ} (hβ : 4 ≤ β) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    Real.log (eps * truncationScale p₀ β lam / lam) ≤
      (2 * (p₀ : ℝ) + 1) * |Real.log lam| := by
  rw [Appendix.truncationScale_of_ge hβ,
    Real.log_div (mul_pos heps (zpow_pos hlam _)).ne' hlam.ne',
    Real.log_mul heps.ne' (zpow_ne_zero _ hlam.ne'), Real.log_zpow,
    abs_of_nonpos (Real.log_nonpos hlam.le hlam1)]
  have he : Real.log eps ≤ 0 := Real.log_nonpos heps.le heps1
  push_cast
  linarith

/-- Final radial cutoff gain with the coefficient independent of `ε₀`.
The number of radii is `k+1`. The cutoff and the smallness threshold are explicit
in the quantifier order used in the paper. -/
theorem radial_cutoff_gain {β : ℝ} (hβ : 2 < β) (p₀ k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
        cutoffLogIntegral β lam (eps * truncationScale p₀ β lam) k q ≤
          ENNReal.ofReal (C * eps ^ (alphaExponent β * (k + 1)) * lam ^ ((2 - β) * (k + 1))) := by
  by_cases hβ4 : β < 4
  · obtain ⟨C, hC, hbound⟩ := radial_cutoff_gain_lt_four hβ hβ4 k q
    refine ⟨C, hC, fun eps heps heps1 => ⟨min eps 1, lt_min heps zero_lt_one, ?_⟩⟩
    intro lam hlam hsmall
    have hlameps : lam ≤ eps := hsmall.trans (min_le_left _ _)
    have hlam1 : lam ≤ 1 := hsmall.trans (min_le_right _ _)
    have hR := Appendix.one_le_truncationScale (p₀ := p₀) hβ hlam hlam1
    have hlh : lam ≤ eps * truncationScale p₀ β lam :=
      hlameps.trans (le_mul_of_one_le_right heps.le hR)
    refine (hbound lam _ hlam hlh).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hp : (eps * truncationScale p₀ β lam) ^ ((4 - β) * (k + 1)) =
        eps ^ ((4 - β) * (k + 1)) * lam ^ ((2 - β) * (k + 1)) := by
      rw [Real.mul_rpow heps.le (Appendix.truncationScale_pos hlam).le,
        Real.rpow_mul (Appendix.truncationScale_pos hlam).le,
        Appendix.rpow_truncationScale_of_lt hβ4 hlam, ← Real.rpow_mul hlam.le]
    rw [hp, alphaExponent, ite_eq_left hβ4]
    have he : eps ^ ((4 - β) * (k + 1)) ≤ eps ^ ((4 - β) / 2 * (k + 1)) := by
      apply Real.rpow_le_rpow_of_exponent_ge heps heps1
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      nlinarith
    calc
      _ ≤ C * (eps ^ ((4 - β) / 2 * (k + 1)) * lam ^ ((2 - β) * (k + 1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hlam.le _)) hC.le
      _ = _ := by ring
  · have hge : 4 ≤ β := le_of_not_gt hβ4
    have hα : alphaExponent β = 1 / 2 := by rw [alphaExponent, ite_eq_right hβ4]
    by_cases heq : β = 4
    · subst β
      obtain ⟨C, hC, hbound⟩ := radial_cutoff_gain_four k q
      refine ⟨C, hC, fun eps heps heps1 => ?_⟩
      obtain ⟨δ, hδ, hδbound⟩ := small_power_log_moment
        (show (0 : ℝ) < 2 * ((k : ℝ) + 1) by positivity)
        (Real.rpow_pos_of_pos heps ((1 / 2 : ℝ) * (k + 1))) (2 * (p₀ : ℝ) + 1) (k + 1 + q)
      refine ⟨min δ (min eps 1), lt_min hδ (lt_min heps zero_lt_one), ?_⟩
      intro lam hlam hsmall
      have hlamδ : lam ≤ δ := hsmall.trans (min_le_left _ _)
      have hlameps : lam ≤ eps := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hlam1 : lam ≤ 1 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hlh : lam ≤ eps * truncationScale p₀ 4 lam := hlameps.trans
        (le_mul_of_one_le_right heps.le (Appendix.one_le_truncationScale (by norm_num) hlam hlam1))
      have hlog := log_cutoff_le (p₀ := p₀) (by norm_num : (4 : ℝ) ≤ 4) hlam hlam1 heps heps1
      have hL : 0 ≤ 1 + Real.log (eps * truncationScale p₀ 4 lam / lam) := by
        have := Real.log_nonneg ((one_le_div hlam).2 hlh)
        linarith
      have hp := hδbound lam hlam hlamδ
      have hpow := pow_le_pow_left₀ hL (add_le_add_right hlog 1) (k + 1 + q)
      have hmul := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hlam.le (2 * (k + 1)))
      refine (hbound lam _ hlam hlh).trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [hα]
      have he : lam ^ (2 * ((k : ℝ) + 1)) * lam ^ ((2 - 4) * ((k : ℝ) + 1)) = 1 := by
        rw [← Real.rpow_add hlam]
        convert Real.rpow_zero lam using 1
        ring_nf
      have hgain : (1 + Real.log (eps * truncationScale p₀ 4 lam / lam)) ^ (k + 1 + q) ≤
          eps ^ ((1 / 2 : ℝ) * (k + 1)) * lam ^ (((2 : ℝ) - 4) * ((k : ℝ) + 1)) := by
        calc
          _ = (lam ^ (2 * ((k : ℝ) + 1)) *
              lam ^ (((2 : ℝ) - 4) * ((k : ℝ) + 1))) *
              (1 + Real.log (eps * truncationScale p₀ 4 lam / lam)) ^ (k + 1 + q) := by rw [he, one_mul]
          _ = (lam ^ (2 * ((k : ℝ) + 1)) *
              (1 + Real.log (eps * truncationScale p₀ 4 lam / lam)) ^ (k + 1 + q)) *
              lam ^ (((2 : ℝ) - 4) * ((k : ℝ) + 1)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hmul.trans hp)
            (Real.rpow_nonneg hlam.le _)
      calc
        _ ≤ C * (eps ^ ((1 / 2 : ℝ) * (k + 1)) *
            lam ^ (((2 : ℝ) - 4) * ((k : ℝ) + 1))) := mul_le_mul_of_nonneg_left hgain hC.le
        _ = _ := by ring
    · have hgt : 4 < β := lt_of_le_of_ne hge (Ne.symm heq)
      obtain ⟨C, hC, hbound⟩ := radial_cutoff_gain_gt_four hgt k q
      refine ⟨C, hC, fun eps heps heps1 => ?_⟩
      obtain ⟨δ, hδ, hδbound⟩ := small_power_log_moment
        (show (0 : ℝ) < 2 * ((k : ℝ) + 1) by positivity)
        (Real.rpow_pos_of_pos heps ((1 / 2 : ℝ) * (k + 1))) (2 * (p₀ : ℝ) + 1) q
      refine ⟨min δ (min eps 1), lt_min hδ (lt_min heps zero_lt_one), ?_⟩
      intro lam hlam hsmall
      have hlamδ : lam ≤ δ := hsmall.trans (min_le_left _ _)
      have hlameps : lam ≤ eps := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hlam1 : lam ≤ 1 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hlh : lam ≤ eps * truncationScale p₀ β lam := hlameps.trans
        (le_mul_of_one_le_right heps.le (Appendix.one_le_truncationScale hβ hlam hlam1))
      have hlog := log_cutoff_le (p₀ := p₀) hge hlam hlam1 heps heps1
      have hL : 0 ≤ 1 + Real.log (eps * truncationScale p₀ β lam / lam) := by
        have := Real.log_nonneg ((one_le_div hlam).2 hlh)
        linarith
      have hp := hδbound lam hlam hlamδ
      have hpow := pow_le_pow_left₀ hL (add_le_add_right hlog 1) q
      have hmul := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hlam.le (2 * (k + 1)))
      have he : lam ^ ((4 - β) * (k + 1)) =
          lam ^ (2 * ((k : ℝ) + 1)) * lam ^ ((2 - β) * (k + 1)) := by
        rw [← Real.rpow_add hlam]
        congr 1
        ring
      refine (hbound lam _ hlam hlh).trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [he, hα]
      have hgain := mul_le_mul_of_nonneg_right (hmul.trans hp)
        (mul_nonneg hC.le (Real.rpow_nonneg hlam.le ((2 - β) * (k + 1))))
      nlinarith

end MultipoleBKT.RouteLog

end
