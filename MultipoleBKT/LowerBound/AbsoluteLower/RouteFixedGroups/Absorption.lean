/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Absorption
public import MultipoleBKT.Main.TheoremTwo.Parameters

/-!
# Uniform logarithm absorption for large clusters

the calculation after
(A.69) in the proof of Lemma 4.58. Compare the physical cutoff logarithm
with `|log λ|`. The remaining small-power estimate is uniform in every
integer cluster size `k ≥ 3`.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open Filter Set Topology

/-- The exponent margin printed after (A.69). -/
theorem high_beta_exponent_margin {p₀ k : ℕ} {a : ℝ} (hp : 1 ≤ p₀) (hk : 2 * p₀ < k)
    (ha : (2 * (p₀ : ℝ) + 1) * a ≤ 1 / 2) :
    (2 - a * (2 * p₀ + 1)) * k - 2 - 2 * p₀ ≥ (k : ℝ) / 6 := by
  have hpR : (1 : ℝ) ≤ p₀ := by exact_mod_cast hp
  have hkR : 2 * (p₀ : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : 2 * p₀ + 1 ≤ k)
  have hk0 : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_right ha hk0]

/-- A single small cutoff absorbs the critical logarithm for all cluster sizes.
The physical cutoff logarithm is controlled by the logarithmic bound in the same bound. -/
theorem uniform_high_beta_log_cutoff (p₀ : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ {β lam eps : ℝ}, 4 ≤ β → 0 < lam → lam ≤ δ →
      0 < eps → eps ≤ 1 → ∀ {k : ℕ}, 3 ≤ k →
        lam ^ ((k : ℝ) / 12) *
          max (1 + Real.log (eps * truncationScale p₀ β lam / lam))
            (if β = 4 then |Real.log lam| else 1) ≤ 1 := by
  let D : ℝ := 2 * p₀ + 1
  have hD : 1 ≤ D := by dsimp only [D]; have := (Nat.cast_nonneg p₀ : (0 : ℝ) ≤ p₀); linarith
  have ht : Tendsto (fun lam : ℝ => lam ^ (1 / 4 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)).tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
  have hl : Tendsto (fun lam : ℝ => |Real.log lam| * lam ^ (1 / 4 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    have he := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 4)).abs
    simp only [abs_zero] at he
    apply he.congr'
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hlam) _)]
  have hlim : Tendsto (fun lam : ℝ => lam ^ (1 / 4 : ℝ) + D * (|Real.log lam| * lam ^ (1 / 4 : ℝ)))
      (𝓝[>] 0) (𝓝 0) := by simpa only [mul_zero, add_zero] using ht.add (hl.const_mul D)
  have he := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  refine ⟨min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro β lam eps hβ hlam hlδ heps heps1 k hk
  have hlam1 : lam ≤ 1 := hlδ.trans (min_le_right _ _)
  have hsmall := (hsub ⟨hlam, hlδ.trans (min_le_left _ _)⟩).le
  have hlog := RouteLog.log_cutoff_le (p₀ := p₀) hβ hlam hlam1 heps heps1
  have hmax : max (1 + Real.log (eps * truncationScale p₀ β lam / lam))
      (if β = 4 then |Real.log lam| else 1) ≤ 1 + D * |Real.log lam| := by
    apply max_le
    · exact add_le_add le_rfl hlog
    · split_ifs
      · nlinarith [abs_nonneg (Real.log lam)]
      · have : 0 ≤ D * |Real.log lam| := mul_nonneg (zero_le_one.trans hD) (abs_nonneg _)
        linarith
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  calc
    _ ≤ lam ^ ((k : ℝ) / 12) * (1 + D * |Real.log lam|) :=
      mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg hlam.le _)
    _ ≤ lam ^ (1 / 4 : ℝ) * (1 + D * |Real.log lam|) := by
      apply mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith : (1 / 4 : ℝ) ≤ (k : ℝ) / 12))
        (by positivity)
    _ ≤ 1 := by nlinarith [hsmall]

/-- The final small-power and critical-logarithm absorption after (A.69).
The exponent margin is split into two equal parts. One pays for `ε₀`,
and the other absorbs the logarithm uniformly in `k`. -/
theorem high_beta_power_log_absorption (p₀ : ℕ) (hp : 1 ≤ p₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ {β lam eps a : ℝ}, 4 ≤ β →
      0 < lam → lam ≤ δ → 0 < eps → eps ≤ 1 → lam ^ (1 / 12 : ℝ) ≤ eps →
      (2 * (p₀ : ℝ) + 1) * a ≤ 1 / 2 → ∀ {k : ℕ}, 2 * p₀ < k →
        lam ^ (2 * k - 2 - (2 * p₀ + 1) * a * k) *
          (if β = 4 then |Real.log lam| else 1) ≤ lam ^ (2 * p₀) * eps ^ ((k : ℝ) - 2) := by
  obtain ⟨δ, hδ, hδ1, hb⟩ := uniform_high_beta_log_cutoff p₀
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro β lam eps a hβ hlam hlδ heps heps1 hle ha k hk
  have hk3 : 3 ≤ k := by omega
  have hlam1 : lam ≤ 1 := hlδ.trans hδ1
  have hmargin := high_beta_exponent_margin hp hk ha
  have hm : 2 * (p₀ : ℝ) + (k : ℝ) / 6 ≤ 2 * k - 2 - (2 * p₀ + 1) * a * k := by
    nlinarith [hmargin]
  let L := if β = 4 then |Real.log lam| else 1
  have hL : 0 ≤ L := by dsimp only [L]; split_ifs <;> positivity
  have hlog : lam ^ ((k : ℝ) / 12) * L ≤ 1 :=
    (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_nonneg hlam.le _)).trans
      (hb hβ hlam hlδ heps heps1 hk3)
  have hepspow : lam ^ ((k : ℝ) / 12) ≤ eps ^ (k : ℝ) := by
    have he : lam ^ ((k : ℝ) / 12) = (lam ^ (1 / 12 : ℝ)) ^ (k : ℝ) := by
      rw [← Real.rpow_mul hlam.le]
      congr 1
      ring
    rw [he]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hlam.le _) hle (by positivity)
  calc
    _ ≤ lam ^ (2 * (p₀ : ℝ) + (k : ℝ) / 6) * L :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hlam hlam1 hm) hL
    _ = lam ^ (2 * (p₀ : ℝ)) * (lam ^ ((k : ℝ) / 12) *
        (lam ^ ((k : ℝ) / 12) * L)) := by
      rw [show 2 * (p₀ : ℝ) + (k : ℝ) / 6 =
        (2 * (p₀ : ℝ) + (k : ℝ) / 12) + (k : ℝ) / 12 by ring,
        Real.rpow_add hlam, Real.rpow_add hlam]
      ring
    _ ≤ lam ^ (2 * (p₀ : ℝ)) * (eps ^ (k : ℝ) * 1) := by gcongr
    _ ≤ _ := by
      rw [mul_one]
      have hp := Real.rpow_le_rpow_of_exponent_ge heps heps1 (by linarith : (k : ℝ) - 2 ≤ k)
      have hcast : 2 * (p₀ : ℝ) = ((2 * p₀ : ℕ) : ℝ) := by push_cast; rfl
      rw [hcast, Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left hp (pow_nonneg hlam.le _)

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
