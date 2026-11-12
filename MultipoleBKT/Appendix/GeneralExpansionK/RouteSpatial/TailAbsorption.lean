/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailVector

/-!
# Final absorption in case F

See (A.64). Substitute the truncation scale only after the three logarithmic
radial displays. The extra positive power of lambda absorbs the logarithms
at and above four.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset MultipoleBKT.RouteLog GeneralExpansion Appendix
open scoped ENNReal

/-- A final scalar polynomial bound at the physical temperature, used only
after integrating the spatial and inner radial logarithms. -/
theorem cutoff_tail_log_bound {β : ℝ} (hβ : 4 ≤ β) (p₀ k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      lam ^ (2 * ((k : ℝ) + 2)) *
        (1 + Real.log (eps * truncationScale p₀ β lam / lam)) ^ q ≤ C := by
  obtain ⟨C,hC,hb⟩ := power_log_uniform (show 0 < 2 * ((k : ℝ) + 2) by positivity)
    (show (0 : ℝ) ≤ 2 * p₀ + 1 by positivity) q
  refine ⟨C,hC,fun eps lam hlam hle heps => ?_⟩
  have heps0 := hlam.trans_le hle
  have hlh : lam ≤ eps * truncationScale p₀ β lam := hle.trans
    (le_mul_of_one_le_right heps0.le (one_le_truncationScale (by linarith) hlam (hle.trans heps)))
  have hL : 0 ≤ 1 + Real.log (eps * truncationScale p₀ β lam / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  have hp := pow_le_pow_left₀ hL
    (add_le_add_right (log_cutoff_le hβ hlam (hle.trans heps) heps0 heps) 1) q
  exact (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hlam.le _)).trans (hb lam hlam (hle.trans heps))

/-- Below four, the cutoff substitution is exact. -/
theorem caseF_power_scaling {β eps lam : ℝ} (hβ4 : β < 4) (hlam : 0 < lam)
    (heps : 0 < eps) (p₀ k : ℕ) :
    (eps * truncationScale p₀ β lam) ^ ((4 - β) * (k + 2) - 2) =
      eps ^ ((4 - β) * (k + 2) - 2) * lam ^ ((2 - β) * (k + 2)) *
        truncationScale p₀ β lam ^ (-2 : ℝ) := by
  have hR := truncationScale_pos (p₀ := p₀) (β := β) hlam
  rw [Real.mul_rpow heps.le hR.le,
    show (4 - β) * ((k : ℝ) + 2) - 2 = (4 - β) * ((k : ℝ) + 2) + -2 by ring,
    Real.rpow_add hR]
  have hsc := rpow_truncationScale_mul_of_lt (p₀ := p₀) (k := k + 2) hlam hβ4
  simp only [Nat.cast_add, Nat.cast_ofNat] at hsc
  rw [hsc]
  ring

/-- The critical logarithmic display is absorbed after its evaluation. -/
theorem caseF_four_absorb (p₀ k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      orderedTail 4 lam (eps * truncationScale p₀ 4 lam) k (k + 2) ≤
        ENNReal.ofReal (C * eps ^ (-2 : ℝ) * lam ^ ((2 - 4 : ℝ) * (k + 2)) *
          truncationScale p₀ 4 lam ^ (-2 : ℝ)) := by
  obtain ⟨A,hA,htail⟩ := caseF_four k
  obtain ⟨B,hB,hlog⟩ := cutoff_tail_log_bound (by norm_num : (4 : ℝ) ≤ 4) p₀ k (2 * (k + 2))
  refine ⟨A * B,mul_pos hA hB,fun eps lam hlam hle heps => ?_⟩
  have heps0 := hlam.trans_le hle
  have hR := truncationScale_pos (p₀ := p₀) (β := 4) hlam
  have hlh : lam ≤ eps * truncationScale p₀ 4 lam := hle.trans
    (le_mul_of_one_le_right heps0.le (one_le_truncationScale (by norm_num) hlam (hle.trans heps)))
  refine (htail lam _ hlam hlh).trans (ENNReal.ofReal_le_ofReal ?_)
  have hh := mul_pos heps0 hR
  have he : lam ^ ((2 - 4 : ℝ) * (k + 2)) * lam ^ (2 * ((k : ℝ) + 2)) = 1 := by
    rw [← Real.rpow_add hlam]
    ring_nf
    exact Real.rpow_zero _
  have hp := mul_le_mul_of_nonneg_left (hlog eps lam hlam hle heps)
    (show 0 ≤ A * eps ^ (-2 : ℝ) * lam ^ ((2 - 4 : ℝ) * (k + 2)) *
      truncationScale p₀ 4 lam ^ (-2 : ℝ) by positivity)
  rw [Real.mul_rpow heps0.le hR.le]
  calc
    _ = (A * eps ^ (-2 : ℝ) * lam ^ ((2 - 4 : ℝ) * (k + 2)) *
        truncationScale p₀ 4 lam ^ (-2 : ℝ)) *
        (lam ^ (2 * ((k : ℝ) + 2)) *
          (1 + Real.log (eps * truncationScale p₀ 4 lam / lam)) ^ (2 * (k + 2))) := by
      calc
        _ = (A * eps ^ (-2 : ℝ) * truncationScale p₀ 4 lam ^ (-2 : ℝ) *
          (1 + Real.log (eps * truncationScale p₀ 4 lam / lam)) ^ (2 * (k + 2))) * 1 := by ring
        _ = _ := by rw [← he]; ring
    _ ≤ _ := hp.trans_eq (by ring)

/-- Above four, the endpoint power has a surplus of `lambda^(2(k+2))`.
The additional nonnegative powers are discarded only after the radial calculation. -/
theorem caseF_gt_four_absorb {β : ℝ} (hβ : 4 < β) (p₀ k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      orderedTail β lam (eps * truncationScale p₀ β lam) k (k + 2) ≤
        ENNReal.ofReal (C * eps ^ (2 - β) * lam ^ ((2 - β) * (k + 2)) *
          truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  obtain ⟨A,hA,htail⟩ := orderedTail_gt_four hβ k (k + 2)
  obtain ⟨B,hB,hlog⟩ := cutoff_tail_log_bound hβ.le p₀ k (k + 2)
  refine ⟨A * B,mul_pos hA hB,fun eps lam hlam hle heps => ?_⟩
  have heps0 := hlam.trans_le hle
  let R := truncationScale p₀ β lam
  have hR : 0 < R := truncationScale_pos hlam
  have hR1 : 1 ≤ R := one_le_truncationScale (by linarith) hlam (hle.trans heps)
  have hlh : lam ≤ eps * R := hle.trans (le_mul_of_one_le_right heps0.le hR1)
  refine (htail lam _ hlam hlh).trans (ENNReal.ofReal_le_ofReal ?_)
  have hRp : R ^ (4 - β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR1 (by linarith)
  have hlp : lam ^ (β - 4) ≤ 1 := Real.rpow_le_one hlam.le (hle.trans heps) (by linarith)
  have heR : R ^ (2 - β) = R ^ (-2 : ℝ) * R ^ (4 - β) := by
    rw [← Real.rpow_add hR]
    congr 1
    ring
  have hel : lam ^ ((4 - β) * (k + 1)) =
      lam ^ ((2 - β) * (k + 2)) * lam ^ (2 * ((k : ℝ) + 2)) * lam ^ (β - 4) := by
    rw [← Real.rpow_add hlam, ← Real.rpow_add hlam]
    congr 1
    ring
  rw [Real.mul_rpow heps0.le hR.le, heR, hel]
  let L := (1 + Real.log (eps * R / lam)) ^ (k + 2)
  have hL : 0 ≤ L := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    dsimp only [L]
    positivity
  have hs : R ^ (4 - β) * lam ^ (β - 4) ≤ 1 :=
    (mul_le_mul hRp hlp (Real.rpow_nonneg hlam.le _) (by norm_num)).trans_eq (one_mul 1)
  have hrest : R ^ (4 - β) * lam ^ (β - 4) *
      (lam ^ (2 * ((k : ℝ) + 2)) * L) ≤ B := by
    calc
      _ ≤ 1 * (lam ^ (2 * ((k : ℝ) + 2)) * L) :=
        mul_le_mul_of_nonneg_right hs (mul_nonneg (Real.rpow_nonneg hlam.le _) hL)
      _ ≤ B := by simpa only [one_mul] using hlog eps lam hlam hle heps
  calc
    _ = (A * eps ^ (2 - β) * lam ^ ((2 - β) * (k + 2)) * R ^ (-2 : ℝ)) *
        (R ^ (4 - β) * lam ^ (β - 4) * (lam ^ (2 * ((k : ℝ) + 2)) * L)) := by ring
    _ ≤ (A * eps ^ (2 - β) * lam ^ ((2 - β) * (k + 2)) * R ^ (-2 : ℝ)) * B :=
      mul_le_mul_of_nonneg_left hrest (by positivity)
    _ = _ := by ring

/-- The final case-F normalization, after the three explicit radial regimes.
The coefficient may depend on the fixed cutoff epsilon, as in (A.64). -/
theorem caseF_bound {β : ℝ} (hβ : 2 < β) (p₀ k : ℕ)
    (hkp : ((k + 2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ eps →
      orderedTail β lam (eps * truncationScale p₀ β lam) k (k + 2) ≤
        ENNReal.ofReal (C * lam ^ ((2 - β) * (k + 2)) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  intro eps heps heps1
  by_cases hlt : β < 4
  · have hsize : (4 - β) * ((k : ℝ) + 2) < 2 := by
      have hb := (transitionBeta_lt_iff (show 1 ≤ k + 2 by omega) β).1
        ((le_pStar_iff (show 1 ≤ k + 2 by omega)).1 hkp)
      push_cast at hb
      linarith
    obtain ⟨A,hA,hb⟩ := orderedTail_lt_four hβ hlt k (k + 2) hsize
    refine ⟨A * eps ^ ((4 - β) * (k + 2) - 2), mul_pos hA (Real.rpow_pos_of_pos heps _),
      fun lam hlam hle => ?_⟩
    have hlh : lam ≤ eps * truncationScale p₀ β lam := hle.trans
      (le_mul_of_one_le_right heps.le (one_le_truncationScale hβ hlam (hle.trans heps1)))
    refine (hb lam _ hlam hlh).trans_eq ?_
    rw [caseF_power_scaling hlt hlam heps p₀ k]
    congr 1
    ring
  · by_cases heq : β = 4
    · subst β
      obtain ⟨A,hA,hb⟩ := caseF_four_absorb p₀ k
      refine ⟨A * eps ^ (-2 : ℝ), mul_pos hA (Real.rpow_pos_of_pos heps _),
        fun lam hlam hle => ?_⟩
      exact hb eps lam hlam hle heps1
    · have hgt : 4 < β := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      obtain ⟨A,hA,hb⟩ := caseF_gt_four_absorb hgt p₀ k
      refine ⟨A * eps ^ (2 - β), mul_pos hA (Real.rpow_pos_of_pos heps _),
        fun lam hlam hle => ?_⟩
      exact hb eps lam hlam hle heps1

end MultipoleBKT.ExpansionK.RouteSpatial

end
