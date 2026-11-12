/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegralZ.LowerBound

/-!
# The singleton disk and allowed roots

See Proposition 5.18.
The positive endpoint avoids the boundary layer and the closed disks of radius
`(M+1)λ` around the bad endpoints. The displacement has norm at most `λ`.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegralZ.RouteSingleton

open MeasureTheory Set Metric MultipoleIntegral UpperBound
open scoped ENNReal
open TwoComponentCoulomb (box)

/-- Excluding the bad endpoint disks makes every displacement in the singleton disk good.
See Proposition 5.18. -/
theorem isGoodZ_of_disk {N p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} (hM : 0 ≤ M) {e : ℂ × ℂ}
    (hr : ‖e.1 - e.2‖ ≤ lam) (hx : e.1 ∉ badNbhd V Z ((M + 1) * lam)) :
    IsGoodZ p₀ β lam M ε₀ V Z e := by
  by_contra hn
  obtain ⟨j, hj, hd⟩ := exists_near_of_not_isGoodZ hM hn
  rw [max_eq_right hr] at hd
  apply hx
  simp only [badNbhd, mem_iUnion, mem_union, mem_closedBall, dist_eq_norm]
  have key (q : ℂ) (hq : ‖e.2 - q‖ ≤ M * lam) : ‖e.1 - q‖ ≤ (M + 1) * lam := by
    have := norm_sub_le_norm_sub_add_norm_sub e.1 e.2 q
    nlinarith
  have direct (q : ℂ) (hq : ‖e.1 - q‖ ≤ M * lam) : ‖e.1 - q‖ ≤ (M + 1) * lam := by
    have := (norm_nonneg (e.1 - e.2)).trans hr
    nlinarith
  unfold dipoleDist at hd
  rcases min_le_iff.1 hd with h | h <;> rcases min_le_iff.1 h with h | h
  · exact ⟨j, hj, Or.inl (direct _ h)⟩
  · exact ⟨j, hj, Or.inr (direct _ h)⟩
  · exact ⟨j, hj, Or.inl (key _ h)⟩
  · exact ⟨j, hj, Or.inr (key _ h)⟩

/-- The boundary layer of width `2λ` keeps both singleton endpoints in the square. -/
theorem mem_box_of_disk {N : ℕ} {lam : ℝ} (hlam : 0 < lam) {e : ℂ × ℂ}
    (hx : e.1 ∈ innerBox N (2 * lam)) (hr : ‖e.1 - e.2‖ ≤ lam) :
    e ∈ box N ×ˢ box N := by
  simp only [innerBox, Complex.mem_reProdIm, mem_Icc] at hx
  have hb : ball e.1 (2 * lam) ⊆ box N :=
    ball_subset_box hx.1.1 (by linarith [hx.1.2]) hx.2.1 (by linarith [hx.2.2])
  refine ⟨hb (by simpa using (show (0 : ℝ) < 2 * lam by positivity)), hb ?_⟩
  rw [mem_ball, dist_eq_norm, norm_sub_rev]
  linarith

/-- The allowed root area is at least `N/8`. The removed disks have area at most
`2π |V_bad| (M+1)² λ² ≤ 2π N (M+1)² λ²`.
See Proposition 5.18. -/
theorem root_area {N : ℕ} {lam M : ℝ} (hlam : 0 < lam) (hM : 0 ≤ M)
    (hsmall : lam ≤ (16 * (M + 1))⁻¹) (hN : 8 * lam ≤ Real.sqrt N)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    ENNReal.ofReal (N / 8) ≤ volume (innerBox N (2 * lam) \ badNbhd V Z ((M + 1) * lam)) := by
  have hVN : (V.card : ℝ) ≤ N := by
    have h := Finset.card_le_univ V
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  have hρ : (M + 1) * lam ≤ 1 / 16 := by
    calc (M + 1) * lam ≤ (M + 1) * (16 * (M + 1))⁻¹ := by gcongr
         _ = 1 / 16 := by field_simp
  have hbad : volume (badNbhd V Z ((M + 1) * lam)) ≤ ENNReal.ofReal (N / 8) := by
    refine (volume_badNbhd_le V Z (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : 16 * Real.pi * ((M + 1) * lam) ^ 2 ≤ 1 := by
      have := Real.pi_le_four
      have hρ0 : 0 ≤ (M + 1) * lam := by positivity
      have hs : ((M + 1) * lam) ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four (sq_nonneg ((M + 1) * lam))]
    have hmul : 2 * (V.card : ℝ) * Real.pi * ((M + 1) * lam) ^ 2 ≤
        2 * N * Real.pi * ((M + 1) * lam) ^ 2 := by gcongr
    nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  calc ENNReal.ofReal (N / 8) = ENNReal.ofReal (N / 4) - ENNReal.ofReal (N / 8) := by
        rw [← ENNReal.ofReal_sub _ (by positivity)]
        congr 1
        ring
       _ ≤ volume (innerBox N (2 * lam)) - volume (badNbhd V Z ((M + 1) * lam)) :=
        tsub_le_tsub (ofReal_quarter_le_volume_innerBox (by positivity) (by linarith : 4 * (2 * lam) ≤ Real.sqrt N)) hbad
       _ ≤ _ := le_measure_sdiff

end MultipoleBKT.MultipoleIntegralZ.RouteSingleton

end
