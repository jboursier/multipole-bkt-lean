/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneAssembly
public import MultipoleBKT.UpperBound.BadPointTypes.Radial
public import MultipoleBKT.Frozen.ErrorRate

/-!
# Lemma 5.40: the per-unit estimates

The paper: proof of Lemma 5.40, Step 5: with
`ν = λ^{1-β/2}` (the normalization per charge, `ν^{2n} = λ^{(2-β)n}`) and `δ = δ_{β,λ}`,

* one overcrowded cluster summed over its dyadic scales: `X ≤ C N δ ν^{q+1}`
  (`crowdSum_le`; for `β < 4` because `(q+1)(2-β/2) - 2 ≥ 1 > 0` (proof of Lemma 5.40) and `R^{4-β} = λ^{2-β}`,
  for `β ≥ 4` because `q - 1 = 2p₀`, (5.130));
* one long singleton: `Y = N (h/4)^{-β/2} ≤ C N δ ν` (`singleTerm_le`);
* one good charge: `K_g = ∫_{|u| ≤ h} max(|u|/4, λ)^{-β/2} ≤ C ν` (`goodIntegral_le`; for
  `β = 4` the logarithm, proof of Lemma 5.40, is absorbed by `λ(1 + |log λ|) ≤ C`).

The constants depend on `β`, `p₀` and `ε₀`; `λ ≤ 1` and `λ ≤ ε₀ R̄` are assumed.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset MeasureTheory
open scoped ENNReal

variable {p₀ : ℕ} {β lam ε₀ : ℝ}

/-! ### The scales -/

theorem truncationScale_rpow_half (hβ4 : β < 4) (hlam : 0 < lam) :
    truncationScale p₀ β lam ^ (2 - β / 2) = lam ^ (1 - β / 2) := by
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  rw [show (2 : ℝ) - β / 2 = (4 - β) * (1 / 2) by ring, Real.rpow_mul hR.le,
    Appendix.rpow_truncationScale_of_lt hβ4 hlam, ← Real.rpow_mul hlam.le]
  ring_nf

theorem inv_sq_truncationScale_le_errorRate (hβ : 2 < β) (hβ4 : β < 4) :
    (truncationScale p₀ β lam ^ 2)⁻¹ ≤ errorRate p₀ β lam := by
  unfold errorRate
  rw [ite_eq_left ⟨hβ, hβ4⟩, ite_eq_right (by linarith), add_zero]
  have htsum : 0 ≤ ∑' q : ℕ, (if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0) :=
    tsum_nonneg fun q => by split_ifs <;> simp
  have hR : truncationScale p₀ β lam = (criticalScale β lam).toReal := by
    unfold truncationScale
    rw [ite_eq_left hβ4]
  rw [← hR, zpow_neg, zpow_two, ← sq]
  have : 0 ≤ (truncationScale p₀ β lam ^ 2)⁻¹ := by positivity
  nlinarith

theorem errorRate_of_ge (hβ4 : 4 ≤ β) : errorRate p₀ β lam = lam ^ (2 * p₀) := by
  unfold errorRate
  rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_left hβ4, zero_add]

theorem errorRate_nonneg (hlam : 0 < lam) : 0 ≤ errorRate p₀ β lam := by
  unfold errorRate
  refine add_nonneg ?_ ?_
  · split_ifs
    · refine mul_nonneg (zpow_nonneg ENNReal.toReal_nonneg _) (add_nonneg zero_le_one ?_)
      exact tsum_nonneg fun q => by split_ifs <;> simp
    · exact le_rfl
  · split_ifs
    · positivity
    · exact le_rfl

/-- The clustering parameter for `β ≥ 4`. -/
theorem clusterThreshold_of_ge (hβ4 : 4 ≤ β) : clusterThreshold p₀ β = 2 * p₀ + 1 := by
  unfold clusterThreshold
  rw [ite_eq_right (by linarith)]

/-- For `β ∈ (2, 4)`, `(q(β) + 1)(2 - β/2) > 3` (proof of Lemma 5.40). -/
theorem three_lt_clusterThreshold (hβ4 : β < 4) :
    3 < ((clusterThreshold p₀ β : ℕ) + 1 : ℝ) * (2 - β / 2) := by
  unfold clusterThreshold
  rw [ite_eq_left hβ4]
  have hpos : 0 < 2 - β / 2 := by linarith
  have h1 := Nat.lt_floor_add_one (3 / (2 - β / 2))
  rw [div_lt_iff₀ hpos] at h1
  linarith

theorem clusterThreshold_pos (hp₀ : 1 ≤ p₀) (hβ : 2 < β) : 1 ≤ clusterThreshold p₀ β := by
  by_cases hβ4 : β < 4
  · have h := three_lt_clusterThreshold (p₀ := p₀) hβ4
    have hpos : 2 - β / 2 ≤ 1 := by linarith
    by_contra hq
    push Not at hq
    have : clusterThreshold p₀ β = 0 := by omega
    rw [this] at h
    push_cast at h
    linarith
  · rw [clusterThreshold_of_ge (not_lt.1 hβ4)]
    omega

/-! ### One overcrowded cluster -/

theorem dyad_rpow (hlam : 0 < lam) (e : ℝ) (s : ℕ) :
    dyad lam s ^ e = lam ^ e * ((2 : ℝ) ^ e) ^ s := by
  unfold dyad
  rw [Real.mul_rpow hlam.le (by positivity), ← Real.rpow_natCast (2 : ℝ) s,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ e) s,
    ← Real.rpow_mul (by norm_num), mul_comm (s : ℝ) e]

/-- `λ 2^K ≤ h` for `K = ⌊log₂ ⌊h/λ⌋⌋` and `0 < λ ≤ h`. -/
theorem lam_mul_two_pow_log_le {h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) :
    lam * 2 ^ Nat.log 2 ⌊h / lam⌋₊ ≤ h := by
  have h1 : (1 : ℝ) ≤ h / lam := by rw [le_div_iff₀ hlam]; linarith
  have hfl : ⌊h / lam⌋₊ ≠ 0 := by
    have := Nat.floor_pos.2 h1
    omega
  have h2 : ((2 ^ Nat.log 2 ⌊h / lam⌋₊ : ℕ) : ℝ) ≤ h / lam :=
    (Nat.cast_le.2 (Nat.pow_log_le_self 2 hfl)).trans (Nat.floor_le (by linarith))
  push_cast at h2
  rw [le_div_iff₀ hlam] at h2
  linarith

/-- **One overcrowded cluster, summed over its dyadic scale** (proof of Lemma 5.40):
`N (64π)^q ∑_{s ≤ K} (λ 2^s)^{q(2-β/2)-β/2} ≤ C N δ ν^{q+1}`, `ν = λ^{1-β/2}`. -/
theorem crowdSum_le (hβ : 2 < β) : ∃ C : ℝ, 0 < C ∧ ∀ ε₀ lam : ℝ, 0 < ε₀ →
    ε₀ ≤ 1 → 0 < lam → lam ≤ 1 → lam ≤ cutoff p₀ β lam ε₀ → ∀ Nₐ : ℕ,
      ∑ s ∈ Finset.range (Nat.log 2 ⌊cutoff p₀ β lam ε₀ / lam⌋₊ + 1),
          crowdTerm (clusterThreshold p₀ β) β lam Nₐ s ≤
        C * Nₐ * errorRate p₀ β lam * (lam ^ (1 - β / 2)) ^ (clusterThreshold p₀ β + 1) := by
  set q := clusterThreshold p₀ β with hq
  set e := clusterExponent q β with he
  have he' : e = ((q : ℝ) + 1) * (2 - β / 2) - 2 := by rw [he]; unfold clusterExponent; ring
  refine ⟨(64 * Real.pi) ^ q * max ((2 : ℝ) ^ e) 2, by positivity, fun ε₀ lam hε₀ hε₀1 hlam
    hlam1 hlh Nₐ => ?_⟩
  set h := cutoff p₀ β lam ε₀ with hh
  set K := Nat.log 2 ⌊h / lam⌋₊
  set ν := lam ^ (1 - β / 2) with hν
  have hν0 : 0 < ν := Real.rpow_pos_of_pos hlam _
  have hδ0 := errorRate_nonneg (p₀ := p₀) (β := β) hlam
  -- factor out the constants
  have hsum : ∑ s ∈ Finset.range (K + 1), crowdTerm q β lam Nₐ s =
      (Nₐ : ℝ) * (64 * Real.pi) ^ q * (lam ^ e * ∑ s ∈ Finset.range (K + 1), ((2 : ℝ) ^ e) ^ s) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun s _ => ?_
    unfold crowdTerm
    rw [← he, dyad_rpow hlam]
  rw [hsum]
  have hN : (0 : ℝ) ≤ (Nₐ : ℝ) * (64 * Real.pi) ^ q := by positivity
  -- it suffices to bound the geometric part
  suffices hg : lam ^ e * ∑ s ∈ Finset.range (K + 1), ((2 : ℝ) ^ e) ^ s ≤
      max ((2 : ℝ) ^ e) 2 * (errorRate p₀ β lam * ν ^ (q + 1)) by
    calc (Nₐ : ℝ) * (64 * Real.pi) ^ q * (lam ^ e * ∑ s ∈ Finset.range (K + 1), ((2 : ℝ) ^ e) ^ s)
        ≤ (Nₐ : ℝ) * (64 * Real.pi) ^ q * (max ((2 : ℝ) ^ e) 2 * (errorRate p₀ β lam *
            ν ^ (q + 1))) := mul_le_mul_of_nonneg_left hg hN
      _ = _ := by ring
  by_cases hβ4 : β < 4
  · -- `e > 1`: the largest scale dominates
    have he1 : 1 < e := by
      rw [he']
      have := three_lt_clusterThreshold (p₀ := p₀) hβ4
      rw [← hq] at this
      linarith
    set r := (2 : ℝ) ^ e with hr
    have hr2 : 2 ≤ r := by
      rw [hr]
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ e := Real.rpow_le_rpow_of_exponent_le (by norm_num) he1.le
    have hgeom : ∑ s ∈ Finset.range (K + 1), r ^ s ≤ r ^ (K + 1) := by
      rw [geom_sum_eq (by linarith) (K + 1), div_le_iff₀ (by linarith)]
      have : 0 ≤ r ^ (K + 1) := by positivity
      nlinarith
    have hK : lam ^ e * r ^ (K + 1) = r * (lam * 2 ^ K) ^ e := by
      rw [Real.mul_rpow hlam.le (by positivity), ← Real.rpow_natCast (2 : ℝ) K,
        ← Real.rpow_mul (by norm_num), mul_comm (K : ℝ) e, Real.rpow_mul (by norm_num),
        Real.rpow_natCast, pow_succ, hr]
      ring
    have hle_h : (lam * 2 ^ K) ^ e ≤ h ^ e :=
      Real.rpow_le_rpow (by positivity) (lam_mul_two_pow_log_le hlam hlh) (by linarith)
    have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
    have hhR : h ^ e ≤ truncationScale p₀ β lam ^ e := by
      rw [hh]
      unfold cutoff
      rw [Real.mul_rpow hε₀.le hR.le]
      refine mul_le_of_le_one_left (Real.rpow_nonneg hR.le _) ?_
      exact Real.rpow_le_one hε₀.le hε₀1 (by linarith)
    have hRe : truncationScale p₀ β lam ^ e =
        ν ^ (q + 1) * (truncationScale p₀ β lam ^ 2)⁻¹ := by
      rw [he', hν, ← truncationScale_rpow_half (p₀ := p₀) hβ4 hlam, ← Real.rpow_natCast,
        ← Real.rpow_mul hR.le, ← Real.rpow_two, ← Real.rpow_neg hR.le, ← Real.rpow_add hR]
      congr 1
      push_cast
      ring
    have hδ := inv_sq_truncationScale_le_errorRate (p₀ := p₀) (lam := lam) hβ hβ4
    calc lam ^ e * ∑ s ∈ Finset.range (K + 1), r ^ s
        ≤ lam ^ e * r ^ (K + 1) :=
          mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hlam.le _)
      _ = r * (lam * 2 ^ K) ^ e := hK
      _ ≤ r * (ν ^ (q + 1) * errorRate p₀ β lam) := by
          refine mul_le_mul_of_nonneg_left (hle_h.trans (hhR.trans ?_)) (by positivity)
          rw [hRe]
          exact mul_le_mul_of_nonneg_left hδ (by positivity)
      _ ≤ max r 2 * (errorRate p₀ β lam * ν ^ (q + 1)) := by
          rw [mul_comm (ν ^ (q + 1))]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- `e ≤ -2`: the smallest scale dominates
    have hβ4' : 4 ≤ β := not_lt.1 hβ4
    have hq' : q = 2 * p₀ + 1 := clusterThreshold_of_ge hβ4'
    have he2 : e ≤ -2 := by
      rw [he']
      have : ((q : ℝ) + 1) * (2 - β / 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      linarith
    set r := (2 : ℝ) ^ e with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 / 4 := by
      rw [hr]
      calc (2 : ℝ) ^ e ≤ 2 ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he2
        _ = 1 / 4 := by norm_num
    have hgeom : ∑ s ∈ Finset.range (K + 1), r ^ s ≤ 2 := by
      rw [geom_sum_eq (by linarith) (K + 1), div_le_iff_of_neg (by linarith)]
      have : 0 ≤ r ^ (K + 1) := by positivity
      linarith
    have hlame : lam ^ e = ν ^ (q + 1) * errorRate p₀ β lam := by
      rw [errorRate_of_ge hβ4', he', hν, ← Real.rpow_natCast (lam ^ (1 - β / 2)),
        ← Real.rpow_mul hlam.le, ← Real.rpow_natCast lam (2 * p₀), ← Real.rpow_add hlam]
      congr 1
      rw [hq']
      push_cast
      ring
    calc lam ^ e * ∑ s ∈ Finset.range (K + 1), r ^ s ≤ lam ^ e * 2 :=
          mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hlam.le _)
      _ = 2 * (errorRate p₀ β lam * ν ^ (q + 1)) := by rw [hlame]; ring
      _ ≤ max r 2 * (errorRate p₀ β lam * ν ^ (q + 1)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ### One long singleton -/

theorem truncationScale_of_ge_rpow (hβ4 : 4 ≤ β) :
    truncationScale p₀ β lam = lam ^ (-(2 * (p₀ : ℝ))) := by
  rw [Appendix.truncationScale_of_ge hβ4, ← Real.rpow_intCast]
  push_cast
  ring_nf

/-- **One long singleton** (proof of Lemma 5.40): `(h/4)^{-β/2} ≤ C δ ν` for `0 < λ ≤ 1`. -/
theorem singleTerm_le (hβ : 2 < β) (hε₀ : 0 < ε₀) : ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
    lam ≤ 1 → (cutoff p₀ β lam ε₀ / 4) ^ (-(β / 2)) ≤
      C * errorRate p₀ β lam * lam ^ (1 - β / 2) := by
  refine ⟨(ε₀ / 4) ^ (-(β / 2)), by positivity, fun lam hlam hlam1 => ?_⟩
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hsplit : (cutoff p₀ β lam ε₀ / 4) ^ (-(β / 2)) =
      (ε₀ / 4) ^ (-(β / 2)) * truncationScale p₀ β lam ^ (-(β / 2)) := by
    unfold cutoff
    rw [show ε₀ * truncationScale p₀ β lam / 4 = ε₀ / 4 * truncationScale p₀ β lam by ring,
      Real.mul_rpow (by positivity) hR.le]
  rw [hsplit, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  by_cases hβ4 : β < 4
  · have h1 : truncationScale p₀ β lam ^ (-(β / 2)) =
        lam ^ (1 - β / 2) * (truncationScale p₀ β lam ^ 2)⁻¹ := by
      rw [← truncationScale_rpow_half (p₀ := p₀) hβ4 hlam, ← Real.rpow_two,
        ← Real.rpow_neg hR.le, ← Real.rpow_add hR]
      ring_nf
    rw [h1, mul_comm (errorRate p₀ β lam)]
    exact mul_le_mul_of_nonneg_left (inv_sq_truncationScale_le_errorRate hβ hβ4)
      (Real.rpow_nonneg hlam.le _)
  · have hβ4' : 4 ≤ β := not_lt.1 hβ4
    rw [truncationScale_of_ge_rpow hβ4', errorRate_of_ge hβ4', ← Real.rpow_mul hlam.le,
      ← Real.rpow_natCast lam (2 * p₀), ← Real.rpow_add hlam]
    refine Real.rpow_le_rpow_of_exponent_ge hlam hlam1 ?_
    push_cast
    have : (0 : ℝ) ≤ p₀ := Nat.cast_nonneg _
    nlinarith

/-! ### One good charge -/

/-- `max(|u|/4, λ)^{-β/2} ≤ 4^{β/2} max(|u|, λ)^{-β/2}`. -/
theorem goodKernel_le (hβ : 0 ≤ β) (hlam : 0 < lam) (h : ℝ) (u : ℂ) :
    goodKernel β lam h u ≤ ENNReal.ofReal ((4 : ℝ) ^ (β / 2)) *
      (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (-(β / 2)))) u := by
  unfold goodKernel
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) h
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm : 0 < max ‖u‖ lam := lt_max_of_lt_right hlam
    have h1 : max ‖u‖ lam / 4 ≤ max (‖u‖ / 4) lam := by
      rcases le_total ‖u‖ lam with h' | h'
      · rw [max_eq_right h']
        exact (div_le_self hlam.le (by norm_num)).trans (le_max_right _ _)
      · rw [max_eq_left h']
        exact le_max_left _ _
    calc max (‖u‖ / 4) lam ^ (-(β / 2)) ≤ (max ‖u‖ lam / 4) ^ (-(β / 2)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
      _ = (4 : ℝ) ^ (β / 2) * max ‖u‖ lam ^ (-(β / 2)) := by
          rw [div_eq_mul_inv, Real.mul_rpow hm.le (by norm_num), Real.inv_rpow (by norm_num),
            ← Real.rpow_neg (by norm_num), neg_neg]
          ring
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]

/-- **One good charge** (proof of Lemma 5.40): `∫_{|u| ≤ h} max(|u|/4, λ)^{-β/2} du ≤ C ν` for
`0 < λ ≤ min(1, h)`, `h = ε₀ R̄`, `ε₀ ≤ 1`. -/
theorem goodIntegral_le (hβ : 2 < β) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) : ∃ C : ℝ, 0 < C ∧
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → lam ≤ cutoff p₀ β lam ε₀ →
      ∫⁻ u, goodKernel β lam (cutoff p₀ β lam ε₀) u ≤
        ENNReal.ofReal (C * lam ^ (1 - β / 2)) := by
  set C1 := 2 * Real.pi * (1 + 1 / (2 - β / 2))
  set C2 := 2 * Real.pi * (1 + 1 / (-(2 - β / 2)))
  set C3 := 2 * Real.pi * (2 * p₀ + 2)
  refine ⟨(4 : ℝ) ^ (β / 2) * (|C1| + |C2| + C3), by positivity, fun lam hlam hlam1 hlh => ?_⟩
  set h := cutoff p₀ β lam ε₀ with hh
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ (β / 2) := by positivity
  refine (lintegral_mono fun u => goodKernel_le (by linarith) hlam h u).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the radial integral is at most `(|C1| + |C2| + C3) ν`
  suffices hrad : ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (-(β / 2)))) u ≤
        ENNReal.ofReal ((|C1| + |C2| + C3) * lam ^ (1 - β / 2)) by
    calc ENNReal.ofReal ((4 : ℝ) ^ (β / 2)) * ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
          (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (-(β / 2)))) u
        ≤ ENNReal.ofReal ((4 : ℝ) ^ (β / 2)) *
            ENNReal.ofReal ((|C1| + |C2| + C3) * lam ^ (1 - β / 2)) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul h4, mul_assoc]
  have hν : 0 < lam ^ (1 - β / 2) := Real.rpow_pos_of_pos hlam _
  have hC3 : 0 ≤ C3 := by positivity
  rcases lt_trichotomy β 4 with hβ4 | hβ4 | hβ4
  · -- `β < 4`: dominated by `|u| ≈ h`
    have hE : 0 < -(β / 2) + 2 := by linarith
    refine (lintegral_closedBall_max_rpow_le_of_pos hlam hlh hE).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hhν : h ^ (-(β / 2) + 2) ≤ lam ^ (1 - β / 2) := by
      rw [hh]
      unfold cutoff
      rw [Real.mul_rpow hε₀.le hR.le, show -(β / 2) + 2 = 2 - β / 2 by ring,
        truncationScale_rpow_half hβ4 hlam]
      exact mul_le_of_le_one_left hν.le (Real.rpow_le_one hε₀.le hε₀1 (by linarith))
    calc 2 * Real.pi * ((1 + 1 / (-(β / 2) + 2)) * h ^ (-(β / 2) + 2))
        = C1 * h ^ (-(β / 2) + 2) := by
          simp only [C1]
          rw [show -(β / 2) + 2 = 2 - β / 2 by ring]
          ring
      _ ≤ |C1| * lam ^ (1 - β / 2) :=
          mul_le_mul (le_abs_self _) hhν (Real.rpow_nonneg (by linarith) _) (abs_nonneg _)
      _ ≤ (|C1| + |C2| + C3) * lam ^ (1 - β / 2) := by
          gcongr
          linarith [abs_nonneg C2]
  · -- `β = 4`: the logarithm
    subst hβ4
    have hm2 : -((4 : ℝ) / 2) = -2 := by norm_num
    rw [hm2]
    refine (lintegral_closedBall_max_rpow_le_of_eq hlam hlh).trans (ENNReal.ofReal_le_ofReal ?_)
    have hlog : Real.log (h / lam) ≤ (2 * p₀ + 1) * lam⁻¹ := by
      have hhl : h / lam ≤ lam ^ (-(2 * (p₀ : ℝ) + 1)) := by
        rw [hh]
        unfold cutoff
        rw [truncationScale_of_ge_rpow le_rfl, div_le_iff₀ hlam,
          show -(2 * (p₀ : ℝ) + 1) = -(2 * (p₀ : ℝ)) - 1 by ring,
          Real.rpow_sub hlam, Real.rpow_one, div_mul_cancel₀ _ hlam.ne']
        exact mul_le_of_le_one_left (Real.rpow_nonneg hlam.le _) hε₀1
      have hpos : 0 < h / lam := div_pos (hlam.trans_le hlh) hlam
      calc Real.log (h / lam) ≤ Real.log (lam ^ (-(2 * (p₀ : ℝ) + 1))) :=
            Real.log_le_log hpos hhl
        _ = (2 * p₀ + 1) * Real.log lam⁻¹ := by
            rw [Real.log_rpow hlam, Real.log_inv]
            ring
        _ ≤ (2 * p₀ + 1) * lam⁻¹ := by
            gcongr
            have := Real.log_le_sub_one_of_pos (inv_pos.2 hlam)
            linarith
    have hinv : (1 : ℝ) ≤ lam⁻¹ := one_le_inv_iff₀.2 ⟨hlam, hlam1⟩
    have hν4 : lam ^ (1 - (4 : ℝ) / 2) = lam⁻¹ := by
      rw [show 1 - (4 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
    rw [hν4]
    calc 2 * Real.pi * (1 + Real.log (h / lam)) ≤ 2 * Real.pi * (lam⁻¹ + (2 * p₀ + 1) * lam⁻¹) := by
          gcongr
      _ = C3 * lam⁻¹ := by simp only [C3]; ring
      _ ≤ (|C1| + |C2| + C3) * lam⁻¹ := by
          gcongr
          linarith [abs_nonneg C1, abs_nonneg C2]
  · -- `β > 4`: dominated by `|u| ≈ λ`
    have hE : -(β / 2) + 2 < 0 := by linarith
    refine (lintegral_closedBall_max_rpow_le_of_neg hlam hlh hE).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hlν : lam ^ (-(β / 2) + 2) ≤ lam ^ (1 - β / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
    calc 2 * Real.pi * ((1 + 1 / (-(-(β / 2) + 2))) * lam ^ (-(β / 2) + 2))
        = C2 * lam ^ (-(β / 2) + 2) := by
          simp only [C2]
          rw [show -(-(β / 2) + 2) = -(2 - β / 2) by ring]
          ring
      _ ≤ |C2| * lam ^ (1 - β / 2) :=
          mul_le_mul (le_abs_self _) hlν (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
      _ ≤ (|C1| + |C2| + C3) * lam ^ (1 - β / 2) := by
          gcongr
          linarith [abs_nonneg C1]

end BadPointTypes

end MultipoleBKT

end
