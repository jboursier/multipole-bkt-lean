/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoReduce
public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneEstimates
public import MultipoleBKT.Main.TheoremTwo.Parameters

/-!
# Lemma 5.41 for `β ∈ (2, 4)`

The paper: Lemma 5.41 (1),
(5.139), and the series estimate.

For `m > p = p(β) = p*(β)`, `β ≤ β_m` (`le_transitionBeta_of_lt`), so the exponent
`E_m = (4-β)m - 2` of one multipole is nonnegative, and it vanishes only for `m = p + 1` and
`β = β_{p+1}` (`exponent_pos_of_ne`). One multipole of `m` short dipoles contributes
(`lintegral_blockWeight_cut_le_root` and the radial integrals)
`bLow(m) = m^{m+1} N e^{βc_χ} K^{m-1} 2π X_m`, `X_m = (1 + 1/E_m) h^{E_m}` if `E_m > 0` and
`X_m = 1 + log(h/λ)` if `E_m = 0` (`blockBoundLow`, `lintegral_blockWeight_cut_le_low`).
Normalised, `X_m λ^{-(2-β)m} ≤ C ε₀^{E_m} R^{-2} (1 + log(h/λ))`, and the series over `m` is
geometric with ratio `C e^t ε₀^{4-β}` (the paper proof of Lemma 5.41): this is where `ε₀ < ε̃₀(β, M, t)` is used.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset MultipoleIntegral Filter
open scoped ENNReal

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

/-- `p*(β) < ∞` for `β < 4`. -/
theorem pStar_ne_top (hβ4 : β < 4) : pStar β ≠ ⊤ := by
  intro htop
  set q : ℕ := ⌊2 / (4 - β)⌋₊ + 1
  have hq : (q : ℕ∞) ≤ pStar β := by rw [htop]; exact le_top
  have hq1 : 1 ≤ q := by omega
  have hlt := (Appendix.le_pStar_iff hq1).mp hq
  have h4' : 0 < 4 - β := by linarith
  have hfl : 2 / (4 - β) < (q : ℝ) := by
    have := Nat.lt_floor_add_one (2 / (4 - β))
    simpa [q] using this
  unfold transitionBeta at hlt
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have : 2 / (q : ℝ) > 4 - β := by linarith
  rw [gt_iff_lt, lt_div_iff₀ hq0] at this
  rw [div_lt_iff₀ h4'] at hfl
  linarith

/-- For `m > p(β)` (and `β < 4`), `β ≤ β_m`. -/
theorem le_transitionBeta_of_lt (hβ4 : β < 4) {m : ℕ} (hm : pBeta p₀ β < m) :
    β ≤ transitionBeta m := by
  have hm1 : 1 ≤ m := by omega
  unfold pBeta at hm
  rw [ite_eq_left hβ4] at hm
  have hnot : ¬ (m : ℕ∞) ≤ pStar β := by
    intro h
    rw [← ENat.natCast_toNat (pStar_ne_top hβ4)] at h
    exact absurd (Nat.cast_le.1 h) (not_le.2 hm)
  rw [Appendix.le_pStar_iff hm1] at hnot
  exact not_lt.1 hnot

/-- The exponent `E_m = (4-β)m - 2 ≥ 0` for `m > p(β)`. -/
theorem exponent_nonneg (hβ4 : β < 4) {m : ℕ} (hm : pBeta p₀ β < m) :
    0 ≤ (4 - β) * m - 2 := by
  have h := le_transitionBeta_of_lt hβ4 hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold transitionBeta at h
  have : 2 / (m : ℝ) ≤ 4 - β := by linarith
  rw [div_le_iff₀ hm0] at this
  linarith

/-- `E_m > 0` unless `m = p + 1` and `β = β_{p+1}`. In all cases `E_m ≥ E_{p+1}`, and
`E_m ≥ 4 - β` for `m ≥ p + 2`. -/
theorem exponent_pos_of_ne (hβ4 : β < 4) {m : ℕ} (hm : pBeta p₀ β < m)
    (hne : (4 - β) * m - 2 ≠ 0) :
    min (4 - β) (if (4 - β) * (pBeta p₀ β + 1 : ℕ) - 2 = 0 then 4 - β else
      (4 - β) * (pBeta p₀ β + 1 : ℕ) - 2) ≤ (4 - β) * m - 2 := by
  have h0 := exponent_nonneg (p₀ := p₀) hβ4 (m := pBeta p₀ β + 1) (by omega)
  rcases Nat.lt_or_ge (pBeta p₀ β + 1) m with hlt | hge
  · refine (min_le_left _ _).trans ?_
    have : ((pBeta p₀ β + 1 : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast hlt
    nlinarith
  · have hmeq : m = pBeta p₀ β + 1 := by omega
    subst hmeq
    refine (min_le_right _ _).trans (le_of_eq ?_)
    rw [ite_eq_right hne]

/-- The radial factor `X_m` of one multipole of `m` dipoles (`β < 4`):
`(1 + 1/E_m) h^{E_m}` if `E_m = (4-β)m - 2 ≠ 0`, `1 + log(h/λ)` if `E_m = 0`. -/
noncomputable def radialFactor (β lam h : ℝ) (m : ℕ) : ℝ :=
  if (4 - β) * m - 2 = 0 then 1 + Real.log (h / lam)
  else (1 + 1 / ((4 - β) * m - 2)) * h ^ ((4 - β) * m - 2)

/-- **The bound on one multipole of `m` short dipoles for `β < 4`**:
`m^{m+1} N e^{βc_χ} K^{m-1} 2π X_m`. -/
noncomputable def blockBoundLow (χ : ℂ → ℝ) (β lam M h : ℝ) (Nₐ : ℕ) (m : ℕ) : ℝ :=
  ((m ^ m : ℕ) : ℝ) * Nₐ * m * (Real.exp (β * kernelConst χ) * innerConst χ β M ^ (m - 1)) *
    (2 * Real.pi * radialFactor β lam h m)

theorem radialFactor_nonneg (hlam : 0 < lam) {h : ℝ} (hlh : lam ≤ h) {m : ℕ}
    (hm : 0 ≤ (4 - β) * m - 2) : 0 ≤ radialFactor β lam h m := by
  unfold radialFactor
  have hh : 0 < h := hlam.trans_le hlh
  split_ifs with h0
  · have : 0 ≤ Real.log (h / lam) := Real.log_nonneg (by rw [le_div_iff₀ hlam]; linarith)
    linarith
  · have hpos : 0 < (4 - β) * m - 2 := lt_of_le_of_ne hm (Ne.symm h0)
    positivity

theorem blockBoundLow_nonneg (hβ4 : β < 4) (hlam : 0 < lam) {h : ℝ} (hlh : lam ≤ h) (Nₐ : ℕ)
    {m : ℕ} (hm : 0 ≤ (4 - β) * m - 2) : 0 ≤ blockBoundLow χ β lam M h Nₐ m := by
  unfold blockBoundLow
  have := radialFactor_nonneg hlam hlh hm
  have := innerConst_nonneg (χ := χ) (M := M) hβ4
  positivity

/-- **One multipole of `m > p` short dipoles** (`β < 4`, eq. (5.138) and (5.139)). -/
theorem lintegral_blockWeight_cut_le_low (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hβ4 : β < 4)
    (hM : 0 ≤ M) (hlam : 0 < lam) {h : ℝ} (hlh : lam ≤ h) (Nₐ : ℕ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (hm : 0 ≤ (4 - β) * Fintype.card ι - 2) :
    ∫⁻ y : ι → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam h Nₐ) y ≤
      ENNReal.ofReal (blockBoundLow χ β lam M h Nₐ (Fintype.card ι)) := by
  set m := Fintype.card ι
  have hm1 : 1 ≤ m := Fintype.card_pos
  have hK := innerConst_nonneg (χ := χ) (M := M) hβ4
  set E := (4 - β) * ((m - 1 : ℕ) : ℝ) - β with hE
  have hE2 : E + 2 = (4 - β) * m - 2 := by
    rw [hE, Nat.cast_sub hm1]
    push_cast
    ring
  -- the radial integral of the root
  have hrad : ∫⁻ t : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun t => ENNReal.ofReal (max ‖t‖ lam ^ E)) t ≤
        ENNReal.ofReal (2 * Real.pi * radialFactor β lam h m) := by
    unfold radialFactor
    split_ifs with h0
    · have hE' : E = -2 := by linarith
      rw [hE']
      exact lintegral_closedBall_max_rpow_le_of_eq hlam hlh
    · have hpos : 0 < E + 2 := by rw [hE2]; exact lt_of_le_of_ne hm (Ne.symm h0)
      refine (lintegral_closedBall_max_rpow_le_of_pos hlam hlh hpos).trans (le_of_eq ?_)
      rw [hE2]
  refine (lintegral_blockWeight_cut_le_root hχ hβ hβ4 hM hlam h Nₐ).trans ?_
  calc ((m ^ m : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) * (m : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (β * kernelConst χ) * innerConst χ β M ^ (m - 1)) *
          ∫⁻ t : ℂ, (Metric.closedBall (0 : ℂ) h).indicator (fun t => ENNReal.ofReal
            (max ‖t‖ lam ^ ((4 - β) * (m - 1 : ℕ) - β))) t)
      ≤ ((m ^ m : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) * (m : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (β * kernelConst χ) * innerConst χ β M ^ (m - 1)) *
            ENNReal.ofReal (2 * Real.pi * radialFactor β lam h m)) := by
        gcongr
    _ = ENNReal.ofReal (blockBoundLow χ β lam M h Nₐ m) := by
        have hX := radialFactor_nonneg hlam hlh hm
        unfold blockBoundLow
        symm
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        ring

/-- `∑_{j < n} (j+1) x^{j+1} ≤ 2x` for `0 ≤ x ≤ 1/4`. -/
theorem sum_succ_mul_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * x ^ (j + 1) ≤ 2 * x := by
  have hterm : ∀ j : ℕ, ((j : ℝ) + 1) * x ^ (j + 1) ≤ x * (2 * x) ^ j := by
    intro j
    have h2 : (j : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
    calc ((j : ℝ) + 1) * x ^ (j + 1) ≤ 2 ^ j * x ^ (j + 1) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = x * (2 * x) ^ j := by rw [mul_pow, pow_succ]; ring
  have hgeom : ∑ j ∈ Finset.range n, (2 * x) ^ j ≤ 2 := by
    rw [geom_sum_eq (by linarith) n, div_le_iff_of_neg (by linarith)]
    have : 0 ≤ (2 * x) ^ n := by positivity
    linarith
  calc ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * x ^ (j + 1)
      ≤ ∑ j ∈ Finset.range n, x * (2 * x) ^ j := sum_le_sum fun j _ => hterm j
    _ = x * ∑ j ∈ Finset.range n, (2 * x) ^ j := by rw [mul_sum]
    _ ≤ x * 2 := mul_le_mul_of_nonneg_left hgeom hx0
    _ = 2 * x := by ring

/-- The normalised radial factor (`β < 4`, `λ ≤ 1`, `ε₀ ≤ 1`, `λ ≤ h = ε₀ R`):
`X_m λ^{-(2-β)m} ≤ (1 + 1/E_min) ε₀^{-2} (ε₀^{4-β})ᵐ R^{-2} (1 + log(h/λ) 𝟙_{β = β_{p+1}})`. -/
theorem radialFactor_mul_le (hβ4 : β < 4) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hlh : lam ≤ cutoff p₀ β lam ε₀) {m : ℕ} (hm : pBeta p₀ β < m) :
    radialFactor β lam (cutoff p₀ β lam ε₀) m * (lam ^ (2 - β)) ^ (-(m : ℝ)) ≤
      (1 + 1 / min (4 - β) (if (4 - β) * (pBeta p₀ β + 1 : ℕ) - 2 = 0 then 4 - β else
          (4 - β) * (pBeta p₀ β + 1 : ℕ) - 2)) *
        ε₀ ^ (-(2 : ℝ)) * (ε₀ ^ (4 - β)) ^ m * (truncationScale p₀ β lam ^ 2)⁻¹ *
          (1 + if β = transitionBeta (pBeta p₀ β + 1) then
            Real.log (cutoff p₀ β lam ε₀ / lam) else 0) := by
  set R := truncationScale p₀ β lam with hR
  have hR0 : 0 < R := Appendix.truncationScale_pos hlam
  set h := cutoff p₀ β lam ε₀ with hh
  have hhR : h = ε₀ * R := rfl
  have hm0 := exponent_nonneg (p₀ := p₀) hβ4 hm
  set Emin := min (4 - β) (if (4 - β) * (pBeta p₀ β + 1 : ℕ) - 2 = 0 then 4 - β else
    (4 - β) * (pBeta p₀ β + 1 : ℕ) - 2) with hEmin
  have hEmin0 : 0 < Emin := by
    refine lt_min (by linarith) ?_
    split_ifs with h0
    · linarith
    · exact lt_of_le_of_ne (exponent_nonneg (p₀ := p₀) hβ4 (m := pBeta p₀ β + 1) (by omega))
        (Ne.symm h0)
  have hlog0 : 0 ≤ Real.log (h / lam) :=
    Real.log_nonneg (by rw [le_div_iff₀ hlam]; linarith)
  have hlogF : 0 ≤ (if β = transitionBeta (pBeta p₀ β + 1) then Real.log (h / lam) else 0) := by
    split_ifs <;> linarith
  -- `λ^{(2-β)m} = R^{(4-β)m}`
  have hnorm : (lam ^ (2 - β)) ^ (-(m : ℝ)) = R ^ (-((4 - β) * m)) := by
    rw [← Appendix.rpow_truncationScale_of_lt hβ4 hlam, ← hR, ← Real.rpow_mul hR0.le]
    ring_nf
  rw [hnorm]
  have hε₀m : ε₀ ^ (-(2 : ℝ)) * (ε₀ ^ (4 - β)) ^ m = ε₀ ^ ((4 - β) * m - 2) := by
    rw [← Real.rpow_natCast (ε₀ ^ (4 - β)) m, ← Real.rpow_mul hε₀.le, ← Real.rpow_add hε₀]
    ring_nf
  have hR2 : (R ^ 2)⁻¹ = R ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hR0.le, Real.rpow_two]
  unfold radialFactor
  by_cases h0 : (4 - β) * m - 2 = 0
  · -- `E_m = 0` forces `m = p + 1` and `β = β_{p+1}`
    rw [ite_eq_left h0]
    have hm1 : m = pBeta p₀ β + 1 := by
      by_contra hne
      have h2 : pBeta p₀ β + 2 ≤ m := by omega
      have h3 := exponent_nonneg (p₀ := p₀) hβ4 (m := pBeta p₀ β + 1) (by omega)
      have h4 : ((pBeta p₀ β + 1 : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast h2
      nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ 4 - β)]
    have hcrit : β = transitionBeta (pBeta p₀ β + 1) := by
      rw [← hm1]
      unfold transitionBeta
      have hm0' : (0 : ℝ) < (m : ℝ) := by
        have : 0 < m := by omega
        exact_mod_cast this
      field_simp
      linarith
    rw [ite_eq_left hcrit]
    have hRm : R ^ (-((4 - β) * m)) = (R ^ 2)⁻¹ := by
      rw [hR2]; congr 1; linarith
    rw [hRm]
    have hεm : ε₀ ^ (-(2 : ℝ)) * (ε₀ ^ (4 - β)) ^ m = 1 := by
      rw [hε₀m, h0, Real.rpow_zero]
    have h1 : 1 ≤ 1 + 1 / Emin := le_add_of_nonneg_right (by positivity)
    calc (1 + Real.log (h / lam)) * (R ^ 2)⁻¹
        = 1 * ((R ^ 2)⁻¹ * (1 + Real.log (h / lam))) := by ring
      _ ≤ (1 + 1 / Emin) * ((R ^ 2)⁻¹ * (1 + Real.log (h / lam))) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by rw [mul_assoc (1 + 1 / Emin) (ε₀ ^ (-(2 : ℝ))), hεm]; ring
  · -- `E_m > 0`
    rw [ite_eq_right h0]
    have hpos : 0 < (4 - β) * m - 2 := lt_of_le_of_ne hm0 (Ne.symm h0)
    have hE : Emin ≤ (4 - β) * m - 2 := exponent_pos_of_ne hβ4 hm h0
    have hinv : 1 / ((4 - β) * m - 2) ≤ 1 / Emin := one_div_le_one_div_of_le hEmin0 hE
    have hhE : h ^ ((4 - β) * m - 2) * R ^ (-((4 - β) * m)) =
        ε₀ ^ ((4 - β) * m - 2) * R ^ (-(2 : ℝ)) := by
      rw [hhR, Real.mul_rpow hε₀.le hR0.le, mul_assoc, ← Real.rpow_add hR0]
      ring_nf
    have h0' : 0 ≤ (1 + 1 / Emin) * ε₀ ^ ((4 - β) * m - 2) * R ^ (-(2 : ℝ)) := by
      positivity
    calc (1 + 1 / ((4 - β) * m - 2)) * h ^ ((4 - β) * m - 2) * R ^ (-((4 - β) * m))
        = (1 + 1 / ((4 - β) * m - 2)) * (ε₀ ^ ((4 - β) * m - 2) * R ^ (-(2 : ℝ))) := by
          rw [mul_assoc, hhE]
      _ ≤ (1 + 1 / Emin) * (ε₀ ^ ((4 - β) * m - 2) * R ^ (-(2 : ℝ))) := by
          gcongr
      _ = (1 + 1 / Emin) * ε₀ ^ ((4 - β) * m - 2) * R ^ (-(2 : ℝ)) * 1 := by ring
      _ ≤ (1 + 1 / Emin) * ε₀ ^ ((4 - β) * m - 2) * R ^ (-(2 : ℝ)) *
            (1 + if β = transitionBeta (pBeta p₀ β + 1) then Real.log (h / lam) else 0) :=
          mul_le_mul_of_nonneg_left (by linarith) h0'
      _ = _ := by
          rw [hR2, mul_assoc (1 + 1 / Emin) (ε₀ ^ (-(2 : ℝ))), hε₀m]

/-- The smallest positive exponent `E_min` of a multipole of more than `p` dipoles. -/
noncomputable def exponentMin (p₀ : ℕ) (β : ℝ) : ℝ :=
  min (4 - β) (if (4 - β) * (pBeta p₀ β + 1 : ℕ) - 2 = 0 then 4 - β else
    (4 - β) * (pBeta p₀ β + 1 : ℕ) - 2)

theorem exponentMin_pos (hβ4 : β < 4) : 0 < exponentMin p₀ β := by
  unfold exponentMin
  refine lt_min (by linarith) ?_
  split_ifs with h0
  · linarith
  · exact lt_of_le_of_ne (exponent_nonneg (p₀ := p₀) hβ4 (m := pBeta p₀ β + 1) (by omega))
      (Ne.symm h0)

/-- **One term of the series** (`β < 4`): with `y₀ = e^t/(c₀ λ^{2-β})` and
`x = e Kp e^t ε₀^{4-β}/c₀`, `bLow(m) y₀ᵐ / m! ≤ A m xᵐ`,
`A = N e^{βc_χ} 2π (1 + 1/E_min) ε₀^{-2} R^{-2} (1 + log(h/λ) 𝟙_{β = β_{p+1}})`. -/
theorem blockTerm_le_low (hβ4 : β < 4) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hlh : lam ≤ cutoff p₀ β lam ε₀) {c₀ t : ℝ} (hc₀ : 0 < c₀) (Nₐ : ℕ) {m : ℕ}
    (hm : pBeta p₀ β < m) :
    blockBoundLow χ β lam M (cutoff p₀ β lam ε₀) Nₐ m / m.factorial *
        (Real.exp t / (c₀ * lam ^ (2 - β))) ^ m ≤
      (Nₐ * Real.exp (β * kernelConst χ) * (2 * Real.pi) * (1 + 1 / exponentMin p₀ β) *
          ε₀ ^ (-(2 : ℝ)) * (truncationScale p₀ β lam ^ 2)⁻¹ *
          (1 + if β = transitionBeta (pBeta p₀ β + 1) then
            Real.log (cutoff p₀ β lam ε₀ / lam) else 0)) *
        (m * (Real.exp 1 * max 1 (innerConst χ β M) * Real.exp t * ε₀ ^ (4 - β) / c₀) ^ m) := by
  set K := innerConst χ β M
  set Kp := max 1 K
  have hK : 0 ≤ K := innerConst_nonneg hβ4
  have hm1 : 1 ≤ m := by omega
  have hm0 := exponent_nonneg (p₀ := p₀) hβ4 hm
  set X := radialFactor β lam (cutoff p₀ β lam ε₀) m
  have hX := radialFactor_nonneg hlam hlh hm0
  have hXb := radialFactor_mul_le (p₀ := p₀) hβ4 hlam hε₀ hlh hm
  set L := 1 + if β = transitionBeta (pBeta p₀ β + 1) then
    Real.log (cutoff p₀ β lam ε₀ / lam) else 0
  have hlb : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hfac : ((m ^ m : ℕ) : ℝ) / m.factorial ≤ Real.exp 1 ^ m := by
    have := Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m
    rw [← Real.exp_nat_mul, mul_one]
    exact_mod_cast this
  have hKm : K ^ (m - 1) ≤ Kp ^ m :=
    (pow_le_pow_left₀ hK (le_max_right 1 K) _).trans
      (pow_le_pow_right₀ (le_max_left 1 K) (Nat.sub_le m 1))
  have hy : (Real.exp t / (c₀ * lam ^ (2 - β))) ^ m =
      (Real.exp t / c₀) ^ m * (lam ^ (2 - β)) ^ (-(m : ℝ)) := by
    rw [div_mul_eq_div_div, div_pow, Real.rpow_neg hlb.le, Real.rpow_natCast, div_eq_mul_inv]
  unfold blockBoundLow
  rw [hy]
  have hexp : 0 ≤ Real.exp (β * kernelConst χ) := (Real.exp_pos _).le
  calc ((m ^ m : ℕ) : ℝ) * Nₐ * m * (Real.exp (β * kernelConst χ) * K ^ (m - 1)) *
        (2 * Real.pi * X) / m.factorial * ((Real.exp t / c₀) ^ m * (lam ^ (2 - β)) ^ (-(m : ℝ)))
      = (((m ^ m : ℕ) : ℝ) / m.factorial) * (Nₐ * m * Real.exp (β * kernelConst χ) *
          (2 * Real.pi) * K ^ (m - 1) * (Real.exp t / c₀) ^ m) *
          (X * (lam ^ (2 - β)) ^ (-(m : ℝ))) := by ring
    _ ≤ Real.exp 1 ^ m * (Nₐ * m * Real.exp (β * kernelConst χ) * (2 * Real.pi) * Kp ^ m *
          (Real.exp t / c₀) ^ m) *
          ((1 + 1 / exponentMin p₀ β) * ε₀ ^ (-(2 : ℝ)) * (ε₀ ^ (4 - β)) ^ m *
            (truncationScale p₀ β lam ^ 2)⁻¹ * L) := by
        have hXb' : X * (lam ^ (2 - β)) ^ (-(m : ℝ)) ≤ (1 + 1 / exponentMin p₀ β) *
            ε₀ ^ (-(2 : ℝ)) * (ε₀ ^ (4 - β)) ^ m * (truncationScale p₀ β lam ^ 2)⁻¹ * L := hXb
        have ha : 0 ≤ (Nₐ : ℝ) * m * Real.exp (β * kernelConst χ) * (2 * Real.pi) := by positivity
        have hb : 0 ≤ (Real.exp t / c₀) ^ m := by positivity
        have h2 : (Nₐ : ℝ) * m * Real.exp (β * kernelConst χ) * (2 * Real.pi) * K ^ (m - 1) *
            (Real.exp t / c₀) ^ m ≤ (Nₐ : ℝ) * m * Real.exp (β * kernelConst χ) * (2 * Real.pi) *
              Kp ^ m * (Real.exp t / c₀) ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKm ha) hb
        refine mul_le_mul (mul_le_mul hfac h2 (by positivity) (by positivity)) hXb'
          (by positivity) (by positivity)
    _ = _ := by
        rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow]
        field_simp

end BadPointTypes

end MultipoleBKT

end
