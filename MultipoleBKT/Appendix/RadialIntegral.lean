/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import MultipoleBKT.Frozen.CriticalScale
public import MultipoleBKT.Frozen.PStar
public import MultipoleBKT.Frozen.TransitionBeta
public import MultipoleBKT.Frozen.TruncationScale

/-!
# Lemma A.2: the radial integrals of the multipole partition function

We prove Lemma A.2: for
`k ∈ ℕ*`, `β > 2` and `ε₀ ∈ (0, 1)`,

* (A.2) `λ^{(2-β)k} γ_{β,λ,k} ≍ ∫₀^∞ max(r, λ)^{(4-β)k-3} 1_{r ≤ ε₀ R̄_{β,λ}} dr`
  (`MultipoleBKT.Appendix.lemsupplapp_two_sided`, with the explicit constant `radialConst`;
  `lemsupplapp_two_sided_exists` is the form "there exist `C`, `λ₀`");
* (A.3) if moreover `k ≤ p*(β)`,
  `∫₀^∞ max(r, λ)^{(4-β)k-3} 1_{r ≥ ε₀ R̄_{β,λ}} dr ≲ λ^{(2-β)k} R̄_{β,λ}^{-2}`
  (`MultipoleBKT.Appendix.lemsupplapp_tail`, with the explicit constant `tailConst`;
  `lemsupplapp_tail_exists`).

The paper's `≍` means two inequalities with constants depending on `β`, `k`, `ε₀`; here they are
`C⁻¹ · (λ^{(2-β)k} γ) ≤ ∫ ≤ C · (λ^{(2-β)k} γ)` for a constant `C > 0` and every
`0 < λ ≤ λ₀`, where `λ₀ ∈ (0, 1)` also depends on `β, k, ε₀` only (see below). The integrals are
Bochner integrals over `(0, ∞)`; the statements include integrability, so that the upper bounds
are not vacuous.

## Internal definitions

* `R̄_{β,λ}` (Definition 2.18) is the frozen
  `MultipoleBKT.truncationScale p₀ β λ`: `R_{β,λ}` if `β < 4` and `λ^{-2p₀}` if `β ≥ 4`.
* `MultipoleBKT.Appendix.gammaBeta p₀ β λ k` is `γ_{β,λ,k}` (Definition 4.22) in terms of the frozen `pStar` and `transitionBeta`. The three cases of the paper
  are, in the order `k ≤ p*(β)`; `k = p*(β) + 1` and `β = β_{p*(β)+1}`; and the remaining case
  (`k > p*(β)` and either `β ∈ (β_{p*}, β_{p*+1})` or `β = β_{p*+1}`, `k > p*+1`), which is the
  `else` branch (`gammaBeta_of_case_two`). The values in the three regimes of the exponent
  `E = (4-β)k - 2` (`E < 0`, `E > 0`, `E = 0`) are `gammaBeta_of_neg`, `gammaBeta_of_pos` and
  `gammaBeta_of_eq_zero`; for `k ≥ 1` they are exhaustive.

## The regimes and the smallness of `λ`

Put `E = (4-β)k - 2`, so that the integrand is `max(r, λ)^{E-1}`. Then `k ≤ p*(β)` iff `E < 0`
(`le_pStar_iff`, `transitionBeta_lt_iff`) and `E ≥ 0` forces `β < 4`.

* `E < 0` (this includes all `k` when `β ≥ 4`): the integral is `λ^E + (h^E - λ^E)/E` with
  `h = ε₀ R̄`, between `λ^E` and `(1 + 1/|E|) λ^E`, and `λ^E = λ^{(2-β)k} λ^{2(k-1)}`.
* `E > 0`: the integral is comparable to `h^E = ε₀^E λ^{(2-β)k} R^{-2}` (because
  `R^{4-β} = λ^{2-β}`).
* `E = 0` (`β = β_k`, `k = p*(β) + 1`): the integral is `1 + log ε₀ + k |log λ|`, comparable to
  `|log λ| = λ^{(2-β)k} R^{-2} |log λ|`.

The smallness condition on `λ` in (A.2) ensures `λ ≤ ε₀ R̄_{β,λ}` and, in the
logarithmic regime, `|log λ|` large compared to `log (1/ε₀)`; the upper bound in the logarithmic
regime fails as `λ → 1` because `|log λ| → 0`. We take `λ ≤ λ₀ = min (1/2) (min ε₀ (ε₀^{2/k}))`
(`lamBound`), so `C` (`radialConst`, `tailConst`) and `λ₀` depend only on `β, k, ε₀`; they do not
depend on `p₀`, since `R̄ ≥ 1` (`one_le_truncationScale`) is all that is used about `R̄` besides
`R̄^{4-β} ≤ λ^{2-β}` (`rpow_truncationScale_le`, with equality for `β < 4`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MultipoleBKT

namespace Appendix

/-- The exponent `γ_{β,λ,k}`, Definition 4.22, for
`k ∈ ℕ*`: `λ^{2(k-1)}` if `k ≤ p*(β)`; `R̄_{β,λ}^{-2} |log λ|` if `k = p*(β) + 1` and
`β = β_{p*(β)+1}`; and `R̄_{β,λ}^{-2}` otherwise (that is, if `k > p*(β)` and either
`β ∈ (β_{p*(β)}, β_{p*(β)+1})` or `β = β_{p*(β)+1}` and `k > p*(β) + 1`; see
`gammaBeta_of_case_two`). The convention `β_∞ = 4` plays no role since for `p*(β) = ∞` only the
first case occurs. Total in `β`, `λ`, `k`; used for `β > 2`, `k ≥ 1`. -/
noncomputable def gammaBeta (p₀ : ℕ) (β lam : ℝ) (k : ℕ) : ℝ :=
  if (k : ℕ∞) ≤ pStar β then lam ^ (2 * ((k : ℤ) - 1))
  else if (k : ℕ∞) = pStar β + 1 ∧ β = transitionBeta ((pStar β).toNat + 1) then
    truncationScale p₀ β lam ^ (-2 : ℤ) * |Real.log lam|
  else truncationScale p₀ β lam ^ (-2 : ℤ)

theorem transitionBeta_mono {q q' : ℕ} (hq : 1 ≤ q) (h : q ≤ q') :
    transitionBeta q ≤ transitionBeta q' := by
  unfold transitionBeta
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have : (q : ℝ) ≤ q' := by exact_mod_cast h
  have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hq0 this
  linarith

theorem transitionBeta_lt_iff {k : ℕ} (hk : 1 ≤ k) (β : ℝ) :
    transitionBeta k < β ↔ (4 - β) * k - 2 < 0 := by
  unfold transitionBeta
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have : 4 - 2 / (k : ℝ) < β ↔ 4 - β < 2 / (k : ℝ) := by constructor <;> intro h <;> linarith
  rw [this, lt_div_iff₀ hk0]
  constructor <;> intro h <;> linarith

theorem le_pStar_iff {β : ℝ} {k : ℕ} (hk : 1 ≤ k) : (k : ℕ∞) ≤ pStar β ↔ transitionBeta k < β := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have : pStar β ≤ ((k - 1 : ℕ) : ℕ∞) := by
      unfold pStar
      refine iSup₂_le fun q hq => ?_
      have hqk : q ≤ k - 1 := by
        by_contra hcon
        have : k ≤ q := by omega
        have := transitionBeta_mono hk this
        linarith [hq.2]
      exact_mod_cast hqk
    have h2 := h.trans this
    have : k ≤ k - 1 := by exact_mod_cast h2
    omega
  · intro h
    unfold pStar
    exact le_iSup₂_of_le k ⟨hk, h⟩ le_rfl

theorem eq_transitionBeta_iff {k : ℕ} (hk : 1 ≤ k) (β : ℝ) :
    β = transitionBeta k ↔ (4 - β) * k - 2 = 0 := by
  unfold transitionBeta
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    field_simp
    linarith

theorem gammaBeta_of_neg {p₀ : ℕ} {β lam : ℝ} {k : ℕ} (hk : 1 ≤ k) (h : (4 - β) * k - 2 < 0) :
    gammaBeta p₀ β lam k = lam ^ (2 * ((k : ℤ) - 1)) := by
  unfold gammaBeta
  rw [ite_eq_left ((le_pStar_iff hk).mpr ((transitionBeta_lt_iff hk β).mpr h))]

theorem gammaBeta_of_pos {p₀ : ℕ} {β lam : ℝ} {k : ℕ} (hk : 1 ≤ k) (h : 0 < (4 - β) * k - 2) :
    gammaBeta p₀ β lam k = truncationScale p₀ β lam ^ (-2 : ℤ) := by
  have h1 : ¬ (k : ℕ∞) ≤ pStar β := by
    rw [le_pStar_iff hk, transitionBeta_lt_iff hk]
    linarith
  have h2 : ¬ ((k : ℕ∞) = pStar β + 1 ∧ β = transitionBeta ((pStar β).toNat + 1)) := by
    rintro ⟨h3, h4⟩
    have hne : pStar β ≠ ⊤ := by
      intro htop
      rw [htop] at h3
      simp at h3
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hj] at h3 h4
    have hjk : k = j + 1 := by exact_mod_cast h3
    simp only [ENat.toNat_natCast] at h4
    rw [← hjk, eq_transitionBeta_iff hk] at h4
    linarith
  unfold gammaBeta
  rw [ite_eq_right h1, ite_eq_right h2]

theorem gammaBeta_of_eq_zero {p₀ : ℕ} {β lam : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (h : (4 - β) * k - 2 = 0) :
    gammaBeta p₀ β lam k = truncationScale p₀ β lam ^ (-2 : ℤ) * |Real.log lam| := by
  have h1 : ¬ (k : ℕ∞) ≤ pStar β := by
    rw [le_pStar_iff hk, transitionBeta_lt_iff hk]
    linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < 4 - β := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hge : ((k - 1 : ℕ) : ℕ∞) ≤ pStar β := by
    by_cases hk1 : k - 1 = 0
    · rw [hk1]
      simp
    · rw [le_pStar_iff (by omega), transitionBeta_lt_iff (by omega)]
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk]
        simp
      rw [this]
      nlinarith
  have hlt : pStar β < k := not_le.mp h1
  have hle : pStar β ≤ ((k - 1 : ℕ) : ℕ∞) := by
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    rw [← hj] at hlt ⊢
    have : j < k := by exact_mod_cast hlt
    exact_mod_cast (by omega : j ≤ k - 1)
  have hps : pStar β = ((k - 1 : ℕ) : ℕ∞) := le_antisymm hle hge
  have h2 : (k : ℕ∞) = pStar β + 1 ∧ β = transitionBeta ((pStar β).toNat + 1) := by
    rw [hps, ENat.toNat_natCast]
    refine ⟨?_, ?_⟩
    · exact_mod_cast (by omega : k = k - 1 + 1)
    · rw [Nat.sub_add_cancel hk]
      exact (eq_transitionBeta_iff hk β).mpr h
  unfold gammaBeta
  rw [ite_eq_right h1, ite_eq_left h2]

/-- The third case of Definition 4.22 on the `else` branch:
for `k > p*(β)` and either `β ∈ (β_{p*(β)}, β_{p*(β)+1})` or `β = β_{p*(β)+1}` and
`k > p*(β) + 1`, `γ_{β,λ,k} = R̄_{β,λ}^{-2}`. -/
theorem gammaBeta_of_case_two {p₀ : ℕ} {β lam : ℝ} {k : ℕ} (h1 : pStar β < k)
    (h2 : (transitionBeta (pStar β).toNat < β ∧ β < transitionBeta ((pStar β).toNat + 1)) ∨
      (β = transitionBeta ((pStar β).toNat + 1) ∧ (pStar β).toNat + 1 < k)) :
    gammaBeta p₀ β lam k = truncationScale p₀ β lam ^ (-2 : ℤ) := by
  have hne : pStar β ≠ ⊤ := ne_top_of_lt h1
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hne
  have h3 : ¬ (k : ℕ∞) ≤ pStar β := not_le.mpr h1
  have h4 : ¬ ((k : ℕ∞) = pStar β + 1 ∧ β = transitionBeta ((pStar β).toNat + 1)) := by
    rintro ⟨h5, h6⟩
    rw [← hj] at h5 h6 h2
    simp only [ENat.toNat_natCast] at h2 h6
    have hjk : k = j + 1 := by exact_mod_cast h5
    rcases h2 with ⟨-, h7⟩ | ⟨-, h7⟩
    · linarith
    · omega
  unfold gammaBeta
  rw [ite_eq_right h3, ite_eq_right h4]

theorem truncationScale_of_lt {p₀ : ℕ} {β lam : ℝ} (hβ : β < 4) (hlam : 0 < lam) :
    truncationScale p₀ β lam = lam ^ (-(β - 2) / (4 - β)) := by
  unfold truncationScale criticalScale
  rw [ite_eq_left hβ, ite_eq_left hβ, ENNReal.toReal_ofReal (Real.rpow_nonneg hlam.le _)]

theorem truncationScale_of_ge {p₀ : ℕ} {β lam : ℝ} (hβ : 4 ≤ β) :
    truncationScale p₀ β lam = lam ^ (-(2 * (p₀ : ℤ))) := by
  unfold truncationScale
  rw [ite_eq_right (not_lt.mpr hβ)]

theorem truncationScale_pos {p₀ : ℕ} {β lam : ℝ} (hlam : 0 < lam) :
    0 < truncationScale p₀ β lam := by
  by_cases hβ : β < 4
  · rw [truncationScale_of_lt hβ hlam]
    exact Real.rpow_pos_of_pos hlam _
  · rw [truncationScale_of_ge (not_lt.mp hβ)]
    exact zpow_pos hlam _

theorem one_le_truncationScale {p₀ : ℕ} {β lam : ℝ} (hβ : 2 < β) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) : 1 ≤ truncationScale p₀ β lam := by
  by_cases hβ4 : β < 4
  · rw [truncationScale_of_lt hβ4 hlam]
    refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 ?_
    have : 0 < 4 - β := by linarith
    have : 0 ≤ (β - 2) / (4 - β) := div_nonneg (by linarith) this.le
    rw [neg_div]
    linarith
  · rw [truncationScale_of_ge (not_lt.mp hβ4)]
    exact one_le_zpow_of_nonpos₀ hlam hlam1 (by omega)

theorem rpow_truncationScale_of_lt {p₀ : ℕ} {β lam : ℝ} (hβ : β < 4) (hlam : 0 < lam) :
    truncationScale p₀ β lam ^ (4 - β) = lam ^ (2 - β) := by
  rw [truncationScale_of_lt hβ hlam, ← Real.rpow_mul hlam.le]
  congr 1
  have : (4 - β) ≠ 0 := by linarith
  field_simp
  ring

theorem rpow_truncationScale_le {p₀ : ℕ} {β lam : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) : truncationScale p₀ β lam ^ (4 - β) ≤ lam ^ (2 - β) := by
  by_cases hβ4 : β < 4
  · exact (rpow_truncationScale_of_lt hβ4 hlam).le
  · rw [truncationScale_of_ge (not_lt.mp hβ4), ← Real.rpow_intCast, ← Real.rpow_mul hlam.le]
    refine Real.rpow_le_rpow_of_exponent_ge hlam hlam1 ?_
    have hp : (0 : ℝ) ≤ (p₀ : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [not_lt.mp hβ4]

theorem log_truncationScale_of_lt {p₀ : ℕ} {β lam : ℝ} (hβ : β < 4) (hlam : 0 < lam) :
    Real.log (truncationScale p₀ β lam) = -(β - 2) / (4 - β) * Real.log lam := by
  rw [truncationScale_of_lt hβ hlam, Real.log_rpow hlam]


section Core

variable {lam h : ℝ}

theorem continuous_max_rpow (hlam : 0 < lam) (e : ℝ) : Continuous fun r : ℝ => max r lam ^ e :=
  (continuous_id.max continuous_const).rpow_const fun _ =>
    Or.inl (lt_max_of_lt_right hlam).ne'

theorem integral_indicator_Iic (h e lam : ℝ) :
    ∫ r in Ioi (0 : ℝ), (Iic h).indicator (fun r => max r lam ^ e) r =
      ∫ r in Ioc 0 h, max r lam ^ e := by
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]

theorem integral_Ioc_max_rpow (hlam : 0 < lam) (hlh : lam ≤ h) (e : ℝ) :
    ∫ r in Ioc 0 h, max r lam ^ e = lam ^ (e + 1) + ∫ r in lam..h, r ^ e := by
  rw [← intervalIntegral.integral_of_le (hlam.trans_le hlh).le]
  have hI : ∀ a b : ℝ, IntervalIntegrable (fun r => max r lam ^ e) volume a b :=
    fun a b => (continuous_max_rpow hlam e).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 lam) (hI lam h)]
  congr 1
  · have : ∫ r in (0 : ℝ)..lam, max r lam ^ e = ∫ r in (0 : ℝ)..lam, lam ^ e := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hlam.le] at hr
      rw [max_eq_right hr.2]
    rw [this, intervalIntegral.integral_const, smul_eq_mul, sub_zero, Real.rpow_add_one hlam.ne',
      mul_comm]
  · refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hlh] at hr
    rw [max_eq_left hr.1]

theorem integral_rpow_of_ne (hlam : 0 < lam) (hlh : lam ≤ h) {e : ℝ} (he : e ≠ -1) :
    ∫ r in lam..h, r ^ e = (h ^ (e + 1) - lam ^ (e + 1)) / (e + 1) := by
  refine integral_rpow (Or.inr ⟨he, ?_⟩)
  rw [uIcc_of_le hlh]
  exact fun hmem => absurd hmem.1 (not_le.mpr hlam)

theorem integral_rpow_neg_one (hlam : 0 < lam) (hlh : lam ≤ h) :
    ∫ r in lam..h, r ^ (-1 : ℝ) = Real.log (h / lam) := by
  simp_rw [Real.rpow_neg_one]
  exact integral_inv_of_pos hlam (hlam.trans_le hlh)

end Core


section Regimes

variable {lam h E : ℝ}

/-- The integral `∫₀^∞ max(r, λ)^(E-1) 1_{r ≤ h} dr`, for `λ ≤ h` and `E ≠ 0`. -/
theorem radial_value_of_ne (hlam : 0 < lam) (hlh : lam ≤ h) (hE : E ≠ 0) :
    ∫ r in Ioi (0 : ℝ), (Iic h).indicator (fun r => max r lam ^ (E - 1)) r =
      lam ^ E + (h ^ E - lam ^ E) / E := by
  have hne : E - 1 ≠ -1 := by intro h'; apply hE; linarith
  rw [integral_indicator_Iic, integral_Ioc_max_rpow hlam hlh, integral_rpow_of_ne hlam hlh hne]
  simp

/-- The integral `∫₀^∞ max(r, λ)^(-1) 1_{r ≤ h} dr = 1 + log (h / λ)`, for `λ ≤ h`. -/
theorem radial_value_zero (hlam : 0 < lam) (hlh : lam ≤ h) :
    ∫ r in Ioi (0 : ℝ), (Iic h).indicator (fun r => max r lam ^ ((0 : ℝ) - 1)) r =
      1 + Real.log (h / lam) := by
  rw [integral_indicator_Iic, integral_Ioc_max_rpow hlam hlh]
  have : ((0 : ℝ) - 1) = -1 := by norm_num
  rw [this, integral_rpow_neg_one hlam hlh]
  simp

theorem radial_bounds_neg (hlam : 0 < lam) (hlh : lam ≤ h) (hE : E < 0) :
    lam ^ E ≤ ∫ r in Ioi (0 : ℝ), (Iic h).indicator (fun r => max r lam ^ (E - 1)) r ∧
    ∫ r in Ioi (0 : ℝ), (Iic h).indicator (fun r => max r lam ^ (E - 1)) r ≤
      (1 + 1 / (-E)) * lam ^ E := by
  rw [radial_value_of_ne hlam hlh hE.ne]
  have hh : 0 < h := hlam.trans_le hlh
  have h1 : h ^ E ≤ lam ^ E := Real.rpow_le_rpow_of_nonpos hlam hlh hE.le
  have h2 : 0 < h ^ E := Real.rpow_pos_of_pos hh E
  have h3 : (h ^ E - lam ^ E) / E = (lam ^ E - h ^ E) / (-E) := by
    rw [div_neg, ← neg_div, neg_sub]
  have hnE : 0 < -E := by linarith
  rw [h3]
  constructor
  · have : 0 ≤ (lam ^ E - h ^ E) / (-E) := div_nonneg (by linarith) hnE.le
    linarith
  · have : (lam ^ E - h ^ E) / (-E) ≤ lam ^ E / (-E) :=
      div_le_div_of_nonneg_right (by linarith) hnE.le
    have h4 : lam ^ E / (-E) = 1 / (-E) * lam ^ E := by ring
    linarith

theorem radial_bounds_pos (hlam : 0 < lam) (hlh : lam ≤ h) (hE : 0 < E) :
    min 1 (1 / E) * h ^ E ≤ ∫ r in Ioi (0 : ℝ), (Iic h).indicator (fun r => max r lam ^ (E - 1)) r ∧
    ∫ r in Ioi (0 : ℝ), (Iic h).indicator (fun r => max r lam ^ (E - 1)) r ≤
      (1 + 1 / E) * h ^ E := by
  rw [radial_value_of_ne hlam hlh hE.ne']
  have hh : 0 < h := hlam.trans_le hlh
  have h1 : lam ^ E ≤ h ^ E := Real.rpow_le_rpow hlam.le hlh hE.le
  have h2 : 0 < lam ^ E := Real.rpow_pos_of_pos hlam E
  set u := lam ^ E with hu
  set w := h ^ E with hw
  set c := 1 / E with hc
  have hcpos : 0 < c := by positivity
  have hform : u + (w - u) / E = u * (1 - c) + w * c := by
    rw [hc]; field_simp; ring
  rw [hform]
  constructor
  · by_cases hc1 : c ≤ 1
    · have : min 1 c = c := min_eq_right hc1
      rw [this]
      nlinarith
    · push Not at hc1
      have : min 1 c = 1 := min_eq_left hc1.le
      rw [this]
      nlinarith
  · nlinarith

end Regimes


section Targets

variable {p₀ : ℕ} {β : ℝ} {k : ℕ} {ε₀ lam : ℝ}

/-- `R̄^{(4-β)k} ≤ λ^{(2-β)k}` for `λ ≤ 1`, with equality for `β < 4`. -/
theorem rpow_truncationScale_mul_le (hlam : 0 < lam) (hlam1 : lam ≤ 1) (β : ℝ) (k : ℕ) :
    truncationScale p₀ β lam ^ ((4 - β) * k) ≤ lam ^ ((2 - β) * k) := by
  have hR := truncationScale_pos (p₀ := p₀) (β := β) hlam
  rw [Real.rpow_mul hR.le, Real.rpow_mul hlam.le]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hR.le _) (rpow_truncationScale_le hlam hlam1)
    (Nat.cast_nonneg k)

theorem rpow_truncationScale_mul_of_lt (hlam : 0 < lam) (hβ : β < 4) (k : ℕ) :
    truncationScale p₀ β lam ^ ((4 - β) * k) = lam ^ ((2 - β) * k) := by
  have hR := truncationScale_pos (p₀ := p₀) (β := β) hlam
  rw [Real.rpow_mul hR.le, Real.rpow_mul hlam.le, rpow_truncationScale_of_lt hβ hlam]

theorem target_neg (hlam : 0 < lam) (hk : 1 ≤ k) (hE : (4 - β) * k - 2 < 0) :
    lam ^ ((2 - β) * k) * gammaBeta p₀ β lam k = lam ^ ((4 - β) * (k : ℝ) - 2) := by
  rw [gammaBeta_of_neg hk hE, ← Real.rpow_intCast, ← Real.rpow_add hlam]
  congr 1
  push_cast
  ring

theorem target_pos (hlam : 0 < lam) (hk : 1 ≤ k)
    (hE : 0 < (4 - β) * k - 2) (hβ : β < 4) (hε₀ : 0 < ε₀) :
    (ε₀ * truncationScale p₀ β lam) ^ ((4 - β) * (k : ℝ) - 2) =
      ε₀ ^ ((4 - β) * (k : ℝ) - 2) * (lam ^ ((2 - β) * k) * gammaBeta p₀ β lam k) := by
  have hR := truncationScale_pos (p₀ := p₀) (β := β) hlam
  rw [gammaBeta_of_pos hk hE, Real.mul_rpow hε₀.le hR.le, sub_eq_add_neg,
    Real.rpow_add hR, rpow_truncationScale_mul_of_lt hlam hβ k]
  have : truncationScale p₀ β lam ^ (-(2 : ℝ)) = truncationScale p₀ β lam ^ (-2 : ℤ) := by
    rw [← Real.rpow_intCast]
    norm_num
  rw [this]

theorem target_zero (hlam : 0 < lam) (hlam1 : lam < 1) (hk : 1 ≤ k)
    (hE : (4 - β) * k - 2 = 0) (hε₀ : 0 < ε₀) :
    lam ^ ((2 - β) * k) * gammaBeta p₀ β lam k = -Real.log lam ∧
    1 + Real.log (ε₀ * truncationScale p₀ β lam / lam) =
      1 + Real.log ε₀ + k * (-Real.log lam) := by
  have hR := truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < 4 - β := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hβ : β < 4 := by linarith
  have hlog : Real.log lam < 0 := Real.log_neg hlam hlam1
  constructor
  · rw [gammaBeta_of_eq_zero hk hE]
    have h1 : truncationScale p₀ β lam ^ ((4 - β) * (k : ℝ)) = truncationScale p₀ β lam ^ 2 := by
      have : (4 - β) * (k : ℝ) = (2 : ℕ) := by push_cast; linarith
      rw [this, Real.rpow_natCast]
    rw [rpow_truncationScale_mul_of_lt hlam hβ k] at h1
    rw [h1, abs_of_neg hlog]
    have : truncationScale p₀ β lam ^ 2 * truncationScale p₀ β lam ^ (-2 : ℤ) = 1 := by
      rw [zpow_neg, zpow_ofNat]
      exact mul_inv_cancel₀ (by positivity)
    calc truncationScale p₀ β lam ^ 2 * (truncationScale p₀ β lam ^ (-2 : ℤ) * -Real.log lam)
        = (truncationScale p₀ β lam ^ 2 * truncationScale p₀ β lam ^ (-2 : ℤ)) * -Real.log lam := by
          ring
      _ = -Real.log lam := by rw [this, one_mul]
  · rw [Real.log_div (by positivity) hlam.ne', Real.log_mul hε₀.ne' hR.ne',
      log_truncationScale_of_lt hβ hlam]
    have : -(β - 2) / (4 - β) = -((k : ℝ) - 1) := by
      field_simp
      nlinarith
    rw [this]
    ring

end Targets


section Main

variable {p₀ : ℕ} {β : ℝ} {k : ℕ} {ε₀ lam : ℝ}

/-- The integrand `max(r, λ)^{(4-β)k-3}` of Lemma A.2. -/
noncomputable def radialIntegrand (β lam : ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  max r lam ^ ((4 - β) * (k : ℝ) - 3)

/-- `∫₀^∞ max(r, λ)^{(4-β)k-3} 1_{r ≤ ε₀ R̄_{β,λ}} dr`, the middle term of (A.2). -/
noncomputable def radialIntegral (p₀ : ℕ) (β lam : ℝ) (k : ℕ) (ε₀ : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), (Iic (ε₀ * truncationScale p₀ β lam)).indicator (radialIntegrand β lam k) r

/-- `∫₀^∞ max(r, λ)^{(4-β)k-3} 1_{r ≥ ε₀ R̄_{β,λ}} dr`, the left-hand side of (A.3). -/
noncomputable def radialTail (p₀ : ℕ) (β lam : ℝ) (k : ℕ) (ε₀ : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), (Ici (ε₀ * truncationScale p₀ β lam)).indicator (radialIntegrand β lam k) r

theorem radialIntegrand_eq (β lam : ℝ) (k : ℕ) :
    radialIntegrand β lam k = fun r => max r lam ^ (((4 - β) * (k : ℝ) - 2) - 1) := by
  funext r
  unfold radialIntegrand
  congr 1
  ring

theorem radialIntegral_eq (p₀ : ℕ) (β lam : ℝ) (k : ℕ) (ε₀ : ℝ) :
    radialIntegral p₀ β lam k ε₀ = ∫ r in Ioi (0 : ℝ),
      (Iic (ε₀ * truncationScale p₀ β lam)).indicator
        (fun r => max r lam ^ (((4 - β) * (k : ℝ) - 2) - 1)) r := by
  unfold radialIntegral
  rw [radialIntegrand_eq]

/-- The admissible range of `λ` in the two-sided bound (A.2). -/
noncomputable def lamBound (ε₀ : ℝ) (k : ℕ) : ℝ := min (1 / 2) (min ε₀ (ε₀ ^ (2 / (k : ℝ))))

theorem lamBound_pos (hε₀ : 0 < ε₀) (k : ℕ) : 0 < lamBound ε₀ k := by
  unfold lamBound
  exact lt_min (by norm_num) (lt_min hε₀ (Real.rpow_pos_of_pos hε₀ _))

theorem lamBound_lt_one (ε₀ : ℝ) (k : ℕ) : lamBound ε₀ k < 1 :=
  lt_of_le_of_lt (min_le_left _ _) (by norm_num)

theorem le_of_le_lamBound {ε₀ lam : ℝ} {k : ℕ} (h : lam ≤ lamBound ε₀ k) :
    lam ≤ 1 / 2 ∧ lam ≤ ε₀ ∧ lam ≤ ε₀ ^ (2 / (k : ℝ)) :=
  ⟨h.trans (min_le_left _ _), h.trans ((min_le_right _ _).trans (min_le_left _ _)),
    h.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem integrable_radialIndicator (hlam : 0 < lam) (h : ℝ) (e : ℝ) :
    Integrable ((Iic h).indicator (fun r => max r lam ^ e)) (volume.restrict (Ioi 0)) := by
  rw [integrable_indicator_iff measurableSet_Iic, IntegrableOn, Measure.restrict_restrict
    measurableSet_Iic, inter_comm, Ioi_inter_Iic]
  exact (continuous_max_rpow hlam e).integrableOn_Ioc

/-- The explicit constant `C` of (A.2), in the three regimes of `E = (4-β)k - 2`:
`1 + 1/|E|` if `E < 0` (that is `k ≤ p*(β)`); `max (1/log 2 + k) (2/k)` if `E = 0`; and
`max ((1 + 1/E) ε₀^E) ((min 1 (1/E) · ε₀^E)⁻¹)` if `E > 0`. -/
noncomputable def radialConst (β : ℝ) (k : ℕ) (ε₀ : ℝ) : ℝ :=
  if (4 - β) * (k : ℝ) - 2 < 0 then 1 + 1 / (-((4 - β) * (k : ℝ) - 2))
  else if (4 - β) * (k : ℝ) - 2 = 0 then max (1 / Real.log 2 + k) (2 / k)
  else max ((1 + 1 / ((4 - β) * (k : ℝ) - 2)) * ε₀ ^ ((4 - β) * (k : ℝ) - 2))
    (min 1 (1 / ((4 - β) * (k : ℝ) - 2)) * ε₀ ^ ((4 - β) * (k : ℝ) - 2))⁻¹

/-- The explicit constant `C = ε₀^E / |E|` of (A.3), `E = (4-β)k - 2 < 0`. -/
noncomputable def tailConst (β : ℝ) (k : ℕ) (ε₀ : ℝ) : ℝ :=
  ε₀ ^ ((4 - β) * (k : ℝ) - 2) / (-((4 - β) * (k : ℝ) - 2))

theorem radialConst_pos {β : ℝ} {k : ℕ} (hk : 1 ≤ k) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    0 < radialConst β k ε₀ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold radialConst
  split_ifs with h1 h2
  · have : 0 < -((4 - β) * (k : ℝ) - 2) := by linarith
    positivity
  · exact lt_max_of_lt_left (by positivity)
  · have h3 : 0 < (4 - β) * (k : ℝ) - 2 := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    exact lt_max_of_lt_left (by positivity)

theorem tailConst_pos {β : ℝ} {k : ℕ} {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hE : (4 - β) * (k : ℝ) - 2 < 0) :
    0 < tailConst β k ε₀ := by
  have : 0 < -((4 - β) * (k : ℝ) - 2) := by linarith
  unfold tailConst
  positivity


theorem radial_two_sided_neg (p₀ : ℕ) {β : ℝ} (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hE : (4 - β) * k - 2 < 0) :
    ∀ lam : ℝ, 0 < lam → lam ≤ lamBound ε₀ k →
      Integrable ((Iic (ε₀ * truncationScale p₀ β lam)).indicator (radialIntegrand β lam k))
        (volume.restrict (Ioi 0)) ∧
      (radialConst β k ε₀)⁻¹ * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) ≤
        radialIntegral p₀ β lam k ε₀ ∧
      radialIntegral p₀ β lam k ε₀ ≤
        radialConst β k ε₀ * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) := by
  have hnE : 0 < -((4 - β) * (k : ℝ) - 2) := by linarith
  have hCdef : radialConst β k ε₀ = 1 + 1 / (-((4 - β) * (k : ℝ) - 2)) := by
    unfold radialConst
    rw [ite_eq_left hE]
  intro lam hlam hle
  rw [hCdef]
  obtain ⟨h12, hε, -⟩ := le_of_le_lamBound hle
  have hR1 := one_le_truncationScale (p₀ := p₀) hβ hlam (by linarith)
  have hlh : lam ≤ ε₀ * truncationScale p₀ β lam :=
    hε.trans (le_mul_of_one_le_right hε₀.le hR1)
  rw [target_neg hlam hk hE]
  refine ⟨?_, ?_⟩
  · rw [radialIntegrand_eq]
    exact integrable_radialIndicator hlam _ _
  · rw [radialIntegral_eq]
    obtain ⟨h1, h2⟩ := radial_bounds_neg hlam hlh hE
    have hpos : 0 < lam ^ ((4 - β) * (k : ℝ) - 2) := Real.rpow_pos_of_pos hlam _
    have hC : 1 ≤ 1 + 1 / (-((4 - β) * (k : ℝ) - 2)) := by
      have : 0 ≤ 1 / (-((4 - β) * (k : ℝ) - 2)) := by positivity
      linarith
    refine ⟨?_, h2⟩
    calc (1 + 1 / (-((4 - β) * (k : ℝ) - 2)))⁻¹ * lam ^ ((4 - β) * (k : ℝ) - 2)
        ≤ 1 * lam ^ ((4 - β) * (k : ℝ) - 2) :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hC) hpos.le
      _ ≤ _ := by rw [one_mul]; exact h1

theorem radial_two_sided_pos (p₀ : ℕ) {β : ℝ} (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hE : 0 < (4 - β) * k - 2) :
    ∀ lam : ℝ, 0 < lam → lam ≤ lamBound ε₀ k →
      Integrable ((Iic (ε₀ * truncationScale p₀ β lam)).indicator (radialIntegrand β lam k))
        (volume.restrict (Ioi 0)) ∧
      (radialConst β k ε₀)⁻¹ * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) ≤
        radialIntegral p₀ β lam k ε₀ ∧
      radialIntegral p₀ β lam k ε₀ ≤
        radialConst β k ε₀ * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hβ4 : β < 4 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  set E := (4 - β) * (k : ℝ) - 2 with hEdef
  have hc₁ : 0 < min 1 (1 / E) * ε₀ ^ E := by
    have : 0 < min 1 (1 / E) := lt_min one_pos (by positivity)
    positivity
  have hc₂ : 0 < (1 + 1 / E) * ε₀ ^ E := by positivity
  have hCdef : radialConst β k ε₀ =
      max ((1 + 1 / E) * ε₀ ^ E) (min 1 (1 / E) * ε₀ ^ E)⁻¹ := by
    unfold radialConst
    rw [ite_eq_right (not_lt.mpr hE.le), ite_eq_right hE.ne']
  intro lam hlam hle
  rw [hCdef]
  obtain ⟨h12, hε, -⟩ := le_of_le_lamBound hle
  have hR1 := one_le_truncationScale (p₀ := p₀) hβ hlam (by linarith)
  have hlh : lam ≤ ε₀ * truncationScale p₀ β lam :=
    hε.trans (le_mul_of_one_le_right hε₀.le hR1)
  have hT : lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k =
      lam ^ ((2 - β) * (k : ℝ)) * truncationScale p₀ β lam ^ (-2 : ℤ) := by
    rw [gammaBeta_of_pos hk hE]
  have hTpos : 0 < lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k := by
    rw [hT]
    have := truncationScale_pos (p₀ := p₀) (β := β) hlam
    positivity
  have hh := target_pos (p₀ := p₀) hlam hk hE hβ4 hε₀
  refine ⟨?_, ?_⟩
  · rw [radialIntegrand_eq]
    exact integrable_radialIndicator hlam _ _
  · rw [radialIntegral_eq]
    obtain ⟨h1, h2⟩ := radial_bounds_pos hlam hlh hE
    rw [hh] at h1 h2
    set T := lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k with hTdef
    constructor
    · have hinv : (max ((1 + 1 / E) * ε₀ ^ E) (min 1 (1 / E) * ε₀ ^ E)⁻¹)⁻¹ ≤
          min 1 (1 / E) * ε₀ ^ E :=
        inv_le_of_inv_le₀ hc₁ (le_max_right _ _)
      calc (max ((1 + 1 / E) * ε₀ ^ E) (min 1 (1 / E) * ε₀ ^ E)⁻¹)⁻¹ * T
          ≤ (min 1 (1 / E) * ε₀ ^ E) * T := mul_le_mul_of_nonneg_right hinv hTpos.le
        _ = min 1 (1 / E) * (ε₀ ^ E * T) := by ring
        _ ≤ _ := h1
    · calc _ ≤ (1 + 1 / E) * (ε₀ ^ E * T) := h2
        _ = ((1 + 1 / E) * ε₀ ^ E) * T := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hTpos.le

theorem radial_two_sided_zero (p₀ : ℕ) {β : ℝ} (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hE : (4 - β) * k - 2 = 0) :
    ∀ lam : ℝ, 0 < lam → lam ≤ lamBound ε₀ k →
      Integrable ((Iic (ε₀ * truncationScale p₀ β lam)).indicator (radialIntegrand β lam k))
        (volume.restrict (Ioi 0)) ∧
      (radialConst β k ε₀)⁻¹ * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) ≤
        radialIntegral p₀ β lam k ε₀ ∧
      radialIntegral p₀ β lam k ε₀ ≤
        radialConst β k ε₀ * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCdef : radialConst β k ε₀ = max (1 / Real.log 2 + k) (2 / k) := by
    unfold radialConst
    rw [ite_eq_right (not_lt.mpr hE.ge), ite_eq_left hE]
  intro lam hlam hle
  rw [hCdef]
  obtain ⟨h12, hε, hεk⟩ := le_of_le_lamBound hle
  have hlam1 : lam < 1 := by linarith
  have hR1 := one_le_truncationScale (p₀ := p₀) hβ hlam (by linarith)
  have hlh : lam ≤ ε₀ * truncationScale p₀ β lam :=
    hε.trans (le_mul_of_one_le_right hε₀.le hR1)
  obtain ⟨hT, hI⟩ := target_zero (p₀ := p₀) hlam hlam1 hk hE hε₀
  rw [hT]
  have hL : 0 < -Real.log lam := neg_pos.mpr (Real.log_neg hlam hlam1)
  have hL2 : Real.log 2 ≤ -Real.log lam := by
    have : Real.log lam ≤ Real.log (1 / 2) := Real.log_le_log hlam h12
    rw [one_div, Real.log_inv] at this
    linarith
  have hLε : -Real.log ε₀ ≤ k / 2 * (-Real.log lam) := by
    have h1 : Real.log lam ≤ Real.log (ε₀ ^ (2 / (k : ℝ))) := Real.log_le_log hlam hεk
    rw [Real.log_rpow hε₀] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2)
    have h3 : (k : ℝ) / 2 * (2 / (k : ℝ) * Real.log ε₀) = Real.log ε₀ := by field_simp
    rw [h3] at h2
    linarith
  have hlogε : Real.log ε₀ < 0 := Real.log_neg hε₀ hε₀1
  refine ⟨?_, ?_⟩
  · rw [radialIntegrand_eq]
    exact integrable_radialIndicator hlam _ _
  · have hval : radialIntegral p₀ β lam k ε₀ = 1 + Real.log (ε₀ * truncationScale p₀ β lam / lam) := by
      rw [radialIntegral_eq, hE]
      exact radial_value_zero hlam hlh
    rw [hval, hI]
    constructor
    · have hC : 2 / (k : ℝ) ≤ max (1 / Real.log 2 + k) (2 / k) := le_max_right _ _
      have hinv : (max (1 / Real.log 2 + k) (2 / (k : ℝ)))⁻¹ ≤ k / 2 := by
        have : (k : ℝ) / 2 = (2 / (k : ℝ))⁻¹ := by rw [inv_div]
        rw [this]
        exact inv_anti₀ (by positivity) hC
      calc (max (1 / Real.log 2 + k) (2 / (k : ℝ)))⁻¹ * -Real.log lam
          ≤ k / 2 * -Real.log lam := mul_le_mul_of_nonneg_right hinv hL.le
        _ ≤ _ := by nlinarith
    · have h1 : 1 ≤ (1 / Real.log 2) * -Real.log lam := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hlog2]
        linarith
      calc 1 + Real.log ε₀ + k * -Real.log lam ≤ 1 + k * -Real.log lam := by linarith
        _ ≤ (1 / Real.log 2) * -Real.log lam + k * -Real.log lam := by linarith
        _ = (1 / Real.log 2 + k) * -Real.log lam := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hL.le

/-- **Lemma A.2, eq. (A.2)**, with explicit constants.
Let `k ≥ 1`, `β > 2` and `ε₀ ∈ (0, 1)`. For every `0 < λ ≤ λ₀ = lamBound ε₀ k`
(`= min (1/2) (min ε₀ (ε₀^{2/k}))`), the integrand is integrable and, with the constant
`C = radialConst β k ε₀ > 0` (`radialConst_pos`; it depends only on `β`, `k`, `ε₀`),
`C⁻¹ λ^{(2-β)k} γ_{β,λ,k} ≤ ∫₀^∞ max(r, λ)^{(4-β)k-3} 1_{r ≤ ε₀ R̄_{β,λ}} dr ≤ C λ^{(2-β)k} γ_{β,λ,k}`.

The lower bound needs
`λ ≤ ε₀ R̄_{β,λ}` and, in the logarithmic regime, large `|log λ|`, so `λ₀` is part of the statement. -/
theorem lemsupplapp_two_sided (p₀ : ℕ) {β : ℝ} (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    ∀ lam : ℝ, 0 < lam → lam ≤ lamBound ε₀ k →
      Integrable ((Iic (ε₀ * truncationScale p₀ β lam)).indicator (radialIntegrand β lam k))
        (volume.restrict (Ioi 0)) ∧
      (radialConst β k ε₀)⁻¹ * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) ≤
        radialIntegral p₀ β lam k ε₀ ∧
      radialIntegral p₀ β lam k ε₀ ≤
        radialConst β k ε₀ * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) := by
  rcases lt_trichotomy ((4 - β) * (k : ℝ) - 2) 0 with hE | hE | hE
  · exact radial_two_sided_neg p₀ hβ hk hε₀ hE
  · exact radial_two_sided_zero p₀ hβ hk hε₀ hε₀1 hE
  · exact radial_two_sided_pos p₀ hβ hk hε₀ hE

/-- **Lemma A.2, eq. (A.2)**, existential form (as in the paper): there are `C > 0` and
`λ₀ ∈ (0, 1)`, depending only on `β`, `k`, `ε₀`, with the conclusion of `lemsupplapp_two_sided`
for all `0 < λ ≤ λ₀`. -/
theorem lemsupplapp_two_sided_exists (p₀ : ℕ) {β : ℝ} (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ < 1 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
      Integrable ((Iic (ε₀ * truncationScale p₀ β lam)).indicator (radialIntegrand β lam k))
        (volume.restrict (Ioi 0)) ∧
      C⁻¹ * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) ≤ radialIntegral p₀ β lam k ε₀ ∧
      radialIntegral p₀ β lam k ε₀ ≤ C * (lam ^ ((2 - β) * (k : ℝ)) * gammaBeta p₀ β lam k) :=
  ⟨radialConst β k ε₀, radialConst_pos hk hε₀, lamBound ε₀ k, lamBound_pos hε₀ k,
    lamBound_lt_one ε₀ k, lemsupplapp_two_sided p₀ hβ hk hε₀ hε₀1⟩

/-- **Lemma A.2, eq. (A.3)**, with explicit constants: for
`k ≤ p*(β)` (that is, `(4-β)k < 2`) and `0 < λ ≤ λ₀ = lamBound ε₀ k`, the integrand of the tail
is integrable and
`∫₀^∞ max(r, λ)^{(4-β)k-3} 1_{r ≥ ε₀ R̄_{β,λ}} dr ≤ C λ^{(2-β)k} R̄_{β,λ}^{-2}` with
`C = tailConst β k ε₀ = ε₀^E / |E|`, `E = (4-β)k - 2 < 0` (`tailConst_pos`). -/
theorem lemsupplapp_tail (p₀ : ℕ) {β : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkp : (k : ℕ∞) ≤ pStar β)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∀ lam : ℝ, 0 < lam → lam ≤ lamBound ε₀ k →
      Integrable ((Ici (ε₀ * truncationScale p₀ β lam)).indicator (radialIntegrand β lam k))
        (volume.restrict (Ioi 0)) ∧
      radialTail p₀ β lam k ε₀ ≤
        tailConst β k ε₀ * (lam ^ ((2 - β) * (k : ℝ)) * truncationScale p₀ β lam ^ (-2 : ℤ)) := by
  have hE : (4 - β) * (k : ℝ) - 2 < 0 :=
    (transitionBeta_lt_iff hk β).mp ((le_pStar_iff hk).mp hkp)
  have hβ : 2 < β := by
    have h1 := (le_pStar_iff hk).mp hkp
    have h2 : transitionBeta 1 ≤ transitionBeta k := transitionBeta_mono le_rfl hk
    have h3 : transitionBeta 1 = 2 := by norm_num [transitionBeta]
    linarith
  have hnE : 0 < -((4 - β) * (k : ℝ) - 2) := by linarith
  intro lam hlam hle
  obtain ⟨h12, hε, -⟩ := le_of_le_lamBound hle
  have hR := truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hR1 := one_le_truncationScale (p₀ := p₀) hβ hlam (by linarith)
  have hlh : lam ≤ ε₀ * truncationScale p₀ β lam :=
    hε.trans (le_mul_of_one_le_right hε₀.le hR1)
  have hhpos : 0 < ε₀ * truncationScale p₀ β lam := hlam.trans_le hlh
  set h := ε₀ * truncationScale p₀ β lam with hh
  set E := (4 - β) * (k : ℝ) - 2 with hEdef
  have hfun : ∀ r ∈ Ici h, radialIntegrand β lam k r = r ^ (E - 1) := by
    intro r hr
    rw [radialIntegrand_eq]
    exact congrArg (· ^ (E - 1)) (max_eq_left (hlh.trans hr))
  have hint : IntegrableOn (fun r : ℝ => r ^ (E - 1)) (Ici h) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hhpos
  refine ⟨?_, ?_⟩
  · rw [integrable_indicator_iff measurableSet_Ici, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (Ici_subset_Ioi.mpr hhpos)]
    exact hint.congr_fun (fun r hr => (hfun r hr).symm) measurableSet_Ici
  · have hval : radialTail p₀ β lam k ε₀ = h ^ E / (-E) := by
      unfold radialTail
      rw [setIntegral_indicator measurableSet_Ici,
        inter_eq_right.mpr (Ici_subset_Ioi.mpr hhpos),
        setIntegral_congr_fun measurableSet_Ici hfun,
        ← setIntegral_congr_set (Ioi_ae_eq_Ici (a := h)),
        integral_Ioi_rpow_of_lt (by linarith) hhpos, sub_add_cancel, neg_div, div_neg]
    rw [hval]
    have hRE : truncationScale p₀ β lam ^ E ≤
        lam ^ ((2 - β) * (k : ℝ)) * truncationScale p₀ β lam ^ (-2 : ℤ) := by
      have h1 : truncationScale p₀ β lam ^ E =
          truncationScale p₀ β lam ^ ((4 - β) * (k : ℝ)) * truncationScale p₀ β lam ^ (-2 : ℤ) := by
        rw [hEdef, sub_eq_add_neg, Real.rpow_add hR]
        congr 1
        rw [← Real.rpow_intCast]
        norm_num
      rw [h1]
      exact mul_le_mul_of_nonneg_right (rpow_truncationScale_mul_le hlam (by linarith) β k)
        (zpow_pos hR _).le
    unfold tailConst
    rw [← hEdef, hh, Real.mul_rpow hε₀.le hR.le, div_eq_mul_inv, div_eq_mul_inv]
    calc ε₀ ^ E * truncationScale p₀ β lam ^ E * (-E)⁻¹
        = ε₀ ^ E * (-E)⁻¹ * truncationScale p₀ β lam ^ E := by ring
      _ ≤ ε₀ ^ E * (-E)⁻¹ * (lam ^ ((2 - β) * (k : ℝ)) * truncationScale p₀ β lam ^ (-2 : ℤ)) :=
          mul_le_mul_of_nonneg_left hRE (by positivity)

/-- **Lemma A.2, eq. (A.3)**, existential form: for `k ≤ p*(β)` there are `C > 0` and
`λ₀ ∈ (0, 1)`, depending only on `β`, `k`, `ε₀`, with the conclusion of `lemsupplapp_tail`. -/
theorem lemsupplapp_tail_exists (p₀ : ℕ) {β : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ < 1 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
      Integrable ((Ici (ε₀ * truncationScale p₀ β lam)).indicator (radialIntegrand β lam k))
        (volume.restrict (Ioi 0)) ∧
      radialTail p₀ β lam k ε₀ ≤
        C * (lam ^ ((2 - β) * (k : ℝ)) * truncationScale p₀ β lam ^ (-2 : ℤ)) :=
  ⟨tailConst β k ε₀,
    tailConst_pos hε₀ ((transitionBeta_lt_iff hk β).mp ((le_pStar_iff hk).mp hkp)),
    lamBound ε₀ k, lamBound_pos hε₀ k, lamBound_lt_one ε₀ k, lemsupplapp_tail p₀ hk hkp hε₀⟩

end Main

end Appendix

end MultipoleBKT

end
