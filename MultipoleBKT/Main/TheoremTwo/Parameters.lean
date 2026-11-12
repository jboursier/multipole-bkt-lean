/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Measure.WithDensity
public import MultipoleBKT.Appendix.RadialIntegral
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.ErrorRate
public import MultipoleBKT.Frozen.AlphaExponent
public import TwoComponentCoulomb.Integrals.Stirling

/-!
# Theorem 2 from the gates: the parameters

Elementary facts about the parameters of Theorem 2:

* `p(β) ≥ 1` and `p(β) ≤ p*(β)` for `β > 2` (Definition 2.8);
* `δ_{β,λ} > 0` and `δ_{β,λ} ≤ λ^{2(p-1)}` for `λ` small (Definition 2.9; the
 paper's "`δ_{β,λ} = o(λ^{2(p-1)})`");
* `α(β) > 0` and the choice of `ε₀` with `ε₀^{-α(β)}` large;
* Stirling in the form `N log N - N + 1 ≤ log N! ≤ N log N - N + 1 + log N`;
* `log N = o(N)`, which absorbs the polynomial number of profiles and the Stirling error into
  `N δ` for `N ≥ N₀(λ)`;
* elementary manipulations of `ofReal (exp _)` in `ℝ≥0∞`.
-/

@[expose] public section

open Filter Topology Set
open scoped ENNReal Nat

namespace MultipoleBKT

namespace TheoremTwo

/-! ### `p(β)` -/

theorem one_le_pBeta' {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ} (hβ : 2 < β) : 1 ≤ pBeta p₀ β := by
  unfold pBeta
  split_ifs with h4
  · have h1 : ((1 : ℕ) : ℕ∞) ≤ pStar β :=
      (Appendix.le_pStar_iff le_rfl).mpr (by unfold transitionBeta; norm_num; linarith)
    have hfin : pStar β ≠ ⊤ := by
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
    have : (1 : ℕ∞) ≤ ((pStar β).toNat : ℕ∞) := by
      rw [ENat.natCast_toNat hfin]; exact_mod_cast h1
    exact_mod_cast this
  · exact hp₀

theorem pBeta_le_pStar {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ} (hβ : 2 < β) :
    (pBeta p₀ β : ℕ∞) ≤ pStar β := by
  have h1 := one_le_pBeta' hp₀ hβ
  unfold pBeta at h1 ⊢
  split_ifs with h4
  · exact ENat.natCast_toNat_le_self _
  · rw [ite_eq_right h4] at h1
    refine (Appendix.le_pStar_iff h1).mpr ?_
    unfold transitionBeta
    have : (0 : ℝ) < 2 / (p₀ : ℝ) := by
      have : (0 : ℝ) < p₀ := by exact_mod_cast h1
      positivity
    linarith [not_lt.mp h4]

theorem transitionBeta_pBeta_lt {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ} (hβ : 2 < β) :
    transitionBeta (pBeta p₀ β) < β :=
  (Appendix.le_pStar_iff (one_le_pBeta' hp₀ hβ)).mp (pBeta_le_pStar hp₀ hβ)

theorem natCast_le_pStar_of_le_pBeta {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ} (hβ : 2 < β) {k : ℕ}
    (hk : k ≤ pBeta p₀ β) : (k : ℕ∞) ≤ pStar β :=
  (Nat.cast_le.mpr hk).trans (pBeta_le_pStar hp₀ hβ)

/-! ### `α(β)` and the choice of `ε₀` -/

theorem alphaExponent_pos (β : ℝ) : 0 < alphaExponent β := by
  unfold alphaExponent
  split_ifs with h
  · linarith
  · norm_num

/-- `ε₀^{-α}` is as large as desired for `ε₀` small. -/
theorem exists_rpow_neg_ge {α ε₁ : ℝ} (hα : 0 < α) (hε₁ : 0 < ε₁) (A : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < ε₁ ∧ A ≤ ε₀ ^ (-α) := by
  set B : ℝ := max A 1
  have hB : 0 < B := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε₀ : ℝ := min (ε₁ / 2) (B ^ (-α⁻¹))
  have hpos : 0 < B ^ (-α⁻¹) := Real.rpow_pos_of_pos hB _
  have hε₀ : 0 < ε₀ := lt_min (by linarith) hpos
  refine ⟨ε₀, hε₀, lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  have h1 : (B ^ (-α⁻¹)) ^ (-α) ≤ ε₀ ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hε₀ (min_le_right _ _) (by linarith)
  have h2 : (B ^ (-α⁻¹)) ^ (-α) = B := by
    rw [← Real.rpow_mul hB.le]
    have : -α⁻¹ * -α = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [h2] at h1
  exact (le_max_left _ _).trans h1

/-! ### The error rate `δ_{β,λ}` -/

theorem tsum_transition_nonneg (β lam : ℝ) :
    0 ≤ ∑' q : ℕ, (if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0) :=
  tsum_nonneg fun q => by split_ifs <;> positivity

theorem tsum_transition_le (β lam : ℝ) :
    (∑' q : ℕ, (if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0)) ≤
      |Real.log lam| := by
  by_cases h : ∃ q₀ : ℕ, 2 ≤ q₀ ∧ β = transitionBeta q₀
  · obtain ⟨q₀, hq₀, hβq₀⟩ := h
    rw [tsum_eq_single q₀]
    · rw [ite_eq_left ⟨hq₀, hβq₀⟩]
    · intro q hq
      rw [ite_eq_right]
      rintro ⟨hq2, hβq⟩
      apply hq
      have h1 : transitionBeta q = transitionBeta q₀ := hβq.symm.trans hβq₀
      unfold transitionBeta at h1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hq00 : (0 : ℝ) < q₀ := by exact_mod_cast (show 0 < q₀ by omega)
      have : (2 : ℝ) / q = 2 / q₀ := by linarith
      field_simp at this
      exact_mod_cast (by linarith : (q : ℝ) = q₀)
  · push Not at h
    have h0 : (fun q : ℕ => if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0) =
        fun _ => 0 := by
      funext q
      rw [ite_eq_right]
      rintro ⟨hq2, hβq⟩
      exact h q hq2 hβq
    rw [h0, tsum_zero]
    positivity

/-- The value of `δ_{β,λ}` for `β ∈ (2,4)`. -/
theorem errorRate_of_lt_four' {p₀ : ℕ} {β lam : ℝ} (hβ : 2 < β) (h4 : β < 4) (hlam : 0 < lam) :
    errorRate p₀ β lam = lam ^ (2 * (β - 2) / (4 - β)) *
      (1 + ∑' q : ℕ, (if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0)) := by
  unfold errorRate criticalScale
  rw [ite_eq_left ⟨hβ, h4⟩, ite_eq_left h4, ite_eq_right (not_le.mpr h4), add_zero,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hlam.le _)]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_mul hlam.le]
  congr 1
  push_cast
  ring

theorem errorRate_of_four_le {p₀ : ℕ} {β lam : ℝ} (h4 : 4 ≤ β) :
    errorRate p₀ β lam = lam ^ (2 * p₀) := by
  unfold errorRate
  rw [ite_eq_right (fun h => absurd h.2 (not_lt.mpr h4)), ite_eq_left h4, zero_add]

theorem errorRate_pos {p₀ : ℕ} {β lam : ℝ} (hβ : 2 < β) (hlam : 0 < lam) :
    0 < errorRate p₀ β lam := by
  by_cases h4 : β < 4
  · rw [errorRate_of_lt_four' hβ h4 hlam]
    have := tsum_transition_nonneg β lam
    have : 0 < lam ^ (2 * (β - 2) / (4 - β)) := Real.rpow_pos_of_pos hlam _
    positivity
  · rw [errorRate_of_four_le (not_lt.mp h4)]
    positivity

/-- `x^θ (1 + |log x|) ≤ 1` for `x > 0` small (`θ > 0`). -/
theorem exists_rpow_mul_log_le {θ : ℝ} (hθ : 0 < θ) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 1 ∧ ∀ x : ℝ, 0 < x → x < x₀ → x ^ θ * (1 + |Real.log x|) ≤ 1 := by
  have h1 : Tendsto (fun x : ℝ => x ^ θ) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ θ) 0 := Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)
    have := hc.tendsto
    rw [Real.zero_rpow hθ.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := tendsto_log_mul_rpow_nhdsGT_zero hθ
  have h3 : Tendsto (fun x : ℝ => x ^ θ - Real.log x * x ^ θ) (𝓝[>] 0) (𝓝 0) := by
    simpa using h1.sub h2
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ^ θ - Real.log x * x ^ θ < 1 :=
    h3.eventually (gt_mem_nhds one_pos)
  have hev' : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds one_pos)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (hev.and hev'))
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun x hx hxε => ?_⟩
  have hdist : dist x 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hx]
    exact lt_of_lt_of_le hxε (min_le_left _ _)
  obtain ⟨hlt, hx1⟩ := hball hdist hx
  have hlog : |Real.log x| = -Real.log x := abs_of_neg (Real.log_neg hx hx1)
  rw [hlog]
  nlinarith

/-- **`δ_{β,λ} ≤ λ^{2(p-1)}` for `λ` small** (the paper's `δ_{β,λ} = o(λ^{2(p-1)})`). For `β ≥ 4`, `δ = λ^{2p}`; for `β ∈ (2,4)`, `δ ≤ λ^e (1 + |log λ|)` with
`e = 2(β-2)/(4-β) > 2(p-1)` because `β_p < β`. -/
theorem exists_errorRate_le_pow {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ} (hβ : 2 < β) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      errorRate p₀ β lam ≤ lam ^ (2 * (pBeta p₀ β - 1)) := by
  by_cases h4 : β < 4
  · set p := pBeta p₀ β
    have hp1 : 1 ≤ p := one_le_pBeta' hp₀ hβ
    have hlt := transitionBeta_pBeta_lt hp₀ hβ
    have h4' : 0 < 4 - β := by linarith
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    have hkey : (4 - β) * p < 2 := by
      unfold transitionBeta at hlt
      have : 4 - β < 2 / (p : ℝ) := by linarith
      rwa [lt_div_iff₀ hp0] at this
    set θ : ℝ := 2 * (β - 2) / (4 - β) - 2 * ((p : ℝ) - 1)
    have hθ : 0 < θ := by
      have : 2 * (β - 2) / (4 - β) - 2 * ((p : ℝ) - 1) = 2 * (2 - (4 - β) * p) / (4 - β) := by
        field_simp
        ring
      simp only [θ]
      rw [this]
      have : 0 < 2 - (4 - β) * p := by linarith
      positivity
    obtain ⟨x₀, hx₀, hx₀1, hx⟩ := exists_rpow_mul_log_le hθ
    refine ⟨x₀, hx₀, hx₀1, fun lam hlam hlamx => ?_⟩
    rw [errorRate_of_lt_four' hβ h4 hlam]
    have hsplit : lam ^ (2 * (β - 2) / (4 - β)) = lam ^ (2 * (p - 1)) * lam ^ θ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hlam]
      congr 1
      simp only [θ]
      push_cast [Nat.cast_sub hp1]
      ring
    rw [hsplit, mul_assoc]
    have h1 := hx lam hlam hlamx
    have h2 := tsum_transition_le β lam
    have h3 : lam ^ θ * (1 + ∑' q : ℕ, (if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam|
        else 0)) ≤ 1 := by
      refine le_trans ?_ h1
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hlam.le _)
    calc lam ^ (2 * (p - 1)) * (lam ^ θ * (1 + ∑' q : ℕ,
          (if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0)))
        ≤ lam ^ (2 * (p - 1)) * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = lam ^ (2 * (p - 1)) := mul_one _
  · refine ⟨1, one_pos, le_rfl, fun lam hlam hlam1 => ?_⟩
    rw [errorRate_of_four_le (not_lt.mp h4)]
    unfold pBeta
    rw [ite_eq_right h4]
    exact pow_le_pow_of_le_one hlam.le hlam1.le (by omega)

/-! ### Stirling -/

/-- **Stirling upper bound**: `log N! ≤ N log N - N + 1 + log N` for `N ≥ 1`. -/
theorem log_factorial_le {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N ! : ℝ) ≤ (N : ℝ) * Real.log N - N + 1 + Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hfac : ((n + 1)! : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfpos : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hlog : Real.log (((n + 1)! : ℕ) : ℝ) = Real.log ((n : ℝ) + 1) + Real.log (n ! : ℝ) := by
      rw [hfac, Real.log_mul (by positivity) hfpos.ne']
    -- `(n+1) (log (n+1) - log n) ≥ 1`
    have hdiff : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
      have h := Real.one_sub_inv_le_log_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
      rw [Real.log_div (by positivity) hn0.ne'] at h
      have : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
      linarith
    have hkey : 1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
      have := mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      rwa [mul_one_div_cancel (by positivity)] at this
    push_cast
    rw [hlog]
    nlinarith [hkey, ih]

/-- Two-sided Stirling: `|log N! - (N log N - N)| ≤ 1 + log N` for `N ≥ 1`. -/
theorem abs_log_factorial_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |Real.log (N ! : ℝ) - ((N : ℝ) * Real.log N - N)| ≤ 1 + Real.log N := by
  have h1 := TwoComponentCoulomb.log_factorial_ge hN
  have h2 := log_factorial_le hN
  have h3 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [abs_le]
  constructor <;> linarith

/-! ### Absorption of `log N` into `N δ` -/

/-- `b (log (N + 1) + 1) ≤ a N` for `N` large, `a > 0`. -/
theorem eventually_log_le (a : ℝ) (ha : 0 < a) (b : ℝ) :
    ∀ᶠ N : ℕ in atTop, b * (Real.log ((N : ℝ) + 1) + 1) ≤ a * N := by
  have hlo := Real.isLittleO_log_id_atTop
  have hb : 0 ≤ |b| + 1 := by positivity
  set ε : ℝ := a / (4 * (|b| + 1))
  have hε : 0 < ε := by positivity
  have h1 := hlo.bound hε
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 := hN.eventually h1
  have h3 : ∀ᶠ N : ℕ in atTop, (4 * (|b| + 1)) / a ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [h2, h3] with N hN1 hN2
  simp only [Real.norm_eq_abs, id] at hN1
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hlog : Real.log ((N : ℝ) + 1) ≤ ε * ((N : ℝ) + 1) := by
    have := (le_abs_self _).trans hN1
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)] at this
  have hlog0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hbound : b * (Real.log ((N : ℝ) + 1) + 1) ≤ (|b| + 1) * (ε * ((N : ℝ) + 1) + 1) := by
    have : b * (Real.log ((N : ℝ) + 1) + 1) ≤ |b| * (Real.log ((N : ℝ) + 1) + 1) :=
      mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith)
    have h' : |b| * (Real.log ((N : ℝ) + 1) + 1) ≤ (|b| + 1) * (ε * ((N : ℝ) + 1) + 1) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) hb
    linarith
  have hεb : (|b| + 1) * ε = a / 4 := by
    simp only [ε]
    field_simp
  have hNa : (|b| + 1) * 4 ≤ a * N := by
    rw [div_le_iff₀ ha] at hN2
    linarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN2
  have hN1' : (1 : ℝ) ≤ N := by
    have : 0 < N := by exact_mod_cast hNpos
    exact_mod_cast this
  have hexp : (|b| + 1) * (ε * ((N : ℝ) + 1) + 1) = a / 4 * N + a / 4 + (|b| + 1) := by
    rw [mul_add, mul_one, ← mul_assoc, hεb]
    ring
  have haN : a / 4 ≤ a / 4 * N := le_mul_of_one_le_right (by positivity) hN1'
  linarith

/-! ### `ofReal (exp _)` in `ℝ≥0∞` -/

theorem ofReal_exp_mul_ofReal_exp (a b : ℝ) :
    ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) = ENNReal.ofReal (Real.exp (a + b)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos a).le, Real.exp_add]

theorem ofReal_exp_le_ofReal_exp {a b : ℝ} (h : a ≤ b) :
    ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp b) :=
  ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)

theorem ofReal_exp_ne_zero (a : ℝ) : ENNReal.ofReal (Real.exp a) ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos a)).ne'

/-- Upper bound on a ratio: `Z⁻¹ I ≤ e^{B - A}` from `e^A ≤ Z` and `I ≤ e^B`. -/
theorem inv_mul_le_ofReal_exp {Z I : ℝ≥0∞} {A B : ℝ} (hZ : ENNReal.ofReal (Real.exp A) ≤ Z)
    (hI : I ≤ ENNReal.ofReal (Real.exp B)) : Z⁻¹ * I ≤ ENNReal.ofReal (Real.exp (B - A)) := by
  have h1 : Z⁻¹ ≤ ENNReal.ofReal (Real.exp (-A)) := by
    rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos A)]
    exact ENNReal.inv_le_inv.mpr hZ
  calc Z⁻¹ * I ≤ ENNReal.ofReal (Real.exp (-A)) * ENNReal.ofReal (Real.exp B) := by gcongr
    _ = ENNReal.ofReal (Real.exp (B - A)) := by
      rw [ofReal_exp_mul_ofReal_exp]; ring_nf

/-- Lower bound on a ratio: `e^{B - A} ≤ Z⁻¹ I` from `Z ≤ e^A` and `e^B ≤ I`. -/
theorem ofReal_exp_le_inv_mul {Z I : ℝ≥0∞} {A B : ℝ} (hZ : Z ≤ ENNReal.ofReal (Real.exp A))
    (hI : ENNReal.ofReal (Real.exp B) ≤ I) : ENNReal.ofReal (Real.exp (B - A)) ≤ Z⁻¹ * I := by
  have h1 : ENNReal.ofReal (Real.exp (-A)) ≤ Z⁻¹ := by
    rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos A)]
    exact ENNReal.inv_le_inv.mpr hZ
  calc ENNReal.ofReal (Real.exp (B - A))
      = ENNReal.ofReal (Real.exp (-A)) * ENNReal.ofReal (Real.exp B) := by
        rw [ofReal_exp_mul_ofReal_exp]; ring_nf
    _ ≤ Z⁻¹ * I := by gcongr

/-- `|log Z.toReal - T| ≤ D` from `e^{T - D} ≤ Z ≤ e^{T + D}`. -/
theorem abs_log_toReal_sub_le {Z : ℝ≥0∞} {T D : ℝ}
    (hlo : ENNReal.ofReal (Real.exp (T - D)) ≤ Z) (hhi : Z ≤ ENNReal.ofReal (Real.exp (T + D))) :
    |Real.log Z.toReal - T| ≤ D := by
  have hZtop : Z ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  have h1 : Real.exp (T - D) ≤ Z.toReal := by
    have := ENNReal.toReal_mono hZtop hlo
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have h2 : Z.toReal ≤ Real.exp (T + D) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hhi
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have hpos : 0 < Z.toReal := lt_of_lt_of_le (Real.exp_pos _) h1
  have h3 : T - D ≤ Real.log Z.toReal := by
    rw [← Real.log_exp (T - D)]
    exact Real.log_le_log (Real.exp_pos _) h1
  have h4 : Real.log Z.toReal ≤ T + D := by
    rw [← Real.log_exp (T + D)]
    exact Real.log_le_log hpos h2
  rw [abs_le]
  constructor <;> linarith

/-- `(N+1)^p e^X = e^{X + p log (N+1)}`. -/
theorem natCast_pow_mul_ofReal_exp (N p : ℕ) (X : ℝ) :
    ((N + 1 : ℕ) : ℝ≥0∞) ^ p * ENNReal.ofReal (Real.exp X) =
      ENNReal.ofReal (Real.exp (X + p * Real.log ((N : ℝ) + 1))) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : ((N + 1 : ℕ) : ℝ≥0∞) ^ p = ENNReal.ofReal (Real.exp (p * Real.log ((N : ℝ) + 1))) := by
    rw [Real.exp_nat_mul, Real.exp_log hN, ENNReal.ofReal_pow hN.le]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  rw [h1, ofReal_exp_mul_ofReal_exp, add_comm]

end TheoremTwo

end MultipoleBKT

end
