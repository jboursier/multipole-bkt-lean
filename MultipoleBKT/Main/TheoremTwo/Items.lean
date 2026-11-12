/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.LargeDeviations
public import MultipoleBKT.Main.TheoremTwo.Coefficients
public import MultipoleBKT.Main.TheoremTwo.RouteQuantitative.RateError

/-!
# Theorem 2: items (2), (3) and (5)

Items of Theorem 2.
The proof follows Steps 1, 2 and 4.
`exists_partitionFunction_bounds` absorbs the quantitative rounding error
from (5.150) at fixed `λ`. Stirling gives item (2).
The bad-point tail and Remark 5.6 give item (3).
The rate-function minimizer API gives item (5).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MultipoleBKT

namespace TheoremTwo

/-- The analytic setup at a fixed `M`: uniform constants `C₁` for (2.47)–(2.48), `C''` for the
size of the minimizer, and `λ₀` below which `RateSetup` holds and the minimizer is unique, with
positive coordinates `C''⁻¹ λ^{2i} ≤ γ*ᵢ ≤ C'' λ^{2i}`. -/
def SetupAt (p : ℕ) (msf : ℝ → ℕ → ℝ) (kmult : ℝ → (ℕ →₀ ℕ) → ℝ) (C₁ C'' l₀ : ℝ) : Prop :=
  0 < C₁ ∧ 0 < C'' ∧ 0 < l₀ ∧ l₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < l₀ →
    RateSetup p (msf lam) (kmult lam) C₁ lam ∧
    (∃! γ, γ ∈ simplex p 0 ∧ IsMinOn (rateFunction p (msf lam) (kmult lam)) (simplex p 0) γ) ∧
    ∀ γ ∈ simplex p 0, IsMinOn (rateFunction p (msf lam) (kmult lam)) (simplex p 0) γ →
      (∀ i, 0 < γ i) ∧ ∀ i : Fin p, 1 ≤ (i : ℕ) →
        C''⁻¹ * lam ^ (2 * (i : ℕ)) ≤ γ i ∧ γ i ≤ C'' * lam ^ (2 * (i : ℕ))

theorem exists_setupAt {p : ℕ} (hp : 1 ≤ p) {msf : ℝ → ℕ → ℝ} {kmult : ℝ → (ℕ →₀ ℕ) → ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      MsfBound p (msf lam) C lam ∧ KmultBound p (kmult lam) C lam) :
    ∃ C₁ C'' l₀ : ℝ, SetupAt p msf kmult C₁ C'' l₀ := by
  obtain ⟨C₁, hC₁, l₁, hl₁, hl₁1, hb⟩ := h
  obtain ⟨l₂, hl₂, hl₂1, C'', hC'', hR⟩ := exists_rateSetup hp hC₁
  refine ⟨C₁, C'', min l₁ l₂, hC₁, hC'', lt_min hl₁ hl₂, (min_le_left _ _).trans hl₁1,
    fun lam hlam hlaml => ?_⟩
  obtain ⟨hm, hk⟩ := hb lam hlam (lt_of_lt_of_le hlaml (min_le_left _ _))
  exact hR lam hlam (lt_of_lt_of_le hlaml (min_le_right _ _)) _ _ hm hk

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β M : ℝ} {msf : ℝ → ℕ → ℝ} {kmult : ℝ → (ℕ →₀ ℕ) → ℝ}
  {C₁ C'' l₀ : ℝ}

/-- **The partition function at fixed `λ`** (Steps 1–2): constants `C_L`, `C_U` and an
`ε₀ ∈ (0,1)` for Proposition 5.43 at `t = 1`, such that for `λ` small and `N ≥ N₀(λ)`,
`e^{L_N - N inf ℐ - C_L N δ} ≤ Z ≤ e^{L_N - N inf ℐ + C_U N δ + p log (N+1)}`. -/
theorem exists_partitionFunction_bounds (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 0 ≤ M)
    (hset : SetupAt (pBeta p₀ β) msf kmult C₁ C'' l₀) (hlow : LowerGateAt χ p₀ β M msf kmult)
    (hup : UpperGateAt χ p₀ β M msf kmult)
    (hmeas : ∀ (N : ℕ) (lam ε₀ : ℝ), Measurable fun c : Fin N → ℂ × ℂ =>
      (badPoints p₀ β lam M ε₀ (matched c)).card) :
    ∃ εU : ℝ, 0 < εU ∧ εU < 1 ∧ ∃ CU : ℝ, 0 < CU ∧ ∃ CL : ℝ, 0 < CL ∧
      ∃ l : ℝ, 0 < l ∧ l ≤ l₀ ∧ ∀ lam : ℝ, 0 < lam → lam < l →
        ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ UpperProfileBound χ p₀ β M εU 1 CU lam msf kmult N ∧
          ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
            N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) -
            CL * N * errorRate p₀ β lam)) ≤ partitionFunction χ N β lam ∧
          partitionFunction χ N β lam ≤ ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
            N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) +
            CU * N * errorRate p₀ β lam + (pBeta p₀ β) * Real.log ((N : ℝ) + 1))) := by
  obtain ⟨hC₁, hC'', hl₀, -, hS⟩ := hset
  obtain ⟨ε₁U, hε₁U, hε₁U1, hU⟩ := hup 1 le_rfl
  obtain ⟨CU, hCU, lU, hlU, -, hUl⟩ := hU (ε₁U / 2) (by positivity) (by linarith)
  obtain ⟨ε₁L, hε₁L, -, hL⟩ := hlow
  obtain ⟨εL, hεL, hεL1, hεLC⟩ := exists_rpow_neg_ge (alphaExponent_pos β) hε₁L C''
  obtain ⟨C4, hC4, lL, hlL, -, hLl⟩ := hL εL hεL hεL1
  refine ⟨ε₁U / 2, by positivity, by linarith, CU, hCU, C4 + 1, by positivity,
    min l₀ (min lU lL), lt_min hl₀ (lt_min hlU hlL), min_le_left _ _, fun lam hlam hlaml => ?_⟩
  have hl0 : lam < l₀ := lt_of_lt_of_le hlaml (min_le_left _ _)
  have hlU' : lam < lU := lt_of_lt_of_le hlaml ((min_le_right _ _).trans (min_le_left _ _))
  have hlL' : lam < lL := lt_of_lt_of_le hlaml ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hs, hex, hmins⟩ := hS lam hlam hl0
  obtain ⟨γs, ⟨hγs, hmin⟩, -⟩ := hex
  obtain ⟨-, hbd⟩ := hmins γs hγs hmin
  obtain ⟨-, N₁, hN₁⟩ := hUl lam hlam hlU'
  obtain ⟨-, N₂, hN₂⟩ := hLl lam hlam hlL'
  have hδ : 0 < errorRate p₀ β lam := errorRate_pos hβ hlam
  filter_upwards [eventually_ge_atTop (max 1 (max N₁ N₂)),
    eventually_rounding_absorb (p := pBeta p₀ β) (C := C₁) (lam := lam)
      (show (1 : ℝ) ≤ (pBeta p₀ β : ℝ) ^ 2 from by
        have hp : (1 : ℝ) ≤ pBeta p₀ β := by exact_mod_cast hs.hp
        nlinarith) hδ] with N hN hround
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hUN := hN₁ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hLN := hN₂ N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  refine ⟨hN1, hUN, ?_, ?_⟩
  · refine le_trans (ofReal_exp_le_ofReal_exp ?_) (partitionFunction_ge hs hγs hmin
      (A := C'') (fun i hi => (hbd i hi).2) hεLC hLN hround.1)
    nlinarith [hround.2]
  · exact partitionFunction_le hs hχ hM (by positivity) (hmeas N lam _) hUN hN1

/-- `log N! - (N log N - N) ∈ [0, 1 + log N]` and the absorption of `log N` into `N δ`. -/
theorem eventually_stirling_absorb {δ : ℝ} (hδ : 0 < δ) (b : ℝ) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧
      0 ≤ Real.log (N.factorial : ℝ) - ((N : ℝ) * Real.log N - N) ∧
      Real.log (N.factorial : ℝ) - ((N : ℝ) * Real.log N - N) + b * Real.log ((N : ℝ) + 1) ≤
        N * δ := by
  filter_upwards [eventually_ge_atTop 1, eventually_log_le δ hδ (|b| + 1)] with N hN hlog
  have hst := abs_log_factorial_sub_le hN
  have hst' := TwoComponentCoulomb.log_factorial_ge hN
  have hlogN : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast hN) (by linarith)
  have hlog1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  refine ⟨hN, by linarith, ?_⟩
  have h1 := (abs_le.mp hst).2
  have hb : b * Real.log ((N : ℝ) + 1) ≤ |b| * Real.log ((N : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self b) hlog1
  have hexp : (|b| + 1) * (Real.log ((N : ℝ) + 1) + 1) =
      |b| * Real.log ((N : ℝ) + 1) + |b| + Real.log ((N : ℝ) + 1) + 1 := by ring
  have := abs_nonneg b
  linarith

/-- **Item (2)**, eq. (2.49). -/
theorem item_two (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 0 ≤ M)
    (hset : SetupAt (pBeta p₀ β) msf kmult C₁ C'' l₀) (hlow : LowerGateAt χ p₀ β M msf kmult)
    (hup : UpperGateAt χ p₀ β M msf kmult)
    (hmeas : ∀ (N : ℕ) (lam ε₀ : ℝ), Measurable fun c : Fin N → ℂ × ℂ =>
      (badPoints p₀ β lam M ε₀ (matched c)).card) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        (∀ γ ∈ simplex (pBeta p₀ β) 0, Summable fun nm : ℕ+ × (Fin (pBeta p₀ β) → ℕ) =>
          ‖rateSeriesTerm (pBeta p₀ β) (kmult lam) γ nm.1 nm.2‖) ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          0 < partitionFunction χ N β lam ∧ partitionFunction χ N β lam < ∞ ∧
          |Real.log (partitionFunction χ N β lam).toReal
              - (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant χ β) - 1)
                - N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) ''
                    simplex (pBeta p₀ β) 0))|
            ≤ C * N * errorRate p₀ β lam := by
  have hset' := hset
  obtain ⟨-, -, -, hl₀1, hS⟩ := hset'
  obtain ⟨εU, hεU, -, CU, hCU, CL, hCL, l, hl, hll₀, hZ⟩ :=
    exists_partitionFunction_bounds hχ hβ hM hset hlow hup hmeas
  refine ⟨CL + CU + 1, by positivity, l, hl, hll₀.trans hl₀1, fun lam hlam hlaml => ?_⟩
  obtain ⟨hs, -, -⟩ := hS lam hlam (lt_of_lt_of_le hlaml hll₀)
  refine ⟨fun γ hγ => hs.summable hγ, ?_⟩
  have hδ : 0 < errorRate p₀ β lam := errorRate_pos hβ hlam
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hZ lam hlam hlaml).and
    (eventually_stirling_absorb hδ (pBeta p₀ β : ℝ)))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨hN1, -, hlo, hhi⟩, -, hσ0, hσ⟩ := hN₀ N hN
  set inf0 := sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0)
  set δ := errorRate p₀ β lam
  set T := 2 * N * Real.log N + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant χ β) - 1)
    - N * inf0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hF : freeTerm χ β lam N - N * inf0 =
      T + (Real.log (N.factorial : ℝ) - ((N : ℝ) * Real.log N - N)) := by
    unfold freeTerm; simp only [T]; ring
  have hNδ : 0 ≤ (N : ℝ) * δ := by positivity
  have hlo' : ENNReal.ofReal (Real.exp (T - (CL + CU + 1) * N * δ)) ≤
      partitionFunction χ N β lam := by
    refine le_trans (ofReal_exp_le_ofReal_exp ?_) hlo
    rw [hF]
    nlinarith
  have hhi' : partitionFunction χ N β lam ≤
      ENNReal.ofReal (Real.exp (T + (CL + CU + 1) * N * δ)) := by
    refine hhi.trans (ofReal_exp_le_ofReal_exp ?_)
    rw [hF]
    nlinarith
  refine ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (Real.exp_pos _)) hlo',
    lt_of_le_of_lt hhi' ENNReal.ofReal_lt_top, ?_⟩
  have := abs_log_toReal_sub_le hlo' hhi'
  simpa [T, mul_assoc] using this

/-- **Item (3)**, eqs. (2.50) and (2.51). -/
theorem item_three (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 0 ≤ M)
    (hset : SetupAt (pBeta p₀ β) msf kmult C₁ C'' l₀) (hlow : LowerGateAt χ p₀ β M msf kmult)
    (hup : UpperGateAt χ p₀ β M msf kmult)
    (hmeas : ∀ (N : ℕ) (lam ε₀ : ℝ), Measurable fun c : Fin N → ℂ × ℂ =>
      (badPoints p₀ β lam M ε₀ (matched c)).card) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, 1 ≤ n →
        gibbsMeasure χ N β lam {c | (n : ℤ) ≤
            |(∑ k ∈ Finset.Icc 1 (pBeta p₀ β), (k : ℤ) * multipoleCount M lam c k) - N|}
          ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * n + C * N * errorRate p₀ β lam)) ∧
        gibbsMeasure χ N β lam {c | n ≤ {i : Fin N | criticalScale β lam ≤
            ENNReal.ofReal ‖(c i).1 - (c (stableMatching c i)).2‖}.ncard}
          ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * n + C * N * errorRate p₀ β lam)) := by
  have hset' := hset
  obtain ⟨-, -, -, hl₀1, hS⟩ := hset'
  obtain ⟨εU, hεU, hεU1, CU, hCU, CL, hCL, l, hl, hll₀, hZ⟩ :=
    exists_partitionFunction_bounds hχ hβ hM hset hlow hup hmeas
  refine ⟨CU + CL + 1, by positivity, l, hl, hll₀.trans hl₀1, fun lam hlam hlaml => ?_⟩
  obtain ⟨hs, -, -⟩ := hS lam hlam (lt_of_lt_of_le hlaml hll₀)
  have hδ : 0 < errorRate p₀ β lam := errorRate_pos hβ hlam
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hZ lam hlam hlaml).and
    (eventually_log_le (errorRate p₀ β lam) hδ (pBeta p₀ β : ℝ)))
  refine ⟨N₀, fun N hN n hn => ?_⟩
  obtain ⟨⟨hN1, hUN, hlo, -⟩, habs⟩ := hN₀ N hN
  have htail := gibbsMeasure_badPoints_le hs hχ hM hεU.le (hmeas N lam εU) hUN hN1 hlo (n : ℝ)
  have hlog1 : 0 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hfin : ENNReal.ofReal (Real.exp (-(n : ℝ) / 2 + (CU + CL) * N * errorRate p₀ β lam +
      (pBeta p₀ β) * Real.log ((N : ℝ) + 1))) ≤
      ENNReal.ofReal (Real.exp (-(1 / 2) * n + (CU + CL + 1) * N * errorRate p₀ β lam)) := by
    refine ofReal_exp_le_ofReal_exp ?_
    have : (pBeta p₀ β : ℝ) * Real.log ((N : ℝ) + 1) ≤ errorRate p₀ β lam * N := by
      nlinarith [habs]
    nlinarith
  refine ⟨(measure_mono fun c hc => ?_).trans (htail.trans hfin),
    (measure_mono fun c hc => ?_).trans (htail.trans hfin)⟩
  · -- `|∑ k 𝒩_k - N| = N - ∑ k 𝒩_k ≤ N - ∑ k 𝒩_k^good ≤ |I_bad|`
    have hc' : (n : ℤ) ≤
        |(∑ k ∈ Finset.Icc 1 (pBeta p₀ β), (k : ℤ) * multipoleCount M lam c k) - N| := hc
    have h1 := sum_mul_multipoleCount_le (M := M) (lam := lam) c (Finset.Icc 1 (pBeta p₀ β))
    have h2 := card_le_card_badPoints_add_sum (p₀ := p₀) (β := β) (lam := lam) (ε₀ := εU) hM c
    have h3 : ∑ k ∈ Finset.Icc 1 (pBeta p₀ β), k * goodMultipoleCount p₀ β lam M εU c k ≤
        ∑ k ∈ Finset.Icc 1 (pBeta p₀ β), k * multipoleCount M lam c k :=
      Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left k
        (goodMultipoleCount_le_multipoleCount c k)
    have hcast : (∑ k ∈ Finset.Icc 1 (pBeta p₀ β), (k : ℤ) * multipoleCount M lam c k) =
        ((∑ k ∈ Finset.Icc 1 (pBeta p₀ β), k * multipoleCount M lam c k : ℕ) : ℤ) := by
      push_cast; rfl
    rw [hcast, abs_sub_comm, abs_of_nonneg (by omega)] at hc'
    show (n : ℝ) ≤ (badPoints p₀ β lam M εU (matched c)).card
    have : n ≤ (badPoints p₀ β lam M εU (matched c)).card := by omega
    exact_mod_cast this
  · have hc' : n ≤ {i : Fin N | criticalScale β lam ≤
        ENNReal.ofReal ‖(c i).1 - (c (stableMatching c i)).2‖}.ncard := hc
    have h1 := ncard_le_card_badPoints (p₀ := p₀) (β := β) (M := M) hlam hεU1 c
    show (n : ℝ) ≤ (badPoints p₀ β lam M εU (matched c)).card
    exact_mod_cast hc'.trans h1

/-- **Item (5)**, eq. (2.53). -/
theorem item_five (hset : SetupAt (pBeta p₀ β) msf kmult C₁ C'' l₀) :
    (∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        (∀ γ ∈ simplex (pBeta p₀ β) 0, Summable fun nm : ℕ+ × (Fin (pBeta p₀ β) → ℕ) =>
          ‖rateSeriesTerm (pBeta p₀ β) (kmult lam) γ nm.1 nm.2‖) ∧
        ∃! γstar : Fin (pBeta p₀ β) → ℝ, γstar ∈ simplex (pBeta p₀ β) 0 ∧
          IsMinOn (rateFunction (pBeta p₀ β) (msf lam) (kmult lam)) (simplex (pBeta p₀ β) 0)
            γstar) ∧
      ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            ∃ γstar ∈ simplex (pBeta p₀ β) 0,
              IsMinOn (rateFunction (pBeta p₀ β) (msf lam) (kmult lam)) (simplex (pBeta p₀ β) 0)
                γstar ∧
              C⁻¹ * lam ^ (2 * (i : ℕ)) ≤ γstar i ∧ γstar i ≤ C * lam ^ (2 * (i : ℕ)) := by
  obtain ⟨-, hC'', hl₀, hl₀1, hS⟩ := hset
  refine ⟨⟨l₀, hl₀, hl₀1, fun lam hlam hlaml => ?_⟩, fun i hi =>
    ⟨C'', hC'', l₀, hl₀, hl₀1, fun lam hlam hlaml => ?_⟩⟩
  · obtain ⟨hs, hex, -⟩ := hS lam hlam hlaml
    exact ⟨fun γ hγ => hs.summable hγ, hex⟩
  · obtain ⟨-, hex, hmins⟩ := hS lam hlam hlaml
    obtain ⟨γs, ⟨hγs, hmin⟩, -⟩ := hex
    exact ⟨γs, hγs, hmin, (hmins γs hγs hmin).2 i hi⟩

end TheoremTwo

end MultipoleBKT

end
