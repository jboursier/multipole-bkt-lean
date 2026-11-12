/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.Items

/-!
# Theorem 2: items (4) and (6)

Steps 3 and 5 of the proof of Theorem 2. Item (4), (2.52), uses the contraction
`D_p/(Nρ)` and absorbs the quantitative entropy error uniformly over
profile centers. Item (6), (2.54), uses the integrated
Hessian gap for the lower tail. The upper tail follows (5.155), through the weighted good-point and nongood-point counts.
Its near-unit bad-count exponent is relaxed only in the final comparison.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MultipoleBKT

namespace TheoremTwo

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β M : ℝ} {msf : ℝ → ℕ → ℝ} {kmult : ℝ → (ℕ →₀ ℕ) → ℝ}
  {C₁ C'' l₀ : ℝ}

/-- Remark 5.6 in Step 1 of the proof of Theorem 2: the nongood size-`k` multipoles contain at most `|I_bad|` points. -/
theorem mul_sub_goodMultipoleCount_le_card (hM : 0 ≤ M) {ε₀ lam : ℝ} {N : ℕ}
    (c : Fin N → ℂ × ℂ) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k ≤ pBeta p₀ β) :
    k * (multipoleCount M lam c k - goodMultipoleCount p₀ β lam M ε₀ c k) ≤
      (badPoints p₀ β lam M ε₀ (matched c)).card := by
  have h1 := sum_mul_multipoleCount_le (M := M) (lam := lam) c (Finset.Icc 1 (pBeta p₀ β))
  have h2 := card_le_card_badPoints_add_sum (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) hM c
  set T := Finset.Icc 1 (pBeta p₀ β)
  set D : ℕ → ℕ := fun j => multipoleCount M lam c j - goodMultipoleCount p₀ β lam M ε₀ c j
  have hD : ∀ j, multipoleCount M lam c j = goodMultipoleCount p₀ β lam M ε₀ c j + D j :=
    fun j => (Nat.add_sub_cancel' (goodMultipoleCount_le_multipoleCount c j)).symm
  have h3 : ∑ j ∈ T, j * multipoleCount M lam c j =
      ∑ j ∈ T, j * goodMultipoleCount p₀ β lam M ε₀ c j + ∑ j ∈ T, j * D j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hD j, mul_add]
  have h4 : k * D k ≤ ∑ j ∈ T, j * D j :=
    Finset.single_le_sum (f := fun j => j * D j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_Icc.mpr ⟨hk1, hkp⟩)
  change k * D k ≤ _
  omega

/-- The sharp threshold comparison in Step 1. Above the type-two threshold, the entire multipole count is at most
`|I_bad|`. The weak threshold is also valid and includes the endpoint needed in item (6). -/
theorem multipoleCount_le_card_badPoints_of_threshold (hM : 0 ≤ M) {ε₀ lam : ℝ}
    (hε₀ : 0 ≤ ε₀) {N : ℕ} (c : Fin N → ℂ × ℂ) {k : ℕ}
    (hk2 : 2 ≤ k) (hkp : k ≤ pBeta p₀ β)
    (ht : ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) ≤
      (multipoleCount M lam c k : ℝ)) :
    multipoleCount M lam c k ≤ (badPoints p₀ β lam M ε₀ (matched c)).card := by
  have hg := mul_goodMultipoleCount_le (lam := lam) hM hε₀ c (by omega : 1 ≤ k) hkp
  have hd := mul_sub_goodMultipoleCount_le_card (p₀ := p₀) (β := β) (lam := lam)
    (ε₀ := ε₀) hM c (by omega : 1 ≤ k) hkp
  have hle := goodMultipoleCount_le_multipoleCount (p₀ := p₀) (β := β)
    (lam := lam) (M := M) (ε₀ := ε₀) c k
  have hd' : (k : ℝ) * ((multipoleCount M lam c k : ℝ) -
      goodMultipoleCount p₀ β lam M ε₀ c k) ≤
      (badPoints p₀ β lam M ε₀ (matched c)).card := by
    exact_mod_cast hd
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hn : (0 : ℝ) ≤ multipoleCount M lam c k := Nat.cast_nonneg _
  have hn2 := mul_le_mul_of_nonneg_right hk hn
  exact_mod_cast (show (multipoleCount M lam c k : ℝ) ≤
    (badPoints p₀ β lam M ε₀ (matched c)).card by nlinarith)

/-- The sharp upper count tail (5.155). The coefficient `1 - rateB = 1 - O(λ²)` is retained. -/
theorem gibbsMeasure_multipoleCount_sharp_tail
    {ε₀ C lam : ℝ} {N : ℕ} (hs : RateSetup (pBeta p₀ β) (msf lam) (kmult lam) C₁ lam)
    (hχ : IsMollifier χ) (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀)
    (hmeas : Measurable fun c : Fin N → ℂ × ℂ => (badPoints p₀ β lam M ε₀ (matched c)).card)
    (hU : UpperProfileBound χ p₀ β M ε₀ 1 C lam msf kmult N) (hN : 1 ≤ N) {C' : ℝ}
    (hZ : ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
        N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) -
        C' * N * errorRate p₀ β lam)) ≤ partitionFunction χ N β lam) (s : ℝ)
    {k : ℕ} (hk2 : 2 ≤ k) (hkp : k ≤ pBeta p₀ β)
    (hsT : ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) ≤ s) :
    gibbsMeasure χ N β lam {c | s ≤ (multipoleCount M lam c k : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(1 - rateB (pBeta p₀ β) C₁ lam) * s + (C + C') * N * errorRate p₀ β lam +
        (pBeta p₀ β) * Real.log ((N : ℝ) + 1))) := by
  refine (measure_mono fun c hc => ?_).trans
    (gibbsMeasure_badPoints_sharp_le hs hχ hM hε₀ hmeas hU hN hZ s)
  have hc' : s ≤ (multipoleCount M lam c k : ℝ) := hc
  have hcount := multipoleCount_le_card_badPoints_of_threshold hM hε₀ c hk2 hkp (hsT.trans hc')
  exact hc'.trans (Nat.cast_le.mpr hcount)

/-- **Item (6)**, eq. (2.54). -/
theorem item_six (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 0 ≤ M)
    (hset : SetupAt (pBeta p₀ β) msf kmult C₁ C'' l₀) (hlow : LowerGateAt χ p₀ β M msf kmult)
    (hup : UpperGateAt χ p₀ β M msf kmult)
    (hmeas : ∀ (N : ℕ) (lam ε₀ : ℝ), Measurable fun c : Fin N → ℂ × ℂ =>
      (badPoints p₀ β lam M ε₀ (matched c)).card) :
    ∀ k : ℕ, 2 ≤ k → k ≤ pBeta p₀ β →
      ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ C₀min : ℝ, 0 < C₀min ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
        ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            gibbsMeasure χ N β lam {c | (multipoleCount M lam c k : ℝ) ∉
                Set.Ioo (C₀⁻¹ * N * lam ^ (2 * (k - 1))) (C₀ * N * lam ^ (2 * (k - 1)))}
              ≤ ENNReal.ofReal (Real.exp
                  (-C * N * lam ^ (2 * (k - 1)) + C' * N * errorRate p₀ β lam)) := by
  intro k hk2 hkp
  have hset' := hset
  obtain ⟨-, hC'', -, hl₀1, hS⟩ := hset'
  obtain ⟨εU, hεU, hεU1, CU, hCU, CL, hCL, l, hl, hll₀, hZ⟩ :=
    exists_partitionFunction_bounds hχ hβ hM hset hlow hup hmeas
  set i : Fin (pBeta p₀ β) := ⟨k - 1, by omega⟩
  have hi : 1 ≤ (i : ℕ) := by simp only [i]; omega
  have hik : (i : ℕ) + 1 = k := by simp only [i]; omega
  set a₀ := εU ^ (-alphaExponent β)
  have ha₀ : 0 < a₀ := Real.rpow_pos_of_pos hεU _
  set C₀min := max (2 * a₀) (4 * C'')
  have hC₀min : 0 < C₀min := lt_max_of_lt_left (by positivity)
  refine ⟨min (1 / (8 * C'')) (C₀min / 4), lt_min (by positivity) (by positivity),
    CU + CL + 1, by positivity, C₀min, hC₀min, fun C₀ hC₀m => ?_⟩
  have hC₀ : 0 < C₀ := hC₀min.trans_le hC₀m
  have h2a : 2 * a₀ ≤ C₀ := (le_max_left _ _).trans hC₀m
  have h4C : 4 * C'' ≤ C₀ := (le_max_right _ _).trans hC₀m
  refine ⟨l, hl, hll₀.trans hl₀1, fun lam hlam hlaml => ?_⟩
  obtain ⟨hs, hex, hmins⟩ := hS lam hlam (lt_of_lt_of_le hlaml hll₀)
  obtain ⟨γs, ⟨hγs, hmin⟩, -⟩ := hex
  obtain ⟨hpos, hbd⟩ := hmins γs hγs hmin
  have hδ : 0 < errorRate p₀ β lam := errorRate_pos hβ hlam
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hZ lam hlam hlaml).and
    (eventually_log_le (errorRate p₀ β lam) hδ ((pBeta p₀ β : ℝ) + 1)))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨hN1, hUN, hlo, -⟩, habs⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set lk := lam ^ (2 * (k - 1))
  have hlk : lk = lam ^ (2 * (i : ℕ)) := rfl
  have hlk0 : 0 < lk := pow_pos hlam _
  set C := min (1 / (8 * C'')) (C₀min / 4)
  set Y := ENNReal.ofReal (Real.exp (-C * N * lk + (CU + CL) * N * errorRate p₀ β lam +
    (pBeta p₀ β) * Real.log ((N : ℝ) + 1)))
  -- the lower tail
  have hlow' : gibbsMeasure χ N β lam
      {c | (multipoleCount M lam c ((i : ℕ) + 1) : ℝ) ≤ (C₀⁻¹ * lk) * N} ≤ Y := by
    have ha : C₀⁻¹ * lk ≤ γs i / 4 := by
      have h1 := (hbd i hi).1
      have h2 : C₀⁻¹ ≤ (4 * C'')⁻¹ := inv_anti₀ (by positivity) h4C
      calc C₀⁻¹ * lk ≤ (4 * C'')⁻¹ * lk := mul_le_mul_of_nonneg_right h2 hlk0.le
        _ = (C''⁻¹ * lam ^ (2 * (i : ℕ))) / 4 := by rw [hlk]; field_simp
        _ ≤ γs i / 4 := by linarith
    refine (gibbsMeasure_multipoleCount_le hs hχ hM hεU.le (hmeas N lam εU) hUN hN1 hlo hγs hmin
      hpos i hi ha).trans (ofReal_exp_le_ofReal_exp ?_)
    have h1 := (hbd i hi).1
    have hC1 : C ≤ 1 / (8 * C'') := min_le_left _ _
    have : C * lk ≤ γs i / 8 := by
      calc C * lk ≤ 1 / (8 * C'') * lk := mul_le_mul_of_nonneg_right hC1 hlk0.le
        _ = (C''⁻¹ * lam ^ (2 * (i : ℕ))) / 8 := by rw [hlk]; field_simp
        _ ≤ γs i / 8 := by linarith
    nlinarith
  -- the upper tail
  have hup' : gibbsMeasure χ N β lam
      {c | (C₀ * N * lk : ℝ) ≤ (multipoleCount M lam c k : ℝ)} ≤ Y := by
    have hsT : εU ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) ≤ C₀ * N * lk := by
      have haC : a₀ ≤ C₀ := by linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right haC hN0.le) hlk0.le
    refine (gibbsMeasure_multipoleCount_sharp_tail hs hχ hM hεU.le (hmeas N lam εU)
      hUN hN1 hlo (C₀ * N * lk) hk2 hkp hsT).trans (ofReal_exp_le_ofReal_exp ?_)
    have hC2 : C ≤ C₀ / 4 := (min_le_right _ _).trans
      (div_le_div_of_nonneg_right hC₀m (by norm_num))
    have hcoef : 1 / 2 ≤ 1 - rateB (pBeta p₀ β) C₁ lam := by linarith [hs.hB]
    have hmul := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ C₀ * N * lk)
    have hCN := mul_le_mul_of_nonneg_right hC2 (mul_nonneg hN0.le hlk0.le)
    nlinarith
  have hsub : {c : Fin N → ℂ × ℂ | (multipoleCount M lam c k : ℝ) ∉
      Set.Ioo (C₀⁻¹ * N * lam ^ (2 * (k - 1))) (C₀ * N * lam ^ (2 * (k - 1)))} ⊆
      {c | (multipoleCount M lam c ((i : ℕ) + 1) : ℝ) ≤ (C₀⁻¹ * lk) * N} ∪
      {c | (C₀ * N * lk : ℝ) ≤ (multipoleCount M lam c k : ℝ)} := by
    intro c hc
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo, not_and_or, not_lt] at hc
    rcases hc with hc | hc
    · left
      show (multipoleCount M lam c ((i : ℕ) + 1) : ℝ) ≤ (C₀⁻¹ * lk) * N
      rw [hik]
      linarith
    · exact Or.inr hc
  have hsum : Y + Y ≤ ENNReal.ofReal (Real.exp (-C * N * lk +
      (CU + CL + 1) * N * errorRate p₀ β lam)) := by
    rw [← two_mul]
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (Real.exp (Real.log 2)) := by
      rw [Real.exp_log (by norm_num)]; simp
    rw [h2, ofReal_exp_mul_ofReal_exp]
    refine ofReal_exp_le_ofReal_exp ?_
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlog1 : 0 ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
    nlinarith
  calc gibbsMeasure χ N β lam {c | (multipoleCount M lam c k : ℝ) ∉
        Set.Ioo (C₀⁻¹ * N * lam ^ (2 * (k - 1))) (C₀ * N * lam ^ (2 * (k - 1)))}
      ≤ gibbsMeasure χ N β lam
          ({c | (multipoleCount M lam c ((i : ℕ) + 1) : ℝ) ≤ (C₀⁻¹ * lk) * N} ∪
            {c | (C₀ * N * lk : ℝ) ≤ (multipoleCount M lam c k : ℝ)}) :=
        measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ Y + Y := add_le_add hlow' hup'
    _ ≤ _ := hsum

/-- **Item (4)**, eq. (2.52). -/
theorem item_four (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) (hM : 0 ≤ M)
    (hset : SetupAt (pBeta p₀ β) msf kmult C₁ C'' l₀) (hlow : LowerGateAt χ p₀ β M msf kmult)
    (hup : UpperGateAt χ p₀ β M msf kmult)
    (hmeas : ∀ (N : ℕ) (lam ε₀ : ℝ), Measurable fun c : Fin N → ℂ × ℂ =>
      (badPoints p₀ β lam M ε₀ (matched c)).card) :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          (∀ γ ∈ simplex (pBeta p₀ β) 0, Summable fun nm : ℕ+ × (Fin (pBeta p₀ β) → ℕ) =>
            ‖rateSeriesTerm (pBeta p₀ β) (kmult lam) γ nm.1 nm.2‖) ∧
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ γ ∈ simplex (pBeta p₀ β) 0,
            (∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) → γ i ≤ C₀ * lam ^ (2 * (i : ℕ))) →
            ENNReal.ofReal (Real.exp (-N * (sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) ''
                  {γ' | γ' ∈ simplex (pBeta p₀ β) 0 ∧ ‖γ' - γ‖ ≤ C₀ * errorRate p₀ β lam}) -
                sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0))
                - C * N * errorRate p₀ β lam))
                ≤ gibbsMeasure χ N β lam {c | ∀ i : Fin (pBeta p₀ β),
                  |(multipoleCount M lam c ((i : ℕ) + 1) : ℝ) - N * γ i|
                    ≤ C₀ * N * errorRate p₀ β lam} ∧
              gibbsMeasure χ N β lam {c | ∀ i : Fin (pBeta p₀ β),
                  |(multipoleCount M lam c ((i : ℕ) + 1) : ℝ) - N * γ i|
                    ≤ C₀ * N * errorRate p₀ β lam}
                ≤ ENNReal.ofReal (Real.exp (-N * (sInf (rateFunction (pBeta p₀ β) (msf lam)
                    (kmult lam) '' {γ' | γ' ∈ simplex (pBeta p₀ β) 0 ∧
                      ‖γ' - γ‖ ≤ C₀ * errorRate p₀ β lam}) -
                  sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0))
                  + C * N * errorRate p₀ β lam)) := by
  intro C₀ hC₀
  have hset' := hset
  obtain ⟨hC₁, -, -, hl₀1, hS⟩ := hset'
  obtain ⟨εU, hεU, -, CU, hCU, CL, hCL, l, hl, hll₀, hZ⟩ :=
    exists_partitionFunction_bounds hχ hβ hM hset hlow hup hmeas
  set T := Real.log ((pBeta p₀ β).factorial : ℝ) + |Real.log (2 * C₀)| + |Real.log C₁| + 1
  have hT1 : 1 ≤ T := by
    have : 0 ≤ Real.log ((pBeta p₀ β).factorial : ℝ) := Real.log_nonneg
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    have := abs_nonneg (Real.log (2 * C₀))
    have := abs_nonneg (Real.log C₁)
    simp only [T]; linarith
  obtain ⟨ε₁T, hε₁T, -, hUT⟩ := hup T hT1
  obtain ⟨CT, hCT, lT, hlT, -, hTl⟩ := hUT (ε₁T / 2) (by positivity) (by linarith)
  obtain ⟨ε₁L, hε₁L, -, hL⟩ := hlow
  obtain ⟨εL, hεL, hεL1, hεLC⟩ := exists_rpow_neg_ge (alphaExponent_pos β) hε₁L (2 * C₀)
  obtain ⟨C4, hC4, lL, hlL, -, hLl⟩ := hL εL hεL hεL1
  obtain ⟨lδ, hlδ, -, hδle⟩ := exists_errorRate_le_pow hp₀ hβ
  refine ⟨CT + CL + C4 + CU + 2, by positivity, min l (min lT (min lL lδ)),
    lt_min hl (lt_min hlT (lt_min hlL hlδ)), (min_le_left _ _).trans (hll₀.trans hl₀1),
    fun lam hlam hlaml => ?_⟩
  have hl' : lam < l := lt_of_lt_of_le hlaml (min_le_left _ _)
  have hlT' : lam < lT := lt_of_lt_of_le hlaml ((min_le_right _ _).trans (min_le_left _ _))
  have hlL' : lam < lL := lt_of_lt_of_le hlaml
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hlδ' : lam < lδ := lt_of_lt_of_le hlaml
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hs, -, -⟩ := hS lam hlam (lt_of_lt_of_le hl' hll₀)
  refine ⟨fun γ hγ => hs.summable hγ, ?_⟩
  have hδ0 : 0 < errorRate p₀ β lam := errorRate_pos hβ hlam
  have hlam1 : lam ≤ 1 := hs.hlam1.le
  have hδi : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) → errorRate p₀ β lam ≤ lam ^ (2 * (i : ℕ)) :=
    fun i _ => (hδle lam hlam hlδ').trans (pow_le_pow_of_le_one hlam.le hlam1 (by omega))
  set ρ := C₀ * errorRate p₀ β lam
  have hρ : 0 < ρ := mul_pos hC₀ hδ0
  have hD : (1 : ℝ) ≤ 2 * roundingRadius (pBeta p₀ β) := by
    linarith [one_le_roundingRadius hs.hp]
  obtain ⟨-, N₁, hN₁⟩ := hTl lam hlam hlT'
  obtain ⟨-, N₂, hN₂⟩ := hLl lam hlam hlL'
  have hmargin : ∀ᶠ N : ℕ in atTop, roundingRadius (pBeta p₀ β) ≤ (N : ℝ) * ρ := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop
      (roundingRadius (pBeta p₀ β) / ρ)] with N hN
    exact (div_le_iff₀ hρ).mp hN
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (((((hZ lam hlam hl').and
    (eventually_log_le (errorRate p₀ β lam) hδ0 (pBeta p₀ β : ℝ))).and
    (eventually_ge_atTop (max N₁ N₂))).and hmargin).and
    (eventually_rounding_absorb (p := pBeta p₀ β) (C := C₁) (lam := lam) hD hδ0))
  refine ⟨N₀, fun N hN γ hγ hγC => ?_⟩
  obtain ⟨⟨⟨⟨⟨hN1, -, hlo, hhi⟩, habs⟩, hNN⟩, hNs⟩, hround⟩ := hN₀ N hN
  have hlog1 : 0 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hplog : (pBeta p₀ β : ℝ) * Real.log ((N : ℝ) + 1) ≤ errorRate p₀ β lam * N := by
    nlinarith [habs]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNδ : 0 ≤ (N : ℝ) * errorRate p₀ β lam := by positivity
  constructor
  · refine le_trans (ofReal_exp_le_ofReal_exp ?_) (le_gibbsMeasure_event hs
      (hN₂ N ((le_max_right _ _).trans hNN)) hround.1 hhi hC₀ hεLC hδ0 hδi hNs hγ hγC)
    nlinarith [hround.2]
  · refine (gibbsMeasure_event_le hs hχ hM (by positivity) (hmeas N lam _)
      (hN₁ N ((le_max_left _ _).trans hNN)) hN1 hlo hC₀ hδ0.le le_rfl hδi hγ hγC).trans
      (ofReal_exp_le_ofReal_exp ?_)
    nlinarith

end TheoremTwo

end MultipoleBKT

end
