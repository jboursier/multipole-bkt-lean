/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.Master
public import MultipoleBKT.Main.TheoremTwo.RateAnalysis
public import MultipoleBKT.Main.TheoremTwo.RouteQuantitative.RateError

/-!
# Theorem 2: partition bounds and count tails at fixed `λ` and `N`

Steps 1, 2 and 5 of the proof of Theorem 2.
The partition lower bound retains the explicit entropy rounding error
before (5.150).
The missing-mass comparison (5.153)
gives the near-unit bad-count exponent, relaxed at (5.154). Step 2 gives the partition upper bound.
The lower-count tail, (5.158),
uses the first-coordinate mass shift and the integrated Hessian gap
`RateSetup.source_gap`, retaining the bad-point penalty until the end.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MultipoleBKT

namespace TheoremTwo

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β M ε₀ C C₁ lam : ℝ} {msf : ℝ → ℕ → ℝ}
  {kmult : ℝ → (ℕ →₀ ℕ) → ℝ} {N : ℕ}

/-! ### The good profile as a point of `Δ_{p,x}` -/

/-- For a configuration `c`, with `S = ∑ i 𝒩_i^good`: `𝒩^good/N ∈ Δ_{p,x}` with
`x = 1 - S/N ∈ [0,1]` and `N x ≤ |I_bad|` (Remark 5.6). -/
theorem goodProfile_facts (hM : 0 ≤ M) (c : Fin N → ℂ × ℂ) (hN : 1 ≤ N) :
    (fun i => (goodProfile p₀ β lam M ε₀ c i : ℝ) / N) ∈ simplex (pBeta p₀ β)
        (1 - ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * goodProfile p₀ β lam M ε₀ c i : ℕ) : ℝ) / N) ∧
      1 - ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * goodProfile p₀ β lam M ε₀ c i : ℕ) : ℝ) / N ∈
        Icc (0 : ℝ) 1 ∧
      (N : ℝ) * (1 - ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) *
          goodProfile p₀ β lam M ε₀ c i : ℕ) : ℝ) / N) ≤
        (badPoints p₀ β lam M ε₀ (matched c)).card := by
  have hsum := sum_good_profile_le (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) c
    (pBeta p₀ β)
  obtain ⟨h1, h2⟩ := profile_mem_simplex hN hsum
  refine ⟨h1, h2, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle := le_card_badPoints_add_profile (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) hM c
  have hle' : (N : ℝ) ≤ (badPoints p₀ β lam M ε₀ (matched c)).card +
      ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * goodProfile p₀ β lam M ε₀ c i : ℕ) : ℝ) := by
    exact_mod_cast hle
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hN0.ne']
  linarith

/-- The bad points pay for the comparison of infima: if `B ≤ θ`, then
`-|I_bad| - N ℐ(𝒩^good/N) ≤ -(1 - θ)|I_bad| - N inf_{Δ_{p,0}} ℐ`. -/
theorem neg_card_sub_le (hs : RateSetup (pBeta p₀ β) (msf lam) (kmult lam) C₁ lam) (hM : 0 ≤ M)
    (c : Fin N → ℂ × ℂ) (hN : 1 ≤ N) {θ : ℝ} (hθ : rateB (pBeta p₀ β) C₁ lam ≤ θ) :
    -1 * ((badPoints p₀ β lam M ε₀ (matched c)).card : ℝ) -
        N * rateFunction (pBeta p₀ β) (msf lam) (kmult lam)
          (fun i => (goodProfile p₀ β lam M ε₀ c i : ℝ) / N) ≤
      -(1 - θ) * (badPoints p₀ β lam M ε₀ (matched c)).card -
        N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) := by
  obtain ⟨hu, hx, hxB⟩ := goodProfile_facts (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) hM c hN
  have h := hs.sInf_sub_le hx hu
  have hB0 := rateB_nonneg (pBeta p₀ β) C₁ lam
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set x := 1 - ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * goodProfile p₀ β lam M ε₀ c i : ℕ) : ℝ) / N
  have h1 : rateB (pBeta p₀ β) C₁ lam * (N * x) ≤ θ * (badPoints p₀ β lam M ε₀ (matched c)).card :=
    mul_le_mul hθ hxB (mul_nonneg hN0 hx.1) (hB0.trans hθ)
  nlinarith [mul_le_mul_of_nonneg_left h hN0]

/-! ### The partition function -/

/-- **Lower bound on `Z`** (equation (5.150)): Proposition 4.62 at a profile `n` with
`‖n/N - γ*‖ ≤ p²/N`, `n_i ≤ N γ*_i ≤ ε₀^{-α} λ^{2i} N`. -/
theorem partitionFunction_ge (hs : RateSetup (pBeta p₀ β) (msf lam) (kmult lam) C₁ lam)
    {γs : Fin (pBeta p₀ β) → ℝ} (hγs : γs ∈ simplex (pBeta p₀ β) 0)
    (hmin : IsMinOn (rateFunction (pBeta p₀ β) (msf lam) (kmult lam)) (simplex (pBeta p₀ β) 0) γs)
    {A : ℝ} (hA : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) → γs i ≤ A * lam ^ (2 * (i : ℕ)))
    (hAε : A ≤ ε₀ ^ (-alphaExponent β)) (hL : LowerProfileBound χ p₀ β M ε₀ C lam msf kmult N)
    (hN : 2 ≤ N) :
    ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
        N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) -
        C * N * errorRate p₀ β lam - roundingConst (pBeta p₀ β) C₁ ((pBeta p₀ β : ℝ) ^ 2) *
          (Real.log N + |Real.log lam|))) ≤ partitionFunction χ N β lam := by
  set Ir := rateFunction (pBeta p₀ β) (msf lam) (kmult lam)
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨n, hn, hnle, hnclose⟩ := exists_profile hs.hp hγs hN1
  have h420 : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
      (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N := by
    intro i hi
    have hl : 0 ≤ lam ^ (2 * (i : ℕ)) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
    calc (n i : ℝ) ≤ N * γs i := hnle i hi
      _ ≤ N * (A * lam ^ (2 * (i : ℕ))) := mul_le_mul_of_nonneg_left (hA i hi) hN0.le
      _ ≤ N * (ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAε hl) hN0.le
      _ = ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N := by ring
  have hmem : (fun i => (n i : ℝ) / N) ∈ simplex (pBeta p₀ β) 0 := by
    have := (profile_mem_simplex hN1 hn.le).1
    rwa [hn, div_self hN0.ne', sub_self] at this
  have hnorm : ‖(fun i => (n i : ℝ) / N) - γs‖ ≤ (pBeta p₀ β : ℝ) ^ 2 / N :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Real.norm_eq_abs, Pi.sub_apply]; exact hnclose i
  have hD : (1 : ℝ) ≤ (pBeta p₀ β : ℝ) ^ 2 := by
    have hp : (1 : ℝ) ≤ pBeta p₀ β := by exact_mod_cast hs.hp
    nlinarith
  have herror := rate_rounding_error hs hD hN hmem hγs hnorm
  have hinf : sInf (Ir '' simplex (pBeta p₀ β) 0) = Ir γs :=
    RateSetup.sInf_eq_of_isMinOn hγs hmin
  have hlow := master_lower hL n hn h420 Set.univ (Set.subset_univ _)
  rw [← partitionFunction_eq] at hlow
  refine le_trans (ofReal_exp_le_ofReal_exp ?_) hlow
  rw [hinf]
  have hI := mul_le_mul_of_nonneg_left
    (le_abs_self (Ir (fun i => (n i : ℝ) / N) - Ir γs)) hN0.le
  nlinarith

/-- **Upper bound on `Z`** (Step 2). -/
theorem partitionFunction_le (hs : RateSetup (pBeta p₀ β) (msf lam) (kmult lam) C₁ lam)
    (hχ : IsMollifier χ) (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀)
    (hmeas : Measurable fun c : Fin N → ℂ × ℂ => (badPoints p₀ β lam M ε₀ (matched c)).card)
    (hU : UpperProfileBound χ p₀ β M ε₀ 1 C lam msf kmult N) (hN : 1 ≤ N) :
    partitionFunction χ N β lam ≤ ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
        N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) +
        C * N * errorRate p₀ β lam + (pBeta p₀ β) * Real.log ((N : ℝ) + 1))) := by
  have hθ : rateB (pBeta p₀ β) C₁ lam ≤ 1 := hs.hB.trans (by norm_num)
  have h := master_upper hχ hs.hlam hM hε₀ hmeas hU Set.univ
    (-(N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0)))
    fun c _ => by
      have := neg_card_sub_le (ε₀ := ε₀) hs hM c hN hθ
      simp only [sub_self, neg_zero, zero_mul, zero_sub] at this
      exact this
  rw [partitionFunction_eq]
  refine h.trans (ofReal_exp_le_ofReal_exp (le_of_eq ?_))
  ring

/-! ### The bad points -/

/-- The near-unit bad-count exponent before (5.154). -/
theorem gibbsMeasure_badPoints_sharp_le (hs : RateSetup (pBeta p₀ β) (msf lam) (kmult lam) C₁ lam)
    (hχ : IsMollifier χ) (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀)
    (hmeas : Measurable fun c : Fin N → ℂ × ℂ => (badPoints p₀ β lam M ε₀ (matched c)).card)
    (hU : UpperProfileBound χ p₀ β M ε₀ 1 C lam msf kmult N) (hN : 1 ≤ N) {C' : ℝ}
    (hZ : ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
        N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) -
        C' * N * errorRate p₀ β lam)) ≤ partitionFunction χ N β lam) (s : ℝ) :
    gibbsMeasure χ N β lam {c | s ≤ (badPoints p₀ β lam M ε₀ (matched c)).card} ≤
      ENNReal.ofReal (Real.exp (-(1 - rateB (pBeta p₀ β) C₁ lam) * s + (C + C') * N * errorRate p₀ β lam +
        (pBeta p₀ β) * Real.log ((N : ℝ) + 1))) := by
  set inf0 := sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0)
  have h := master_upper hχ hs.hlam hM hε₀ hmeas hU
    {c | s ≤ (badPoints p₀ β lam M ε₀ (matched c)).card} (-(1 - rateB (pBeta p₀ β) C₁ lam) * s - N * inf0)
    fun c hc => by
      have := neg_card_sub_le (ε₀ := ε₀) hs hM c hN le_rfl
      have hc' : s ≤ (badPoints p₀ β lam M ε₀ (matched c)).card := hc
      nlinarith [mul_le_mul_of_nonneg_left hc' (by linarith [hs.hB] :
        0 ≤ 1 - rateB (pBeta p₀ β) C₁ lam)]
  rw [gibbsMeasure_eq]
  refine (inv_mul_le_ofReal_exp hZ h).trans (ofReal_exp_le_ofReal_exp (le_of_eq ?_))
  ring

/-- **The number of bad points** (equation (5.154)):
`ℙ(|I_bad| ≥ s) ≤ e^{-s/2 + (C + C') N δ + p log (N+1)}`. -/
theorem gibbsMeasure_badPoints_le (hs : RateSetup (pBeta p₀ β) (msf lam) (kmult lam) C₁ lam)
    (hχ : IsMollifier χ) (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀)
    (hmeas : Measurable fun c : Fin N → ℂ × ℂ => (badPoints p₀ β lam M ε₀ (matched c)).card)
    (hU : UpperProfileBound χ p₀ β M ε₀ 1 C lam msf kmult N) (hN : 1 ≤ N) {C' : ℝ}
    (hZ : ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
        N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) -
        C' * N * errorRate p₀ β lam)) ≤ partitionFunction χ N β lam) (s : ℝ) :
    gibbsMeasure χ N β lam {c | s ≤ (badPoints p₀ β lam M ε₀ (matched c)).card} ≤
      ENNReal.ofReal (Real.exp (-s / 2 + (C + C') * N * errorRate p₀ β lam +
        (pBeta p₀ β) * Real.log ((N : ℝ) + 1))) := by
  have hsub : {c : Fin N → ℂ × ℂ | s ≤ (badPoints p₀ β lam M ε₀ (matched c)).card} ⊆
      {c | max s 0 ≤ (badPoints p₀ β lam M ε₀ (matched c)).card} := by
    intro c hc
    exact max_le (show s ≤ (badPoints p₀ β lam M ε₀ (matched c)).card from hc)
      (Nat.cast_nonneg _)
  refine (measure_mono hsub).trans ((gibbsMeasure_badPoints_sharp_le hs hχ hM hε₀
    hmeas hU hN hZ (max s 0)).trans (ofReal_exp_le_ofReal_exp ?_))
  have hB := hs.hB
  have hB0 := rateB_nonneg (pBeta p₀ β) C₁ lam
  have hm : 0 ≤ max s 0 := le_max_right _ _
  have hms : s ≤ max s 0 := le_max_left _ _
  nlinarith [mul_le_mul_of_nonneg_right hB hm]

/-! ### Step 5: the lower tail of `𝒩_k` -/

/-- **The lower tail** (equation (5.158)): if `a ≤ γ*_i / 4` (`i ≥ 1`, `k = i + 1`), then
`ℙ(𝒩_k ≤ a N) ≤ e^{-N γ*_i/8 + (C + C') N δ + p log (N+1)}`. -/
theorem gibbsMeasure_multipoleCount_le
    (hs : RateSetup (pBeta p₀ β) (msf lam) (kmult lam) C₁ lam)
    (hχ : IsMollifier χ) (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀)
    (hmeas : Measurable fun c : Fin N → ℂ × ℂ => (badPoints p₀ β lam M ε₀ (matched c)).card)
    (hU : UpperProfileBound χ p₀ β M ε₀ 1 C lam msf kmult N) (hN : 1 ≤ N) {C' : ℝ}
    (hZ : ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
        N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) -
        C' * N * errorRate p₀ β lam)) ≤ partitionFunction χ N β lam)
    {γs : Fin (pBeta p₀ β) → ℝ} (hγs : γs ∈ simplex (pBeta p₀ β) 0)
    (hmin : IsMinOn (rateFunction (pBeta p₀ β) (msf lam) (kmult lam)) (simplex (pBeta p₀ β) 0) γs)
    (hpos : ∀ k, 0 < γs k) (i : Fin (pBeta p₀ β)) (hi : 1 ≤ (i : ℕ)) {a : ℝ}
    (ha : a ≤ γs i / 4) :
    gibbsMeasure χ N β lam {c | (multipoleCount M lam c ((i : ℕ) + 1) : ℝ) ≤ a * N} ≤
      ENNReal.ofReal (Real.exp (-(N * (γs i / 8)) + (C + C') * N * errorRate p₀ β lam +
        (pBeta p₀ β) * Real.log ((N : ℝ) + 1))) := by
  set Ir := rateFunction (pBeta p₀ β) (msf lam) (kmult lam)
  set inf0 := sInf (Ir '' simplex (pBeta p₀ β) 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hinf : inf0 = Ir γs := RateSetup.sInf_eq_of_isMinOn hγs hmin
  have h := master_upper hχ hs.hlam hM hε₀ hmeas hU
    {c | (multipoleCount M lam c ((i : ℕ) + 1) : ℝ) ≤ a * N} (-(N * inf0) - N * (γs i / 8))
    fun c hc => by
      obtain ⟨hu, hx, hxB⟩ := goodProfile_facts (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀)
        hM c hN
      set u := fun j => (goodProfile p₀ β lam M ε₀ c j : ℝ) / N
      set x := 1 - ((∑ j : Fin (pBeta p₀ β), ((j : ℕ) + 1) * goodProfile p₀ β lam M ε₀ c j : ℕ) :
        ℝ) / N
      obtain ⟨η, hη, hηu, hηle⟩ := hs.exists_shift hx hu
      -- `η_i = u_i ≤ 𝒩_{i+1}/N ≤ a ≤ γ*_i/4`
      have hηi : η i ≤ γs i / 4 := by
        rw [hηu i hi]
        have hg := goodMultipoleCount_le_multipoleCount (p₀ := p₀) (β := β) (lam := lam)
          (M := M) (ε₀ := ε₀) c ((i : ℕ) + 1)
        have hc' : (multipoleCount M lam c ((i : ℕ) + 1) : ℝ) ≤ a * N := hc
        have : (goodProfile p₀ β lam M ε₀ c i : ℝ) ≤ a * N :=
          (Nat.cast_le.mpr hg).trans hc'
        calc u i = (goodProfile p₀ β lam M ε₀ c i : ℝ) / N := rfl
          _ ≤ a * N / N := div_le_div_of_nonneg_right this hN0.le
          _ = a := by field_simp
          _ ≤ γs i / 4 := ha
      have hgap := hs.source_gap hγs hmin hη i
      have hmax : max (η i) (γs i) = γs i := max_eq_right (by linarith [hpos i])
      rw [hmax] at hgap
      have hsq : γs i / 8 ≤ (η i - γs i) ^ 2 / (4 * γs i) := by
        rw [le_div_iff₀ (mul_pos (by norm_num) (hpos i))]
        have hη0 := (hη.1 i).1
        nlinarith [sq_nonneg (η i - γs i / 4)]
      have hθ : rateB (pBeta p₀ β) C₁ lam ≤ 1 / 2 := hs.hB.trans (by norm_num)
      have h1 : Ir η - Ir u ≤ rateB (pBeta p₀ β) C₁ lam * x := by linarith
      have h2 : rateB (pBeta p₀ β) C₁ lam * (N * x) ≤
          (1 / 2) * (badPoints p₀ β lam M ε₀ (matched c)).card :=
        mul_le_mul hθ hxB (mul_nonneg hN0.le hx.1) (by norm_num)
      -- Keep the bad-point penalty in the written profile estimate before summing.
      have hprofile : -1 * ((badPoints p₀ β lam M ε₀ (matched c)).card : ℝ) - N * Ir u ≤
          -N * (Ir η - Ir γs) -
            (badPoints p₀ β lam M ε₀ (matched c)).card / 2 - N * Ir γs := by
        nlinarith [mul_le_mul_of_nonneg_left h1 hN0.le]
      rw [hinf]
      nlinarith [mul_le_mul_of_nonneg_left (hsq.trans hgap) hN0.le,
        Nat.cast_nonneg (α := ℝ) (badPoints p₀ β lam M ε₀ (matched c)).card]
  rw [gibbsMeasure_eq]
  refine (inv_mul_le_ofReal_exp hZ h).trans (ofReal_exp_le_ofReal_exp (le_of_eq ?_))
  ring

end TheoremTwo

end MultipoleBKT

end
