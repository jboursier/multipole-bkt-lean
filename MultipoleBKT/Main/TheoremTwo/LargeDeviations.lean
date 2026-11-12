/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.Bounds
public import MultipoleBKT.Main.TheoremTwo.RouteQuantitative.RateError
public import MultipoleBKT.Main.TheoremTwo.RouteQuantitative.Contraction

/-!
# Theorem 2: large deviations at fixed `λ` and `N`

Step 3 of the proof of Theorem 2.
The upper bound (5.156) uses the segment from `z` to `max(z, γ)`
and the one-sided rate comparison, then sums the good profiles.
For the lower bound, a minimizer of the rate on the ball is contracted by
`D_p/(Nρ)` and rounded. The resulting profile stays in the ball and lies
within `2D_p/N` of that minimizer. The direct entropy comparison and the
gradient bound for the cluster term give `C(log N + |log λ|)`.
The displayed bound retains this error before its absorption in item (4).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MultipoleBKT

namespace TheoremTwo

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β M ε₀ C C₁ lam : ℝ} {msf : ℝ → ℕ → ℝ}
  {kmult : ℝ → (ℕ →₀ ℕ) → ℝ} {N : ℕ}

/-- The ball `{γ' ∈ Δ_{p,0} : ‖γ' - γ‖ ≤ ρ}` is a compact subset of `Δ_{p,0}`. -/
theorem isCompact_ball_simplex {p : ℕ} (γ : Fin p → ℝ) (ρ : ℝ) :
    IsCompact {γ' | γ' ∈ simplex p 0 ∧ ‖γ' - γ‖ ≤ ρ} := by
  have : {γ' | γ' ∈ simplex p 0 ∧ ‖γ' - γ‖ ≤ ρ} = simplex p 0 ∩ Metric.closedBall γ ρ := by
    ext γ'
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [this]
  exact (isCompact_simplex 0).inter_right Metric.isClosed_closedBall

/-- **The upper bound of (2.52)** (equation (5.156)). -/
theorem gibbsMeasure_event_le (hs : RateSetup (pBeta p₀ β) (msf lam) (kmult lam) C₁ lam)
    (hχ : IsMollifier χ) (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀)
    (hmeas : Measurable fun c : Fin N → ℂ × ℂ => (badPoints p₀ β lam M ε₀ (matched c)).card)
    {T : ℝ} (hU : UpperProfileBound χ p₀ β M ε₀ T C lam msf kmult N) (hN : 1 ≤ N) {C' : ℝ}
    (hZ : ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
        N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) -
        C' * N * errorRate p₀ β lam)) ≤ partitionFunction χ N β lam)
    {C₀ : ℝ} (hC₀ : 0 < C₀) (hδ0 : 0 ≤ errorRate p₀ β lam)
    (hT : Real.log ((pBeta p₀ β).factorial : ℝ) + |Real.log (2 * C₀)| + |Real.log C₁| + 1 ≤ T)
    (hδ : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) → errorRate p₀ β lam ≤ lam ^ (2 * (i : ℕ)))
    {γ : Fin (pBeta p₀ β) → ℝ} (hγ : γ ∈ simplex (pBeta p₀ β) 0)
    (hγC : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) → γ i ≤ C₀ * lam ^ (2 * (i : ℕ))) :
    gibbsMeasure χ N β lam {c | ∀ i : Fin (pBeta p₀ β),
        |(multipoleCount M lam c ((i : ℕ) + 1) : ℝ) - N * γ i| ≤ C₀ * N * errorRate p₀ β lam} ≤
      ENNReal.ofReal (Real.exp (-N * (sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) ''
            {γ' | γ' ∈ simplex (pBeta p₀ β) 0 ∧ ‖γ' - γ‖ ≤ C₀ * errorRate p₀ β lam}) -
          sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0)) +
        (C + C') * N * errorRate p₀ β lam + (pBeta p₀ β) * Real.log ((N : ℝ) + 1))) := by
  set Ir := rateFunction (pBeta p₀ β) (msf lam) (kmult lam)
  set δ := errorRate p₀ β lam
  set Bγ := {γ' | γ' ∈ simplex (pBeta p₀ β) 0 ∧ ‖γ' - γ‖ ≤ C₀ * δ}
  set J := sInf (Ir '' Bγ)
  set L := Real.log ((pBeta p₀ β).factorial : ℝ) + |Real.log (2 * C₀)| + |Real.log C₁| + 1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : 0 ≤ C₀ * δ := mul_nonneg hC₀.le hδ0
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log ((pBeta p₀ β).factorial : ℝ) := Real.log_nonneg
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    positivity
  have hbdd : BddBelow (Ir '' Bγ) :=
    (hs.bddBelow 0).mono (Set.image_mono fun γ' hγ' => hγ'.1)
  have h := master_upper hχ hs.hlam hM hε₀ hmeas hU {c | ∀ i : Fin (pBeta p₀ β),
      |(multipoleCount M lam c ((i : ℕ) + 1) : ℝ) - N * γ i| ≤ C₀ * N * δ} (-(N * J))
    fun c hc => by
      obtain ⟨hu, hx, hxB⟩ := goodProfile_facts (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀)
        hM c hN
      set u := fun j => (goodProfile p₀ β lam M ε₀ c j : ℝ) / N
      set x := 1 - ((∑ j : Fin (pBeta p₀ β), ((j : ℕ) + 1) * goodProfile p₀ β lam M ε₀ c j : ℕ) :
        ℝ) / N
      set z : Fin (pBeta p₀ β) → ℝ := fun j => (multipoleCount M lam c ((j : ℕ) + 1) : ℝ) / N
      have hz0 : ∀ j, 0 ≤ z j := fun j => by positivity
      have hzsum : ∑ j : Fin (pBeta p₀ β), ((j : ℕ) + 1 : ℝ) * z j ≤ 1 := by
        have h1 := sum_profile_le (M := M) (lam := lam) c (pBeta p₀ β)
        have h2 : ((∑ j : Fin (pBeta p₀ β), ((j : ℕ) + 1) *
            multipoleCount M lam c ((j : ℕ) + 1) : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
        have h3 : ∑ j : Fin (pBeta p₀ β), ((j : ℕ) + 1 : ℝ) * z j =
            ((∑ j : Fin (pBeta p₀ β), ((j : ℕ) + 1) *
              multipoleCount M lam c ((j : ℕ) + 1) : ℕ) : ℝ) / N := by
          push_cast
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [z]
          ring
        rw [h3, div_le_one hN0]
        exact h2
      have hzγ : ∀ j, |z j - γ j| ≤ C₀ * δ := by
        intro j
        have h1 := hc j
        have h2 : z j - γ j = ((multipoleCount M lam c ((j : ℕ) + 1) : ℝ) - N * γ j) / N := by
          simp only [z]; field_simp
        rw [h2, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
        linarith
      obtain ⟨η, hη, hηγ, hzη⟩ := exists_mem_simplex_ge hγ hρ hz0 hzsum hzγ
      have huz : ∀ j, u j ≤ z j := fun j => by
        have hg := goodMultipoleCount_le_multipoleCount (p₀ := p₀) (β := β) (lam := lam)
          (M := M) (ε₀ := ε₀) c ((j : ℕ) + 1)
        exact div_le_div_of_nonneg_right (by exact_mod_cast hg) hN0.le
      have hu0 : ∀ j, 0 ≤ u j := fun j => by positivity
      have huη : ∀ j, u j ≤ η j := fun j => (huz j).trans (hzη j)
      have hηA : ∀ j : Fin (pBeta p₀ β), 1 ≤ (j : ℕ) → η j ≤ (2 * C₀) * lam ^ (2 * (j : ℕ)) := by
        intro j hj
        have h1 : |η j - γ j| ≤ C₀ * δ := by
          have := norm_le_pi_norm (η - γ) j
          rw [Pi.sub_apply, Real.norm_eq_abs] at this
          exact this.trans hηγ
        have h2 := (abs_le.mp h1).2
        have h3 := hγC j hj
        have h4 := mul_le_mul_of_nonneg_left (hδ j hj) hC₀.le
        linarith
      have hlip := hs.sub_le_of_le (by positivity : (0 : ℝ) < 2 * C₀) hη hηA hu0 huη
      have hsum : ∑ j, (η j - u j) ≤ x := by
        have h1 : ∑ j, (η j - u j) ≤ ∑ j : Fin (pBeta p₀ β), ((j : ℕ) + 1 : ℝ) * (η j - u j) :=
          Finset.sum_le_sum fun j _ => by
            have : 0 ≤ η j - u j := sub_nonneg.mpr (huη j)
            have : (1 : ℝ) ≤ (j : ℕ) + 1 := by
              linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ (j : ℕ))]
            nlinarith
        have h2 : ∑ j : Fin (pBeta p₀ β), ((j : ℕ) + 1 : ℝ) * (η j - u j) = 1 - (1 - x) := by
          rw [Finset.sum_congr rfl fun j _ => mul_sub _ _ _, Finset.sum_sub_distrib]
          have hη2 := hη.2
          have hu2 := hu.2
          rw [sub_zero] at hη2
          rw [hη2, hu2]
        rw [h2] at h1
        linarith
      have hJ : J ≤ Ir η := csInf_le hbdd ⟨η, ⟨hη, hηγ⟩, rfl⟩
      have hTL : L ≤ T := hT
      have hB0 : (0 : ℝ) ≤ (badPoints p₀ β lam M ε₀ (matched c)).card := Nat.cast_nonneg _
      have hk1 : Ir η - Ir u ≤ L * x := hlip.trans (mul_le_mul_of_nonneg_left hsum hL0)
      have hk2 : L * (N * x) ≤ T * (badPoints p₀ β lam M ε₀ (matched c)).card :=
        mul_le_mul hTL hxB (mul_nonneg hN0.le hx.1) (hL0.trans hTL)
      nlinarith [mul_le_mul_of_nonneg_left hk1 hN0.le]
  rw [gibbsMeasure_eq]
  refine (inv_mul_le_ofReal_exp hZ h).trans (ofReal_exp_le_ofReal_exp (le_of_eq ?_))
  ring

/-- **The lower bound of (2.52)**. -/
theorem le_gibbsMeasure_event (hs : RateSetup (pBeta p₀ β) (msf lam) (kmult lam) C₁ lam)
    (hL : LowerProfileBound χ p₀ β M ε₀ C lam msf kmult N) (hN : 2 ≤ N) {C' : ℝ}
    (hZ : partitionFunction χ N β lam ≤ ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
        N * sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0) +
        C' * N * errorRate p₀ β lam + (pBeta p₀ β) * Real.log ((N : ℝ) + 1))))
    {C₀ : ℝ} (hC₀ : 0 < C₀) (hAε : 2 * C₀ ≤ ε₀ ^ (-alphaExponent β))
    (hδ0 : 0 < errorRate p₀ β lam)
    (hδ : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) → errorRate p₀ β lam ≤ lam ^ (2 * (i : ℕ)))
    (hmargin : roundingRadius (pBeta p₀ β) ≤ N * (C₀ * errorRate p₀ β lam))
    {γ : Fin (pBeta p₀ β) → ℝ} (hγ : γ ∈ simplex (pBeta p₀ β) 0)
    (hγC : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) → γ i ≤ C₀ * lam ^ (2 * (i : ℕ))) :
    ENNReal.ofReal (Real.exp (-N * (sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) ''
            {γ' | γ' ∈ simplex (pBeta p₀ β) 0 ∧ ‖γ' - γ‖ ≤ C₀ * errorRate p₀ β lam}) -
          sInf (rateFunction (pBeta p₀ β) (msf lam) (kmult lam) '' simplex (pBeta p₀ β) 0)) -
        (C + C') * N * errorRate p₀ β lam - (pBeta p₀ β) * Real.log ((N : ℝ) + 1) -
        roundingConst (pBeta p₀ β) C₁ (2 * roundingRadius (pBeta p₀ β)) *
          (Real.log N + |Real.log lam|))) ≤
      gibbsMeasure χ N β lam {c | ∀ i : Fin (pBeta p₀ β),
        |(multipoleCount M lam c ((i : ℕ) + 1) : ℝ) - N * γ i| ≤ C₀ * N * errorRate p₀ β lam} := by
  set Ir := rateFunction (pBeta p₀ β) (msf lam) (kmult lam)
  set δ := errorRate p₀ β lam
  set ρ := C₀ * δ
  set Bγ := {γ' | γ' ∈ simplex (pBeta p₀ β) 0 ∧ ‖γ' - γ‖ ≤ ρ}
  set J := sInf (Ir '' Bγ)
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hρ : 0 < ρ := mul_pos hC₀ hδ0
  -- a minimizer of `ℐ` on the ball
  obtain ⟨η, hηB, hηmin⟩ := (isCompact_ball_simplex γ ρ).exists_isMinOn
    ⟨γ, hγ, by rw [sub_self, norm_zero]; exact hρ.le⟩
    ((hs.continuousOn 0).mono fun γ' hγ' => hγ'.1)
  have hJ : J = Ir η := IsLeast.csInf_eq ⟨⟨η, hηB, rfl⟩, by rintro _ ⟨η', hη', rfl⟩; exact hηmin hη'⟩
  -- Contract by `D_p/(Nρ)`, then take floors, with distance at most `2D_p/N`.
  obtain ⟨n, hn, hnle, hvγ, hvη⟩ := exists_profile_in_ball hs.hp hN1 hγ hηB.1 hρ hηB.2 hmargin
  set v : Fin (pBeta p₀ β) → ℝ := fun i => (n i : ℝ) / N
  have hv : v ∈ simplex (pBeta p₀ β) 0 := by
    have := (profile_mem_simplex hN1 hn.le).1
    rwa [hn, div_self hN0.ne', sub_self] at this
  have hD : (1 : ℝ) ≤ 2 * roundingRadius (pBeta p₀ β) := by
    linarith [one_le_roundingRadius hs.hp]
  have herror := rate_rounding_error hs hD hN hv hηB.1 hvη
  have hIv : (N : ℝ) * (Ir v - J) ≤
      roundingConst (pBeta p₀ β) C₁ (2 * roundingRadius (pBeta p₀ β)) *
        (Real.log N + |Real.log lam|) := by
    rw [hJ]
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) hN0.le).trans herror
  -- The same profile satisfies the admissibility condition of Proposition 4.62.
  have h420 : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
      (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N := by
    intro i hi
    have h3 : γ i + ρ ≤ 2 * C₀ * lam ^ (2 * (i : ℕ)) := by
      have := hγC i hi
      have := mul_le_mul_of_nonneg_left (hδ i hi) hC₀.le
      dsimp [ρ, δ]
      linarith
    have hl : 0 ≤ lam ^ (2 * (i : ℕ)) := pow_nonneg hs.hlam.le _
    calc (n i : ℝ) ≤ N * (γ i + ρ) := hnle i hi
      _ ≤ N * (2 * C₀ * lam ^ (2 * (i : ℕ))) := mul_le_mul_of_nonneg_left h3 hN0.le
      _ ≤ N * (ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAε hl) hN0.le
      _ = ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N := by ring
  -- the event of the gate is contained in the event of (2.52)
  have hE : {c : Fin N → ℂ × ℂ |
      (∀ i : Fin (pBeta p₀ β), multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
      ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤ ε₀ * truncationScale p₀ β lam} ⊆
      {c | ∀ i : Fin (pBeta p₀ β),
        |(multipoleCount M lam c ((i : ℕ) + 1) : ℝ) - N * γ i| ≤ C₀ * N * δ} := by
    rintro c ⟨hc, -⟩ i
    rw [hc i]
    have h1 : |v i - γ i| ≤ ρ := by
      have := norm_le_pi_norm (v - γ) i
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      exact this.trans hvγ
    have h2 : (n i : ℝ) - N * γ i = N * (v i - γ i) := by simp only [v]; field_simp
    rw [h2, abs_mul, abs_of_pos hN0]
    calc (N : ℝ) * |v i - γ i| ≤ N * ρ := mul_le_mul_of_nonneg_left h1 hN0.le
      _ = C₀ * N * δ := by simp only [ρ]; ring
  have hlow := master_lower hL n hn h420 _ hE
  rw [gibbsMeasure_eq]
  refine le_trans (ofReal_exp_le_ofReal_exp ?_) (ofReal_exp_le_inv_mul hZ hlow)
  nlinarith

end TheoremTwo

end MultipoleBKT

end
