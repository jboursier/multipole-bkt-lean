/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoLow

/-!
# Lemma 5.41: control of the bad points of type `(2,1)`

The paper: Lemma 5.41 (including the partition enumeration and series in its proof).

* `lemma_5_41_low` (item (1), `β ∈ (2, 4)`): for every `t ≥ 1` there is `ε̃₀ > 0` such that for
  every `ε₀ ∈ (0, ε̃₀)` there is `C` with, for `λ` small and `N` large, for every `n`,
  `(N/n)ⁿ Z^{(2,1)}_{bad,n} e^{tn} / (N C_{β,λ,ε₀})ⁿ ≤ exp(C N R_{β,λ}^{-2}
    (1 + |log λ| 𝟙_{β = β_{p(β)+1}}))`,
  written multiplicatively.

The proof: `Z ≤ n! y^{-n} exp(∑_{m > p} bLow(m) yᵐ/m!)` (`typeTwoOnePartitionFunction_le_exp`) at
`y = e^t / C_{β,λ,ε₀}` gives the prefactor `(N C_{β,λ,ε₀})ⁿ (n/N)ⁿ e^{-tn}` (since `n! ≤ nⁿ`), and
the series, bounded at the larger `y₀ = e^t/(c₀ λ^{2-β})` (`c₀ = 𝒵_β/2`, (4.12)), is
`≤ A ∑ m xᵐ ≤ A` with `x = e K₊ e^t ε₀^{4-β}/c₀ ≤ 1/4` (`blockTerm_le_low`,
`sum_succ_mul_pow_le`); finally `log(h/λ) ≤ (2/(4-β)) |log λ|`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset MultipoleIntegral Filter
open scoped ENNReal

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β M : ℝ}

/-- `log(h/λ) ≤ (2/(4-β)) |log λ|` for `β < 4`, `0 < λ ≤ 1`, `ε₀ ≤ 1`, `λ ≤ h = ε₀ R`. -/
theorem log_cutoff_div_le (hβ4 : β < 4) {lam ε₀ : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) :
    Real.log (cutoff p₀ β lam ε₀ / lam) ≤ 2 / (4 - β) * |Real.log lam| := by
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have h4 : 0 < 4 - β := by linarith
  have hh : 0 < cutoff p₀ β lam ε₀ := by unfold cutoff; positivity
  have hle : cutoff p₀ β lam ε₀ / lam ≤ lam ^ (-(2 / (4 - β))) := by
    unfold cutoff
    rw [Appendix.truncationScale_of_lt hβ4 hlam, div_le_iff₀ hlam]
    calc ε₀ * lam ^ (-(β - 2) / (4 - β)) ≤ 1 * lam ^ (-(β - 2) / (4 - β)) :=
          mul_le_mul_of_nonneg_right hε₀1 (Real.rpow_nonneg hlam.le _)
      _ = lam ^ (-(2 / (4 - β))) * lam := by
          rw [one_mul, ← Real.rpow_add_one hlam.ne']
          congr 1
          field_simp
          ring
  have hlog : Real.log lam ≤ 0 := Real.log_nonpos hlam.le hlam1
  calc Real.log (cutoff p₀ β lam ε₀ / lam) ≤ Real.log (lam ^ (-(2 / (4 - β)))) :=
        Real.log_le_log (div_pos hh hlam) hle
    _ = 2 / (4 - β) * |Real.log lam| := by
        rw [Real.log_rpow hlam, abs_of_nonpos hlog]
        ring

/-- **Lemma 5.41 (1)** (Lemma 5.41, `β ∈ (2, 4)`, the paper). -/
theorem lemma_5_41_low (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) (hβ4 : β < 4)
    (hM : 0 ≤ M) :
    ∀ t : ℝ, 1 ≤ t → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ → ∃ C : ℝ, 0 < C ∧
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
        typeTwoOnePartitionFunction χ p₀ β lam M ε₀ N n ≤
          ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
              (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) / N) ^ n *
            (Real.exp (-(t * n)) * Real.exp (C * N * ((criticalScale β lam).toReal ^ 2)⁻¹ *
              (1 + if β = transitionBeta (pBeta p₀ β + 1) then |Real.log lam| else 0)))) := by
  intro t ht
  have hZ := dipoleConstant_pos hχ hβ
  set c₀ := 1 / 2 * dipoleConstant χ β with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set Kp := max 1 (innerConst χ β M) with hKp
  have hKp1 : 1 ≤ Kp := le_max_left _ _
  have h4 : 0 < 4 - β := by linarith
  set a := c₀ / (4 * Real.exp 1 * Kp * Real.exp t) with ha
  have ha0 : 0 < a := by positivity
  refine ⟨min 1 (a ^ (1 / (4 - β))), lt_min one_pos (Real.rpow_pos_of_pos ha0 _),
    fun ε₀ hε₀ hlt => ?_⟩
  have hε₀1 : ε₀ ≤ 1 := (hlt.trans_le (min_le_left _ _)).le
  -- the ratio of the geometric series
  set x := Real.exp 1 * Kp * Real.exp t * ε₀ ^ (4 - β) / c₀ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx4 : x ≤ 1 / 4 := by
    have hε : ε₀ ^ (4 - β) ≤ a := by
      calc ε₀ ^ (4 - β) ≤ (a ^ (1 / (4 - β))) ^ (4 - β) :=
            Real.rpow_le_rpow hε₀.le (hlt.trans_le (min_le_right _ _)).le h4.le
        _ = a := by
            rw [← Real.rpow_mul ha0.le, show 1 / (4 - β) * (4 - β) = 1 by field_simp,
              Real.rpow_one]
    rw [hx, div_le_iff₀ hc₀0]
    calc Real.exp 1 * Kp * Real.exp t * ε₀ ^ (4 - β)
        ≤ Real.exp 1 * Kp * Real.exp t * a := by gcongr
      _ = 1 / 4 * c₀ := by rw [ha]; field_simp
  set E := exponentMin p₀ β
  have hE := exponentMin_pos (p₀ := p₀) hβ4
  set C₂ := Real.exp (β * kernelConst χ) * (2 * Real.pi) * (1 + 1 / E) * ε₀ ^ (-(2 : ℝ)) with hC₂
  have hC₂0 : 0 < C₂ := by positivity
  refine ⟨C₂ * max 1 (2 / (4 - β)), by positivity, ?_⟩
  obtain ⟨lam₁, hlam₁, hnorm⟩ := eventually_half_le_normalization hχ hβ hp₀ hε₀ hε₀1
  obtain ⟨lam₂, hlam₂, hcut⟩ := eventually_lam_le_cutoff hβ hp₀ hε₀
  refine ⟨min lam₁ lam₂, lt_min hlam₁ hlam₂, fun lam hlam hlt' => ?_⟩
  obtain ⟨hlam1, hlh⟩ := hcut lam hlam (hlt'.trans_le (min_le_right _ _))
  filter_upwards [hnorm lam hlam (hlt'.trans_le (min_le_left _ _)), eventually_ge_atTop 1]
    with N hNC hN1 n
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlb : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  set Cε := truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam)
  have hCε : c₀ * lam ^ (2 - β) ≤ Cε := hNC
  have hCε0 : 0 < Cε := lt_of_lt_of_le (by positivity) hCε
  set h := cutoff p₀ β lam ε₀
  set b : ℕ → ℝ := fun m => if pBeta p₀ β < m then blockBoundLow χ β lam M h N m else 0 with hb
  have hb0 : ∀ m, 0 ≤ b m := fun m => by
    simp only [hb]
    split_ifs with hm
    · exact blockBoundLow_nonneg hβ4 hlam hlh N (exponent_nonneg (p₀ := p₀) hβ4 hm)
    · exact le_rfl
  have hblock : ∀ T : Finset (Fin n), pBeta p₀ β < T.card →
      ∫⁻ y : T → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam h N) y ≤
        ENNReal.ofReal (b T.card) := by
    intro T hT
    have hTc : Fintype.card T = T.card := Fintype.card_coe T
    have : Nonempty T := Fintype.card_pos_iff.1 (by omega)
    have hm := exponent_nonneg (p₀ := p₀) hβ4 hT
    rw [← hTc] at hm
    have h1 := lintegral_blockWeight_cut_le_low (ι := T) hχ (by linarith) hβ4 hM hlam hlh N hm
    rw [hTc] at h1
    simp only [hb, ite_eq_left hT]
    exact h1
  set y := Real.exp t / Cε
  have hy : 0 < y := by positivity
  refine (typeTwoOnePartitionFunction_le_exp hχ hlam p₀ ε₀ N b hb0 hblock hy).trans
    (ENNReal.ofReal_le_ofReal ?_)
  -- the prefactor
  have hpre : (n.factorial : ℝ) / y ^ n ≤
      (N * Cε) ^ n * ((n : ℝ) / N) ^ n * Real.exp (-(t * n)) := by
    have hnn : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have heq : (N * Cε) ^ n * ((n : ℝ) / N) ^ n * Real.exp (-(t * n)) = (n : ℝ) ^ n / y ^ n := by
      rw [show -(t * n) = n * (-t) by ring, Real.exp_nat_mul, Real.exp_neg, ← mul_pow, ← mul_pow,
        ← div_pow]
      congr 1
      rw [show y = Real.exp t / Cε from rfl]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hnn (by positivity)
  -- the series
  set y₀ := Real.exp t / (c₀ * lam ^ (2 - β))
  have hyy₀ : y ≤ y₀ := div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hCε
  set L := 1 + if β = transitionBeta (pBeta p₀ β + 1) then Real.log (h / lam) else 0
  set A := N * Real.exp (β * kernelConst χ) * (2 * Real.pi) * (1 + 1 / E) *
    ε₀ ^ (-(2 : ℝ)) * (truncationScale p₀ β lam ^ 2)⁻¹ * L with hA
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log (h / lam) :=
      Real.log_nonneg (by rw [le_div_iff₀ hlam]; linarith)
    simp only [L]
    split_ifs <;> linarith
  have hA0 : 0 ≤ A := by positivity
  have hseries : ∑ m ∈ Finset.range n, (if pBeta p₀ β < m + 1 then b (m + 1) else 0) /
      (m + 1).factorial * y ^ (m + 1) ≤ A := by
    calc ∑ m ∈ Finset.range n, (if pBeta p₀ β < m + 1 then b (m + 1) else 0) /
          (m + 1).factorial * y ^ (m + 1)
        ≤ ∑ m ∈ Finset.range n, A * (((m : ℝ) + 1) * x ^ (m + 1)) := by
          refine sum_le_sum fun m _ => ?_
          split_ifs with hm
          · simp only [hb, ite_eq_left hm]
            have hbm := blockBoundLow_nonneg (χ := χ) (M := M) hβ4 hlam hlh N
              (exponent_nonneg (p₀ := p₀) hβ4 hm)
            calc blockBoundLow χ β lam M h N (m + 1) / (m + 1).factorial * y ^ (m + 1)
                ≤ blockBoundLow χ β lam M h N (m + 1) / (m + 1).factorial * y₀ ^ (m + 1) := by
                  gcongr
              _ ≤ A * (((m + 1 : ℕ) : ℝ) * x ^ (m + 1)) :=
                  blockTerm_le_low hβ4 hlam hε₀ hlh hc₀0 N hm
              _ = A * (((m : ℝ) + 1) * x ^ (m + 1)) := by push_cast; ring
          · rw [zero_div, zero_mul]
            positivity
      _ = A * ∑ m ∈ Finset.range n, ((m : ℝ) + 1) * x ^ (m + 1) := by rw [mul_sum]
      _ ≤ A * (2 * x) := mul_le_mul_of_nonneg_left (sum_succ_mul_pow_le hx0 hx4 n) hA0
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left (by linarith) hA0
      _ = A := mul_one A
  -- the exponent
  have hAle : A ≤ C₂ * max 1 (2 / (4 - β)) * N * ((criticalScale β lam).toReal ^ 2)⁻¹ *
      (1 + if β = transitionBeta (pBeta p₀ β + 1) then |Real.log lam| else 0) := by
    have hR : truncationScale p₀ β lam = (criticalScale β lam).toReal := by
      unfold truncationScale; rw [ite_eq_left hβ4]
    have hL : L ≤ max 1 (2 / (4 - β)) *
        (1 + if β = transitionBeta (pBeta p₀ β + 1) then |Real.log lam| else 0) := by
      simp only [L]
      split_ifs
      · have hlog := log_cutoff_div_le (p₀ := p₀) hβ4 hlam hlam1 hε₀ hε₀1
        have h1 : 1 ≤ max 1 (2 / (4 - β)) := le_max_left _ _
        have h2 : 2 / (4 - β) ≤ max 1 (2 / (4 - β)) := le_max_right _ _
        have habs : 0 ≤ |Real.log lam| := abs_nonneg _
        nlinarith
      · simp only [add_zero, mul_one]
        exact le_max_left _ _
    rw [hA, ← hR]
    have hR0 := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
    have hpos : 0 ≤ (N : ℝ) * Real.exp (β * kernelConst χ) * (2 * Real.pi) * (1 + 1 / E) *
        ε₀ ^ (-(2 : ℝ)) * (truncationScale p₀ β lam ^ 2)⁻¹ := by positivity
    calc (N : ℝ) * Real.exp (β * kernelConst χ) * (2 * Real.pi) * (1 + 1 / E) *
          ε₀ ^ (-(2 : ℝ)) * (truncationScale p₀ β lam ^ 2)⁻¹ * L
        ≤ (N : ℝ) * Real.exp (β * kernelConst χ) * (2 * Real.pi) * (1 + 1 / E) *
          ε₀ ^ (-(2 : ℝ)) * (truncationScale p₀ β lam ^ 2)⁻¹ * (max 1 (2 / (4 - β)) *
            (1 + if β = transitionBeta (pBeta p₀ β + 1) then |Real.log lam| else 0)) :=
          mul_le_mul_of_nonneg_left hL hpos
      _ = _ := by rw [hC₂]; ring
  calc (n.factorial : ℝ) / y ^ n * Real.exp (∑ m ∈ Finset.range n,
        (if pBeta p₀ β < m + 1 then b (m + 1) else 0) / (m + 1).factorial * y ^ (m + 1))
      ≤ ((N * Cε) ^ n * ((n : ℝ) / N) ^ n * Real.exp (-(t * n))) *
          Real.exp (C₂ * max 1 (2 / (4 - β)) * N * ((criticalScale β lam).toReal ^ 2)⁻¹ *
            (1 + if β = transitionBeta (pBeta p₀ β + 1) then |Real.log lam| else 0)) :=
        mul_le_mul hpre (Real.exp_le_exp.2 (hseries.trans hAle)) (Real.exp_pos _).le
          (by positivity)
    _ = _ := by ring

end BadPointTypes

end MultipoleBKT

end
