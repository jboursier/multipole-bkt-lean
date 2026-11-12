/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeThreeIntegral
public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoHigh

/-!
# Lemma 5.39: control of the bad points of type 3

The paper: Lemma 5.39 and its proof.

* `nearConst_le` (the radial integrals of Steps 2–3): the
  one-dipole constant `K = ∫ 4π M² max(|w|, λ)² 𝟙_{|w| ≤ ε₀R̄} 4^β max(|w|, λ)^{-β} dw` is at most
  `A λ^{2-β}` (`β < 4`: `h^{4-β} ≤ R^{4-β} = λ^{2-β}`; `β > 4`: `λ^{4-β} ≤ λ^{2-β}`; `β = 4`:
  `1 + log(h/λ) ≤ (2p₀+2) λ^{-1} ≤ (2p₀+2) λ^{-2}`), so `K ≤ a C_{β,λ,ε₀}` by (4.12);
* `typeThree_sum_le` (Step 4): the sum over the seed sets and the parent maps is
  at most `(C_{β,λ,ε₀} N₃)^{N₃} e^{-tN₃} e^{Q (N₁ + N₂)}`, `Q = (2 max(1, a) e^t)^{p(β)}`, using
  `N₃ ≤ p(β) |S|`, `binom(N₃, s) ≤ 2^{N₃}` and `N₃^{N₃ - s} s! ≤ N₃^{N₃}`;
* `lemma_5_39`: the statement, written multiplicatively:
  `Z_{bad,N₁,N₂,N₃} ≤ (N C_{β,λ,ε₀})^{N₃} (N₃/N)^{N₃} e^{-tN₃} e^{e^{Ct}(N₁+N₂)}
    Z^{(1)}_{bad,N₁} Z^{(2)}_{bad,N₂}`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset TheoremTwo UpperBound MultipoleIntegral Filter
open scoped ENNReal

variable {n : ℕ} {M β lam : ℝ}

/-! ### The one-dipole constant -/

/-- The radial constant: `1 + 1/(4-β)` (`β < 4`), `2p₀ + 2` (`β = 4`), `1 + 1/(β-4)` (`β > 4`). -/
noncomputable def typeThreeRadialConst (p₀ : ℕ) (β : ℝ) : ℝ :=
  if β < 4 then 1 + 1 / (4 - β) else if β = 4 then 2 * p₀ + 2 else 1 + 1 / (β - 4)

theorem typeThreeRadialConst_nonneg (p₀ : ℕ) (β : ℝ) : 0 ≤ typeThreeRadialConst p₀ β := by
  unfold typeThreeRadialConst
  split_ifs with h1 h2
  · have : 0 < 4 - β := by linarith
    positivity
  · positivity
  · have : 0 < β - 4 := lt_of_le_of_ne (by linarith) (fun h => h2 (by linarith))
    positivity

/-- The constant `A = 4π M² 4^β 2π κ`. -/
noncomputable def nearConstBound (p₀ : ℕ) (β M : ℝ) : ℝ :=
  4 * Real.pi * M ^ 2 * 4 ^ β * (2 * Real.pi * typeThreeRadialConst p₀ β)

theorem nearConstBound_nonneg (p₀ : ℕ) (β M : ℝ) : 0 ≤ nearConstBound p₀ β M := by
  unfold nearConstBound
  have := typeThreeRadialConst_nonneg p₀ β
  positivity

/-- **The one-dipole constant** `K ≤ A λ^{2-β}` (for `0 < λ ≤ 1`, `0 < ε₀ ≤ 1`, `λ ≤ ε₀ R̄`). -/
theorem nearConst_le {p₀ : ℕ} {ε₀ : ℝ} (hβ : 2 < β) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hlh : lam ≤ cutoff p₀ β lam ε₀) :
    nearConst M β lam (cutoff p₀ β lam ε₀) ≤ ENNReal.ofReal (nearConstBound p₀ β M * lam ^ (2 - β)) := by
  set h := cutoff p₀ β lam ε₀ with hhdef
  have hh : 0 < h := hlam.trans_le hlh
  -- pull out the constants
  have hpt : ∀ w : ℂ, ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2) *
      lengthWeight β lam h w ≤ ENNReal.ofReal (4 * Real.pi * M ^ 2 * 4 ^ β) *
        (Metric.closedBall (0 : ℂ) h).indicator
          (fun w => ENNReal.ofReal (max ‖w‖ lam ^ (2 - β))) w := by
    intro w
    unfold lengthWeight
    by_cases hw : w ∈ Metric.closedBall (0 : ℂ) h
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      have hm : 0 < max ‖w‖ lam := lt_max_of_lt_right hlam
      have : max ‖w‖ lam ^ (2 : ℝ) * max ‖w‖ lam ^ (-β) = max ‖w‖ lam ^ (2 - β) := by
        rw [← Real.rpow_add hm]; ring_nf
      rw [← this, mul_pow, show (max ‖w‖ lam) ^ 2 = max ‖w‖ lam ^ (2 : ℝ) by
        rw [Real.rpow_two]]
      ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero, mul_zero]
  unfold nearConst
  refine (lintegral_mono hpt).trans ?_
  have hmeas : Measurable fun w : ℂ => (Metric.closedBall (0 : ℂ) h).indicator
      (fun w => ENNReal.ofReal (max ‖w‖ lam ^ (2 - β))) w :=
    Measurable.indicator (ENNReal.measurable_ofReal.comp
      ((continuous_norm.max continuous_const).measurable.pow_const _))
      Metric.isClosed_closedBall.measurableSet
  rw [lintegral_const_mul _ hmeas]
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hrad : ∫⁻ w : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun w => ENNReal.ofReal (max ‖w‖ lam ^ (2 - β))) w ≤
        ENNReal.ofReal (2 * Real.pi * typeThreeRadialConst p₀ β * lam ^ (2 - β)) := by
    by_cases hβ4 : β < 4
    · refine (lintegral_closedBall_max_rpow_le_of_pos hlam hlh (by linarith)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hκ : typeThreeRadialConst p₀ β = 1 + 1 / (4 - β) := by
        unfold typeThreeRadialConst; rw [ite_eq_left hβ4]
      rw [hκ, show 2 - β + 2 = 4 - β by ring]
      have h4 : 0 < 4 - β := by linarith
      have hhe : h ^ (4 - β) ≤ lam ^ (2 - β) := by
        rw [hhdef, Real.mul_rpow hε₀.le hR.le, Appendix.rpow_truncationScale_of_lt hβ4 hlam]
        calc ε₀ ^ (4 - β) * lam ^ (2 - β) ≤ 1 * lam ^ (2 - β) :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_one hε₀.le hε₀1 h4.le)
                (Real.rpow_nonneg hlam.le _)
          _ = lam ^ (2 - β) := one_mul _
      have : 0 ≤ 2 * Real.pi * (1 + 1 / (4 - β)) := by positivity
      calc 2 * Real.pi * ((1 + 1 / (4 - β)) * h ^ (4 - β))
          = 2 * Real.pi * (1 + 1 / (4 - β)) * h ^ (4 - β) := by ring
        _ ≤ 2 * Real.pi * (1 + 1 / (4 - β)) * lam ^ (2 - β) :=
            mul_le_mul_of_nonneg_left hhe this
    · by_cases hβ4' : β = 4
      · subst hβ4'
        have hκ : typeThreeRadialConst p₀ 4 = 2 * p₀ + 2 := by
          unfold typeThreeRadialConst; rw [ite_eq_right (by norm_num), ite_eq_left rfl]
        rw [show (2 : ℝ) - 4 = -2 by norm_num]
        refine (lintegral_closedBall_max_rpow_le_of_eq hlam hlh).trans
          (ENNReal.ofReal_le_ofReal ?_)
        rw [hκ]
        have hη := eta_le_high (p₀ := p₀) (β := 4) le_rfl hlam hlam1 hε₀ hε₀1
        have hl2 : lam ^ (-2 : ℝ) = (lam ^ 2)⁻¹ := by
          rw [Real.rpow_neg hlam.le, Real.rpow_two]
        rw [hl2]
        have hlsq : 0 < lam ^ 2 := by positivity
        have hkey : 1 + Real.log (h / lam) ≤ (2 * p₀ + 2) * (lam ^ 2)⁻¹ := by
          rw [le_mul_inv_iff₀ hlsq]
          calc (1 + Real.log (h / lam)) * lam ^ 2 = lam ^ 2 * (1 + Real.log (h / lam)) := by
                ring
            _ ≤ (2 * p₀ + 2) * lam := hη
            _ ≤ 2 * p₀ + 2 := by
                have : (0 : ℝ) ≤ 2 * p₀ + 2 := by positivity
                nlinarith
        have : 0 ≤ 2 * Real.pi := by positivity
        calc 2 * Real.pi * (1 + Real.log (h / lam))
            ≤ 2 * Real.pi * ((2 * p₀ + 2) * (lam ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hkey this
          _ = 2 * Real.pi * (2 * p₀ + 2) * (lam ^ 2)⁻¹ := by ring
      · have hβ4'' : 4 < β := lt_of_le_of_ne (not_lt.1 hβ4) (Ne.symm hβ4')
        refine (lintegral_closedBall_max_rpow_le_of_neg hlam hlh (by linarith)).trans
          (ENNReal.ofReal_le_ofReal ?_)
        have hκ : typeThreeRadialConst p₀ β = 1 + 1 / (β - 4) := by
          unfold typeThreeRadialConst; rw [ite_eq_right hβ4, ite_eq_right hβ4']
        rw [hκ, show -(2 - β + 2) = β - 4 by ring, show 2 - β + 2 = 4 - β by ring]
        have hl : lam ^ (4 - β) ≤ lam ^ (2 - β) :=
          Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
        have h4 : 0 < β - 4 := by linarith
        have : 0 ≤ 2 * Real.pi * (1 + 1 / (β - 4)) := by positivity
        calc 2 * Real.pi * ((1 + 1 / (β - 4)) * lam ^ (4 - β))
            = 2 * Real.pi * (1 + 1 / (β - 4)) * lam ^ (4 - β) := by ring
          _ ≤ 2 * Real.pi * (1 + 1 / (β - 4)) * lam ^ (2 - β) :=
              mul_le_mul_of_nonneg_left hl this
  calc ENNReal.ofReal (4 * Real.pi * M ^ 2 * 4 ^ β) * ∫⁻ w : ℂ,
        (Metric.closedBall (0 : ℂ) h).indicator
          (fun w => ENNReal.ofReal (max ‖w‖ lam ^ (2 - β))) w
      ≤ ENNReal.ofReal (4 * Real.pi * M ^ 2 * 4 ^ β) *
          ENNReal.ofReal (2 * Real.pi * typeThreeRadialConst p₀ β * lam ^ (2 - β)) := by gcongr
    _ = ENNReal.ofReal (nearConstBound p₀ β M * lam ^ (2 - β)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        unfold nearConstBound
        ring_nf

/-! ### Step 4: the sum over the seed sets -/

theorem card_parentSet {k : ℕ} (S : Finset (Fin k)) : (parentSet S).card = k ^ Sᶜ.card := by
  classical
  unfold parentSet
  rw [Fintype.card_piFinset]
  have : ∀ c : Fin k, (if c ∈ S then ({c} : Finset (Fin k)) else univ).card =
      if c ∈ S then 1 else k := fun c => by
    split_ifs
    · exact Finset.card_singleton c
    · rw [Finset.card_univ, Fintype.card_fin]
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 2
  ext c
  simp

/-- **Step 4** (proof of Lemma 5.39): for `K ≤ a C` and `t ≥ 0`,
`∑_{S, N₃ ≤ p|S|} ∑_{par} ((N₁ + N₂) K)^{|S|} K^{N₃ - |S|}
  ≤ (C N₃)^{N₃} e^{-tN₃} e^{(2 max(1, a) e^t)^p (N₁ + N₂)}`. -/
theorem typeThree_sum_le {N₁ N₂ N₃ p : ℕ} {K a Cn t : ℝ} (hK0 : 0 ≤ K)
    (hKa : K ≤ a * Cn) (hCn : 0 < Cn) (ht : 0 ≤ t) :
    ∑ S ∈ seedSets N₃ p, ∑ _par ∈ parentSet S, (((N₁ + N₂ : ℕ) : ℝ) * K) ^ S.card * K ^ Sᶜ.card ≤
      (Cn * N₃) ^ N₃ * Real.exp (-(t * N₃)) *
        Real.exp ((2 * max 1 a * Real.exp t) ^ p * (N₁ + N₂)) := by
  classical
  set a' := max 1 a with ha'
  have ha'1 : 1 ≤ a' := le_max_left _ _
  set b := 2 * a' * Real.exp t with hb
  have hb1 : 1 ≤ b := by
    have : 1 ≤ Real.exp t := Real.one_le_exp ht
    rw [hb]; nlinarith
  set Y : ℝ := b ^ p * (N₁ + N₂) with hY
  have hY0 : 0 ≤ Y := by positivity
  set L : ℝ := (Cn * N₃) ^ N₃ * Real.exp (-(t * N₃)) * (1 / 2) ^ N₃ with hL
  have hL0 : 0 ≤ L := by positivity
  -- one seed set
  have hterm : ∀ S ∈ seedSets N₃ p, ∑ _par ∈ parentSet S,
      (((N₁ + N₂ : ℕ) : ℝ) * K) ^ S.card * K ^ Sᶜ.card ≤ L * (Y ^ S.card / S.card.factorial) := by
    intro S hS
    have hNs : N₃ ≤ p * S.card := (Finset.mem_filter.1 hS).2
    set s := S.card with hs
    have hsN : s ≤ N₃ := by
      have := Finset.card_le_univ S
      rwa [Fintype.card_fin] at this
    have hcompl : Sᶜ.card = N₃ - s := by
      rw [Finset.card_compl, Fintype.card_fin]
    rw [Finset.sum_const, card_parentSet, nsmul_eq_mul, hcompl]
    push_cast
    have hKN : K ^ s * K ^ (N₃ - s) = K ^ N₃ := by
      rw [← pow_add, Nat.add_sub_cancel' hsN]
    have hKpow : K ^ N₃ ≤ (a' * Cn) ^ N₃ :=
      pow_le_pow_left₀ hK0 (hKa.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hCn.le)) _
    have hfact : (N₃ : ℝ) ^ (N₃ - s) * (s.factorial : ℝ) ≤ (N₃ : ℝ) ^ N₃ := by
      have h1 : (s.factorial : ℝ) ≤ (N₃ : ℝ) ^ s := by
        have : s.factorial ≤ s ^ s := Nat.factorial_le_pow s
        have h2 : s ^ s ≤ N₃ ^ s := Nat.pow_le_pow_left hsN s
        exact_mod_cast this.trans h2
      calc (N₃ : ℝ) ^ (N₃ - s) * (s.factorial : ℝ) ≤ (N₃ : ℝ) ^ (N₃ - s) * (N₃ : ℝ) ^ s :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (N₃ : ℝ) ^ N₃ := by rw [← pow_add, Nat.sub_add_cancel hsN]
    have hbpow : b ^ N₃ ≤ (b ^ p) ^ s := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hb1 hNs
    have hkey : (N₃ : ℝ) ^ (N₃ - s) * a' ^ N₃ * ((s.factorial : ℝ) * 2 ^ N₃ * Real.exp t ^ N₃) ≤
        (N₃ : ℝ) ^ N₃ * (b ^ p) ^ s := by
      calc (N₃ : ℝ) ^ (N₃ - s) * a' ^ N₃ * ((s.factorial : ℝ) * 2 ^ N₃ * Real.exp t ^ N₃)
          = ((N₃ : ℝ) ^ (N₃ - s) * (s.factorial : ℝ)) * b ^ N₃ := by
            rw [hb, mul_pow, mul_pow]; ring
        _ ≤ (N₃ : ℝ) ^ N₃ * (b ^ p) ^ s :=
            mul_le_mul hfact hbpow (by positivity) (by positivity)
    have hpos : 0 < (s.factorial : ℝ) * 2 ^ N₃ * Real.exp t ^ N₃ := by positivity
    have hkey' : (N₃ : ℝ) ^ (N₃ - s) * a' ^ N₃ ≤
        (N₃ : ℝ) ^ N₃ * (b ^ p) ^ s / ((s.factorial : ℝ) * 2 ^ N₃ * Real.exp t ^ N₃) :=
      (le_div_iff₀ hpos).2 hkey
    calc (N₃ : ℝ) ^ (N₃ - s) * ((((N₁ : ℝ) + N₂) * K) ^ s * K ^ (N₃ - s))
        = (N₃ : ℝ) ^ (N₃ - s) * (((N₁ : ℝ) + N₂) ^ s * K ^ N₃) := by
          rw [mul_pow, mul_assoc, hKN]
      _ ≤ (N₃ : ℝ) ^ (N₃ - s) * (((N₁ : ℝ) + N₂) ^ s * (a' * Cn) ^ N₃) := by
          gcongr
      _ = Cn ^ N₃ * ((N₁ : ℝ) + N₂) ^ s * ((N₃ : ℝ) ^ (N₃ - s) * a' ^ N₃) := by ring
      _ ≤ Cn ^ N₃ * ((N₁ : ℝ) + N₂) ^ s *
            ((N₃ : ℝ) ^ N₃ * (b ^ p) ^ s / ((s.factorial : ℝ) * 2 ^ N₃ * Real.exp t ^ N₃)) :=
          mul_le_mul_of_nonneg_left hkey' (by positivity)
      _ = L * (Y ^ s / s.factorial) := by
          rw [hL, hY, Real.exp_neg, show t * (N₃ : ℝ) = N₃ * t by ring, Real.exp_nat_mul,
            show ((1 : ℝ) / 2) ^ N₃ = ((2 : ℝ) ^ N₃)⁻¹ by rw [one_div, inv_pow]]
          generalize b ^ p = B
          field_simp
          rw [mul_pow, mul_pow]
          ring
  -- summing
  have hsum_all : ∑ S : Finset (Fin N₃), Y ^ S.card / S.card.factorial ≤
      2 ^ N₃ * Real.exp Y := by
    have h := Finset.sum_powerset_apply_card (fun m => Y ^ m / m.factorial)
      (x := (univ : Finset (Fin N₃)))
    rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h
    rw [h]
    calc ∑ m ∈ range (N₃ + 1), N₃.choose m • (Y ^ m / m.factorial)
        ≤ ∑ m ∈ range (N₃ + 1), 2 ^ N₃ * (Y ^ m / m.factorial) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [nsmul_eq_mul]
          have : (N₃.choose m : ℝ) ≤ 2 ^ N₃ := by exact_mod_cast Nat.choose_le_two_pow N₃ m
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 ^ N₃ * ∑ m ∈ range (N₃ + 1), Y ^ m / m.factorial := by rw [Finset.mul_sum]
      _ ≤ 2 ^ N₃ * Real.exp Y :=
          mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hY0 _) (by positivity)
  calc ∑ S ∈ seedSets N₃ p, ∑ _par ∈ parentSet S,
        (((N₁ + N₂ : ℕ) : ℝ) * K) ^ S.card * K ^ Sᶜ.card
      ≤ ∑ S ∈ seedSets N₃ p, L * (Y ^ S.card / S.card.factorial) := Finset.sum_le_sum hterm
    _ ≤ ∑ S : Finset (Fin N₃), L * (Y ^ S.card / S.card.factorial) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => by positivity
    _ = L * ∑ S : Finset (Fin N₃), Y ^ S.card / S.card.factorial := by rw [Finset.mul_sum]
    _ ≤ L * (2 ^ N₃ * Real.exp Y) := mul_le_mul_of_nonneg_left hsum_all hL0
    _ = (Cn * N₃) ^ N₃ * Real.exp (-(t * N₃)) * Real.exp Y := by
        rw [hL, mul_assoc, ← mul_assoc ((1 / 2 : ℝ) ^ N₃), ← mul_pow]
        norm_num

/-! ### Lemma 5.39 -/

/-- `Q + β log 12 ≤ e^{Ct}` for `t ≥ 1`, `Q = (2a' e^t)^p`, `C = p + log((2a')^p + β log 12 + 1)`. -/
theorem exponent_le_exp {p : ℕ} {a' t : ℝ} (ha' : 1 ≤ a') (hβ : 0 ≤ β) (ht : 1 ≤ t) :
    (2 * a' * Real.exp t) ^ p + β * Real.log 12 ≤
      Real.exp ((p + Real.log ((2 * a') ^ p + β * Real.log 12 + 1)) * t) := by
  set L := (2 * a') ^ p + β * Real.log 12 + 1 with hL
  have hl12 : 0 ≤ β * Real.log 12 := mul_nonneg hβ (Real.log_nonneg (by norm_num))
  have h2a : 1 ≤ (2 * a') ^ p := one_le_pow₀ (by linarith)
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have hLpos : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hept : 1 ≤ Real.exp (p * t) := Real.one_le_exp (by positivity)
  have h1 : (2 * a' * Real.exp t) ^ p = (2 * a') ^ p * Real.exp (p * t) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  have h2 : L ≤ Real.exp (Real.log L * t) := by
    calc L = Real.exp (Real.log L) := (Real.exp_log hLpos).symm
      _ ≤ Real.exp (Real.log L * t) :=
          Real.exp_le_exp.2 (le_mul_of_one_le_right hlogL ht)
  calc (2 * a' * Real.exp t) ^ p + β * Real.log 12
      = (2 * a') ^ p * Real.exp (p * t) + β * Real.log 12 := by rw [h1]
    _ ≤ L * Real.exp (p * t) := by
        rw [hL]
        nlinarith
    _ ≤ Real.exp (Real.log L * t) * Real.exp (p * t) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp ((p + Real.log L) * t) := by rw [← Real.exp_add]; ring_nf

/-- **Lemma 5.39**: there is `C > 0` (depending on
`χ, β, M, p₀`) such that for all `t ≥ 1` and `ε₀ ∈ (0, 1]`, for `λ` small and `N` large, for every
partition `[n] = V₁ ∪ V₂ ∪ V₃` (`N_k = |V_k|`),
`(N/N₃)^{N₃} Z_{bad,N₁,N₂,N₃} e^{tN₃} / (N C_{β,λ,ε₀})^{N₃}
  ≤ e^{e^{Ct}(N₁+N₂)} Z^{(1)}_{bad,N₁} Z^{(2)}_{bad,N₂}`, written multiplicatively. -/
theorem lemma_5_39 {χ : ℂ → ℝ} {p₀ : ℕ} (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β)
    (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop,
        ∀ (n : ℕ) (V₁ V₂ V₃ : Finset (Fin n)), Disjoint V₁ V₂ → Disjoint V₁ V₃ →
          Disjoint V₂ V₃ → V₁ ∪ V₂ ∪ V₃ = univ →
          typedBadPartitionFunction p₀ β lam M ε₀ N n V₁ V₂ V₃ ≤
            ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
                (ε₀ * truncationScale p₀ β lam)) ^ V₃.card * ((V₃.card : ℝ) / N) ^ V₃.card *
              (Real.exp (-(t * V₃.card)) *
                Real.exp (Real.exp (C * t) * (V₁.card + V₂.card)))) *
              typeOnePartitionFunction p₀ β lam ε₀ N V₁.card *
              typeTwoPartitionFunction χ p₀ β lam M ε₀ N V₂.card := by
  have hβ0 : 0 ≤ β := by linarith
  have hZ := dipoleConstant_pos hχ hβ
  set c₀ := 1 / 2 * dipoleConstant χ β with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set a := nearConstBound p₀ β M / c₀ with ha
  have ha0 : 0 ≤ a := div_nonneg (nearConstBound_nonneg p₀ β M) hc₀0.le
  set a' := max 1 a with ha'
  have ha'1 : 1 ≤ a' := le_max_left _ _
  set p := pBeta p₀ β
  set C := (p : ℝ) + Real.log ((2 * a') ^ p + β * Real.log 12 + 1) with hC
  have hCpos : 0 < C := by
    have hl12 : 0 ≤ β * Real.log 12 := mul_nonneg hβ0 (Real.log_nonneg (by norm_num))
    have h2a : 1 ≤ (2 * a') ^ p := one_le_pow₀ (by linarith)
    have : 0 < Real.log ((2 * a') ^ p + β * Real.log 12 + 1) := Real.log_pos (by linarith)
    positivity
  refine ⟨C, hCpos, fun t ht ε₀ hε₀ hε₀1 => ?_⟩
  obtain ⟨lam₁, hlam₁, hnorm⟩ := eventually_half_le_normalization hχ hβ hp₀ hε₀ hε₀1
  obtain ⟨lam₂, hlam₂, hcut⟩ := eventually_lam_le_cutoff hβ hp₀ hε₀
  refine ⟨min lam₁ lam₂, lt_min hlam₁ hlam₂, fun lam hlam hlt => ?_⟩
  obtain ⟨hlam1, hlh⟩ := hcut lam hlam (hlt.trans_le (min_le_right _ _))
  filter_upwards [hnorm lam hlam (hlt.trans_le (min_le_left _ _)), eventually_ge_atTop 1]
    with N hNC hN1 n V₁ V₂ V₃ h12 h13 h23 hcov
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  set Cε := truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam) with hCε
  have hCε' : c₀ * lam ^ (2 - β) ≤ Cε := hNC
  have hCε0 : 0 < Cε := lt_of_lt_of_le (by positivity) hCε'
  set K := nearConstBound p₀ β M * lam ^ (2 - β) with hK
  have hK0 : 0 ≤ K := mul_nonneg (nearConstBound_nonneg p₀ β M) (by positivity)
  have hKa : K ≤ a * Cε := by
    rw [hK, ha]
    calc nearConstBound p₀ β M * lam ^ (2 - β)
        = nearConstBound p₀ β M / c₀ * (c₀ * lam ^ (2 - β)) := by field_simp
      _ ≤ nearConstBound p₀ β M / c₀ * Cε := mul_le_mul_of_nonneg_left hCε' ha0
  have hq := clusterThreshold_pos hp₀ hβ
  have hh : 0 < cutoff p₀ β lam ε₀ := by
    unfold cutoff
    have := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
    positivity
  have hmain := typedBadPartitionFunction_le (χ := χ) (Nₐ := N) hχ hq hh hlam hβ0 hM h12 h13
    h23 hcov hK0 (nearConst_le hβ hlam hlam1 hε₀ hε₀1 hlh)
  refine hmain.trans ?_
  -- the real bound
  set N₁ := V₁.card
  set N₂ := V₂.card
  set N₃ := V₃.card
  have hsum := typeThree_sum_le (N₁ := N₁) (N₂ := N₂) (N₃ := N₃) (p := p) hK0 hKa hCε0
    (by linarith : (0 : ℝ) ≤ t)
  have h12β : ((12 : ℝ) ^ β) ^ N₂ ≤ Real.exp (β * Real.log 12 * (N₁ + N₂)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.rpow_def_of_pos (by norm_num)]
    refine Real.exp_le_exp.2 ?_
    have : 0 ≤ Real.log 12 * β := mul_nonneg (Real.log_nonneg (by norm_num)) hβ0
    have hN1 : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg _
    nlinarith
  have hexp := exponent_le_exp (p := p) (β := β) ha'1 hβ0 ht
  set Q := (2 * max 1 a * Real.exp t) ^ p
  have hreal : (12 ^ β) ^ N₂ * ∑ S ∈ seedSets N₃ p, ∑ _par ∈ parentSet S,
      (((N₁ + N₂ : ℕ) : ℝ) * K) ^ S.card * K ^ Sᶜ.card ≤
      (N * Cε) ^ N₃ * ((N₃ : ℝ) / N) ^ N₃ *
        (Real.exp (-(t * N₃)) * Real.exp (Real.exp (C * t) * (N₁ + N₂))) := by
    have hNN : (N * Cε) ^ N₃ * ((N₃ : ℝ) / N) ^ N₃ = (Cε * N₃) ^ N₃ := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hNN]
    have hsum0 : 0 ≤ ∑ S ∈ seedSets N₃ p, ∑ _par ∈ parentSet S,
        (((N₁ + N₂ : ℕ) : ℝ) * K) ^ S.card * K ^ Sᶜ.card :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    calc (12 ^ β) ^ N₂ * ∑ S ∈ seedSets N₃ p, ∑ _par ∈ parentSet S,
          (((N₁ + N₂ : ℕ) : ℝ) * K) ^ S.card * K ^ Sᶜ.card
        ≤ Real.exp (β * Real.log 12 * (N₁ + N₂)) *
            ((Cε * N₃) ^ N₃ * Real.exp (-(t * N₃)) * Real.exp (Q * (N₁ + N₂))) :=
          mul_le_mul h12β hsum hsum0 (Real.exp_pos _).le
      _ = (Cε * N₃) ^ N₃ * (Real.exp (-(t * N₃)) *
            Real.exp ((Q + β * Real.log 12) * (N₁ + N₂))) := by
          rw [add_mul, Real.exp_add]; ring
      _ ≤ (Cε * N₃) ^ N₃ * (Real.exp (-(t * N₃)) *
            Real.exp (Real.exp (C * t) * (N₁ + N₂))) := by
          gcongr
  calc typeOnePartitionFunction p₀ β lam ε₀ N N₁ * typeTwoPartitionFunction χ p₀ β lam M ε₀ N N₂ *
        ENNReal.ofReal ((12 ^ β) ^ N₂ * ∑ S ∈ seedSets N₃ p, ∑ _par ∈ parentSet S,
          (((N₁ + N₂ : ℕ) : ℝ) * K) ^ S.card * K ^ Sᶜ.card)
      ≤ typeOnePartitionFunction p₀ β lam ε₀ N N₁ * typeTwoPartitionFunction χ p₀ β lam M ε₀ N N₂ *
          ENNReal.ofReal ((N * Cε) ^ N₃ * ((N₃ : ℝ) / N) ^ N₃ *
            (Real.exp (-(t * N₃)) * Real.exp (Real.exp (C * t) * (N₁ + N₂)))) := by
        gcongr
    _ = _ := by ring

end BadPointTypes

end MultipoleBKT

end
