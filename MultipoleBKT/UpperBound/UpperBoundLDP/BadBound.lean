/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.BadSplit
public import MultipoleBKT.UpperBound.BadPointTypes.TypeThree
public import MultipoleBKT.UpperBound.BadPointTypes.TypeOne
public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwo
public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoHigh
public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoTwo
public import MultipoleBKT.UpperBound.Hierarchical.IntegrandBound
public import MultipoleBKT.Main.TheoremTwo.Parameters

/-!
# Proposition 5.38: the partition function of the bad points

The paper: Proposition 5.38: for every
`t ≥ 1`, for `ε₀` small and `λ` small, there is `C` such that

  `binom(N,m) Z_{bad,m} e^{tm} / (N C_{β,λ,ε₀})^m ≤ e^{CNδ_{β,λ}}` for `m ≤ N`.

The labellings in (5.132) and (5.115) are grouped by their
class counts (`RouteCount.sum_counts`). Their two multinomials have product
`m! / (n₁! n₃! ∏ⱼ nⱼ!)`, where the product runs over the type-2 classes.
`RouteCount.multinomial_entropy_factorial` cancels each class normalization,
retaining `n₂! / N^{n₂}` in `typeTwo_factorial_bound` for cancellation with
the outer multinomial. Thus the total entropy cost is `e^m`.

As written, Lemma 5.39 is applied at `u = t + 1 + log(3(p+1))` and the other
bounds at `s = u + e^{Cu}`. The class-count sums cost at most `3^m (p+1)^{n₂}`.
The type `(2,2,k)` threshold absorbs `e^{sn} C^n ε₀^{αn/k}`, and `k = 1` is empty
(`typeTwoTwo_bound`). Lemmas 5.40 and 5.41 supply the final `e^{CNδ}`.
The remaining `binom(N,m) m! / N^m` is at most one
(`RouteCount.choose_factorial_le`). This gives the displayed entropy estimate
in the proof of Proposition 5.38 with its factorials cancelled in the order of the two splits.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBoundLDP

open MeasureTheory Finset Filter TheoremTwo BadPointTypes UpperBound
open scoped ENNReal

open RouteCount

/-! ### Finitely many constants -/

/-- One positive constant for finitely many indices, for a property monotone in the constant. -/
theorem exists_pos_forall_finset {ι : Type*} (S : Finset ι) {P : ι → ℝ → Prop}
    (hmono : ∀ i C C', 0 < C → C ≤ C' → P i C → P i C')
    (h : ∀ i ∈ S, ∃ C, 0 < C ∧ P i C) : ∃ C, 0 < C ∧ ∀ i ∈ S, P i C := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a S ha ih =>
    obtain ⟨C₁, hC₁, h₁⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨C₂, hC₂, h₂⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hmono i C₂ _ hC₂ (le_max_right _ _) h₂
    · exact hmono i C₁ _ hC₁ (le_max_left _ _) (h₁ i hi)

/-- One positive threshold for finitely many indices, for a property antitone in the threshold. -/
theorem exists_pos_forall_finset' {ι : Type*} (S : Finset ι) {P : ι → ℝ → Prop}
    (hanti : ∀ i l l', 0 < l' → l' ≤ l → P i l → P i l')
    (h : ∀ i ∈ S, ∃ l, 0 < l ∧ P i l) : ∃ l, 0 < l ∧ ∀ i ∈ S, P i l := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a S ha ih =>
    obtain ⟨l₁, hl₁, h₁⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨l₂, hl₂, h₂⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨min l₁ l₂, lt_min hl₁ hl₂, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hanti i l₂ _ (lt_min hl₁ hl₂) (min_le_right _ _) h₂
    · exact hanti i l₁ _ (lt_min hl₁ hl₂) (min_le_left _ _) (h₁ i hi)

/-! ### Elementary bounds -/

theorem truncatedDipoleNormalization_nonneg' (χ : ℂ → ℝ) (N : ℕ) (β lam R : ℝ) :
    0 ≤ truncatedDipoleNormalization χ N β lam R := by
  unfold truncatedDipoleNormalization
  refine mul_nonneg (by positivity) (integral_nonneg fun q => ?_)
  exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

/-- The error of Lemma 5.41 for `β ∈ (2,4)` is at most `δ_{β,λ}`. -/
theorem lowError_le_errorRate {p₀ : ℕ} {β lam : ℝ} (hβ : 2 < β) (h4 : β < 4) (hp₀ : 1 ≤ p₀) :
    ((criticalScale β lam).toReal ^ 2)⁻¹ *
        (1 + if β = transitionBeta (pBeta p₀ β + 1) then |Real.log lam| else 0) ≤
      errorRate p₀ β lam := by
  have hp1 : 1 ≤ pBeta p₀ β := one_le_pBeta' hp₀ hβ
  unfold errorRate
  rw [ite_eq_left (show 2 < β ∧ β < 4 from ⟨hβ, h4⟩), ite_eq_right (not_le.mpr h4), add_zero]
  have hz : ((criticalScale β lam).toReal ^ 2)⁻¹ = (criticalScale β lam).toReal ^ (-2 : ℤ) := by
    rw [zpow_neg, zpow_ofNat]
  rw [hz]
  refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg ENNReal.toReal_nonneg _)
  split_ifs with hβp
  · have hsum : (∑' q : ℕ, if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0) =
        |Real.log lam| := by
      rw [tsum_eq_single (pBeta p₀ β + 1)]
      · rw [ite_eq_left (show 2 ≤ pBeta p₀ β + 1 ∧ β = transitionBeta (pBeta p₀ β + 1) from
          ⟨by omega, hβp⟩)]
      · intro q hq
        rw [ite_eq_right]
        rintro ⟨hq2, hβq⟩
        apply hq
        have h1 : transitionBeta q = transitionBeta (pBeta p₀ β + 1) := hβq.symm.trans hβp
        unfold transitionBeta at h1
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
        have hq00 : (0 : ℝ) < ((pBeta p₀ β + 1 : ℕ) : ℝ) := by positivity
        have : (2 : ℝ) / q = 2 / ((pBeta p₀ β + 1 : ℕ) : ℝ) := by
          push_cast at h1 ⊢
          linarith
        field_simp at this
        exact_mod_cast (by linarith : (q : ℝ) = ((pBeta p₀ β + 1 : ℕ) : ℝ))
    rw [hsum]
  · have := tsum_transition_nonneg β lam
    linarith

/-! ### The classes `(2,2,k)` -/

section TypeTwoTwo

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

open scoped Classical in
/-- Below the threshold, the class `(2,2,k)` is empty: `Z^{(2,2,k)}_{bad,n} = 0` for
`1 ≤ n ≤ ε₀^{-α(β)} N λ^{2(k-1)}`. -/
theorem typeTwoTwoPartitionFunction_eq_zero (k : ℕ) {Nₐ n : ℕ} (hn : 1 ≤ n)
    (hthr : (n : ℝ) ≤ ε₀ ^ (-alphaExponent β) * Nₐ * lam ^ (2 * (k - 1))) :
    typeTwoTwoPartitionFunction χ k p₀ β lam M ε₀ Nₐ n = 0 := by
  have hfalse : ∀ d : Fin n → ℂ × ℂ, typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d ≠ univ := by
    intro d hd
    have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
    unfold typeTwoTwoBad at hd
    dsimp only at hd
    split_ifs at hd with hc
    · have hle : (((univ \ badPointsTypeOne p₀ β lam ε₀ d).filter fun i =>
          (multipoleClassOn M lam d (univ \ badPointsTypeOne p₀ β lam ε₀ d) i).card = k).card : ℝ)
          ≤ n := by
        have := card_le_univ ((univ \ badPointsTypeOne p₀ β lam ε₀ d).filter fun i =>
          (multipoleClassOn M lam d (univ \ badPointsTypeOne p₀ β lam ε₀ d) i).card = k)
        rw [Fintype.card_fin] at this
        exact_mod_cast this
      linarith
    · rw [← hd] at hne
      exact not_nonempty_empty hne
  unfold typeTwoTwoPartitionFunction
  simp only [hfalse, false_and, ite_false, zero_mul, lintegral_zero]

/-- **The classes `(2,2,k)`** (Lemma 5.42 and the threshold): for `1 ≤ k ≤ p(β)` there is `C`
such that for `ε₀ ∈ (0,1]`, `λ` small and `N` large, for `n ≤ N`,
`Z^{(2,2,k)}_{bad,n} ≤ (N C_{β,λ,ε₀})^n (n/N)^n wₖⁿ`, with `w₁ = 0` and `wₖ = C ε₀^{α(β)/k}`. -/
theorem typeTwoTwo_bound (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) {k : ℕ}
    (hk1 : 1 ≤ k) (hkp : k ≤ pBeta p₀ β) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, n ≤ N →
        typeTwoTwoPartitionFunction χ k p₀ β lam M ε₀ N n ≤
          ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
              (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) * (1 / N)) ^ n *
            (if k = 1 then 0 else C * ε₀ ^ (alphaExponent β / k)) ^ n * 1) := by
  obtain ⟨C, hC, h42⟩ := lemma_5_42 hχ hp₀ hβ hk1 hkp hM
  refine ⟨C, hC, fun ε₀ hε₀ hε₀1 => ?_⟩
  obtain ⟨lam₀, hlam₀, hl⟩ := h42 ε₀ hε₀ hε₀1
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  filter_upwards [hl lam hlam hlt, eventually_ge_atTop 1] with N hN hN1 n hnN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set A := (N : ℝ) * truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam)
  have hα := alphaExponent_pos β
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (hN 0).trans (le_of_eq ?_)
    simp
  set X := (N : ℝ) * lam ^ (2 * (k - 1)) with hX
  have hX0 : 0 ≤ X := by positivity
  have hthr_eq :
      ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) = ε₀ ^ (-alphaExponent β) * X := by
    rw [hX]; ring
  by_cases hbelow : (n : ℝ) ≤ ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1))
  · rw [typeTwoTwoPartitionFunction_eq_zero k hn hbelow]
    exact zero_le
  push Not at hbelow
  have hk1' : k ≠ 1 := by
    intro hk
    subst hk
    have h1 : (1 : ℝ) ≤ ε₀ ^ (-alphaExponent β) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε₀ hε₀1 (by linarith)
    have : (n : ℝ) ≤ ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (1 - 1)) := by
      rw [Nat.sub_self, mul_zero, pow_zero, mul_one]
      calc (n : ℝ) ≤ N := by exact_mod_cast hnN
        _ = 1 * N := (one_mul _).symm
        _ ≤ ε₀ ^ (-alphaExponent β) * N := mul_le_mul_of_nonneg_right h1 hN0.le
    linarith
  rw [ite_eq_right hk1']
  refine (hN n).trans (ENNReal.ofReal_le_ofReal ?_)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hA0 : 0 ≤ A := by
    have := truncatedDipoleNormalization_nonneg' χ N β lam (ε₀ * truncationScale p₀ β lam)
    positivity
  -- `X/n < ε₀^α`
  have hXn : X / n ≤ ε₀ ^ alphaExponent β := by
    rw [hthr_eq] at hbelow
    rw [div_le_iff₀ hn0]
    have hpos : 0 < ε₀ ^ alphaExponent β := Real.rpow_pos_of_pos hε₀ _
    have h1 : ε₀ ^ alphaExponent β * ε₀ ^ (-alphaExponent β) = 1 := by
      rw [← Real.rpow_add hε₀, add_neg_cancel, Real.rpow_zero]
    nlinarith [mul_lt_mul_of_pos_left hbelow hpos]
  have hpow : (X / n) ^ ((n : ℝ) / k) ≤ (ε₀ ^ (alphaExponent β / k)) ^ n := by
    calc (X / n) ^ ((n : ℝ) / k) ≤ (ε₀ ^ alphaExponent β) ^ ((n : ℝ) / k) :=
          Real.rpow_le_rpow (by positivity) hXn (by positivity)
      _ = (ε₀ ^ (alphaExponent β / k)) ^ n := by
          rw [← Real.rpow_mul hε₀.le, ← Real.rpow_natCast, ← Real.rpow_mul hε₀.le]
          congr 1
          field_simp
  have hXeq : (N : ℝ) * lam ^ (2 * (k - 1)) / n = X / n := rfl
  rw [hXeq, mul_one, div_eq_mul_one_div (n : ℝ) (N : ℝ), mul_pow C]
  have hCn : 0 ≤ C ^ n := by positivity
  have hAn : 0 ≤ A ^ n * ((n : ℝ) * (1 / N)) ^ n := by positivity
  calc A ^ n * ((n : ℝ) * (1 / N)) ^ n * (C ^ n * (X / n) ^ ((n : ℝ) / k))
      ≤ A ^ n * ((n : ℝ) * (1 / N)) ^ n * (C ^ n * (ε₀ ^ (alphaExponent β / k)) ^ n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hCn) hAn
    _ = _ := by ring

end TypeTwoTwo

/-! ### The class `(2,1)` and type 2 -/

/-- `e^{-t n} = (e^{-t})^n` and `n/N = n · (1/N)`. -/
theorem lemma_form_eq (A t E : ℝ) (n N : ℕ) :
    A ^ n * ((n : ℝ) / N) ^ n * (Real.exp (-(t * n)) * E) =
      A ^ n * ((n : ℝ) * (1 / N)) ^ n * Real.exp (-t) ^ n * E := by
  rw [show -(t * n) = (n : ℝ) * (-t) by ring, Real.exp_nat_mul, div_eq_mul_one_div (n : ℝ)]
  ring

section TypeTwo

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β M : ℝ}

/-- **The class `(2,1)`** (Lemma 5.41, both cases): for `s ≥ 1` and `ε₀` small, there is `C` such
that for `λ` small and `N` large,
`Z^{(2,1)}_{bad,n} ≤ (N C_{β,λ,ε₀})^n (n/N)^n e^{-s n} e^{C N δ}`. -/
theorem typeTwoOne_bound (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) (hM : 0 ≤ M) :
    ∀ s : ℝ, 1 ≤ s → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
          typeTwoOnePartitionFunction χ p₀ β lam M ε₀ N n ≤
            ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
                (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) * (1 / N)) ^ n *
              Real.exp (-s) ^ n * Real.exp (C * N * errorRate p₀ β lam)) := by
  intro s hs
  by_cases h4 : β < 4
  · obtain ⟨ε₁, hε₁, h⟩ := lemma_5_41_low hχ hp₀ hβ h4 hM s hs
    refine ⟨min ε₁ 1, lt_min hε₁ one_pos, min_le_right _ _, fun ε₀ hε₀ hlt => ?_⟩
    obtain ⟨C, hC, lam₀, hlam₀, hl⟩ := h ε₀ hε₀ (hlt.trans_le (min_le_left _ _))
    refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt' => ?_⟩
    filter_upwards [hl lam hlam hlt'] with N hN n
    refine (hN n).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [lemma_form_eq]
    have hA : 0 ≤ (N * truncatedDipoleNormalization χ N β lam
        (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) * (1 / N)) ^ n * Real.exp (-s) ^ n := by
      have := truncatedDipoleNormalization_nonneg' χ N β lam (ε₀ * truncationScale p₀ β lam)
      positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hA
    have herr := lowError_le_errorRate (lam := lam) hβ h4 hp₀
    have hCN : 0 ≤ C * N := by positivity
    calc C * N * ((criticalScale β lam).toReal ^ 2)⁻¹ *
          (1 + if β = transitionBeta (pBeta p₀ β + 1) then |Real.log lam| else 0)
        = C * N * (((criticalScale β lam).toReal ^ 2)⁻¹ *
          (1 + if β = transitionBeta (pBeta p₀ β + 1) then |Real.log lam| else 0)) := by ring
      _ ≤ C * N * errorRate p₀ β lam := mul_le_mul_of_nonneg_left herr hCN
  · obtain ⟨C, hC, h⟩ := lemma_5_41_high hχ hp₀ (not_lt.mp h4) hM s hs
    refine ⟨1, one_pos, le_rfl, fun ε₀ hε₀ hlt => ?_⟩
    obtain ⟨lam₀, hlam₀, hl⟩ := h ε₀ hε₀ hlt.le
    refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt' => ?_⟩
    filter_upwards [hl lam hlam hlt'] with N hN n
    refine (hN n).trans (le_of_eq ?_)
    rw [lemma_form_eq, errorRate_of_four_le (not_lt.mp h4)]

/-- **Type 2** (eq. (5.132) with Lemmas 5.41 and 5.42): for `s ≥ 1` and `ε₀` small
(depending on `s`), there is `C` such that for `λ` small and `N` large, for `n ≤ N`,
`Z^{(2)}_{bad,n} ≤ (N C_{β,λ,ε₀})^n n! N^{-n} ((p+1)e^{1-s})^n e^{C N δ}`.
The factor `n!` is retained for the outer multinomial in (5.115). -/
theorem typeTwo_factorial_bound (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) (hM : 0 ≤ M) :
    ∀ s : ℝ, 1 ≤ s → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, n ≤ N →
          typeTwoPartitionFunction χ p₀ β lam M ε₀ N n ≤
            ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
                (ε₀ * truncationScale p₀ β lam)) ^ n * (n.factorial * (1 / (N : ℝ)) ^ n) *
              ((pBeta p₀ β + 1) * Real.exp (1 - s)) ^ n * Real.exp (C * N * errorRate p₀ β lam)) := by
  intro s hs
  set p := pBeta p₀ β with hp
  have hp1 : 1 ≤ p := one_le_pBeta' hp₀ hβ
  have hα := alphaExponent_pos β
  obtain ⟨ε₂₁, hε₂₁, hε₂₁1, h21⟩ := typeTwoOne_bound hχ hp₀ hβ hM s hs
  -- the classes `(2,2,k)`, uniformly in `k`
  obtain ⟨C₂₂, hC₂₂, h22⟩ := exists_pos_forall_finset (Finset.Icc 1 p)
    (P := fun k C => ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, n ≤ N →
        typeTwoTwoPartitionFunction χ k p₀ β lam M ε₀ N n ≤
          ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
              (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) * (1 / N)) ^ n *
            (if k = 1 then 0 else C * ε₀ ^ (alphaExponent β / k)) ^ n * 1))
    (fun k C C' hC hCC' h ε₀ hε₀ hε₀1 => by
      obtain ⟨lam₀, hlam₀, hl⟩ := h ε₀ hε₀ hε₀1
      refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
      filter_upwards [hl lam hlam hlt] with N hN n hn
      refine (hN n hn).trans (ENNReal.ofReal_le_ofReal ?_)
      have hA : 0 ≤ (N * truncatedDipoleNormalization χ N β lam
          (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) * (1 / N)) ^ n := by
        have := truncatedDipoleNormalization_nonneg' χ N β lam (ε₀ * truncationScale p₀ β lam)
        positivity
      rw [mul_one, mul_one]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ n) hA
      · split_ifs
        · exact le_rfl
        · have := Real.rpow_nonneg hε₀.le (alphaExponent β / k)
          positivity
      · split_ifs
        · exact le_rfl
        · exact mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg hε₀.le _))
    (fun k hk => typeTwoTwo_bound hχ hp₀ hβ (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2 hM)
  -- the smallness of `ε₀`
  set εw := min 1 ((Real.exp (-s) / C₂₂) ^ ((p : ℝ) / alphaExponent β)) with hεw
  have hεw0 : 0 < εw := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hsmall : ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ εw → ∀ k : ℕ, 1 ≤ k → k ≤ p →
      C₂₂ * ε₀ ^ (alphaExponent β / k) ≤ Real.exp (-s) := by
    intro ε₀ hε₀ hle k hk1 hkp
    have hε₀1 : ε₀ ≤ 1 := hle.trans (min_le_left _ _)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have h1 : ε₀ ^ (alphaExponent β / k) ≤ ε₀ ^ (alphaExponent β / p) :=
      Real.rpow_le_rpow_of_exponent_ge hε₀ hε₀1 (div_le_div_of_nonneg_left hα.le hk0
        (by exact_mod_cast hkp))
    have h2 : ε₀ ^ (alphaExponent β / p) ≤
        ((Real.exp (-s) / C₂₂) ^ ((p : ℝ) / alphaExponent β)) ^ (alphaExponent β / p) :=
      Real.rpow_le_rpow hε₀.le (hle.trans (min_le_right _ _)) (by positivity)
    have h3 : ((Real.exp (-s) / C₂₂) ^ ((p : ℝ) / alphaExponent β)) ^ (alphaExponent β / p) =
        Real.exp (-s) / C₂₂ := by
      rw [← Real.rpow_mul (by positivity)]
      rw [show (p : ℝ) / alphaExponent β * (alphaExponent β / p) = 1 by field_simp,
        Real.rpow_one]
    have h4 : ε₀ ^ (alphaExponent β / k) ≤ Real.exp (-s) / C₂₂ := h1.trans (h2.trans h3.le)
    rw [le_div_iff₀ hC₂₂] at h4
    linarith
  refine ⟨min ε₂₁ εw, lt_min hε₂₁ hεw0, (min_le_left _ _).trans hε₂₁1,
    fun ε₀ hε₀ hlt => ?_⟩
  have hε₀1 : ε₀ ≤ 1 := (hlt.le.trans (min_le_left _ _)).trans hε₂₁1
  obtain ⟨C, hC, lam₁, hlam₁, h21'⟩ := h21 ε₀ hε₀ (hlt.trans_le (min_le_left _ _))
  obtain ⟨lam₂, hlam₂, h22'⟩ := exists_pos_forall_finset' (Finset.Icc 1 p)
    (P := fun k l => ∀ lam : ℝ, 0 < lam → lam < l → ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, n ≤ N →
        typeTwoTwoPartitionFunction χ k p₀ β lam M ε₀ N n ≤
          ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
              (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) * (1 / N)) ^ n *
            (if k = 1 then 0 else C₂₂ * ε₀ ^ (alphaExponent β / k)) ^ n * 1))
    (fun k l l' _ hll' h lam hlam hlt => h lam hlam (hlt.trans_le hll'))
    (fun k hk => h22 k hk ε₀ hε₀ hε₀1)
  refine ⟨C, hC, min lam₁ lam₂, lt_min hlam₁ hlam₂, fun lam hlam hlt' => ?_⟩
  have hlt1 : lam < lam₁ := hlt'.trans_le (min_le_left _ _)
  have hlt2 : lam < lam₂ := hlt'.trans_le (min_le_right _ _)
  filter_upwards [h21' lam hlam hlt1,
    (eventually_all_finset (Finset.Icc 1 p)).2 fun k hk => h22' k hk lam hlam hlt2,
    eventually_ge_atTop 1] with N hN21 hN22 hN1 n hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set A := (N : ℝ) * truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam)
  have hA0 : 0 ≤ A := by
    have := truncatedDipoleNormalization_nonneg' χ N β lam (ε₀ * truncationScale p₀ β lam)
    positivity
  have hq := one_le_clusterThreshold (p₀ := p₀) hβ
  have hh : 0 < cutoff p₀ β lam ε₀ := by
    unfold cutoff
    exact mul_pos hε₀ (Appendix.truncationScale_pos hlam)
  -- The individual type-2 class normalizations are retained through the count.
  set w : Fin (p + 1) → ℝ := fun j =>
    if (j : ℕ) = 0 then Real.exp (-s) else
      if (j : ℕ) = 1 then 0 else C₂₂ * ε₀ ^ (alphaExponent β / (j : ℕ)) with hw
  set E : Fin (p + 1) → ℝ := fun j =>
    if (j : ℕ) = 0 then Real.exp (C * N * errorRate p₀ β lam) else 1 with hE
  have hw0 : ∀ j, 0 ≤ w j := fun j => by
    simp only [hw]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
    · have := Real.rpow_nonneg hε₀.le (alphaExponent β / (j : ℕ))
      positivity
  have hE0 : ∀ j, 0 ≤ E j := fun j => by
    simp only [hE]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact zero_le_one
  have hwle : ∀ j, w j ≤ Real.exp (-s) := fun j => by
    simp only [hw]
    split_ifs with h0 h1
    · exact le_rfl
    · exact (Real.exp_pos _).le
    · exact hsmall ε₀ hε₀ (hlt.le.trans (min_le_right _ _)) j (by omega)
        (Nat.lt_succ_iff.1 j.2)
  have hZ : ∀ (j : Fin (p + 1)) (k : ℕ), k ≤ n →
      typeTwoClassPartitionFunction χ p₀ β lam M ε₀ N j k ≤
        ENNReal.ofReal (A ^ k * (k * (1 / N)) ^ k * w j ^ k * E j) := by
    intro j k hk
    unfold typeTwoClassPartitionFunction
    by_cases h0 : (j : ℕ) = 0
    · rw [ite_eq_left h0]
      simp only [hw, hE, h0, ite_true]
      exact hN21 k
    · rw [ite_eq_right h0]
      have hj := hN22 (j : ℕ) (Finset.mem_Icc.2 ⟨by omega, Nat.lt_succ_iff.1 j.2⟩) k
        (hk.trans hn)
      refine hj.trans (le_of_eq ?_)
      simp only [hw, hE, h0, ite_false]
  have hsplit := typeTwoPartitionFunction_le_sum (M := M) hχ hq hh (by linarith) hlam N n
  refine hsplit.trans ((sum_entropy_le (x := 1 / (N : ℝ)) hA0 (by positivity) (Real.exp_pos (-s)).le hE0
    (fun j k hk => (hZ j k hk).trans (ENNReal.ofReal_le_ofReal (by
      have hAk : 0 ≤ A ^ k * (k * (1 / N)) ^ k := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hw0 j) (hwle j) k) hAk) (hE0 j))))).trans
    (ENNReal.ofReal_le_ofReal ?_))
  have hprodE : ∏ j, E j = Real.exp (C * N * errorRate p₀ β lam) := by
    rw [Fin.prod_univ_succ]
    simp only [hE, Fin.val_zero, ite_true, Fin.val_succ, Nat.succ_ne_zero, ite_false,
      Finset.prod_const_one, mul_one]
  rw [hprodE]
  rw [show Real.exp 1 * Real.exp (-s) = Real.exp (1 - s) by
    rw [← Real.exp_add, sub_eq_add_neg]]
  push_cast
  exact le_rfl

end TypeTwo

/-! ### Proposition 5.38 -/

theorem disjoint_fiber {m K : ℕ} (f : Fin m → Fin K) {i j : Fin K} (hij : i ≠ j) :
    Disjoint (fiber f i) (fiber f j) := by
  rw [Finset.disjoint_left]
  intro a hi hj
  rw [mem_fiber] at hi hj
  exact hij (hi.symm.trans hj)

theorem fiber_three_cover {m : ℕ} (f : Fin m → Fin 3) :
    fiber f 0 ∪ fiber f 1 ∪ fiber f 2 = univ := by
  refine eq_univ_of_forall fun a => ?_
  have h3 := (f a).isLt
  have : (f a : ℕ) = 0 ∨ (f a : ℕ) = 1 ∨ (f a : ℕ) = 2 := by omega
  simp only [mem_union, mem_fiber]
  rcases this with h | h | h
  · exact Or.inl (Or.inl (Fin.ext h))
  · exact Or.inl (Or.inr (Fin.ext h))
  · exact Or.inr (Fin.ext h)

section Prop538

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β M : ℝ}

/-- **Proposition 5.38**, written
multiplicatively: for every `t ≥ 1` there is `ε₁ ∈ (0, 1]` such that for `ε₀ ∈ (0, ε₁)` there is `C`
such that for `λ` small and `N` large, for every `m ≤ N`,
`binom(N, m) Z_{bad,m} e^{t m} ≤ (N C_{β,λ,ε₀})^m e^{C N δ_{β,λ}}`. -/
theorem bad_points_bound (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) (hM : 0 ≤ M) :
    ∀ t : ℝ, 1 ≤ t → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m ≤ N →
          (N.choose m : ℝ≥0∞) * badPartitionFunction p₀ β lam M ε₀ N m *
              ENNReal.ofReal (Real.exp (t * m)) ≤
            ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
                (ε₀ * truncationScale p₀ β lam)) ^ m * Real.exp (C * N * errorRate p₀ β lam)) := by
  intro t ht
  obtain ⟨C₃₉, hC₃₉, h39⟩ := lemma_5_39 (χ := χ) hχ hp₀ hβ hM
  set p := pBeta p₀ β
  set u := t + 1 + Real.log (3 * (p + 1)) with hu
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hlogp : 0 ≤ Real.log (3 * (p + 1)) := Real.log_nonneg (by linarith)
  have hu1 : 1 ≤ u := by linarith
  set c := Real.exp (C₃₉ * u) with hc
  set s := u + c with hs
  have hs1 : 1 ≤ s := by have := Real.exp_pos (C₃₉ * u); linarith
  have hcs : Real.exp c * Real.exp (-s) = Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; rw [hs]; ring
  have hcount : 3 * ((p + 1) * Real.exp (1 - u)) = Real.exp (-t) := by
    rw [hu, show 1 - (t + 1 + Real.log (3 * (p + 1))) =
      -t - Real.log (3 * (p + 1)) by ring, Real.exp_sub,
      Real.exp_log (by positivity)]
    field_simp
  obtain ⟨ε₂, hε₂, hε₂1, h2⟩ := typeTwo_factorial_bound hχ hp₀ hβ hM s hs1
  refine ⟨ε₂, hε₂, hε₂1, fun ε₀ hε₀ hlt => ?_⟩
  have hε₀1 : ε₀ ≤ 1 := hlt.le.trans hε₂1
  obtain ⟨C₄₀, hC₄₀, lam₄₀, hlam₄₀, h40⟩ := lemma_5_40 (χ := χ) hχ hp₀ hβ ε₀ hε₀ hε₀1
  obtain ⟨C₂, hC₂, lam₂, hlam₂, h2'⟩ := h2 ε₀ hε₀ hlt
  obtain ⟨lam₃₉, hlam₃₉, h39'⟩ := h39 u hu1 ε₀ hε₀ hε₀1
  refine ⟨Real.exp (C₄₀ * s) + C₂, by positivity, min lam₄₀ (min lam₂ lam₃₉),
    lt_min hlam₄₀ (lt_min hlam₂ hlam₃₉), fun lam hlam hlt' => ?_⟩
  have hl40 : lam < lam₄₀ := hlt'.trans_le (min_le_left _ _)
  have hl2 : lam < lam₂ := hlt'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hl39 : lam < lam₃₉ := hlt'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  filter_upwards [h40 lam hlam hl40, h2' lam hlam hl2, h39' lam hlam hl39,
    eventually_ge_atTop 1] with N hN40 hN2 hN39 hN1 m hm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set A := (N : ℝ) * truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam)
  have hA0 : 0 ≤ A := by
    have := truncatedDipoleNormalization_nonneg' χ N β lam (ε₀ * truncationScale p₀ β lam)
    positivity
  set δ := errorRate p₀ β lam
  have hδ : 0 ≤ δ := (errorRate_pos hβ hlam).le
  set E₁ := Real.exp (Real.exp (C₄₀ * s) * N * δ)
  set E₂ := Real.exp (C₂ * N * δ)
  -- Lemma 5.39 at `u`, with the other bounds at `s`.
  set Z : Fin 3 → ℕ → ℝ≥0∞ := fun j k =>
    if (j : ℕ) = 0 then ENNReal.ofReal (Real.exp (c * k)) * typeOnePartitionFunction p₀ β lam ε₀ N k
    else if (j : ℕ) = 1 then
      ENNReal.ofReal (Real.exp (c * k)) * typeTwoPartitionFunction χ p₀ β lam M ε₀ N k
    else ENNReal.ofReal (A ^ k * (k * (1 / N)) ^ k * Real.exp (-u) ^ k * 1) with hZdef
  set w : ℝ := (p + 1) * Real.exp (1 - u)
  set E : Fin 3 → ℝ := fun j => if (j : ℕ) = 0 then E₁ else if (j : ℕ) = 1 then E₂ else 1 with hEdef
  have hE0 : ∀ j, 0 ≤ E j := fun j => by
    simp only [hEdef]
    split_ifs <;> positivity
  have hw0 : 0 ≤ w := by positivity
  have hewu : Real.exp 1 * Real.exp (-u) ≤ w := by
    rw [← Real.exp_add]
    change Real.exp (1 - u) ≤ (p + 1) * Real.exp (1 - u)
    nlinarith [Real.exp_pos (1 - u)]
  have hconvert (k : ℕ) (e : ℝ) (he : 0 ≤ e) :
      A ^ k * (k * (1 / N)) ^ k * Real.exp (-u) ^ k * e ≤
        A ^ k * (k.factorial * (1 / (N : ℝ)) ^ k) * w ^ k * e := by
    refine (power_normalization_le_factorial hA0 (by positivity)
      (Real.exp_pos _).le he k).trans ?_
    gcongr
  have hZ : ∀ (j : Fin 3) (k : ℕ), k ≤ m →
      Z j k ≤ ENNReal.ofReal (A ^ k * (k.factorial * (1 / (N : ℝ)) ^ k) * w ^ k * E j) := by
    intro j k hk
    have hexp : ∀ e : ℝ, ENNReal.ofReal (Real.exp (c * k)) *
        ENNReal.ofReal (A ^ k * (k * (1 / N)) ^ k * Real.exp (-s) ^ k * e) =
        ENNReal.ofReal (A ^ k * (k * (1 / N)) ^ k * Real.exp (-u) ^ k * e) := by
      intro e
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [← hcs, mul_pow, show Real.exp (c * k) = Real.exp c ^ k by
        rw [mul_comm, Real.exp_nat_mul]]
      ring
    simp only [hZdef, hEdef]
    by_cases h0 : (j : ℕ) = 0
    · simp only [h0, ite_true]
      refine (mul_le_mul_right (hN40 s hs1 k) _).trans ?_
      rw [lemma_form_eq, hexp]
      exact ENNReal.ofReal_le_ofReal (hconvert k E₁ (by positivity))
    · by_cases h1 : (j : ℕ) = 1
      · simp only [h1, ite_true, show (1 : ℕ) ≠ 0 by decide, ite_false]
        refine (mul_le_mul_right (hN2 k (hk.trans hm)) _).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        have hcw : Real.exp c * ((p + 1) * Real.exp (1 - s)) = w := by
          change _ = (p + 1) * Real.exp (1 - u)
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          rw [hs]
          ring
        rw [show Real.exp (c * k) = Real.exp c ^ k by
          rw [mul_comm, Real.exp_nat_mul], ← hcw, mul_pow]
        dsimp only [p]
        simp only [mul_pow]
        ring
      · simp only [h0, h1, ite_false]
        exact ENNReal.ofReal_le_ofReal (hconvert k 1 zero_le_one)
  -- eq. (5.115) and Lemma 5.39
  have htyped : ∀ f : Fin m → Fin 3,
      typedBadPartitionFunction p₀ β lam M ε₀ N m (fiber f 0) (fiber f 1) (fiber f 2) ≤
        ∏ j, Z j (fiber f j).card := by
    intro f
    refine (hN39 m (fiber f 0) (fiber f 1) (fiber f 2) (disjoint_fiber f (by decide))
      (disjoint_fiber f (by decide)) (disjoint_fiber f (by decide)) (fiber_three_cover f)).trans
      (le_of_eq ?_)
    rw [Fin.prod_univ_three]
    simp only [hZdef, Fin.val_zero, Fin.val_one, Fin.val_two, ite_true, ite_false,
      show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide]
    set n₁ := (fiber f 0).card
    set n₂ := (fiber f 1).card
    set n₃ := (fiber f 2).card
    have hsplit : A ^ n₃ * ((n₃ : ℝ) / N) ^ n₃ * (Real.exp (-(u * n₃)) *
        Real.exp (Real.exp (C₃₉ * u) * (n₁ + n₂))) =
        Real.exp (c * n₁) * Real.exp (c * n₂) *
          (A ^ n₃ * ((n₃ : ℝ) * (1 / N)) ^ n₃ * Real.exp (-u) ^ n₃ * 1) := by
      rw [show -(u * n₃) = (n₃ : ℝ) * (-u) by ring, Real.exp_nat_mul, ← hc,
        mul_add, Real.exp_add, div_eq_mul_one_div (n₃ : ℝ)]
      ring
    rw [hsplit, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  have hsum := badPartitionFunction_le_sum p₀ β lam M ε₀ N m
  have hbad : badPartitionFunction p₀ β lam M ε₀ N m ≤
      ENNReal.ofReal (A ^ m * (m.factorial * (1 / (N : ℝ)) ^ m) *
        (3 * w) ^ m * ∏ j, E j) :=
    hsum.trans ((Finset.sum_le_sum fun f _ => htyped f).trans
      (sum_factorial_le hA0 (by positivity) hw0 hE0 hZ))
  have hprodE : ∏ j, E j = E₁ * E₂ := by
    rw [Fin.prod_univ_three]
    simp only [hEdef, Fin.val_zero, Fin.val_one, Fin.val_two, ite_true, ite_false,
      show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      mul_one]
  change 3 * w = Real.exp (-t) at hcount
  rw [hcount, hprodE] at hbad
  -- The combined multinomial entropy costs have already been absorbed in `u`.
  -- Only `binom(N,m) m! / N^m` remains.
  have hchoose := choose_factorial_le (m := m) hN1
  calc (N.choose m : ℝ≥0∞) * badPartitionFunction p₀ β lam M ε₀ N m *
        ENNReal.ofReal (Real.exp (t * m))
      ≤ ENNReal.ofReal (N.choose m : ℝ) *
          ENNReal.ofReal (A ^ m * (m.factorial * (1 / (N : ℝ)) ^ m) *
            Real.exp (-t) ^ m * (E₁ * E₂)) * ENNReal.ofReal (Real.exp (t * m)) := by
        rw [ENNReal.ofReal_natCast]
        gcongr
    _ = ENNReal.ofReal (A ^ m * (E₁ * E₂) *
          ((N.choose m : ℝ) * (m.factorial * (1 / (N : ℝ)) ^ m))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show Real.exp (-t) ^ m = Real.exp (-(t * m)) by
          rw [← Real.exp_nat_mul]; congr 1; ring]
        rw [show Real.exp (t * m) = (Real.exp (-(t * m)))⁻¹ by rw [Real.exp_neg, inv_inv]]
        field_simp
    _ ≤ ENNReal.ofReal (A ^ m * (E₁ * E₂) * 1) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hchoose (by positivity))
    _ = ENNReal.ofReal (A ^ m * Real.exp ((Real.exp (C₄₀ * s) + C₂) * N * δ)) := by
        congr 1
        rw [mul_one, ← Real.exp_add]
        congr 2
        ring

end Prop538

end UpperBoundLDP

end MultipoleBKT

end
