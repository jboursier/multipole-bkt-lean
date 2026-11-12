/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.Canonical
public import MultipoleBKT.RateFunction.HypertreeCount
public import MultipoleBKT.Frozen.RateFunction
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Convergence of the cluster series in the rate function

Let `h(γ) = ∑_{n ≥ 1} ∑_{m ∈ ℕ^p} rateSeriesTerm p kmult γ n m` be the cluster part of the
rate function `ℐ_{β,p,λ}` (Definition 2.15; the function `h` in Step 1 of the proof of Theorem 2). Under the coefficient bound (2.48),

  `|𝗄^mult((#_k X)_k)| ≤ C λ^{2(|X| - 1)}` for subpartitions `X` with `|V_X| ≤ p`,

we prove that for `λ` small enough (depending on `C` and `p`) the `(n, m)` term is bounded by
`C' λ² 2^{-n} 2^{-(m_1 + ⋯ + m_p)}` uniformly for `|γ_i| ≤ 2`, even after multiplication by
`8^{m_1 + ⋯ + m_p}` (`MultipoleBKT.abs_rateSeriesTerm_one_mul_le`). Consequently the series
is absolutely summable over `(n, m)` and `|h(γ)| ≤ C' λ²`
(`MultipoleBKT.rateSeries_summable_and_bound`), which is the first claim of Step 1 of the proof
of Theorem 2.

## Route

As in Step 1 of the proof of Theorem 2, we bound the terms of each degree directly. With
`M = m_1 + ⋯ + m_p = |Y(m)|` blocks, a hypertree `X` with `X_1 ∪ ⋯ ∪ X_n = Y(m)` has
`∑ᵢ (|X_i| - 1) = M - 1` and `n < M`, so (2.48) bounds the product of the activities by
`C^n λ^{2(M-1)}`, and the weighted hypertree count `∑_X ω(X) ≤ n^M (M + n)^n`
(`MultipoleBKT.sum_hypertreeWeight_le`) together with `n^M ≤ M! e^n`,
`(M + n)^n ≤ n! e^{M+n}` and `M!/∏ᵢ mᵢ! ≤ p^M` bounds the `(n, m)` coefficient by
`(p e³ max(C, 1))^M λ^{2(M-1)}` (`MultipoleBKT.abs_rateSeriesTerm_one_le`).
-/

@[expose] public section

namespace MultipoleBKT

open Finset Real
open scoped Nat

/-- The monomial `γ^m = ∏ᵢ γᵢ^{mᵢ}`. -/
noncomputable def piPow {p : ℕ} (m : Fin p → ℕ) (γ : Fin p → ℝ) : ℝ :=
  ∏ i, γ i ^ m i

/-- The `(n, m)` term of the cluster series is its value at `γ = 1` times the monomial `γ^m`. -/
theorem rateSeriesTerm_eq_mul_piPow (p : ℕ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) (n : ℕ+)
    (m : Fin p → ℕ) :
    rateSeriesTerm p kmult γ n m = rateSeriesTerm p kmult 1 n m * piPow m γ := by
  unfold rateSeriesTerm piPow
  have : ∏ i, γ i ^ m i / (m i)! = (∏ i, (1 : Fin p → ℝ) i ^ m i / (m i)!) * ∏ i, γ i ^ m i := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    simp only [Pi.one_apply, one_pow]
    ring
  rw [this]
  ring

/-- `|γ^m| ≤ R^{m_1 + ⋯ + m_p}` when `|γᵢ| ≤ R`. -/
theorem abs_piPow_le {p : ℕ} (m : Fin p → ℕ) {γ : Fin p → ℝ} {R : ℝ} (hγ : ∀ i, |γ i| ≤ R) :
    |piPow m γ| ≤ R ^ (∑ i, m i) := by
  rw [piPow, abs_prod, ← prod_pow_eq_pow_sum]
  refine prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hγ i) _

section Multinomial

/-- `M! ≤ p^M ∏ᵢ mᵢ!` for `M = m_1 + ⋯ + m_p`. -/
theorem factorial_sum_le_pow_mul_prod {p : ℕ} (m : Fin p → ℕ) :
    (∑ i, m i)! ≤ p ^ (∑ i, m i) * ∏ i, (m i)! := by
  have hspec := Nat.multinomial_spec (univ : Finset (Fin p)) m
  have hle : Nat.multinomial univ m ≤ p ^ (∑ i, m i) := by
    have h := sum_pow_eq_sum_piAntidiag (univ : Finset (Fin p)) (fun _ => (1 : ℕ)) (∑ i, m i)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one, one_pow,
      prod_const_one] at h
    rw [h]
    exact single_le_sum (f := fun k => Nat.multinomial univ k) (fun _ _ => Nat.zero_le _)
      (mem_piAntidiag.mpr ⟨rfl, fun i _ => mem_univ i⟩)
  rw [← hspec, mul_comm]
  exact Nat.mul_le_mul_right _ hle

end Multinomial

section CoefficientBound

variable {p : ℕ} {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

/-- The hypothesis (2.48) on the coefficients `𝗄^mult`, for one value of `λ`, with a uniform
constant `C`. -/
def KmultBound (p : ℕ) (kmult : (ℕ →₀ ℕ) → ℝ) (C lam : ℝ) : Prop :=
  ∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ p →
    |kmult (blockProfile X)| ≤ C * lam ^ (2 * ((X.card : ℤ) - 1))

/-- The product of the activities over a hypertree on `Y(m)` is at most
`max(C,1)^n λ^{2(M-1)}`. -/
theorem abs_ite_prod_kmult_le (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    {n : ℕ} {m : Fin p → ℕ} {X : Fin n → Finset (Finset ℕ)}
    (hX : X ∈ hypertrees n (canonicalPartition m))
    (hU : univ.biUnion X = canonicalPartition m) :
    |if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, kmult (blockProfile (X i)) else 0| ≤
      max C 1 ^ n * lam ^ (2 * ((∑ i, m i) - 1)) := by
  have hpos : 0 ≤ max C 1 ^ n * lam ^ (2 * ((∑ i, m i) - 1)) := by positivity
  split_ifs with hV
  · obtain ⟨hXA, h2, -, -⟩ := hypertrees_props hX
    have hsum := sum_card_sub_one_of_mem_hypertrees hX hU
    rw [card_canonicalPartition] at hsum
    rw [abs_prod]
    calc ∏ i, |kmult (blockProfile (X i))|
        ≤ ∏ i, (max C 1 * lam ^ (2 * ((X i).card - 1))) := by
          refine prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
          have h := hk (X i) (isSubpartition_of_subset_canonicalPartition (hXA i)) (hV i)
          have hexp : (2 * (((X i).card : ℤ) - 1)) = ((2 * ((X i).card - 1) : ℕ) : ℤ) := by
            have := h2 i
            push_cast [Nat.cast_sub (by omega : 1 ≤ (X i).card)]
            ring
          rw [hexp, zpow_natCast] at h
          exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      _ = max C 1 ^ n * lam ^ (2 * ((∑ i, m i) - 1)) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum,
            ← mul_sum, hsum]
  · rw [abs_zero]
    exact hpos

/-- The hypertree sum in the `(n, m)` term vanishes unless `n < M = m_1 + ⋯ + m_p` and is
bounded by `n^M (M + n)^n max(C,1)^n λ^{2(M-1)}`. -/
theorem abs_hypertreeSum_le (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (n : ℕ) (m : Fin p → ℕ) :
    |∑ X ∈ (hypertrees n (canonicalPartition m)).filter
          (fun X => univ.biUnion X = canonicalPartition m),
        (hypertreeWeight X : ℝ) *
          if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, kmult (blockProfile (X i)) else 0| ≤
      if n < ∑ i, m i then
        ((n : ℝ) ^ (∑ i, m i) * ((∑ i, m i : ℕ) + n : ℝ) ^ n) *
          (max C 1 ^ n * lam ^ (2 * ((∑ i, m i) - 1)))
      else 0 := by
  set S := (hypertrees n (canonicalPartition m)).filter
    (fun X => univ.biUnion X = canonicalPartition m)
  split_ifs with hn
  · calc _ ≤ ∑ X ∈ S, |(hypertreeWeight X : ℝ) *
            if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, kmult (blockProfile (X i)) else 0| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ X ∈ S, (hypertreeWeight X : ℝ) * (max C 1 ^ n * lam ^ (2 * ((∑ i, m i) - 1))) := by
          refine sum_le_sum fun X hXS => ?_
          obtain ⟨hX, hU⟩ := mem_filter.mp hXS
          rw [abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left (abs_ite_prod_kmult_le hk hlam hX hU)
            (Nat.cast_nonneg _)
      _ = (∑ X ∈ S, (hypertreeWeight X : ℝ)) * (max C 1 ^ n * lam ^ (2 * ((∑ i, m i) - 1))) :=
          (sum_mul _ _ _).symm
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h := sum_hypertreeWeight_le (canonicalPartition m) n
          rw [card_canonicalPartition] at h
          exact_mod_cast h
  · have hS : S = ∅ := by
      refine filter_eq_empty_iff.mpr fun X hX hU => hn ?_
      have := add_one_le_card_of_mem_hypertrees hX hU
      rw [card_canonicalPartition] at this
      omega
    rw [hS, sum_empty, abs_zero]

/-- The elementary inequality behind the coefficient bound. -/
private theorem coeff_real_le (p n M : ℕ) (hnM : n ≤ M) {P : ℝ} (hP : 0 ≤ P)
    (hPM : (M ! : ℝ) * P ≤ p ^ M) {D L : ℝ} (hD : 1 ≤ D) (hL : 0 ≤ L) :
    1 / (n ! : ℝ) * (P * (((n : ℝ) ^ M * ((M : ℝ) + n) ^ n) * (D ^ n * L))) ≤
      (p * exp 3 * D) ^ M * L := by
  have hn! : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have h1 : (n : ℝ) ^ M ≤ M ! * exp n := by
    have := pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) M
    rwa [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos M), mul_comm] at this
  have h2 : ((M : ℝ) + n) ^ n ≤ n ! * exp (M + n) := by
    have := pow_div_factorial_le_exp ((M : ℝ) + n) (by positivity) n
    rwa [div_le_iff₀ hn!, mul_comm] at this
  have h3 : D ^ n ≤ D ^ M := pow_le_pow_right₀ hD hnM
  have h4 : exp n * exp (M + n) ≤ exp 3 ^ M := by
    rw [← exp_add, ← exp_nat_mul]
    refine exp_le_exp.mpr ?_
    have : (n : ℝ) ≤ M := by exact_mod_cast hnM
    linarith
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  calc 1 / (n ! : ℝ) * (P * (((n : ℝ) ^ M * ((M : ℝ) + n) ^ n) * (D ^ n * L)))
      ≤ 1 / (n ! : ℝ) * (P * (((M ! * exp n) * (n ! * exp (M + n))) * (D ^ M * L))) := by
        gcongr
    _ = ((M ! : ℝ) * P) * (exp n * exp (M + n)) * D ^ M * L := by
        field_simp
    _ ≤ (p : ℝ) ^ M * exp 3 ^ M * D ^ M * L := by
        gcongr
    _ = (p * exp 3 * D) ^ M * L := by rw [mul_pow, mul_pow]

/-- **Coefficient bound.** Under (2.48), the coefficient of `γ^m` in the `(n, m)` term is at most
`(p e³ max(C, 1))^M λ^{2(M-1)}` in absolute value, `M = m_1 + ⋯ + m_p`, and vanishes unless
`n < M`. -/
theorem abs_rateSeriesTerm_one_le (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (n : ℕ+) (m : Fin p → ℕ) :
    |rateSeriesTerm p kmult 1 n m| ≤
      if (n : ℕ) < ∑ i, m i then (p * exp 3 * max C 1) ^ (∑ i, m i) * lam ^ (2 * ((∑ i, m i) - 1))
      else 0 := by
  set M := ∑ i, m i
  have hT := abs_hypertreeSum_le hk hlam n m
  unfold rateSeriesTerm
  rw [abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
  have hP : |∏ i, (1 : Fin p → ℝ) i ^ m i / ((m i)! : ℝ)| = ∏ i, 1 / ((m i)! : ℝ) := by
    simp only [Pi.one_apply, one_pow]
    exact abs_of_nonneg (prod_nonneg fun i _ => by positivity)
  rw [hP]
  have hP0 : 0 ≤ ∏ i, 1 / ((m i)! : ℝ) := prod_nonneg fun i _ => by positivity
  split_ifs at hT ⊢ with hn
  · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hP0) (by positivity)).trans ?_
    refine coeff_real_le p n M hn.le hP0 ?_ (le_max_right _ _) (by positivity)
    have h := factorial_sum_le_pow_mul_prod m
    have hprod : (0 : ℝ) < ∏ i, ((m i)! : ℝ) := prod_pos fun i _ => by positivity
    rw [prod_div_distrib, prod_const_one]
    rw [mul_one_div, div_le_iff₀ hprod]
    exact_mod_cast h
  · have : |∑ X ∈ (hypertrees n (canonicalPartition m)).filter
          (fun X => univ.biUnion X = canonicalPartition m),
        (hypertreeWeight X : ℝ) *
          if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, kmult (blockProfile (X i)) else 0| = 0 :=
      le_antisymm hT (abs_nonneg _)
    rw [this, mul_zero, mul_zero]

/-- The constant `K = 8 p e³ max(C, 1)` of the domination. -/
noncomputable def rateSeriesConst (p : ℕ) (C : ℝ) : ℝ :=
  8 * (p * exp 3 * max C 1)

theorem rateSeriesConst_nonneg (p : ℕ) (C : ℝ) : 0 ≤ rateSeriesConst p C := by
  unfold rateSeriesConst
  have : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
  positivity

/-- **Domination.** If `K λ² ≤ 1/4` with `K = 8 p e³ max(C, 1)`, then
`|coefficient(n, m)| 8^M ≤ 16 K² λ² 2^{-n} 2^{-M}`. -/
theorem abs_rateSeriesTerm_one_mul_le (hk : KmultBound p kmult C lam)
    (hlam : 0 ≤ lam) (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) (n : ℕ+) (m : Fin p → ℕ) :
    |rateSeriesTerm p kmult 1 n m| * 8 ^ (∑ i, m i) ≤
      16 * rateSeriesConst p C ^ 2 * lam ^ 2 * ((1 / 2) ^ (n : ℕ) * (1 / 2) ^ (∑ i, m i)) := by
  set M := ∑ i, m i
  set K := rateSeriesConst p C
  have hK : 0 ≤ K := rateSeriesConst_nonneg p C
  have h := abs_rateSeriesTerm_one_le hk hlam n m
  have hrhs : 0 ≤ 16 * K ^ 2 * lam ^ 2 * ((1 / 2 : ℝ) ^ (n : ℕ) * (1 / 2) ^ M) := by positivity
  split_ifs at h with hn
  · obtain ⟨j, hj⟩ : ∃ j, M = j + 2 := ⟨M - 2, by have := n.pos; omega⟩
    have hnj : (n : ℕ) ≤ j + 1 := by omega
    have hKl : 0 ≤ K * lam ^ 2 := by positivity
    have hx : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2) ^ (n : ℕ) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hnj
    have ha0 : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
    have hab : (1 / 2 : ℝ) ^ j ≤ 2 * (1 / 2) ^ (n : ℕ) := by
      rw [pow_succ] at hx
      linarith
    calc |rateSeriesTerm p kmult 1 n m| * 8 ^ M
        ≤ (p * exp 3 * max C 1) ^ M * lam ^ (2 * (M - 1)) * 8 ^ M :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = K ^ 2 * lam ^ 2 * (K * lam ^ 2) ^ j := by
          rw [hj, show 2 * (j + 2 - 1) = 2 * j + 2 by omega,
            show K = 8 * (p * exp 3 * max C 1) from rfl]
          ring
      _ ≤ K ^ 2 * lam ^ 2 * (1 / 4) ^ j := by
          gcongr
      _ = K ^ 2 * lam ^ 2 * ((1 / 2) ^ j * (1 / 2) ^ j) := by
          congr 1
          rw [← mul_pow]
          norm_num
      _ ≤ K ^ 2 * lam ^ 2 * ((1 / 2) ^ j * (4 * (1 / 2) ^ (n : ℕ))) := by
          gcongr
          linarith
      _ = 16 * K ^ 2 * lam ^ 2 * ((1 / 2) ^ (n : ℕ) * (1 / 2) ^ M) := by
          rw [hj]
          ring
  · rw [le_antisymm h (abs_nonneg _), zero_mul]
    exact hrhs

end CoefficientBound

section Geometric

/-- `∑_{m ∈ ℕ^p} r^{m_1 + ⋯ + m_p} = (1 - r)^{-p}` for `0 ≤ r < 1`. -/
theorem hasSum_pow_sum (p : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m : Fin p → ℕ => r ^ (∑ i, m i)) ((1 - r)⁻¹ ^ p) := by
  induction p with
  | zero =>
    convert hasSum_fintype (fun m : Fin 0 → ℕ => r ^ (∑ i, m i)) using 1
    simp
  | succ p ih =>
    rw [← (Fin.consEquiv fun _ : Fin (p + 1) => ℕ).hasSum_iff]
    have hfun : ((fun m : Fin (p + 1) → ℕ => r ^ (∑ i, m i)) ∘
        (Fin.consEquiv fun _ : Fin (p + 1) => ℕ)) =
        fun x : ℕ × (Fin p → ℕ) => r ^ x.1 * r ^ (∑ i, x.2 i) := by
      funext x
      simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero,
        Fin.cons_succ, pow_add]
    rw [hfun, pow_succ, mul_comm _ (1 - r)⁻¹]
    have hg := hasSum_geometric_of_lt_one hr0 hr1
    exact HasSum.mul (f := fun k : ℕ => r ^ k) (g := fun m : Fin p → ℕ => r ^ (∑ i, m i)) hg ih
      (Summable.mul_of_nonneg (f := fun k : ℕ => r ^ k)
        (g := fun m : Fin p → ℕ => r ^ (∑ i, m i)) hg.summable ih.summable
        (fun _ => by positivity) fun _ => by positivity)

/-- `∑_{n ≥ 1} 2^{-n} = 1`. -/
theorem hasSum_half_pow_pnat : HasSum (fun n : ℕ+ => (1 / 2 : ℝ) ^ (n : ℕ)) 1 := by
  refine (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => (1 / 2 : ℝ) ^ n)).mpr ?_
  have := hasSum_geometric_two.mul_left (1 / 2)
  have h2 : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [h2] at this
  refine this.congr_fun fun n => ?_
  simp only [pow_succ]
  ring

/-- The dominating series `∑_{n, m} 2^{-n} 2^{-(m_1 + ⋯ + m_p)} = 2^p`. -/
theorem hasSum_half_pow_prod (p : ℕ) :
    HasSum (fun nm : ℕ+ × (Fin p → ℕ) => (1 / 2 : ℝ) ^ (nm.1 : ℕ) * (1 / 2) ^ (∑ i, nm.2 i))
      (2 ^ p) := by
  have h1 := hasSum_half_pow_pnat
  have h2 := hasSum_pow_sum p (r := 1 / 2) (by norm_num) (by norm_num)
  have h := HasSum.mul (f := fun n : ℕ+ => (1 / 2 : ℝ) ^ (n : ℕ))
    (g := fun m : Fin p → ℕ => (1 / 2 : ℝ) ^ (∑ i, m i)) h1 h2
    (Summable.mul_of_nonneg (f := fun n : ℕ+ => (1 / 2 : ℝ) ^ (n : ℕ))
      (g := fun m : Fin p → ℕ => (1 / 2 : ℝ) ^ (∑ i, m i)) h1.summable h2.summable
      (fun _ => by positivity) fun _ => by positivity)
  have h3 : (1 : ℝ) * (1 - 1 / 2)⁻¹ ^ p = 2 ^ p := by norm_num
  rw [h3] at h
  exact h

end Geometric

section Summability

variable {p : ℕ} {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

/-- The dominating function `u(n, m) = 16 K² λ² 2^{-n} 2^{-M}`. -/
noncomputable def rateSeriesMajorant (p : ℕ) (C lam : ℝ) (nm : ℕ+ × (Fin p → ℕ)) : ℝ :=
  16 * rateSeriesConst p C ^ 2 * lam ^ 2 * ((1 / 2) ^ (nm.1 : ℕ) * (1 / 2) ^ (∑ i, nm.2 i))

theorem hasSum_rateSeriesMajorant (p : ℕ) (C lam : ℝ) :
    HasSum (rateSeriesMajorant p C lam) (16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2) := by
  have := (hasSum_half_pow_prod p).mul_left (16 * rateSeriesConst p C ^ 2 * lam ^ 2)
  rw [show 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 =
    16 * rateSeriesConst p C ^ 2 * lam ^ 2 * 2 ^ p by ring]
  exact this

theorem summable_rateSeriesMajorant (p : ℕ) (C lam : ℝ) :
    Summable (rateSeriesMajorant p C lam) :=
  (hasSum_rateSeriesMajorant p C lam).summable

theorem rateSeriesMajorant_nonneg (p : ℕ) (C lam : ℝ) (nm : ℕ+ × (Fin p → ℕ)) :
    0 ≤ rateSeriesMajorant p C lam nm := by
  unfold rateSeriesMajorant
  positivity

/-- `|coefficient(n, m)| · R^M · M^k ≤ u(n, m)` for `R ≤ 2` and `k ≤ 2`: the form used for the
series and its first two derivatives. -/
theorem abs_rateSeriesTerm_one_mul_pow_le (hk : KmultBound p kmult C lam)
    (hlam : 0 ≤ lam) (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) (nm : ℕ+ × (Fin p → ℕ))
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 2) {k : ℕ} (hk2 : k ≤ 2) :
    |rateSeriesTerm p kmult 1 nm.1 nm.2| * ((∑ i, nm.2 i : ℕ) : ℝ) ^ k * R ^ (∑ i, nm.2 i) ≤
      rateSeriesMajorant p C lam nm := by
  set M := ∑ i, nm.2 i
  have hMk : ((M : ℕ) : ℝ) ^ k * R ^ M ≤ 8 ^ M := by
    have h1 : ((M : ℕ) : ℝ) ^ k ≤ 4 ^ M := by
      have hM2 : (M : ℝ) ≤ 2 ^ M := by
        have := Nat.lt_two_pow_self (n := M)
        exact_mod_cast this.le
      have hM1 : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
      calc ((M : ℕ) : ℝ) ^ k ≤ ((2 : ℝ) ^ M) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hM2 k
        _ ≤ ((2 : ℝ) ^ M) ^ 2 := pow_le_pow_right₀ hM1 hk2
        _ = 4 ^ M := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h2 : R ^ M ≤ 2 ^ M := pow_le_pow_left₀ hR0 hR M
    calc ((M : ℕ) : ℝ) ^ k * R ^ M ≤ 4 ^ M * 2 ^ M := by gcongr
      _ = 8 ^ M := by rw [← mul_pow]; norm_num
  calc |rateSeriesTerm p kmult 1 nm.1 nm.2| * ((M : ℕ) : ℝ) ^ k * R ^ M
      = |rateSeriesTerm p kmult 1 nm.1 nm.2| * (((M : ℕ) : ℝ) ^ k * R ^ M) := by ring
    _ ≤ |rateSeriesTerm p kmult 1 nm.1 nm.2| * 8 ^ M :=
        mul_le_mul_of_nonneg_left hMk (abs_nonneg _)
    _ ≤ _ := abs_rateSeriesTerm_one_mul_le hk hlam hsmall nm.1 nm.2

/-- The terms of the cluster series are dominated by `u(n, m)` for `|γᵢ| ≤ 2`. -/
theorem abs_rateSeriesTerm_le_majorant (hk : KmultBound p kmult C lam)
    (hlam : 0 ≤ lam) (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ}
    (hγ : ∀ i, |γ i| ≤ 2) (nm : ℕ+ × (Fin p → ℕ)) :
    |rateSeriesTerm p kmult γ nm.1 nm.2| ≤ rateSeriesMajorant p C lam nm := by
  rw [rateSeriesTerm_eq_mul_piPow, abs_mul]
  have h := abs_rateSeriesTerm_one_mul_pow_le hk hlam hsmall nm (by norm_num : (0 : ℝ) ≤ 2)
    le_rfl (by norm_num : 0 ≤ 2)
  rw [pow_zero, mul_one] at h
  exact (mul_le_mul_of_nonneg_left (abs_piPow_le nm.2 hγ) (abs_nonneg _)).trans h

/-- Absolute summability of the cluster series for `|γᵢ| ≤ 2`, with the bound
`∑ |term| ≤ 16 K² 2^p λ²`. -/
theorem summable_abs_rateSeriesTerm (hk : KmultBound p kmult C lam)
    (hlam : 0 ≤ lam) (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ}
    (hγ : ∀ i, |γ i| ≤ 2) :
    Summable (fun nm : ℕ+ × (Fin p → ℕ) => ‖rateSeriesTerm p kmult γ nm.1 nm.2‖) :=
  (summable_rateSeriesMajorant p C lam).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun nm => abs_rateSeriesTerm_le_majorant hk hlam hsmall hγ nm

/-- The iterated sum in the rate function equals the joint sum over `(n, m)`, and is bounded by
`16 K² 2^p λ²`. -/
theorem rateCluster_eq_tsum_and_le (hk : KmultBound p kmult C lam)
    (hlam : 0 ≤ lam) (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ}
    (hγ : ∀ i, |γ i| ≤ 2) :
    ∑' n : ℕ+, ∑' m : Fin p → ℕ, rateSeriesTerm p kmult γ n m =
        ∑' nm : ℕ+ × (Fin p → ℕ), rateSeriesTerm p kmult γ nm.1 nm.2 ∧
      |∑' nm : ℕ+ × (Fin p → ℕ), rateSeriesTerm p kmult γ nm.1 nm.2| ≤
        16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 := by
  have hs := (summable_abs_rateSeriesTerm hk hlam hsmall hγ).of_norm
  refine ⟨(hs.tsum_prod).symm, ?_⟩
  calc |∑' nm : ℕ+ × (Fin p → ℕ), rateSeriesTerm p kmult γ nm.1 nm.2|
      ≤ ∑' nm : ℕ+ × (Fin p → ℕ), rateSeriesMajorant p C lam nm := by
        rw [← Real.norm_eq_abs]
        exact tsum_of_norm_bounded (hasSum_rateSeriesMajorant p C lam).summable.hasSum
          fun nm => abs_rateSeriesTerm_le_majorant hk hlam hsmall hγ nm
    _ = 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 :=
        (hasSum_rateSeriesMajorant p C lam).tsum_eq

/-- A threshold `λ₀` below which `K λ² ≤ 1/4`. -/
noncomputable def rateSeriesLam₀ (p : ℕ) (C : ℝ) : ℝ :=
  1 / (2 * (rateSeriesConst p C + 1))

theorem rateSeriesLam₀_pos (p : ℕ) (C : ℝ) : 0 < rateSeriesLam₀ p C := by
  have := rateSeriesConst_nonneg p C
  unfold rateSeriesLam₀
  positivity

theorem rateSeriesLam₀_le_half (p : ℕ) (C : ℝ) : rateSeriesLam₀ p C ≤ 1 / 2 := by
  have := rateSeriesConst_nonneg p C
  unfold rateSeriesLam₀
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem rateSeriesConst_mul_sq_le (p : ℕ) (C : ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hlam₀ : lam < rateSeriesLam₀ p C) : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4 := by
  set K := rateSeriesConst p C
  have hK := rateSeriesConst_nonneg p C
  have h1 : lam ^ 2 ≤ (1 / (2 * (K + 1))) ^ 2 := pow_le_pow_left₀ hlam hlam₀.le 2
  calc K * lam ^ 2 ≤ K * (1 / (2 * (K + 1))) ^ 2 := mul_le_mul_of_nonneg_left h1 hK
    _ = K / (K + 1) ^ 2 / 4 := by field_simp; ring
    _ ≤ 1 / 4 := by
        rw [div_le_div_iff_of_pos_right (by norm_num), div_le_one (by positivity)]
        nlinarith

/-- **Convergence and bounds** (absolute convergence of the cluster series, proof of Theorem 2, Step 1). For every `C > 0` and `p` there are `λ₀ > 0` and `C' > 0` such that for
`0 < λ < λ₀` and coefficients `kmult` satisfying (2.48) with constant `C`, the series
`∑_{n, m} rateSeriesTerm p kmult γ n m` converges absolutely for every `γ` with `|γᵢ| ≤ 2` (in
particular on `[0,1]^p ⊇ Δ_{p,x}`), and its sum `h(γ)` satisfies `|h(γ)| ≤ C' λ²`. -/
theorem rateSeries_summable_and_bound (p : ℕ) (C : ℝ) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∃ C' : ℝ, 0 < C' ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ kmult : (ℕ →₀ ℕ) → ℝ, KmultBound p kmult C lam →
        ∀ γ : Fin p → ℝ, (∀ i, |γ i| ≤ 2) →
          Summable (fun nm : ℕ+ × (Fin p → ℕ) => ‖rateSeriesTerm p kmult γ nm.1 nm.2‖) ∧
          |∑' n : ℕ+, ∑' m : Fin p → ℕ, rateSeriesTerm p kmult γ n m| ≤ C' * lam ^ 2 := by
  refine ⟨rateSeriesLam₀ p C, rateSeriesLam₀_pos p C,
    16 * rateSeriesConst p C ^ 2 * 2 ^ p + 1, by positivity, ?_⟩
  intro lam hlam hlam₀ kmult hk γ hγ
  have hsmall := rateSeriesConst_mul_sq_le p C hlam.le hlam₀
  refine ⟨summable_abs_rateSeriesTerm hk hlam.le hsmall hγ, ?_⟩
  obtain ⟨heq, hle⟩ := rateCluster_eq_tsum_and_le hk hlam.le hsmall hγ
  rw [heq]
  exact hle.trans (by nlinarith [sq_nonneg lam])

end Summability

end MultipoleBKT

end
