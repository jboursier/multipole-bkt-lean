/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneEstimates
public import MultipoleBKT.UpperBound.BadPointTypes.Normalization

/-!
# Lemma 5.40: control of the bad points of type 1

The paper: Lemma 5.40.
The finite sums first choose positive and negative bad-charge counts and sets, then
injective partner maps and same-sign partitions (`RouteTypeOne.successiveSum`).
The fixed-data integrals give (5.131).

`typeOnePartitionFunction_le_series` gives
`Z^{(1)}_{bad,n} ≤ (C n λ^{2-β})ⁿ S_n(N δ)`, where the two indices of `S_n` count positive
and negative blocks, including singletons. Step 6 (proof of Lemma 5.40) absorbs the constraint
`n ≤ (q+1)(k₀⁺+k₀⁻)` and sums the two exponential series.

`lemma_5_40` retains its multiplicative statement for every `n`, for small `λ` and large `N`.
The latter conditions ensure the standing cutoff condition and the lower normalization bound.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset MeasureTheory Filter
open scoped ENNReal

variable {p₀ : ℕ} {β lam ε₀ : ℝ}

/-- **Lemma 5.40, explicit form**: for `β > 2`, `p₀ ≥ 1`, `ε₀ ∈ (0, 1]` there is `C > 0` such that
for `0 < λ ≤ 1` with `λ ≤ ε₀ R̄` and every `N`, `n`,
`Z^{(1)}_{bad,n} ≤ (C n λ^{2-β})ⁿ S_n(N δ_{β,λ})`. -/
theorem typeOnePartitionFunction_le_series (hp₀ : 1 ≤ p₀) (hβ : 2 < β) (hε₀ : 0 < ε₀)
    (hε₀1 : ε₀ ≤ 1) : ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      lam ≤ cutoff p₀ β lam ε₀ → ∀ Nₐ n : ℕ,
        typeOnePartitionFunction p₀ β lam ε₀ Nₐ n ≤
          ENNReal.ofReal ((C * n * lam ^ (2 - β)) ^ n *
            typeOneSeries (clusterThreshold p₀ β) n (Nₐ * errorRate p₀ β lam)) := by
  obtain ⟨CX, hCX, hX⟩ := crowdSum_le (p₀ := p₀) hβ
  obtain ⟨CY, hCY, hY⟩ := singleTerm_le (p₀ := p₀) hβ hε₀
  obtain ⟨Cg, hCg, hg⟩ := goodIntegral_le (p₀ := p₀) hβ hε₀ hε₀1
  set M := max 1 (max CX (max CY Cg)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  refine ⟨64 * Real.exp 1 * M ^ 2, by positivity, fun lam hlam hlam1 hlh Nₐ n => ?_⟩
  set q := clusterThreshold p₀ β
  set ν := lam ^ (1 - β / 2) with hν
  have hν0 : 0 < ν := Real.rpow_pos_of_pos hlam _
  set δ := errorRate p₀ β lam
  have hδ0 : 0 ≤ δ := errorRate_nonneg hlam
  have hx0 : (0 : ℝ) ≤ Nₐ * δ := by positivity
  set Kg := Cg * ν
  have hKg0 : 0 ≤ Kg := by positivity
  have hh : 0 < cutoff p₀ β lam ε₀ := hlam.trans_le hlh
  have hq := clusterThreshold_pos hp₀ hβ
  have hmain := typeOnePartitionFunction_le_successive (Nₐ := Nₐ) (n := n) hq hh hlam hlh
    (by linarith) hKg0 (hg lam hlam hlam1 hlh)
  rw [← RouteTypeOne.sum_bases_eq_successive] at hmain
  set X := ∑ s ∈ Finset.range (Nat.log 2 ⌊cutoff p₀ β lam ε₀ / lam⌋₊ + 1),
    crowdTerm q β lam Nₐ s
  set Y := (Nₐ : ℝ) * (cutoff p₀ β lam ε₀ / 4) ^ (-(β / 2))
  have hdyad : ∀ s, 0 < dyad lam s := fun s => by unfold dyad; positivity
  have hX0 : 0 ≤ X := sum_nonneg fun s _ => by
    unfold crowdTerm
    have := hdyad s
    positivity
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ (cutoff p₀ β lam ε₀ / 4) ^ (-(β / 2)) := Real.rpow_nonneg (by positivity) _
    positivity
  have hXb : X ≤ M * (Nₐ * δ) * ν ^ (q + 1) := by
    refine (hX ε₀ lam hε₀ hε₀1 hlam hlam1 hlh Nₐ).trans ?_
    have : CX ≤ M := le_max_of_le_right (le_max_left _ _)
    have : 0 ≤ (Nₐ : ℝ) * δ * ν ^ (q + 1) := by positivity
    nlinarith
  have hYb : Y ≤ M * (Nₐ * δ) * ν := by
    have h1 := hY lam hlam hlam1
    have : CY ≤ M := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    have hN0 : (0 : ℝ) ≤ Nₐ := Nat.cast_nonneg _
    calc Y ≤ Nₐ * (CY * δ * ν) := mul_le_mul_of_nonneg_left h1 hN0
      _ ≤ Nₐ * (M * δ * ν) := by gcongr
      _ = M * (Nₐ * δ) * ν := by ring
  have hKgb : Kg ≤ M * ν := by
    have : Cg ≤ M := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
    exact mul_le_mul_of_nonneg_right this hν0.le
  have hsum := RouteTypeOne.sum_integrated_bases_le (n := n) hq
    hM1 hν0 hx0 hX0 hY0 hKg0 hXb hYb hKgb
  have hS0 := typeOneSeries_nonneg q n hx0
  -- divide by `n!`
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hZ : typeOnePartitionFunction p₀ β lam ε₀ Nₐ n ≤
      ENNReal.ofReal (4 ^ (2 * n) * (((2 * n : ℕ) : ℝ) ^ (2 * n) * M ^ (2 * n) * ν ^ (2 * n) *
        typeOneSeries q n (Nₐ * δ)) / n.factorial) := by
    rw [ENNReal.ofReal_div_of_pos hfac, ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.2 hfac).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm,
      ENNReal.ofReal_natCast]
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    refine hsum.trans ?_
    have hn2 : (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ 2 * n)
    have hnexp : n ≤ 2 * n := by omega
    have h4 : (4 : ℝ) ^ n ≤ 4 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) hnexp
    have hn : (n : ℝ) ^ (2 * n) ≤ ((2 * n : ℕ) : ℝ) ^ (2 * n) :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) hn2 _
    calc _ = (4 ^ n * (n : ℝ) ^ (2 * n)) *
        (M ^ (2 * n) * ν ^ (2 * n) * typeOneSeries q n (Nₐ * δ)) := by ring
      _ ≤ (4 ^ (2 * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n)) *
        (M ^ (2 * n) * ν ^ (2 * n) * typeOneSeries q n (Nₐ * δ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h4 hn (by positivity) (by positivity))
            (by positivity)
      _ = _ := by ring
  refine hZ.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the elementary bound `4^{2n} (2n)^{2n} / n! ≤ (64 e)^n nⁿ`
  have hnn : ((n : ℝ) ^ n) / n.factorial ≤ Real.exp n :=
    Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have hν2 : ν ^ (2 * n) = (lam ^ (2 - β)) ^ n := by
    rw [hν, pow_mul, ← Real.rpow_natCast (lam ^ (1 - β / 2)) 2, ← Real.rpow_mul hlam.le]
    norm_num
    ring_nf
  have hexp : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hν2]
  have hfac' : (4 : ℝ) ^ (2 * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n) / n.factorial ≤
      (64 * Real.exp 1) ^ n * (n : ℝ) ^ n := by
    have e1 : (4 : ℝ) ^ (2 * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n) =
        64 ^ n * (n : ℝ) ^ n * (n : ℝ) ^ n := by
      push_cast
      rw [mul_pow, pow_mul, pow_mul, pow_mul, show (64 : ℝ) = 4 * 16 by norm_num, mul_pow]
      ring
    rw [e1, mul_div_assoc]
    calc (64 : ℝ) ^ n * (n : ℝ) ^ n * ((n : ℝ) ^ n / n.factorial)
        ≤ 64 ^ n * (n : ℝ) ^ n * Real.exp 1 ^ n := by
          rw [← hexp]
          gcongr
      _ = (64 * Real.exp 1) ^ n * (n : ℝ) ^ n := by ring
  calc 4 ^ (2 * n) * (((2 * n : ℕ) : ℝ) ^ (2 * n) * M ^ (2 * n) * (lam ^ (2 - β)) ^ n *
        typeOneSeries q n (Nₐ * δ)) / n.factorial
      = (4 ^ (2 * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n) / n.factorial) *
          (M ^ (2 * n) * (lam ^ (2 - β)) ^ n * typeOneSeries q n (Nₐ * δ)) := by ring
    _ ≤ ((64 * Real.exp 1) ^ n * (n : ℝ) ^ n) *
          (M ^ (2 * n) * (lam ^ (2 - β)) ^ n * typeOneSeries q n (Nₐ * δ)) :=
        mul_le_mul_of_nonneg_right hfac' (by positivity)
    _ = (64 * Real.exp 1 * M ^ 2 * n * lam ^ (2 - β)) ^ n * typeOneSeries q n (Nₐ * δ) := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul]
        ring

/-- **The exponential series** (Lemma 5.40, Step 6): for `L ≥ 1`,
`Lⁿ S_n(x) ≤ exp(2 L^{q+1} x)`, using `n ≤ (q+1)(a+b)` (every dipole has a bad charge). -/
theorem typeOneSeries_le_exp {q n : ℕ} {L x : ℝ} (hL : 1 ≤ L) (hx : 0 ≤ x) :
    L ^ n * typeOneSeries q n x ≤ Real.exp (2 * L ^ (q + 1) * x) := by
  set y := L ^ (q + 1) * x with hy
  have hy0 : 0 ≤ y := by positivity
  unfold typeOneSeries
  rw [mul_sum]
  calc ∑ a ∈ Finset.range (2 * n + 1), L ^ n * ∑ b ∈ Finset.range (2 * n + 1),
        (if n ≤ (q + 1) * (a + b) then x ^ (a + b) / (a.factorial * b.factorial) else 0)
      ≤ ∑ a ∈ Finset.range (2 * n + 1), ∑ b ∈ Finset.range (2 * n + 1),
          (y ^ a / a.factorial) * (y ^ b / b.factorial) := by
        refine sum_le_sum fun a _ => ?_
        rw [mul_sum]
        refine sum_le_sum fun b _ => ?_
        split_ifs with hab
        · have hLn : L ^ n ≤ L ^ ((q + 1) * (a + b)) := pow_le_pow_right₀ hL hab
          calc L ^ n * (x ^ (a + b) / (a.factorial * b.factorial))
              ≤ L ^ ((q + 1) * (a + b)) * (x ^ (a + b) / (a.factorial * b.factorial)) :=
                mul_le_mul_of_nonneg_right hLn (by positivity)
            _ = y ^ a / a.factorial * (y ^ b / b.factorial) := by
                have e : L ^ ((q + 1) * (a + b)) = L ^ ((q + 1) * a) * L ^ ((q + 1) * b) := by
                  rw [mul_add, pow_add]
                rw [e, hy, mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
                field_simp
        · rw [mul_zero]
          positivity
    _ = (∑ a ∈ Finset.range (2 * n + 1), y ^ a / a.factorial) *
          ∑ b ∈ Finset.range (2 * n + 1), y ^ b / b.factorial := by
        rw [sum_mul_sum]
    _ ≤ Real.exp y * Real.exp y :=
        mul_le_mul (Real.sum_le_exp_of_nonneg hy0 _) (Real.sum_le_exp_of_nonneg hy0 _)
          (sum_nonneg fun b _ => by positivity) (Real.exp_pos _).le
    _ = Real.exp (2 * L ^ (q + 1) * x) := by
        rw [← Real.exp_add, hy]
        ring_nf

/-- **Lemma 5.40**, for `β > 2`, `p₀ ≥ 1`: for every
`ε₀ ∈ (0, 1]` there is `C > 0` (depending on `χ, β, p₀, ε₀`) such that, for `λ` small and `N`
large, for every `t ≥ 1` and every `n`,
`(N/n)ⁿ Z^{(1)}_{bad,n} e^{tn} / (N C_{β,λ,ε₀})ⁿ ≤ exp(e^{Ct} N δ_{β,λ})`,
written multiplicatively: `Z^{(1)}_{bad,n} ≤ (N C_{β,λ,ε₀})ⁿ (n/N)ⁿ e^{-tn} exp(e^{Ct} N δ_{β,λ})`,
with `C_{β,λ,ε₀} = truncatedDipoleNormalization χ N β λ (ε₀ R̄_{β,λ})`. -/
theorem lemma_5_40 {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ n : ℕ,
        typeOnePartitionFunction p₀ β lam ε₀ N n ≤
          ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
              (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) / N) ^ n *
            (Real.exp (-(t * n)) * Real.exp (Real.exp (C * t) * N * errorRate p₀ β lam))) := by
  intro ε₀ hε₀ hε₀1
  obtain ⟨C₀, hC₀, hser⟩ := typeOnePartitionFunction_le_series hp₀ hβ hε₀ hε₀1
  have hZ := dipoleConstant_pos hχ hβ
  set c₀ := 1 / 2 * dipoleConstant χ β with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set K₁ := C₀ / c₀
  set L₀ := max 1 K₁ with hL₀
  have hL₀1 : 1 ≤ L₀ := le_max_left _ _
  set q := clusterThreshold p₀ β
  set C := Real.log (2 * L₀ ^ (q + 1)) + (q + 1) with hC
  have hlog0 : 0 ≤ Real.log (2 * L₀ ^ (q + 1)) := Real.log_nonneg (by
    have : 1 ≤ L₀ ^ (q + 1) := one_le_pow₀ hL₀1
    linarith)
  refine ⟨C, by positivity, ?_⟩
  obtain ⟨lam₁, hlam₁, hnorm⟩ := eventually_half_le_normalization hχ hβ hp₀ hε₀ hε₀1
  obtain ⟨lam₂, hlam₂, hcut⟩ := eventually_lam_le_cutoff hβ hp₀ hε₀
  refine ⟨min lam₁ lam₂, lt_min hlam₁ hlam₂, fun lam hlam hlt => ?_⟩
  obtain ⟨hlam1, hlh⟩ := hcut lam hlam (hlt.trans_le (min_le_right _ _))
  filter_upwards [hnorm lam hlam (hlt.trans_le (min_le_left _ _)), eventually_ge_atTop 1]
    with N hNC hN1 t ht n
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  set δ := errorRate p₀ β lam
  have hδ0 : 0 ≤ δ := errorRate_nonneg hlam
  have hx0 : (0 : ℝ) ≤ N * δ := by positivity
  set S := typeOneSeries q n (N * δ)
  have hS0 : 0 ≤ S := typeOneSeries_nonneg q n hx0
  have hlb : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  refine (hser lam hlam hlam1 hlh N n).trans (ENNReal.ofReal_le_ofReal ?_)
  have hnormed := le_normalized_of_le (Z := (C₀ * n * lam ^ (2 - β)) ^ n * S)
    (A := C₀ * lam ^ (2 - β)) (c := c₀ * lam ^ (2 - β)) (Y := S) (n := n)
    (le_of_eq (by ring)) hNr (mul_pos hc₀0 hlb) hNC (by positivity) hS0
  refine hnormed.trans ?_
  have hK : C₀ * lam ^ (2 - β) / (c₀ * lam ^ (2 - β)) = K₁ := by
    show _ = C₀ / c₀
    field_simp
  rw [hK]
  refine mul_le_mul_of_nonneg_left ?_ (by
    have : 0 ≤ truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam) :=
      (mul_pos hc₀0 hlb).le.trans hNC
    positivity)
  -- `K₁ⁿ S ≤ e^{-tn} exp(e^{Ct} N δ)`
  set L := L₀ * Real.exp t with hL
  have hL1 : 1 ≤ L := one_le_mul_of_one_le_of_one_le hL₀1 (Real.one_le_exp (by linarith))
  have hseries := typeOneSeries_le_exp (q := q) (n := n) hL1 hx0
  have hKL : K₁ ^ n * Real.exp (t * n) ≤ L ^ n := by
    rw [hL, mul_pow, show t * n = n * t by ring, Real.exp_nat_mul]
    gcongr
    · exact (le_max_right 1 K₁).trans_eq' rfl |>.trans_eq rfl
  have hconst : 2 * L ^ (q + 1) ≤ Real.exp (C * t) := by
    have hL' : L ^ (q + 1) = L₀ ^ (q + 1) * Real.exp (((q : ℝ) + 1) * t) := by
      rw [hL, mul_pow, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    have hCt : Real.exp (C * t) =
        Real.exp (Real.log (2 * L₀ ^ (q + 1)) * t) * Real.exp (((q : ℝ) + 1) * t) := by
      rw [hC, add_mul, Real.exp_add]
    have h1 : 2 * L₀ ^ (q + 1) ≤ Real.exp (Real.log (2 * L₀ ^ (q + 1)) * t) := by
      calc 2 * L₀ ^ (q + 1) = Real.exp (Real.log (2 * L₀ ^ (q + 1))) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (Real.log (2 * L₀ ^ (q + 1)) * t) := by
            gcongr
            nlinarith
    rw [hL', hCt]
    calc 2 * (L₀ ^ (q + 1) * Real.exp (((q : ℝ) + 1) * t))
        = (2 * L₀ ^ (q + 1)) * Real.exp (((q : ℝ) + 1) * t) := by ring
      _ ≤ Real.exp (Real.log (2 * L₀ ^ (q + 1)) * t) * Real.exp (((q : ℝ) + 1) * t) := by
          gcongr
  have hexp_le : Real.exp (2 * L ^ (q + 1) * (N * δ)) ≤
      Real.exp (Real.exp (C * t) * N * δ) := by
    refine Real.exp_le_exp.2 ?_
    calc 2 * L ^ (q + 1) * (N * δ) ≤ Real.exp (C * t) * (N * δ) :=
          mul_le_mul_of_nonneg_right hconst hx0
      _ = Real.exp (C * t) * N * δ := by ring
  have hpos : 0 < Real.exp (t * n) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ hpos]
  calc K₁ ^ n * S * Real.exp (t * n) = (K₁ ^ n * Real.exp (t * n)) * S := by ring
    _ ≤ L ^ n * S := mul_le_mul_of_nonneg_right hKL hS0
    _ ≤ Real.exp (2 * L ^ (q + 1) * (N * δ)) := hseries
    _ ≤ _ := hexp_le

end BadPointTypes

end MultipoleBKT

end
