/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremOne.ClusterLimit
public import MultipoleBKT.RateFunction.HypertreeCount
public import MultipoleBKT.Frozen.MayerTerm
public import MultipoleBKT.Frozen.Mayer
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 1 from the gates: the truncated Mayer series

Facts about the terms `mayerTerm p b n k` of the truncated Mayer series (2.36) (Definition 2.7), for coefficients `b` (the paper's
`𝗄^dip_{β,λ}`):

* `tsum_mayerTerm_eq_sum`: for fixed `n`, the series over `k` is the finite sum over `k ≤ n p`
  (a hypertree with blocks of size `≤ p` has `|⋃ᵢ Vᵢ| ≤ n p`);
* `clusterLimit_eq_neg_tsum_mayerTerm`: the limit of the `n`-th cluster term of
  `MultipoleBKT.TheoremOne.tendsto_clusterSum`, with the Ursell weight, is `-∑_k mayerTerm n k`,
 by the hypertree identity `I(G(V)) = (-1)^{n-1} ω(V)` (eq. (4.150));
* `abs_mayerTerm_le`, `summable_mayerTerm`: if `|b(j)| ≤ C₀ λ^{2(j-1)}` for `2 ≤ j ≤ p` (eq.
  (2.39)), then `|mayerTerm n k| ≤ e (e² C₀ λ)ⁿ (e λ)^{k-1}`, so the double series converges
  absolutely for `λ` small. The proof uses `∑_V ω(V) ≤ n^k (k + n)^n`
  (`MultipoleBKT.sum_hypertreeWeight_le`), `∑ᵢ(|Vᵢ| - 1) = k - 1` and `k ≥ n + 1` for hypertrees.
-/

@[expose] public section

open Finset Filter Topology

namespace MultipoleBKT

namespace TheoremOne

/-- The `k`-th Mayer term vanishes at `k = 0` (no hypertree has empty union) and for
`k > n p`. -/
theorem mayerTerm_formula_eq_zero {p : ℕ} (b : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) {k : ℕ}
    (hk : k = 0 ∨ n * p < k) :
    ∑ V ∈ (hypertrees n (range k)).filter (fun V => univ.biUnion V = range k),
        (hypertreeWeight V : ℝ) * (if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0) = 0 := by
  refine sum_eq_zero fun V hV => ?_
  rw [mem_filter] at hV
  have h1 := add_one_le_card_of_mem_hypertrees hV.1 hV.2
  rw [card_range] at h1
  rcases hk with hk | hk
  · omega
  · rw [ite_eq_right fun hp => absurd (le_mul_of_biUnion_eq_range hV.2 hp) (by omega), mul_zero]

/-- For fixed `n`, the Mayer series over `k` is a finite sum over `k ≤ n p`. -/
theorem tsum_mayerTerm_eq_sum (p : ℕ) (b : ℕ → ℝ) (n : ℕ+) :
    ∑' k : ℕ+, mayerTerm p b n k =
      ∑ k ∈ range (n * p + 1), (-1) ^ (n : ℕ) / ((n : ℕ).factorial : ℝ) *
        (1 / (k.factorial : ℝ) *
          ∑ V ∈ (hypertrees n (range k)).filter (fun V => univ.biUnion V = range k),
            (hypertreeWeight V : ℝ) *
              (if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0)) := by
  set f : ℕ → ℝ := fun k => (-1) ^ (n : ℕ) / ((n : ℕ).factorial : ℝ) *
    (1 / (k.factorial : ℝ) *
      ∑ V ∈ (hypertrees n (range k)).filter (fun V => univ.biUnion V = range k),
        (hypertreeWeight V : ℝ) * (if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0))
    with hf
  have hn : 1 ≤ (n : ℕ) := n.pos
  have h0 : f 0 = 0 := by
    simp only [hf, mayerTerm_formula_eq_zero b hn (Or.inl rfl), mul_zero]
  have hterm : ∀ k : ℕ+, mayerTerm p b n k = f k := fun k => rfl
  rw [tsum_congr hterm, tsum_pnat_eq_tsum_of_eq_zero h0]
  refine tsum_eq_sum fun k hk => ?_
  rw [mem_range, not_lt] at hk
  simp only [hf, mayerTerm_formula_eq_zero b hn (Or.inr (by omega : (n : ℕ) * p < k)), mul_zero]

/-- **The limit of a cluster term** (eq. (5.168)): the limit of the `n`-th
cluster term in `tendsto_clusterSum`, with the Ursell weight and `1/n!`, is
`-∑_k mayerTerm n k`. -/
theorem clusterLimit_eq_neg_tsum_mayerTerm (p : ℕ) (b : ℕ → ℝ) (n : ℕ+) :
    1 / ((n : ℕ).factorial : ℝ) * ∑ k ∈ range (n * p + 1), 1 / (k.factorial : ℝ) *
        ∑ V ∈ (hypertrees n (range k)).filter (fun V => univ.biUnion V = range k),
          (if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0) *
            (ursell (connectionGraph V) : ℝ) =
      -∑' k : ℕ+, mayerTerm p b n k := by
  rw [tsum_mayerTerm_eq_sum, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hU : ∀ V ∈ (hypertrees n (range k)).filter (fun V => univ.biUnion V = range k),
      (if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0) *
          (ursell (connectionGraph V) : ℝ) =
        (-1) ^ ((n : ℕ) - 1) * ((hypertreeWeight V : ℝ) *
          (if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0)) := by
    intro V hV
    rw [ursell_connectionGraph_of_mem_hypertrees (mem_filter.mp hV).1]
    push_cast
    ring
  rw [sum_congr rfl hU, ← mul_sum]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℕ) = m + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  rw [hm, Nat.add_sub_cancel, pow_succ]
  ring

/-- The bound `|∏ᵢ b(|Vᵢ|)| ≤ C₀ⁿ λ^{2(k-1)}` on a hypertree with union `[k]` and blocks of size
`≤ p`. -/
theorem abs_ite_prod_le {p : ℕ} {b : ℕ → ℝ} {C₀ lam : ℝ} (hC₀ : 0 ≤ C₀) (hlam : 0 ≤ lam)
    (hb : ∀ j, 2 ≤ j → j ≤ p → |b j| ≤ C₀ * lam ^ (2 * (j - 1))) {n k : ℕ}
    {V : Fin n → Finset ℕ} (hV : V ∈ hypertrees n (range k)) (hU : univ.biUnion V = range k) :
    |(if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0)| ≤ C₀ ^ n * lam ^ (2 * (k - 1)) := by
  split_ifs with hp
  · obtain ⟨-, h2, -, -⟩ := hypertrees_props hV
    have hs := sum_card_sub_one_of_mem_hypertrees hV hU
    rw [card_range] at hs
    rw [abs_prod]
    calc ∏ i, |b (V i).card| ≤ ∏ i, (C₀ * lam ^ (2 * ((V i).card - 1))) :=
          prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hb _ (h2 i) (hp i)
      _ = C₀ ^ n * lam ^ (2 * (k - 1)) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum,
            ← mul_sum, hs]
  · rw [abs_zero]
    positivity

/-- `(1/n!) (1/k!) n^k (k + n)^n ≤ e^{2n + k}`. -/
theorem inv_factorial_mul_le_exp (n k : ℕ) :
    1 / (n.factorial : ℝ) * (1 / (k.factorial : ℝ)) * ((n : ℝ) ^ k * ((k : ℝ) + n) ^ n) ≤
      Real.exp 1 ^ n * Real.exp 1 ^ (k + n) := by
  have h1 : (n : ℝ) ^ k / k.factorial ≤ Real.exp 1 ^ n := by
    rw [Real.exp_one_pow]
    exact Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg n) k
  have h2 : ((k : ℝ) + n) ^ n / n.factorial ≤ Real.exp 1 ^ (k + n) := by
    rw [Real.exp_one_pow]
    push_cast
    exact Real.pow_div_factorial_le_exp _ (by positivity) n
  calc 1 / (n.factorial : ℝ) * (1 / (k.factorial : ℝ)) * ((n : ℝ) ^ k * ((k : ℝ) + n) ^ n)
      = ((n : ℝ) ^ k / k.factorial) * (((k : ℝ) + n) ^ n / n.factorial) := by ring
    _ ≤ Real.exp 1 ^ n * Real.exp 1 ^ (k + n) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **The bound on the Mayer terms**: if `|b(j)| ≤ C₀ λ^{2(j-1)}` for `2 ≤ j ≤ p` and
`0 ≤ λ ≤ 1`, then `|mayerTerm n k| ≤ e (e² C₀ λ)ⁿ (e λ)^{k-1}`. -/
theorem abs_mayerTerm_le {p : ℕ} {b : ℕ → ℝ} {C₀ lam : ℝ} (hC₀ : 0 ≤ C₀) (hlam : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hb : ∀ j, 2 ≤ j → j ≤ p → |b j| ≤ C₀ * lam ^ (2 * (j - 1)))
    (n k : ℕ+) :
    |mayerTerm p b n k| ≤
      Real.exp 1 * (Real.exp 1 ^ 2 * C₀ * lam) ^ (n : ℕ) * (Real.exp 1 * lam) ^ ((k : ℕ) - 1) := by
  set S := (hypertrees n (range k)).filter (fun V => univ.biUnion V = range k) with hS
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hRHS : 0 ≤
      Real.exp 1 * (Real.exp 1 ^ 2 * C₀ * lam) ^ (n : ℕ) * (Real.exp 1 * lam) ^ ((k : ℕ) - 1) := by
    positivity
  rcases S.eq_empty_or_nonempty with hS0 | ⟨V₀, hV₀⟩
  · unfold mayerTerm
    rw [← hS, hS0, sum_empty, mul_zero, mul_zero, abs_zero]
    exact hRHS
  have hkn : (n : ℕ) + 1 ≤ k := by
    have := add_one_le_card_of_mem_hypertrees (mem_filter.mp hV₀).1 (mem_filter.mp hV₀).2
    rwa [card_range] at this
  have hsum : |∑ V ∈ S, (hypertreeWeight V : ℝ) *
      (if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0)| ≤
      ((n : ℝ) ^ (k : ℕ) * (((k : ℕ) : ℝ) + n) ^ (n : ℕ)) *
        (C₀ ^ (n : ℕ) * lam ^ (2 * ((k : ℕ) - 1))) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ V ∈ S, |(hypertreeWeight V : ℝ) *
          (if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0)|
        ≤ ∑ V ∈ S, (hypertreeWeight V : ℝ) * (C₀ ^ (n : ℕ) * lam ^ (2 * ((k : ℕ) - 1))) := by
          refine sum_le_sum fun V hV => ?_
          rw [abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left
            (abs_ite_prod_le hC₀ hlam hb (mem_filter.mp hV).1 (mem_filter.mp hV).2)
            (Nat.cast_nonneg _)
      _ = (∑ V ∈ S, (hypertreeWeight V : ℝ)) * (C₀ ^ (n : ℕ) * lam ^ (2 * ((k : ℕ) - 1))) := by
          rw [sum_mul]
      _ ≤ ((n : ℝ) ^ (k : ℕ) * (((k : ℕ) : ℝ) + n) ^ (n : ℕ)) *
            (C₀ ^ (n : ℕ) * lam ^ (2 * ((k : ℕ) - 1))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := sum_hypertreeWeight_le (range (k : ℕ)) (n : ℕ)
          rw [card_range] at this
          rw [hS, ← Nat.cast_sum]
          exact_mod_cast this
  have hpow : lam ^ (2 * ((k : ℕ) - 1)) ≤ lam ^ (n : ℕ) * lam ^ ((k : ℕ) - 1) := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one hlam hlam1 (by omega)
  unfold mayerTerm
  rw [← hS, abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℕ).factorial : ℝ)),
    abs_of_pos (by positivity : (0 : ℝ) < 1 / ((k : ℕ).factorial : ℝ))]
  have hk1 : (k : ℕ) = ((k : ℕ) - 1) + 1 := by omega
  calc 1 / ((n : ℕ).factorial : ℝ) * (1 / ((k : ℕ).factorial : ℝ) *
        |∑ V ∈ S, (hypertreeWeight V : ℝ) *
          (if ∀ i, (V i).card ≤ p then ∏ i, b (V i).card else 0)|)
      ≤ 1 / ((n : ℕ).factorial : ℝ) * (1 / ((k : ℕ).factorial : ℝ) *
          (((n : ℝ) ^ (k : ℕ) * (((k : ℕ) : ℝ) + n) ^ (n : ℕ)) *
            (C₀ ^ (n : ℕ) * lam ^ (2 * ((k : ℕ) - 1))))) := by gcongr
    _ = (1 / ((n : ℕ).factorial : ℝ) * (1 / ((k : ℕ).factorial : ℝ)) *
          ((n : ℝ) ^ (k : ℕ) * (((k : ℕ) : ℝ) + n) ^ (n : ℕ))) *
            (C₀ ^ (n : ℕ) * lam ^ (2 * ((k : ℕ) - 1))) := by ring
    _ ≤ (Real.exp 1 ^ (n : ℕ) * Real.exp 1 ^ ((k : ℕ) + n)) *
          (C₀ ^ (n : ℕ) * (lam ^ (n : ℕ) * lam ^ ((k : ℕ) - 1))) := by
        refine mul_le_mul (inv_factorial_mul_le_exp _ _) ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Real.exp 1 * (Real.exp 1 ^ 2 * C₀ * lam) ^ (n : ℕ) *
          (Real.exp 1 * lam) ^ ((k : ℕ) - 1) := by
        rw [hk1]
        simp only [Nat.add_sub_cancel]
        ring

/-- **Absolute summability of the Mayer double series**: under the bounds (2.39)
on the coefficients, for `λ` small. -/
theorem summable_mayerTerm {p : ℕ} {b : ℕ → ℝ} {C₀ lam : ℝ} (hC₀ : 0 ≤ C₀) (hlam : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hb : ∀ j, 2 ≤ j → j ≤ p → |b j| ≤ C₀ * lam ^ (2 * (j - 1)))
    (hsmall : Real.exp 1 ^ 2 * C₀ * lam < 1) (hsmall' : Real.exp 1 * lam < 1) :
    Summable (fun nk : ℕ+ × ℕ+ => ‖mayerTerm p b nk.1 nk.2‖) := by
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hx0 : 0 ≤ Real.exp 1 ^ 2 * C₀ * lam := by positivity
  have hy0 : 0 ≤ Real.exp 1 * lam := by positivity
  have hf : Summable fun n : ℕ+ => (Real.exp 1 ^ 2 * C₀ * lam) ^ (n : ℕ) :=
    (summable_geometric_of_lt_one hx0 hsmall).comp_injective PNat.coe_injective
  have hg : Summable fun k : ℕ+ => (Real.exp 1 * lam) ^ ((k : ℕ) - 1) := by
    have hinj : Function.Injective fun k : ℕ+ => (k : ℕ) - 1 := fun k k' h => by
      have := k.pos
      have := k'.pos
      exact PNat.coe_injective (by simp only at h; omega)
    exact (summable_geometric_of_lt_one hy0 hsmall').comp_injective hinj
  have hprod := (hf.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)).mul_left
    (Real.exp 1)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun nk => ?_) hprod
  rw [Real.norm_eq_abs, ← mul_assoc]
  exact abs_mayerTerm_le hC₀ hlam hlam1 hb nk.1 nk.2

end TheoremOne

end MultipoleBKT

end
