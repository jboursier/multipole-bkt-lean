/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.ResummationFormal
public import MultipoleBKT.Frozen.ConnectionGraph
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Connected-cluster resummation: Lemma 4.7

Lemma 4.7 in the real-valued
form stated after it (the identity holds in `ℝ` when the right-hand side converges
absolutely), which is the form the paper uses:

`log ∑_{n ≥ 0} (1/n!) ∑_{X₁,…,Xₙ disjoint} ∏ K(Xᵢ)
  = ∑_{n ≥ 1} (1/n!) ∑_{X₁,…,Xₙ connected} ∏ K(Xᵢ) I(G(X₁,…,Xₙ))`.

The paper cites Bauerschmidt et al., Thm 4.4, for the formal identity. Here the proof is
self-contained: scale `K` by `t`. The left-hand side becomes a polynomial `Z(t)` and the right-hand
side a power series `F(t)` converging on `[-1, 1]`. The combinatorial recursion of
`MultipoleBKT.Cluster.ResummationFormal` is the coefficient identity `Z' = F' Z`, so
`Z(t) e^{-F(t)}` has zero derivative on `(-1, 1)`. Hence `Z = e^F` there, and at `t = 1` by
continuity.

Main results:

* `MultipoleBKT.Resummation.sum_eq_exp_tsum_of_recursion`: the analytic step, for sequences;
* `MultipoleBKT.lemma_4_7`: Lemma 4.7 for a finite type `C` of polymers with a reflexive
  relation `R` (symmetry is not needed), under summability of the norms of the cluster terms
  (the form of Theorem 1's hypothesis);
* `MultipoleBKT.lemma_4_7_of_summable_abs`: the same under the paper's absolute convergence
  `∑ₙ (1/n!) ∑_X |∏ K(Xᵢ) I(G(X))| < ∞`;
* `MultipoleBKT.lemma_4_7_subsets`, `MultipoleBKT.lemma_4_7_range`: the case of polymers that
  are subsets of a finite set (resp. of `Finset.range N`) with a size filter `P`, related by
  intersection, so that the connection graph is the frozen `MultipoleBKT.connectionGraph`; this
  is the form of Theorem 1's statement (equations (5.164) and (5.166)).
-/

@[expose] public section

namespace MultipoleBKT

open Finset

namespace Resummation

section Analytic

open Set Filter Topology

variable {a z : ℕ → ℝ}

/-- A summable real sequence is bounded by the sum of its absolute values. -/
theorem abs_le_tsum_abs (ha : Summable a) (n : ℕ) : |a n| ≤ ∑' k, |a k| :=
  ha.abs.le_tsum n fun k _ => abs_nonneg (a k)

/-- `∑ aₙ tⁿ` converges for `|t| ≤ 1` when `∑ aₙ` converges absolutely. -/
theorem summable_mul_pow_of_abs_le_one (ha : Summable a) {t : ℝ} (ht : |t| ≤ 1) :
    Summable fun n => a n * t ^ n :=
  Summable.of_norm_bounded ha.abs fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg t) ht)

/-- `n r^(n-1)` is summable for `0 < r < 1`. -/
theorem summable_natCast_mul_pow_pred {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun n : ℕ => (n : ℝ) * r ^ (n - 1) := by
  have hr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have h := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).div_const r
  refine h.congr fun n => ?_
  rcases n with _ | n
  · simp
  · rw [pow_one, Nat.add_sub_cancel, pow_succ, mul_div_assoc, mul_div_cancel_right₀ _ hr0.ne']

/-- `(n + 1) |t|^n` is summable for `|t| < 1`. -/
theorem summable_succ_mul_abs_pow {t : ℝ} (ht : |t| < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) * |t| ^ n := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
    (by rwa [Real.norm_eq_abs, abs_abs] : ‖|t|‖ < 1)
  have h2 := summable_geometric_of_lt_one (abs_nonneg t) ht
  refine (h1.add h2).congr fun n => ?_
  simp only [pow_one]
  ring

/-- Termwise differentiation of `∑ aₙ yⁿ` inside the unit interval. -/
theorem hasDerivAt_tsum_mul_pow (ha : Summable a) {t : ℝ} (ht : |t| < 1) :
    HasDerivAt (fun y => ∑' n, a n * y ^ n) (∑' n, a n * (n * t ^ (n - 1))) t := by
  set r := (|t| + 1) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have htr : |t| < r := by rw [hr]; linarith
  refine hasDerivAt_tsum_of_isPreconnected (t := Ioo (-r) r) (y₀ := 0)
    (u := fun n : ℕ => (∑' k, |a k|) * ((n : ℝ) * r ^ (n - 1)))
    ((summable_natCast_mul_pow_pred hr0 hr1).mul_left _) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hasDerivAt_pow n y).const_mul (a n)) (fun n y hy => ?_)
    ⟨by linarith, hr0⟩ (summable_mul_pow_of_abs_le_one ha (by simp))
    (abs_lt.1 htr)
  have hy' : |y| ≤ r := (abs_lt.2 hy).le
  rw [Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast, abs_pow]
  exact mul_le_mul (abs_le_tsum_abs ha n)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hy' _) (Nat.cast_nonneg n))
    (by positivity) ((abs_nonneg _).trans (abs_le_tsum_abs ha 0))

/-- **The coefficient identity `Z' = F' Z`**, evaluated at `|t| < 1`, for the polynomial
`Z(t) = ∑_{m < M} zₘ tᵐ` and the power series `F(t) = ∑ aₙ tⁿ`. -/
theorem sum_deriv_eq_tsum_deriv_mul (ha : Summable a) {M : ℕ} (hzM : ∀ m, M ≤ m → z m = 0)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * z (n + 1) =
      ∑ k ∈ range (n + 1), (k + 1 : ℝ) * a (k + 1) * z (n - k))
    {t : ℝ} (ht : |t| < 1) :
    ∑ m ∈ range M, z m * (m * t ^ (m - 1)) =
      (∑' n, a n * (n * t ^ (n - 1))) * ∑ m ∈ range M, z m * t ^ m := by
  set f : ℕ → ℝ := fun j => a (j + 1) * ((j + 1 : ℝ) * t ^ j) with hf
  set g : ℕ → ℝ := fun k => z k * t ^ k with hg
  have hfn : Summable fun j => ‖f j‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      ((summable_succ_mul_abs_pow ht).mul_left (∑' k, |a k|))
    rw [hf, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ j + 1)]
    exact mul_le_mul_of_nonneg_right (abs_le_tsum_abs ha _) (by positivity)
  have hgn : Summable fun k => ‖g k‖ :=
    summable_of_ne_finset_zero (s := range M) fun k hk => by
      show ‖z k * t ^ k‖ = 0
      rw [hzM k (by simpa using hk), zero_mul, norm_zero]
  have hF' : Summable fun n => a n * (n * t ^ (n - 1)) := by
    refine (summable_nat_add_iff 1).1 (hfn.of_norm.congr fun j => ?_)
    simp only [hf, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  have hFeq : ∑' n, a n * (n * t ^ (n - 1)) = ∑' j, f j := by
    rw [hF'.tsum_eq_zero_add]
    simp only [hf, CharP.cast_eq_zero, zero_mul, mul_zero, zero_add, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel]
  have hPeq : ∑ m ∈ range M, z m * t ^ m = ∑' k, g k :=
    (tsum_eq_sum fun k hk => by rw [hzM k (by simpa using hk), zero_mul]).symm
  have hP'sum : Summable fun m => z m * (m * t ^ (m - 1)) :=
    summable_of_ne_finset_zero (s := range M) fun k hk => by
      rw [hzM k (by simpa using hk), zero_mul]
  have hP'eq : ∑ m ∈ range M, z m * (m * t ^ (m - 1)) =
      ∑' n, z (n + 1) * ((n + 1 : ℝ) * t ^ n) := by
    have hfin : ∑' m, z m * (m * t ^ (m - 1)) = ∑ m ∈ range M, z m * (m * t ^ (m - 1)) :=
      tsum_eq_sum fun k hk => by rw [hzM k (by simpa using hk), zero_mul]
    rw [← hfin, hP'sum.tsum_eq_zero_add]
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_add, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel]
  rw [hFeq, hPeq, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfn hgn, hP'eq]
  refine tsum_congr fun n => ?_
  have hterm : ∀ k ∈ range (n + 1), f k * g (n - k) =
      t ^ n * ((k + 1 : ℝ) * a (k + 1) * z (n - k)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [hf, hg]
    simp only
    rw [show t ^ n = t ^ k * t ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn]]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hrec n]
  ring

/-- **Analytic step.** Let `∑ aₙ` converge with `a₀ = 0`, and let `z` vanish from `M` on, with
`z₀ = 1` and `(n + 1) z_{n+1} = ∑_{k ≤ n} (k + 1) a_{k+1} z_{n-k}` (the coefficients of
`Z' = F' Z`). Then `∑_{m < M} zₘ = exp (∑ aₙ)`. -/
theorem sum_eq_exp_tsum_of_recursion (ha : Summable a) (ha0 : a 0 = 0) (hz0 : z 0 = 1)
    {M : ℕ} (hzM : ∀ m, M ≤ m → z m = 0)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * z (n + 1) =
      ∑ k ∈ range (n + 1), (k + 1 : ℝ) * a (k + 1) * z (n - k)) :
    ∑ m ∈ range M, z m = Real.exp (∑' n, a n) := by
  set F : ℝ → ℝ := fun y => ∑' n, a n * y ^ n with hF
  set P : ℝ → ℝ := fun y => ∑ m ∈ range M, z m * y ^ m with hP
  have hM : 0 < M := by
    by_contra h
    have h0 := hzM 0 (by omega)
    rw [hz0] at h0
    exact one_ne_zero h0
  -- `P e^{-F}` is constant on `(-1, 1)`
  have hderiv : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun y => P y * Real.exp (-F y)) 0 t := by
    intro t ht
    have ht' : |t| < 1 := abs_lt.2 ht
    have hPd : HasDerivAt P (∑ m ∈ range M, z m * (m * t ^ (m - 1))) t :=
      HasDerivAt.fun_sum fun m _ => (hasDerivAt_pow m t).const_mul (z m)
    have hFd := hasDerivAt_tsum_mul_pow ha ht'
    convert hPd.mul hFd.neg.exp using 1
    rw [sum_deriv_eq_tsum_deriv_mul ha hzM hrec ht']
    ring
  have hG : ∀ t ∈ Ioo (-1 : ℝ) 1, P t * Real.exp (-F t) = 1 := by
    intro t ht
    have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
    rw [isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hderiv y hy).deriv) ht h0]
    have hP0 : P 0 = 1 := by
      rw [hP]
      simp only
      rw [Finset.sum_eq_single 0 (fun m _ hm => by rw [zero_pow hm, mul_zero])
        (fun h => absurd (mem_range.2 hM) h), pow_zero, mul_one, hz0]
    have hF0 : F 0 = 0 := by
      rw [hF]
      simp only
      rw [tsum_eq_single 0 fun m hm => by rw [zero_pow hm, mul_zero], pow_zero, mul_one, ha0]
    rw [hP0, hF0, neg_zero, Real.exp_zero, mul_one]
  -- continuity at `t = 1`
  have hFc : ContinuousOn F (Icc 0 1) := by
    refine continuousOn_tsum (u := fun n => |a n|)
      (fun n => (continuous_const.mul (continuous_pow n)).continuousOn) ha.abs
      fun n y hy => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (pow_le_one₀ (abs_nonneg y) (by rw [abs_of_nonneg hy.1]; exact hy.2))
  have hPc : ContinuousOn P (Icc 0 1) :=
    (continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_pow m)).continuousOn
  have heq : EqOn P (fun y => Real.exp (F y)) (Ico 0 1) := fun t ht => by
    have h := hG t ⟨by linarith [ht.1], ht.2⟩
    rw [Real.exp_neg, ← div_eq_mul_inv, div_eq_one_iff_eq (Real.exp_pos _).ne'] at h
    exact h
  have h1 := heq.of_subset_closure hPc (Real.continuous_exp.comp_continuousOn hFc)
    Ico_subset_Icc_self (by rw [closure_Ico zero_ne_one]) (right_mem_Icc.2 zero_le_one)
  simpa [hP, hF] using h1

end Analytic

section Core

variable {C : Type*} [Fintype C] (R : C → C → Prop) (K : C → ℝ)

/-- **Lemma 4.7, coefficient form.** If `K` vanishes off the reflexive points of `R` and the
normalized cluster sums are summable, the normalized disjoint sums add up to the exponential of
the normalized cluster sums. -/
theorem tsum_disjointCoeff_eq_exp (hK : ∀ x, ¬ R x x → K x = 0)
    (hsum : Summable (clusterCoeff R K)) :
    ∑' n, disjointCoeff R K n = Real.exp (∑' n, clusterCoeff R K n) := by
  rw [tsum_eq_sum (s := range (Fintype.card C + 1)) fun m hm =>
    disjointCoeff_eq_zero_of_card_lt R K hK (by simp at hm; omega)]
  exact sum_eq_exp_tsum_of_recursion hsum (clusterCoeff_zero R K) (disjointCoeff_zero R K)
    (fun m hm => disjointCoeff_eq_zero_of_card_lt R K hK (by omega))
    (succ_mul_disjointCoeff_succ R K)

/-- **Lemma 4.7, coefficient form**, with the cluster series indexed by `ℕ+` and summability of
the norms, as in Theorem 1. -/
theorem disjoint_eq_exp_cluster (hK : ∀ x, ¬ R x x → K x = 0)
    (hsum : Summable fun n : ℕ+ => ‖clusterCoeff R K n‖) :
    0 < ∑' n, disjointCoeff R K n ∧
      Real.log (∑' n, disjointCoeff R K n) = ∑' n : ℕ+, clusterCoeff R K n ∧
      ∑' n, disjointCoeff R K n = Real.exp (∑' n : ℕ+, clusterCoeff R K n) := by
  have hsum' : Summable (clusterCoeff R K) :=
    summable_pnat_iff_summable_nat.1 hsum.of_norm
  rw [tsum_pnat_eq_tsum_of_eq_zero (clusterCoeff_zero R K),
    tsum_disjointCoeff_eq_exp R K hK hsum']
  exact ⟨Real.exp_pos _, Real.log_exp _, rfl⟩

end Core

end Resummation

open Resummation

open scoped Classical in
/-- **Lemma 4.7**, real-valued form. Let `C` be
a finite set of polymers with a reflexive relation `R` ("intersect"; the paper also assumes `R`
symmetric, which is not needed) and `K : C → ℝ`. Write `G(X)` for the connection graph of a tuple
`X : Fin n → C` (`i ~ j` iff `i ≠ j` and `X i`, `X j` are related) and `I` for the Ursell function.
If the cluster series converges absolutely (summability of the norms of its terms, the form of
Theorem 1's hypothesis), then
`Z = ∑_{n ≥ 0} (1/n!) ∑_{X disjoint} ∏ K(X i)` is positive and
`log Z = F = ∑_{n ≥ 1} (1/n!) ∑_{X connected} ∏ K(X i) I(G(X))`. -/
theorem lemma_4_7 {C : Type*} [Fintype C] (R : C → C → Prop) (hR : ∀ x, R x x) (K : C → ℝ)
    (hsum : Summable fun n : ℕ+ => ‖1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (univ : Finset (Fin n → C)).filter
          (fun X => (SimpleGraph.fromRel fun i j => R (X i) (X j)).Connected),
        (∏ i, K (X i)) * (ursell (SimpleGraph.fromRel fun i j => R (X i) (X j)) : ℝ)‖) :
    let Z : ℝ := ∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (univ : Finset (Fin n → C)).filter (fun X => ∀ i j, i ≠ j → ¬ R (X i) (X j)),
        ∏ i, K (X i)
    let F : ℝ := ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (univ : Finset (Fin n → C)).filter
          (fun X => (SimpleGraph.fromRel fun i j => R (X i) (X j)).Connected),
        (∏ i, K (X i)) * (ursell (SimpleGraph.fromRel fun i j => R (X i) (X j)) : ℝ)
    0 < Z ∧ Real.log Z = F ∧ Z = Real.exp F := by
  intro Z F
  have hz : ∀ n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (univ : Finset (Fin n → C)).filter (fun X => ∀ i j, i ≠ j → ¬ R (X i) (X j)),
        ∏ i, K (X i) = disjointCoeff R K n := by
    intro n
    rw [disjointCoeff, disjointSum, Finset.sum_filter, one_div, inv_mul_eq_div]
    congr 1
    refine Finset.sum_congr rfl fun X _ => ?_
    by_cases h : ∀ i j, i ≠ j → ¬ R (X i) (X j)
    · rw [ite_eq_left h, ite_eq_left (relGraph_eq_bot_iff.2 h), mul_one]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (relGraph_eq_bot_iff.1 h')), mul_zero]
  have ha : ∀ n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (univ : Finset (Fin n → C)).filter
          (fun X => (SimpleGraph.fromRel fun i j => R (X i) (X j)).Connected),
        (∏ i, K (X i)) * (ursell (SimpleGraph.fromRel fun i j => R (X i) (X j)) : ℝ) =
      clusterCoeff R K n := by
    intro n
    rw [clusterCoeff, clusterSum, one_div, inv_mul_eq_div]
    congr 1
    refine Finset.sum_filter_of_ne fun X _ hX => ?_
    by_contra hc
    exact hX (by rw [ursell_eq_zero_of_not_connected' hc, Int.cast_zero, mul_zero])
  have hZ : Z = ∑' n, disjointCoeff R K n := tsum_congr hz
  have hF : F = ∑' n : ℕ+, clusterCoeff R K n := tsum_congr fun n => ha n
  rw [hZ, hF]
  exact disjoint_eq_exp_cluster R K (fun x hx => absurd (hR x) hx)
    (hsum.congr fun n => by rw [ha n])

open scoped Classical in
/-- **Lemma 4.7** under the paper's absolute convergence:
`∑_{n ≥ 1} (1/n!) ∑_{X connected} |∏ K(X i) I(G(X))| < ∞` (stated over `ℕ`; its `n = 0` term
vanishes). -/
theorem lemma_4_7_of_summable_abs {C : Type*} [Fintype C] (R : C → C → Prop) (hR : ∀ x, R x x)
    (K : C → ℝ)
    (habs : Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
      ∑ X ∈ (univ : Finset (Fin n → C)).filter
          (fun X => (SimpleGraph.fromRel fun i j => R (X i) (X j)).Connected),
        |(∏ i, K (X i)) * (ursell (SimpleGraph.fromRel fun i j => R (X i) (X j)) : ℝ)|) :
    let Z : ℝ := ∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (univ : Finset (Fin n → C)).filter (fun X => ∀ i j, i ≠ j → ¬ R (X i) (X j)),
        ∏ i, K (X i)
    let F : ℝ := ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (univ : Finset (Fin n → C)).filter
          (fun X => (SimpleGraph.fromRel fun i j => R (X i) (X j)).Connected),
        (∏ i, K (X i)) * (ursell (SimpleGraph.fromRel fun i j => R (X i) (X j)) : ℝ)
    0 < Z ∧ Real.log Z = F ∧ Z = Real.exp F := by
  refine lemma_4_7 R hR K (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_pnat_iff_summable_nat.2 habs))
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℕ).factorial : ℝ))]
  exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)

namespace Resummation

/-- Sums over tuples of elements of `S` whose entries satisfy `P` are sums over tuples of the
subtype of `S.filter P`. -/
theorem sum_filter_piFinset_eq_sum_subtype {β : Type*} {n : ℕ} (S : Finset β) (P : β → Prop)
    [DecidablePred P] (Q : (Fin n → β) → Prop) [DecidablePred Q] (f : (Fin n → β) → ℝ) :
    ∑ V ∈ (Fintype.piFinset fun _ : Fin n => S).filter (fun V => Q V ∧ ∀ i, P (V i)), f V =
      ∑ Y : Fin n → {x // x ∈ S.filter P},
        if Q (fun i => (Y i : β)) then f (fun i => (Y i : β)) else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun V hV i => ⟨V i, mem_filter.2
      ⟨Fintype.mem_piFinset.1 (mem_filter.1 hV).1 i, (mem_filter.1 hV).2.2 i⟩⟩)
    (fun Y _ i => (Y i : β)) (fun V hV => ?_) (fun Y hY => ?_) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)
  · exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hV).2.1⟩
  · exact mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => (mem_filter.1 (Y i).2).1,
      (mem_filter.1 hY).2, fun i => (mem_filter.1 (Y i).2).2⟩

end Resummation

open scoped Classical in
/-- **Lemma 4.7 for polymers that are subsets of a finite set** (the form used in the paper). Polymers are the subsets `V ⊆ A` satisfying `P` (e.g. `2 ≤ |V| ≤ p`), related by
intersection, so that the connection graph is `MultipoleBKT.connectionGraph`; `K(∅) = 0` if `∅`
is a polymer (intersection is reflexive exactly on nonempty sets). If the cluster series
converges absolutely, then the disjoint-family sum
`Z = ∑_{n ≥ 0} (1/n!) ∑_{V₁,…,Vₙ ⊆ A disjoint, P(Vᵢ)} ∏ K(Vᵢ)` is positive and
`log Z = ∑_{n ≥ 1} (1/n!) ∑_{V₁,…,Vₙ ⊆ A connected, P(Vᵢ)} ∏ K(Vᵢ) I(G(V₁,…,Vₙ))`. -/
theorem lemma_4_7_subsets {α : Type*} [DecidableEq α] (A : Finset α) (P : Finset α → Prop)
    [DecidablePred P] (K : Finset α → ℝ) (hK : P ∅ → K ∅ = 0)
    (hsum : Summable fun n : ℕ+ => ‖1 / ((n : ℕ).factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun V => (connectionGraph V).Connected ∧ ∀ i, P (V i)),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)‖) :
    let Z : ℝ := ∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun V => (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ ∀ i, P (V i)),
        ∏ i, K (V i)
    let F : ℝ := ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun V => (connectionGraph V).Connected ∧ ∀ i, P (V i)),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)
    0 < Z ∧ Real.log Z = F ∧ Z = Real.exp F := by
  intro Z F
  let R : {x // x ∈ A.powerset.filter P} → {x // x ∈ A.powerset.filter P} → Prop :=
    fun V W => ((V : Finset α) ∩ W).Nonempty
  let K' : {x // x ∈ A.powerset.filter P} → ℝ := fun V => K V
  have hK' : ∀ V, ¬ R V V → K' V = 0 := by
    intro V hV
    have hV0 : (V : Finset α) = ∅ := by
      simpa [R, Finset.inter_self, Finset.not_nonempty_iff_eq_empty] using hV
    have hPV : P V := (mem_filter.1 V.2).2
    rw [hV0] at hPV
    simp only [K', hV0]
    exact hK hPV
  have hz : ∀ n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun V => (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ ∀ i, P (V i)),
        ∏ i, K (V i) = disjointCoeff R K' n := by
    intro n
    rw [sum_filter_piFinset_eq_sum_subtype, disjointCoeff, disjointSum, one_div, inv_mul_eq_div]
    congr 1
    refine Finset.sum_congr rfl fun Y _ => ?_
    have hiff : (∀ i j, i ≠ j → Disjoint (Y i : Finset α) (Y j)) ↔ relGraph R Y = ⊥ := by
      rw [relGraph_eq_bot_iff]
      simp only [R, Finset.disjoint_iff_inter_eq_empty, Finset.not_nonempty_iff_eq_empty]
    by_cases h : ∀ i j, i ≠ j → Disjoint (Y i : Finset α) (Y j)
    · rw [ite_eq_left h, ite_eq_left (hiff.1 h), mul_one]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.2 h')), mul_zero]
  have ha : ∀ n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun V => (connectionGraph V).Connected ∧ ∀ i, P (V i)),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ) = clusterCoeff R K' n := by
    intro n
    rw [sum_filter_piFinset_eq_sum_subtype, clusterCoeff, clusterSum, one_div, inv_mul_eq_div]
    congr 1
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases h : (connectionGraph fun i => (Y i : Finset α)).Connected
    · rw [ite_eq_left h]
      rfl
    · rw [ite_eq_right h]
      have h' : ¬ (relGraph R Y).Connected := h
      rw [ursell_eq_zero_of_not_connected' h', Int.cast_zero, mul_zero]
  have hZ : Z = ∑' n, disjointCoeff R K' n := tsum_congr hz
  have hF : F = ∑' n : ℕ+, clusterCoeff R K' n := tsum_congr fun n => ha n
  rw [hZ, hF]
  exact disjoint_eq_exp_cluster R K' hK' (hsum.congr fun n => by rw [ha n])

open scoped Classical in
/-- **Lemma 4.7 for subsets of `[N]`**, in the form of Theorem 1's statement: polymers are the
subsets `V ⊆ {0, …, N - 1}` satisfying `P`, related by intersection. -/
theorem lemma_4_7_range (N : ℕ) (P : Finset ℕ → Prop) [DecidablePred P] (K : Finset ℕ → ℝ)
    (hK : P ∅ → K ∅ = 0)
    (hsum : Summable fun n : ℕ+ => ‖1 / ((n : ℕ).factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
          (fun V => (connectionGraph V).Connected ∧ ∀ i, P (V i)),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)‖) :
    let Z : ℝ := ∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
          (fun V => (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ ∀ i, P (V i)),
        ∏ i, K (V i)
    let F : ℝ := ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
          (fun V => (connectionGraph V).Connected ∧ ∀ i, P (V i)),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)
    0 < Z ∧ Real.log Z = F ∧ Z = Real.exp F :=
  lemma_4_7_subsets (Finset.range N) P K hK hsum

end MultipoleBKT

end
