/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.RouteTail.Limit
public import MultipoleBKT.RateFunction.Smoothness
public import MultipoleBKT.RateFunction.Comparison

/-!
# Proposition 5.45: the logarithm of the polymer gas over a partition

The profile asymptotics in the proof of Proposition 5.45, for the polymer gas:
for a partition `π ∈ 𝚷_p([N])`
with `n_i` blocks of size `i + 1` and `γᵢ = n_i/N`,

  `log polymerSum(π) = -N h(γ) + o_λ(N)`, uniformly in `π`,

where `h = ∑_{n ≥ 1} ∑_m rateSeriesTerm(γ, n, m)` is the cluster part of the rate function
(`MultipoleBKT.rateCluster`). The proof sums the hypertree calculation (4.155) for each cluster
order `n` (`MultipoleBKT.PropFiveFortyFive.eventually_abs_clusterSum_sub_le`) over `n`, using the
tail bound of Lemma 4.53 for the cluster series. The same bound passes to the limiting terms
through (4.155), by replication of the block counts
(`MultipoleBKT.PropFiveFortyFive.abs_tsum_rateSeriesTerm_le_of_bounded_cluster_tail`).
-/

@[expose] public section

open Finset Filter Topology

namespace MultipoleBKT

namespace PropFiveFortyFive

/-- The profile `γ = (n_1/N, …, n_p/N)` of a family of blocks. -/
noncomputable def profileVec (p N : ℕ) (π : Finset (Finset ℕ)) : Fin p → ℝ :=
  fun i => (blockCount p π i : ℝ) / N

/-- `(1/2)^n ≤ (2/3)^{n₀} (3/4)^n` for `n ≥ n₀`. -/
theorem half_pow_le {n n₀ : ℕ} (h : n₀ ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ (2 / 3) ^ n₀ * (3 / 4) ^ n := by
  have e : (1 / 2 : ℝ) ^ n = (2 / 3) ^ n * (3 / 4) ^ n := by
    rw [← mul_pow]
    norm_num
  rw [e]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) h)
    (by positivity)

/-- `∑_{n ≥ 1} (3/4)^n ≤ 4`. -/
theorem tsum_pnat_three_quarters_le : ∑' n : ℕ+, (3 / 4 : ℝ) ^ (n : ℕ) ≤ 4 := by
  have hs : Summable fun n : ℕ => (3 / 4 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  calc ∑' n : ℕ+, (3 / 4 : ℝ) ^ (n : ℕ) ≤ ∑' n : ℕ, (3 / 4 : ℝ) ^ n :=
        tsum_comp_le_tsum_of_inj (f := fun n : ℕ => (3 / 4 : ℝ) ^ n) hs (fun _ => by positivity)
          PNat.coe_injective
    _ = 4 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num

/-- **The logarithm of the polymer gas** (the paper,
Proposition 5.45, also (4.145)). Let `K_N` be activities depending only
on the block profile, with `N^{|X|-1} K_N(X) → k((#_j X)_j)` and, for `N` large,
`|K_N(X)| ≤ C₀ (λ²/N)^{|X|-1}` on the polymers, where `k` satisfies (2.48) with constant `C`
and `λ` is small. Then for every `ε > 0`, for `N` large and every `π ∈ 𝚷_p([N])`, the polymer gas
is positive and `|log polymerSum(π) + N h(γ)| ≤ ε N`, `γ` the profile of `π`. -/
theorem exists_log_polymerSum (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (p : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ (kmult : (ℕ →₀ ℕ) → ℝ) (C lam : ℝ) (K : ℕ → Finset (Finset ℕ) → ℝ),
      0 < lam → lam ≤ 1 → Ct * lam ^ 2 ≤ 1 / 2 →
      KmultBound p kmult C lam → rateSeriesConst p C * lam ^ 2 ≤ 1 / 4 →
      (∀ N, 1 ≤ N → IsProfileInvariant (K N)) →
      (∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card → (X.biUnion id).card ≤ p →
        Tendsto (fun N : ℕ => (N : ℝ) ^ (X.card - 1) * K N X) atTop
          (𝓝 (kmult (blockProfile X)))) →
      (∀ᶠ N : ℕ in atTop, ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
        (X.biUnion id).card ≤ p → |K N X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ π ∈ boundedBlockPartitions N p,
        0 < polymerSum p (K N) π ∧
          |Real.log (polymerSum p (K N) π) + N * rateCluster p kmult (profileVec p N π)| ≤
            ε * N := by
  obtain ⟨Ct, hCt, hlogS⟩ := exists_logSeries C₀ hC₀ p
  refine ⟨Ct, hCt, fun kmult C lam K hlam hlam1 hCtl _hk _hsmall hK hlim hact ε hε => ?_⟩
  -- the cut-off `n₀` of the cluster order
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 2 * (2 / 3 : ℝ) ^ n₀ ≤ ε / 4 := by
    obtain ⟨n₀, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < ε / 4 / 2)
      (by norm_num : (2 / 3 : ℝ) < 1)
    refine ⟨n₀, ?_⟩
    rw [lt_div_iff₀ (by positivity)] at hn
    linarith
  -- the hypertree calculation for each order `n < n₀`
  have hord : ∀ n ∈ range n₀, ∀ᶠ N : ℕ in atTop, ∀ A : Finset (Finset ℕ), IsSubpartition A →
      (∀ S ∈ A, S.card ≤ p) → A.card ≤ N →
      |(∑ X ∈ Fintype.piFinset (fun _ : Fin n => A.powerset), clusterWeight p (K N) X) / N -
        ∑ m ∈ profileBox p n, (∏ i, ((blockCount p A i : ℝ) / N) ^ m i / (m i).factorial) *
          hypertreeSum p n kmult m| ≤ ε / 4 * (3 / 4) ^ n := by
    intro n _
    refine eventually_abs_clusterSum_sub_le hK (fun m _ => tendsto_unionSum fun X hX h2 hV =>
      hlim X (isSubpartition_of_subset_canonicalPartition hX) h2 hV) (by positivity)
  filter_upwards [(eventually_all_finset (range n₀)).2 hord, hact, eventually_ge_atTop 1]
    with N hordN hactN hN π hπ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hπP := isSubpartition_of_mem_boundedBlockPartitions hπ
  have hπ1 := card_mem_Icc_of_mem_boundedBlockPartitions hπ
  have hπcard : π.card ≤ N := by
    have h := sum_mul_blockCount_of_mem_boundedBlockPartitions hπ
    rw [← sum_blockCount hπ1, ← h]
    exact sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hπne : π.Nonempty := by
    have h := biUnion_of_mem_boundedBlockPartitions hπ
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, biUnion_empty] at h
    have : 0 ∈ Finset.range N := mem_range.2 hN
    rw [← h] at this
    exact notMem_empty 0 this
  have hKπ : ∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
      |K N X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1) := fun X hX h2 hV =>
    hactN X (SetPartition.isSubpartition_mono hπP hX) h2 hV
  obtain ⟨hbound, hpos⟩ := hlogS N (K N) π lam hπne hπcard hπP hKπ hlam hlam1
  obtain ⟨hZ, hlogZ⟩ := hpos (by linarith)
  refine ⟨hZ, ?_⟩
  set γ := profileVec p N π
  -- the two series
  set a : ℕ+ → ℝ := fun n => 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n (K N) π / N
  set b : ℕ+ → ℝ := fun n => ∑' m : Fin p → ℕ, rateSeriesTerm p kmult γ n m
  have hr : Ct * lam ^ 2 ≤ 1 / 2 := hCtl
  have ha : ∀ n : ℕ+, |a n| ≤ (1 / 2) ^ (n : ℕ) := by
    intro n
    have h := hbound n n.pos
    simp only [a]
    rw [abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    refine h.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr _) hN0.le
  -- Transfer the bounded-cluster tail through (4.155) at the same profile.
  have hb : ∀ n : ℕ+, |b n| ≤ (1 / 2) ^ (n : ℕ) := by
    intro n
    have ht := abs_tsum_rateSeriesTerm_le_of_bounded_cluster_tail hK hlim hact
      (fun L A hne hAN hA hbnd =>
        (hlogS L (K L) A lam hne hAN hA hbnd hlam hlam1).1)
      (by positivity) hN hπP (fun S hS => (hπ1 S hS).2) hπcard n
    exact ht.trans (pow_le_pow_left₀ (by positivity) hCtl _)
  have hgeo : Summable fun n : ℕ+ => (1 / 2 : ℝ) ^ (n : ℕ) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective PNat.coe_injective
  have hsa : Summable a := Summable.of_norm_bounded hgeo fun n => by
    rw [Real.norm_eq_abs]; exact ha n
  have hsb : Summable b := Summable.of_norm_bounded hgeo fun n => by
    rw [Real.norm_eq_abs]; exact hb n
  have hlogZ' : Real.log (polymerSum p (K N) π) = N * ∑' n : ℕ+, a n := by
    rw [hlogZ, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [a]
    field_simp
  have heq : Real.log (polymerSum p (K N) π) + N * rateCluster p kmult γ =
      N * ∑' n : ℕ+, (a n + b n) := by
    rw [hlogZ', hsa.tsum_add hsb, mul_add]
    rfl
  -- termwise bound
  have hterm : ∀ n : ℕ+, |a n + b n| ≤ ε / 4 * (3 / 4) ^ (n : ℕ) := by
    intro n
    by_cases hn : (n : ℕ) < n₀
    · have hcl := hordN n (mem_range.2 hn) π hπP (fun S hS => (hπ1 S hS).2) hπcard
      have hab : a n + b n = 1 / ((n : ℕ).factorial : ℝ) *
          ((∑ X ∈ Fintype.piFinset (fun _ : Fin n => π.powerset), clusterWeight p (K N) X) / N -
            ∑ m ∈ profileBox p n, (∏ i, ((blockCount p π i : ℝ) / N) ^ m i / (m i).factorial) *
              hypertreeSum p n kmult m) := by
        simp only [a, b]
        rw [tsum_rateSeriesTerm_eq]
        unfold clusterSum
        simp only [γ, profileVec]
        ring
      rw [hab, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℕ).factorial)]
      have hf : 1 / ((n : ℕ).factorial : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast Nat.factorial_pos _)]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
      exact (mul_le_of_le_one_left (abs_nonneg _) hf).trans hcl
    · push Not at hn
      calc |a n + b n| ≤ |a n| + |b n| := abs_add_le _ _
        _ ≤ (1 / 2) ^ (n : ℕ) + (1 / 2) ^ (n : ℕ) := add_le_add (ha n) (hb n)
        _ = 2 * (1 / 2) ^ (n : ℕ) := by ring
        _ ≤ 2 * ((2 / 3) ^ n₀ * (3 / 4) ^ (n : ℕ)) :=
            mul_le_mul_of_nonneg_left (half_pow_le hn) (by positivity)
        _ = 2 * (2 / 3) ^ n₀ * (3 / 4) ^ (n : ℕ) := by ring
        _ ≤ ε / 4 * (3 / 4) ^ (n : ℕ) := mul_le_mul_of_nonneg_right hn₀ (by positivity)
  have hgeo' : Summable fun n : ℕ+ => ε / 4 * (3 / 4 : ℝ) ^ (n : ℕ) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      PNat.coe_injective).mul_left _
  have habs : Summable fun n : ℕ+ => ‖a n + b n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs]; exact hterm n) hgeo'
  rw [heq, abs_mul, abs_of_pos hN0, mul_comm ε]
  refine mul_le_mul_of_nonneg_left ?_ hN0.le
  calc |∑' n : ℕ+, (a n + b n)| ≤ ∑' n : ℕ+, ‖a n + b n‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' n : ℕ+, ε / 4 * (3 / 4 : ℝ) ^ (n : ℕ) :=
        Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hterm n) habs hgeo'
    _ = ε / 4 * ∑' n : ℕ+, (3 / 4 : ℝ) ^ (n : ℕ) := tsum_mul_left
    _ ≤ ε / 4 * 4 := mul_le_mul_of_nonneg_left tsum_pnat_three_quarters_le (by positivity)
    _ = ε := by ring

end PropFiveFortyFive

end MultipoleBKT

end
