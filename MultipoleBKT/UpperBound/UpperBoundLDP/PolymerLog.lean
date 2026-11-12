/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.LogEstimate
public import MultipoleBKT.LowerBound.LowerBoundLDP.ClusterLog

/-!
# The logarithm of the polymer gas over a subpartition

The proof of Proposition 5.43 (equations (4.155) and (5.145)) evaluates the cluster series of `𝖪^mult` over a partition
`π` of the good labels `V_good ⊊ [N]` (not of `[N]`): with `γᵢ = n_i/N`,

  `log polymerSum_p(𝖪^mult)(π) = -N h(γ) + o_λ(N)`, uniformly in `π`

(`exists_log_polymerSum_subpartition`). This is
`MultipoleBKT.PropFiveFortyFive.exists_log_polymerSum` for subpartitions with at most `N` blocks
(that proof never uses that `π` covers `[N]`). The empty subpartition is allowed (its polymer gas
is `1`). Both the finite-volume and limiting series are dominated by the
bounded-cluster tail, transferred through (4.155) by the shared lemma
`MultipoleBKT.PropFiveFortyFive.abs_tsum_rateSeriesTerm_le_of_bounded_cluster_tail`.
-/

@[expose] public section

open Finset Filter Topology

namespace MultipoleBKT

namespace UpperBoundLDP

open PropFiveFortyFive

open scoped Classical in
/-- The polymer gas over the empty family is `1`. -/
theorem polymerSum_empty (p : ℕ) (K : Finset (Finset ℕ) → ℝ) : polymerSum p K ∅ = 1 := by
  unfold polymerSum
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    have : ((Fintype.piFinset fun _ : Fin n => (∅ : Finset (Finset ℕ)).powerset).filter fun X =>
        (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧
          ∀ i, 2 ≤ (X i).card ∧ ((X i).biUnion id).card ≤ p) = ∅ := by
      refine filter_eq_empty_iff.2 fun X hX h => ?_
      have hi : (⟨0, Nat.pos_of_ne_zero hn⟩ : Fin n) = ⟨0, Nat.pos_of_ne_zero hn⟩ := rfl
      have hX0 := Fintype.mem_piFinset.1 hX ⟨0, Nat.pos_of_ne_zero hn⟩
      rw [powerset_empty, mem_singleton] at hX0
      have := (h.2 ⟨0, Nat.pos_of_ne_zero hn⟩).1
      rw [hX0, card_empty] at this
      omega
    rw [this, sum_empty, mul_zero]

/-- The connected cluster sums over the empty family vanish. -/
theorem clusterSum_empty (p n : ℕ) (K : Finset (Finset ℕ) → ℝ) : clusterSum p n K ∅ = 0 := by
  unfold clusterSum clusterWeight
  refine sum_eq_zero fun X hX => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ite_eq_right]
    rintro ⟨hc, -⟩
    exact (SimpleGraph.Connected.nonempty hc).elim fun i => i.elim0
  · rw [ite_eq_right]
    rintro ⟨-, h⟩
    have hX0 := Fintype.mem_piFinset.1 hX ⟨0, hn⟩
    rw [powerset_empty, mem_singleton] at hX0
    have := (h ⟨0, hn⟩).1
    rw [hX0, card_empty] at this
    omega

open scoped Classical in
/-- `exists_logSeries` for every subpartition with at most `N` blocks, the empty one included. -/
theorem exists_logSeries' (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (p : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ (N : ℕ) (K : Finset (Finset ℕ) → ℝ) (π : Finset (Finset ℕ)) (lam : ℝ),
      π.card ≤ N → IsSubpartition π →
      (∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
        |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
      0 < lam → lam ≤ 1 →
      (∀ n : ℕ, 1 ≤ n →
        |1 / (n.factorial : ℝ) * clusterSum p n K π| ≤ N * (Ct * lam ^ 2) ^ n) ∧
      (Ct * lam ^ 2 < 1 → 0 < polymerSum p K π ∧
        Real.log (polymerSum p K π) =
          ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K π) := by
  obtain ⟨Ct, hCt, h⟩ := exists_logSeries C₀ hC₀ p
  refine ⟨Ct, hCt, fun N K π lam hπN hπP hK hlam hlam1 => ?_⟩
  rcases π.eq_empty_or_nonempty with rfl | hπ
  · refine ⟨fun n _ => ?_, fun _ => ?_⟩
    · rw [clusterSum_empty, mul_zero, abs_zero]
      positivity
    · rw [polymerSum_empty, Real.log_one]
      refine ⟨one_pos, ?_⟩
      simp only [clusterSum_empty, mul_zero, tsum_zero]
  · exact h N K π lam hπ hπN hπP hK hlam hlam1

open scoped Classical in
/-- **The logarithm of the polymer gas over a subpartition**
(the paper, Proposition 5.43, (5.145)): as
`MultipoleBKT.PropFiveFortyFive.exists_log_polymerSum`, uniformly over the subpartitions `π` with
blocks of size at most `p` and at most `N` blocks. -/
theorem exists_log_polymerSum_subpartition (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (p : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ (kmult : (ℕ →₀ ℕ) → ℝ) (C lam : ℝ) (K : ℕ → Finset (Finset ℕ) → ℝ),
      0 < lam → lam ≤ 1 → Ct * lam ^ 2 ≤ 1 / 2 →
      KmultBound p kmult C lam → rateSeriesConst p C * lam ^ 2 ≤ 1 / 4 →
      (∀ N, 1 ≤ N → IsProfileInvariant (K N)) →
      (∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card → (X.biUnion id).card ≤ p →
        Tendsto (fun N : ℕ => (N : ℝ) ^ (X.card - 1) * K N X) atTop
          (𝓝 (kmult (blockProfile X)))) →
      (∀ᶠ N : ℕ in atTop, ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
        (X.biUnion id).card ≤ p → |K N X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ π : Finset (Finset ℕ), IsSubpartition π →
        (∀ S ∈ π, S.card ≤ p) → π.card ≤ N →
        0 < polymerSum p (K N) π ∧
          |Real.log (polymerSum p (K N) π) + N * rateCluster p kmult (profileVec p N π)| ≤
            ε * N := by
  obtain ⟨Ct, hCt, hlogS⟩ := exists_logSeries' C₀ hC₀ p
  refine ⟨Ct, hCt, fun kmult C lam K hlam hlam1 hCtl _hk _hsmall hK hlim hact ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 2 * (2 / 3 : ℝ) ^ n₀ ≤ ε / 4 := by
    obtain ⟨n₀, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < ε / 4 / 2)
      (by norm_num : (2 / 3 : ℝ) < 1)
    refine ⟨n₀, ?_⟩
    rw [lt_div_iff₀ (by positivity)] at hn
    linarith
  have hord : ∀ n ∈ range n₀, ∀ᶠ N : ℕ in atTop, ∀ A : Finset (Finset ℕ), IsSubpartition A →
      (∀ S ∈ A, S.card ≤ p) → A.card ≤ N →
      |(∑ X ∈ Fintype.piFinset (fun _ : Fin n => A.powerset), clusterWeight p (K N) X) / N -
        ∑ m ∈ profileBox p n, (∏ i, ((blockCount p A i : ℝ) / N) ^ m i / (m i).factorial) *
          hypertreeSum p n kmult m| ≤ ε / 4 * (3 / 4) ^ n := by
    intro n _
    refine eventually_abs_clusterSum_sub_le hK (fun m _ => tendsto_unionSum fun X hX h2 hV =>
      hlim X (isSubpartition_of_subset_canonicalPartition hX) h2 hV) (by positivity)
  filter_upwards [(eventually_all_finset (range n₀)).2 hord, hact, eventually_ge_atTop 1]
    with N hordN hactN hN π hπP hπp hπcard
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hKπ : ∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
      |K N X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1) := fun X hX h2 hV =>
    hactN X (SetPartition.isSubpartition_mono hπP hX) h2 hV
  obtain ⟨hbound, hpos⟩ := hlogS N (K N) π lam hπcard hπP hKπ hlam hlam1
  obtain ⟨hZ, hlogZ⟩ := hpos (by linarith)
  refine ⟨hZ, ?_⟩
  set γ := profileVec p N π
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
      (fun L A _hne hAN hA hbnd =>
        (hlogS L (K L) A lam hAN hA hbnd hlam hlam1).1)
      (by positivity) hN hπP hπp hπcard n
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
  have hterm : ∀ n : ℕ+, |a n + b n| ≤ ε / 4 * (3 / 4) ^ (n : ℕ) := by
    intro n
    by_cases hn : (n : ℕ) < n₀
    · have hcl := hordN n (mem_range.2 hn) π hπP hπp hπcard
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

open scoped Classical in
/-- **The logarithm of the cluster sum, upper bound** (Step 2 of the proof of Proposition 5.43,
the paper, Proposition 5.43, the upper-bound twin of
`MultipoleBKT.LowerBoundLDP.exists_log_disjointSum_ge`), for a subpartition `π` with at most `N` blocks: with `Ct` from Lemma 4.53 for the bound `C₀` and `p`, for
activities `K₁` (vanishing on families of at most one block) and `K₂` bounded by
`C₀ (λ²/N)^{|X|-1}` on the retained clusters, with the full connected series of `K₁` absolutely
convergent and its part over the tuples with some `|V_{X_i}| > p` at most `B`, for `λ` small,
`log Ξ(π) ≤ log polymerSum_p(K₂)(π) + 4 e² ∑_{X ⊂ π retained} |K₁(X) - K₂(X)| + B`. -/
theorem exists_log_disjointSum_le (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (p : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ (N : ℕ) (π : Finset (Finset ℕ)) (K₁ K₂ : Finset (Finset ℕ) → ℝ)
      (lam B : ℝ), IsSubpartition π → π.card ≤ N → 0 < lam → lam ≤ 1 →
      Ct * lam ^ 2 ≤ 1 / 2 → Real.exp 2 * (p * (p * (2 * C₀) * lam ^ 2)) ≤ 1 / 2 →
      (∀ X ⊆ π, X.card ≤ 1 → K₁ X = 0) →
      (∀ X ⊆ π, LowerBoundLDP.Retained p X → |K₁ X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
      (∀ X ⊆ π, LowerBoundLDP.Retained p X → |K₂ X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
      (Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected),
          |(∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ)|) →
      (∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected ∧ ∃ i, p < ((X i).biUnion id).card),
          |(∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ)| ≤ B) →
      0 < LowerBoundLDP.disjointSum K₁ π ∧ 0 < polymerSum p K₂ π ∧
        Real.log (LowerBoundLDP.disjointSum K₁ π) ≤ Real.log (polymerSum p K₂ π) +
          4 * Real.exp 2 *
            (∑ Y ∈ π.powerset, if LowerBoundLDP.Retained p Y then |K₁ Y - K₂ Y| else 0) + B := by
  obtain ⟨Ct, hCt, hlogS⟩ := exists_logSeries' C₀ hC₀ p
  refine ⟨Ct, hCt, fun N π K₁ K₂ lam B hπP hπN hlam hlam1 hCtl hsmall hK1 hb₁ hb₂ habs hbad =>
    ?_⟩
  obtain ⟨hbd₁, -⟩ := hlogS N K₁ π lam hπN hπP (fun X hX h2 hV => hb₁ X hX ⟨h2, hV⟩)
    hlam hlam1
  obtain ⟨hbd₂, hpos₂⟩ := hlogS N K₂ π lam hπN hπP (fun X hX h2 hV => hb₂ X hX ⟨h2, hV⟩)
    hlam hlam1
  obtain ⟨hP₂, hlog₂⟩ := hpos₂ (by linarith)
  have hgeo : ∀ {K : Finset (Finset ℕ) → ℝ},
      (∀ n : ℕ, 1 ≤ n → |1 / (n.factorial : ℝ) * clusterSum p n K π| ≤ N * (Ct * lam ^ 2) ^ n) →
      Summable fun n : ℕ+ => 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K π := by
    intro K hK
    have hr0 : 0 ≤ Ct * lam ^ 2 := by positivity
    have hg : Summable fun n : ℕ+ => (N : ℝ) * (Ct * lam ^ 2) ^ (n : ℕ) :=
      ((summable_geometric_of_lt_one hr0 (by linarith)).mul_left (N : ℝ)).comp_injective
        PNat.coe_injective
    exact Summable.of_norm_bounded hg fun n => by rw [Real.norm_eq_abs]; exact hK n n.pos
  have hs₁ := hgeo hbd₁
  have hs₂ := hgeo hbd₂
  obtain ⟨hZ, E, hE, hlogZ⟩ := LowerBoundLDP.log_disjointSum_eq_add hK1 habs hbad hs₁
  have htel := LowerBoundLDP.abs_tsum_clusterSum_sub_le hπP hπN hC₀ hlam hlam1 hb₁ hb₂ hsmall
    hs₁ hs₂
  refine ⟨hZ, hP₂, ?_⟩
  rw [hlogZ, hlog₂]
  have h1 := (abs_le.mp htel).2
  have h2 := (abs_le.mp hE).2
  linarith

end UpperBoundLDP

end MultipoleBKT

end
