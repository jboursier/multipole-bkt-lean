/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.ClusterLimit
public import MultipoleBKT.Cluster.Resummation
public import MultipoleBKT.Cluster.Tail
public import MultipoleBKT.Frozen.TruncatedPartitionWeight

/-!
# Proposition 5.45: the polymer gas of `Ẑ(π)` and its logarithmic series

The logarithmic series and positivity in the proof of Proposition 5.45: for a partition `π` of `[N]`, the polymer gas
`∑_{n ≥ 0} (1/n!) ∑_{X_1, …, X_n ⊂ π disjoint, 2 ≤ |X_i|, |V_{X_i}| ≤ p} ∏ᵢ K(X_i)` of eq. (5.160)
(`polymerSum`) is positive, and its logarithm is the absolutely convergent series of the
connected cluster sums (`clusterSum`), when `|K(X)| ≤ C₀ (λ²/N)^{|X|-1}` and `λ` is small.
The proof combines Lemma 4.53 (`MultipoleBKT.bounded_cluster_tail`) and Lemma 4.7
(`MultipoleBKT.lemma_4_7_subsets`). The paper also applies these to `t 𝖪^mult`, `0 ≤ t ≤ 1`; this
is not needed here, since Lemma 4.7 already gives `Z = exp F > 0`.
-/

@[expose] public section

open Finset Filter Topology

namespace MultipoleBKT

namespace PropFiveFortyFive

open scoped Classical in
/-- The polymer gas of `Ẑ(π)` (eq. (5.160)):
`∑_{n ≥ 0} (1/n!) ∑_{X_1, …, X_n ⊂ π disjoint, 2 ≤ |X_i|, |V_{X_i}| ≤ p} ∏ᵢ K(X_i)`. -/
noncomputable def polymerSum (p : ℕ) (K : Finset (Finset ℕ) → ℝ) (π : Finset (Finset ℕ)) : ℝ :=
  ∑' n : ℕ, 1 / (n.factorial : ℝ) *
    ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter (fun X =>
        (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧
          ∀ i, 2 ≤ (X i).card ∧ ((X i).biUnion id).card ≤ p),
      ∏ i, K (X i)

/-- The connected cluster sum of order `n` of the polymer gas over `π`:
`∑_{X_1, …, X_n ⊂ π} 𝟙_{G(X) connected, 2 ≤ |X_i|, |V_{X_i}| ≤ p} ∏ᵢ K(X_i) I(G(X))`. -/
noncomputable def clusterSum (p n : ℕ) (K : Finset (Finset ℕ) → ℝ) (π : Finset (Finset ℕ)) : ℝ :=
  ∑ X ∈ Fintype.piFinset (fun _ : Fin n => π.powerset), clusterWeight p K X

/-- `Ẑ(π) = (N C_{β,λ})^N 𝖬^0_∞(π) · polymerSum(π)` (eq. (5.160)). -/
theorem truncatedPartitionWeight_eq (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ) (p : ℕ)
    (π : Finset (Finset ℕ)) :
    truncatedPartitionWeight χ N β lam M p π =
      ((N : ℝ) * dipoleNormalization χ N β lam) ^ N *
        (∏ S ∈ π, multipolePartitionFunction χ N β lam M S) *
          polymerSum p (multipoleActivity χ N β lam M) π := by
  unfold truncatedPartitionWeight polymerSum
  rfl

open scoped Classical in
theorem clusterSum_eq_sum_filter (p n : ℕ) (K : Finset (Finset ℕ) → ℝ) (π : Finset (Finset ℕ)) :
    clusterSum p n K π =
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun V => (connectionGraph V).Connected ∧
            ∀ i, 2 ≤ (V i).card ∧ ((V i).biUnion id).card ≤ p),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ) := by
  unfold clusterSum clusterWeight
  rw [sum_filter]

open scoped Classical in
/-- **The logarithmic series of the polymer gas** (Lemmas 4.53 and 4.7). For `C₀ ≥ 0`
and `p`, there is `C` such that, for a subpartition `π` with `1 ≤ |π| ≤ N` and activities with
`|K(X)| ≤ C₀ (λ²/N)^{|X|-1}` on the polymers, `0 < λ ≤ 1`:
`|(1/n!) clusterSum_n| ≤ N (C λ²)^n` for `n ≥ 1`, and if `C λ² < 1`, the polymer gas is
positive with logarithm `∑_{n ≥ 1} (1/n!) clusterSum_n`. -/
theorem exists_logSeries (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (p : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ (N : ℕ) (K : Finset (Finset ℕ) → ℝ) (π : Finset (Finset ℕ)) (lam : ℝ),
      π.Nonempty → π.card ≤ N → IsSubpartition π →
      (∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
        |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
      0 < lam → lam ≤ 1 →
      (∀ n : ℕ, 1 ≤ n →
        |1 / (n.factorial : ℝ) * clusterSum p n K π| ≤ N * (Ct * lam ^ 2) ^ n) ∧
      (Ct * lam ^ 2 < 1 → 0 < polymerSum p K π ∧
        Real.log (polymerSum p K π) =
          ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K π) := by
  obtain ⟨Ct, hCt, htail⟩ := bounded_cluster_tail C₀ (max p 2) (le_max_right _ _)
  refine ⟨Ct, hCt, fun N K π lam hπ hπN hπP hK hlam hlam1 => ?_⟩
  have hN : 0 < N := (card_pos.2 hπ).trans_le hπN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let K' : Finset (Finset ℕ) → ℝ := fun X =>
    if 2 ≤ X.card ∧ (X.biUnion id).card ≤ p then K X else 0
  have hK'0 : ∀ X ⊆ π, ¬ (2 ≤ X.card ∧ X.card ≤ max p 2) → K' X = 0 := by
    intro X hX h
    simp only [K']
    rw [ite_eq_right]
    rintro ⟨h2, hV⟩
    exact h ⟨h2, ((card_le_card_biUnion (SetPartition.isSubpartition_mono hπP hX)).trans hV).trans
      (le_max_left _ _)⟩
  have hK'b : ∀ X ⊆ π, 2 ≤ X.card → X.card ≤ max p 2 →
      |K' X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1) := by
    intro X hX h2 _
    simp only [K']
    split_ifs with hPX
    · exact hK X hX hPX.1 hPX.2
    · rw [abs_zero]
      positivity
  -- the bound on the cluster terms
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |1 / (n.factorial : ℝ) * clusterSum p n K π| ≤ N * (Ct * lam ^ 2) ^ n := by
    intro n hn
    have ht := htail N π K' lam n hπ hπN hK'0 hK'b hlam hlam1 hn
    have hcmp := sum_filter_abs_prod_mul_ursell_le
      (Fintype.piFinset fun _ : Fin n => π.powerset)
      (fun V => (connectionGraph V).Connected ∧
        ∀ i, 2 ≤ (V i).card ∧ ((V i).biUnion id).card ≤ p) K K' (fun _ _ h => h.1)
      (fun V _ h => by
        rw [abs_prod]
        exact le_of_eq (prod_congr rfl fun i _ => by simp only [K', ite_eq_left (h.2 i)]))
    rw [clusterSum_eq_sum_filter, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n.factorial)]
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    calc 1 / (n.factorial : ℝ) * |∑ V ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun V => (connectionGraph V).Connected ∧
              ∀ i, 2 ≤ (V i).card ∧ ((V i).biUnion id).card ≤ p),
            (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)|
        ≤ 1 / (n.factorial : ℝ) * ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected),
            |(ursell (connectionGraph X) : ℝ)| * ∏ i, |K' (X i)| :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans hcmp) (by positivity)
      _ = N * (1 / (N * n.factorial) * ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected),
            |(ursell (connectionGraph X) : ℝ)| * ∏ i, |K' (X i)|) := by
          field_simp
      _ ≤ N * (Ct * lam ^ 2) ^ n := mul_le_mul_of_nonneg_left ht hN0.le
  refine ⟨hbound, fun hsmall => ?_⟩
  have hr0 : 0 ≤ Ct * lam ^ 2 := by positivity
  have hsum : Summable fun n : ℕ+ => ‖1 / ((n : ℕ).factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun V => (connectionGraph V).Connected ∧
            ∀ i, 2 ≤ (V i).card ∧ ((V i).biUnion id).card ≤ p),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)‖ := by
    have hg : Summable fun n : ℕ+ => (N : ℝ) * (Ct * lam ^ 2) ^ (n : ℕ) :=
      ((summable_geometric_of_lt_one hr0 hsmall).mul_left (N : ℝ)).comp_injective
        PNat.coe_injective
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hg
    rw [Real.norm_eq_abs]
    have := hbound n n.pos
    rwa [clusterSum_eq_sum_filter] at this
  have h47 := lemma_4_7_subsets π
    (fun X : Finset (Finset ℕ) => 2 ≤ X.card ∧ (X.biUnion id).card ≤ p) K
    (fun h => absurd h.1 (by simp)) hsum
  refine ⟨h47.1, h47.2.1.trans (tsum_congr fun n => ?_)⟩
  rw [clusterSum_eq_sum_filter]

end PropFiveFortyFive

end MultipoleBKT

end
