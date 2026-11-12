/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.AbsoluteUpper.Bounded
public import MultipoleBKT.Cluster.Tail
public import MultipoleBKT.Cluster.Resummation

/-!
# The full connected series and `W(Z) = exp(S(Z)) > 0`

The paper: proof of Proposition 5.20:
"For `2 ≤ |X|` and `|V_X| ≤ p = p(β)`, Propositions 4.23 and 5.18 give
`|𝖪^{+,Z}_{ε₀}(X)| ≤ C_{ε₀} (λ²/N)^{|X|-1}`. Lemma 4.53 proves absolute convergence of the subseries
containing only these activities; (5.71) controls its complement. … Continuing (4.4)
from `t = 0` gives `W(Z) = exp(S(Z)) > 0`."

* `summable_connectedTerm_of_small`:
  for an activity `K` vanishing on families of at most one block, bounded by
  `C₀ (λ²/N)^{|X|-1}` on the clusters with `|V_X| ≤ p`, the `n`-th term of the full connected
  series is at most `N (C λ²)^n` plus the `n`-th term of the series of (5.71) (Lemma 4.53,
  `MultipoleBKT.bounded_cluster_tail`, for the subseries of small activities); hence the full
  series converges absolutely when the series of (5.71) converges and `C λ² ≤ 1/2`.
* `disjointSeries_eq_exp`: under the
  absolute convergence of the full connected series, the polymer sum
  `∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) disjoint} K(X₁) ⋯ K(Xₙ)` is `exp` of the connected series,
  hence positive (Lemma 4.7, `MultipoleBKT.lemma_4_7_subsets`, an identity of real numbers under
  absolute convergence; the paper's continuation in `t` is not needed).
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

namespace AbsoluteUpper

variable {π : Finset (Finset ℕ)} {K : Finset (Finset ℕ) → ℝ}

/-- For a subpartition, `|X| ≤ |V_X|`. -/
theorem card_le_card_biUnion_of_isSubpartition {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    X.card ≤ (X.biUnion id).card :=
  card_le_card_biUnion (fun _S hS _T hT hST => hX.2 hS hT hST) fun S hS => hX.1 S hS

/-- A subfamily of a subpartition is a subpartition. -/
theorem isSubpartition_of_subset {X : Finset (Finset ℕ)} (hπ : IsSubpartition π) (hX : X ⊆ π) :
    IsSubpartition X :=
  ⟨fun S hS => hπ.1 S (hX hS), hπ.2.subset (by exact_mod_cast hX)⟩

open scoped Classical in
/-- The connection graph of an empty family is not connected, so the `0`-th connected term
vanishes. -/
theorem connectedTerm_zero : connectedTerm K π 0 = 0 := by
  rw [connectedTerm]
  refine mul_eq_zero_of_right _ (sum_eq_zero fun Xs hXs => ?_)
  exact absurd (mem_filter.1 hXs).2.nonempty (not_nonempty_iff.2 inferInstance)

open scoped Classical in
/-- **The full connected series converges absolutely** (proof of Proposition 5.20): there is `C > 0` depending only on `C₀`
and `p` such that for an activity `K` on the subfamilies of a subpartition `π` with `|π| ≤ N`,
vanishing on families of at most one block and bounded by `C₀ (λ²/N)^{|X|-1}` on the families
with `|V_X| ≤ p`, `0 < λ ≤ 1` and `C λ² ≤ 1/2`: if the series of (5.71) converges, so does
the full connected series (in absolute value). -/
theorem summable_connectedTerm_of_small {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (π : Finset (Finset ℕ)) (N : ℕ) (K : Finset (Finset ℕ) → ℝ) (lam : ℝ),
      IsSubpartition π → π.card ≤ N → (∀ X ⊆ π, X.card ≤ 1 → K X = 0) →
      (∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
        |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
      0 < lam → lam ≤ 1 → C * lam ^ 2 ≤ 1 / 2 →
      Summable (bigClusterTerm K π p) → Summable (connectedTerm K π) := by
  obtain ⟨C, hC, hT⟩ := bounded_cluster_tail C₀ (max p 2) (le_max_right _ _)
  refine ⟨C, hC, fun π N K lam hπ hπN hK1 hK hlam hlam1 hCl hbig => ?_⟩
  set Ks : Finset (Finset ℕ) → ℝ := fun X => if (X.biUnion id).card ≤ p then K X else 0
    with hKs
  have hr0 : 0 ≤ C * lam ^ 2 := by positivity
  -- the bound on the `n`-th term
  have hterm : ∀ n, connectedTerm K π n ≤ N * (C * lam ^ 2) ^ n + bigClusterTerm K π p n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [connectedTerm_zero]
      exact add_nonneg (by positivity) (bigClusterTerm_nonneg K π p 0)
    set S := (Fintype.piFinset fun _ : Fin n => π.powerset).filter
      (fun Xs : Fin n → Finset (Finset ℕ) => (connectionGraph Xs).Connected)
    have hsplit : ∑ Xs ∈ S, |(∏ i, K (Xs i)) * (ursell (connectionGraph Xs) : ℝ)| =
        ∑ Xs ∈ S.filter (fun Xs => ∃ i, p < ((Xs i).biUnion id).card),
            |(∏ i, K (Xs i)) * (ursell (connectionGraph Xs) : ℝ)| +
          ∑ Xs ∈ S.filter (fun Xs => ¬ ∃ i, p < ((Xs i).biUnion id).card),
            |(∏ i, K (Xs i)) * (ursell (connectionGraph Xs) : ℝ)| :=
      (sum_filter_add_sum_filter_not S _ _).symm
    have hbigEq : 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ S.filter (fun Xs => ∃ i, p < ((Xs i).biUnion id).card),
          |(∏ i, K (Xs i)) * (ursell (connectionGraph Xs) : ℝ)| = bigClusterTerm K π p n := by
      rw [bigClusterTerm, filter_filter]
    -- the small part, by Lemma 4.53
    have hsmall : ∑ Xs ∈ S.filter (fun Xs => ¬ ∃ i, p < ((Xs i).biUnion id).card),
        |(∏ i, K (Xs i)) * (ursell (connectionGraph Xs) : ℝ)| ≤
          ∑ Xs ∈ S, |(ursell (connectionGraph Xs) : ℝ)| * ∏ i, |Ks (Xs i)| := by
      refine (sum_le_sum fun Xs hXs => le_of_eq ?_).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
          mul_nonneg (abs_nonneg _) (prod_nonneg fun _ _ => abs_nonneg _))
      have hall := (mem_filter.1 hXs).2
      push Not at hall
      rw [abs_mul, mul_comm, abs_prod]
      congr 1
      refine prod_congr rfl fun i _ => ?_
      rw [hKs]
      simp only [ite_eq_left (hall i)]
    have hS : ∑ Xs ∈ S, |(ursell (connectionGraph Xs) : ℝ)| * ∏ i, |Ks (Xs i)| ≤
        N * n.factorial * (C * lam ^ 2) ^ n := by
      by_cases hπ0 : π.Nonempty
      · have hN : 0 < N := (card_pos.2 hπ0).trans_le hπN
        have hKs0 : ∀ X ⊆ π, ¬ (2 ≤ X.card ∧ X.card ≤ max p 2) → Ks X = 0 := by
          intro X hX hX2
          by_cases hc : X.card ≤ 1
          · simp only [hKs, hK1 X hX hc, ite_self]
          · have hp' : ¬ (X.biUnion id).card ≤ p := by
              have := card_le_card_biUnion_of_isSubpartition (isSubpartition_of_subset hπ hX)
              omega
            simp only [hKs, ite_eq_right hp']
        have hKsb : ∀ X ⊆ π, 2 ≤ X.card → X.card ≤ max p 2 →
            |Ks X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1) := by
          intro X hX h2 _
          by_cases hp' : (X.biUnion id).card ≤ p
          · simp only [hKs, ite_eq_left hp']
            exact hK X hX h2 hp'
          · simp only [hKs, ite_eq_right hp', abs_zero]
            positivity
        have h := hT N π Ks lam n hπ0 hπN hKs0 hKsb hlam hlam1 hn
        have hNf : (0 : ℝ) < N * n.factorial := by
          have : (0 : ℝ) < N := by exact_mod_cast hN
          positivity
        rw [one_div, inv_mul_le_iff₀ hNf] at h
        convert h using 2
        ext Xs
        simp only [S, mem_filter]
      · rw [not_nonempty_iff_eq_empty] at hπ0
        refine (sum_eq_zero fun Xs hXs => ?_).le.trans (by positivity)
        have hXs0 : Xs ⟨0, hn⟩ = ∅ := by
          have := Fintype.mem_piFinset.1 (mem_filter.1 hXs).1 ⟨0, hn⟩
          rw [hπ0, powerset_empty, mem_singleton] at this
          exact this
        have hK0 : Ks ∅ = 0 := by
          simp only [hKs, hK1 ∅ (empty_subset _) (by simp), ite_self]
        rw [prod_eq_zero (mem_univ ⟨0, hn⟩) (by rw [hXs0, hK0, abs_zero]), mul_zero]
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    calc connectedTerm K π n
        = 1 / (n.factorial : ℝ) * ∑ Xs ∈ S.filter (fun Xs => ¬ ∃ i, p < ((Xs i).biUnion id).card),
              |(∏ i, K (Xs i)) * (ursell (connectionGraph Xs) : ℝ)| + bigClusterTerm K π p n := by
          rw [connectedTerm, hsplit, mul_add, hbigEq, add_comm]
      _ ≤ 1 / (n.factorial : ℝ) * (N * n.factorial * (C * lam ^ 2) ^ n) +
            bigClusterTerm K π p n := by
          gcongr
          exact hsmall.trans hS
      _ = N * (C * lam ^ 2) ^ n + bigClusterTerm K π p n := by
          field_simp
  have hgeo : Summable fun n : ℕ => (N : ℝ) * (C * lam ^ 2) ^ n :=
    (summable_geometric_of_lt_one hr0 (by linarith)).mul_left _
  exact Summable.of_nonneg_of_le (connectedTerm_nonneg K π) hterm (hgeo.add hbig)

open scoped Classical in
/-- **`W = exp(S) > 0`** (Lemma 4.7 under absolute convergence): if `K(∅) = 0` and the full connected series of
`K` on `𝒫(π)` converges absolutely, then the polymer sum
`∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) disjoint} K(X₁) ⋯ K(Xₙ)` is positive and equals
`exp(connectedSeries K π)`. -/
theorem disjointSeries_eq_exp (hK : K ∅ = 0) (hsum : Summable (connectedTerm K π)) :
    0 < ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)), ∏ i, K (Xs i) ∧
      ∑' n : ℕ, 1 / (n.factorial : ℝ) *
          ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
              (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)), ∏ i, K (Xs i) =
        Real.exp (connectedSeries K π) := by
  have h47 := lemma_4_7_subsets π (fun _ => True) K (fun _ => hK) (by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_pnat_iff_summable_nat.2 hsum)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℕ).factorial : ℝ)), connectedTerm]
    refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (le_of_eq ?_))
      (by positivity)
    exact sum_congr (by ext V; simp) fun _ _ => rfl)
  have hpos := h47.1
  have hexp := h47.2.2
  refine ⟨hpos.trans_eq ?_, Eq.trans ?_ (hexp.trans ?_)⟩
  · refine tsum_congr fun n => ?_
    congr 1
    exact sum_congr (by ext V; simp) fun _ _ => rfl
  · refine tsum_congr fun n => ?_
    congr 1
    exact sum_congr (by ext V; simp) fun _ _ => rfl
  · rw [connectedSeries]
    congr 1
    refine tsum_congr fun n => ?_
    congr 1
    exact sum_congr (by ext V; simp) fun _ _ => rfl

end AbsoluteUpper

end UpperBound

end MultipoleBKT

end
