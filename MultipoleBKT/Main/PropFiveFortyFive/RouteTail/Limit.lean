/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.Polymer

/-!
# Passing the bounded-cluster tail to the limiting terms

In the paper, (4.155) and (4.88) justify
summation with weight `1/n!` in the proofs of Proposition 4.62, Theorem 2 and Proposition 5.45. For a fixed rational
profile, take the canonical partitions with `k` times as many blocks at scale `kN`.
Their normalized profile is unchanged. The uniform fixed-order asymptotics transfer
the finite-volume tail to the limiting term. No hypertree counting bound is used.
-/

@[expose] public section

open Finset Filter Topology

namespace MultipoleBKT.PropFiveFortyFive

open scoped Classical in
/-- The domination in (4.88) passes through (4.155) to every
limiting cluster term at a partition profile (the proof of Proposition 4.62).
The hypothesis `htail` is the finite-volume bound supplied by `exists_logSeries`. -/
theorem abs_tsum_rateSeriesTerm_le_of_bounded_cluster_tail
    {p : ℕ} {C₀ r lam : ℝ} {K : ℕ → Finset (Finset ℕ) → ℝ}
    {kmult : (ℕ →₀ ℕ) → ℝ}
    (hK : ∀ N, 1 ≤ N → IsProfileInvariant (K N))
    (hlim : ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
      (X.biUnion id).card ≤ p →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (X.card - 1) * K N X) atTop
        (𝓝 (kmult (blockProfile X))))
    (hact : ∀ᶠ N : ℕ in atTop, ∀ X : Finset (Finset ℕ), IsSubpartition X →
      2 ≤ X.card → (X.biUnion id).card ≤ p →
      |K N X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1))
    (htail : ∀ (N : ℕ) (A : Finset (Finset ℕ)), A.Nonempty → A.card ≤ N →
      IsSubpartition A →
      (∀ X ⊆ A, 2 ≤ X.card → (X.biUnion id).card ≤ p →
        |K N X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
      ∀ n : ℕ, 1 ≤ n →
        |1 / (n.factorial : ℝ) * clusterSum p n (K N) A| ≤ N * r ^ n)
    (hr : 0 ≤ r) {N : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ : IsSubpartition π) (hπp : ∀ S ∈ π, S.card ≤ p) (hπN : π.card ≤ N)
    (n : ℕ+) :
    |∑' m : Fin p → ℕ, rateSeriesTerm p kmult
      (fun i => (blockCount p π i : ℝ) / N) n m| ≤ r ^ (n : ℕ) := by
  -- Replicate every block count. The canonical family has the same normalized profile.
  have hcount : ∑ i : Fin p, blockCount p π i = π.card :=
    sum_blockCount fun S hS => ⟨Nat.one_le_iff_ne_zero.2
      (card_ne_zero.2 (hπ.1 S hS)), hπp S hS⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- At each positive tolerance, use (4.155) beyond its uniform threshold.
  have hord := eventually_abs_clusterSum_sub_le (p := p) (n := (n : ℕ)) hK
    (fun m _ => tendsto_unionSum fun X hX h2 hV =>
      hlim X (isSubpartition_of_subset_canonicalPartition hX) h2 hV) hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hord.and hact)
  let k := M + 1
  let L := k * N
  let A := canonicalPartition (fun i : Fin p => k * blockCount p π i)
  have hk : 0 < k := Nat.succ_pos M
  have hL : 0 < L := Nat.mul_pos hk hN
  have hML : M ≤ L := (Nat.le_succ M).trans (Nat.le_mul_of_pos_right k hN)
  have hAP : IsSubpartition A := isSubpartition_canonicalPartition _
  have hAp : ∀ S ∈ A, S.card ≤ p := fun S hS =>
    (card_mem_Icc_of_mem_canonicalPartition S hS).2
  have hAN : A.card ≤ L := by
    rw [show A = canonicalPartition (fun i : Fin p => k * blockCount p π i) from rfl,
      card_canonicalPartition, ← mul_sum, hcount]
    exact Nat.mul_le_mul_left k hπN
  have hprofile : (fun i : Fin p => (blockCount p A i : ℝ) / L) =
      (fun i => (blockCount p π i : ℝ) / N) := by
    funext i
    simp only [A, blockCount_canonicalPartition, L, Nat.cast_mul]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
  have happrox := (hM L hML).1 A hAP hAp hAN
  simp_rw [show ∀ i, (blockCount p A i : ℝ) / L =
    (blockCount p π i : ℝ) / N from congrFun hprofile] at happrox
  -- The empty family has no retained cluster. Otherwise apply the finite-volume tail.
  have hbound : |1 / ((n : ℕ).factorial : ℝ) * clusterSum p n (K L) A| ≤
      L * r ^ (n : ℕ) := by
    rcases A.eq_empty_or_nonempty with hA | hA
    · have hz : clusterSum p n (K L) A = 0 := by
        rw [hA]
        unfold clusterSum clusterWeight
        refine sum_eq_zero fun X hX => ?_
        rw [ite_eq_right]
        rintro ⟨-, h⟩
        have hX0 := Fintype.mem_piFinset.1 hX ⟨0, n.pos⟩
        rw [powerset_empty, mem_singleton] at hX0
        have := (h ⟨0, n.pos⟩).1
        rw [hX0, card_empty] at this
        omega
      rw [hz, mul_zero, abs_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _)
    · exact htail L A hA hAN hAP (fun X hX h2 hV =>
        (hM L hML).2 X (SetPartition.isSubpartition_mono hAP hX) h2 hV) n n.pos
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hnorm : |1 / ((n : ℕ).factorial : ℝ) * clusterSum p n (K L) A / L| ≤
      r ^ (n : ℕ) := by
    rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
    simpa only [mul_comm] using hbound
  have hf : 0 ≤ 1 / ((n : ℕ).factorial : ℝ) := by positivity
  have hf1 : 1 / ((n : ℕ).factorial : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < (n : ℕ).factorial)]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have herr : |1 / ((n : ℕ).factorial : ℝ) * clusterSum p n (K L) A / L +
      ∑' m : Fin p → ℕ, rateSeriesTerm p kmult
        (fun i => (blockCount p π i : ℝ) / N) n m| ≤ ε := by
    rw [tsum_rateSeriesTerm_eq]
    have heq : 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n (K L) A / L +
        -(1 / ((n : ℕ).factorial : ℝ)) *
          ∑ m ∈ profileBox p n,
            (∏ i, ((blockCount p π i : ℝ) / N) ^ m i / (m i).factorial) *
              hypertreeSum p n kmult m =
        1 / ((n : ℕ).factorial : ℝ) *
          (clusterSum p n (K L) A / L -
            ∑ m ∈ profileBox p n,
              (∏ i, ((blockCount p π i : ℝ) / N) ^ m i / (m i).factorial) *
                hypertreeSum p n kmult m) := by ring
    rw [heq, abs_mul, abs_of_nonneg hf]
    exact (mul_le_of_le_one_left (abs_nonneg _) hf1).trans happrox
  -- Let the tolerance decrease to zero to inherit exactly the same tail.
  calc |∑' m : Fin p → ℕ, rateSeriesTerm p kmult
          (fun i => (blockCount p π i : ℝ) / N) n m|
      ≤ |1 / ((n : ℕ).factorial : ℝ) * clusterSum p n (K L) A / L +
          ∑' m : Fin p → ℕ, rateSeriesTerm p kmult
            (fun i => (blockCount p π i : ℝ) / N) n m| +
          |1 / ((n : ℕ).factorial : ℝ) * clusterSum p n (K L) A / L| := by
        simpa only [add_sub_cancel_left] using abs_sub
          (1 / ((n : ℕ).factorial : ℝ) * clusterSum p n (K L) A / L +
            ∑' m : Fin p → ℕ, rateSeriesTerm p kmult
              (fun i => (blockCount p π i : ℝ) / N) n m)
          (1 / ((n : ℕ).factorial : ℝ) * clusterSum p n (K L) A / L)
    _ ≤ ε + r ^ (n : ℕ) := add_le_add herr hnorm
    _ = r ^ (n : ℕ) + ε := add_comm _ _

end MultipoleBKT.PropFiveFortyFive

end
