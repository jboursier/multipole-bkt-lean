/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.LowerBoundLDP.ClusterLog
public import MultipoleBKT.LowerBound.LowerBoundLDP.Relabel
public import MultipoleBKT.LowerBound.Hierarchical.StartLow
public import MultipoleBKT.Main.PropFiveFortyFive.Goal

/-!
# Proposition 4.62: the bookkeeping at fixed `N` and profile

The final deduction of (4.141) from (4.142)–(4.145) in the proof of Proposition 4.62. The paper leaves this deduction implicit.

* `mem_profilePartitions_iff`, `card_profilePartitions`, `profilePartitions_nonempty`: the
  partitions of the profile `n` of Lemma 4.18 (`MultipoleBKT.Hierarchical.profilePartitions`) are
  those of `𝚷_p([N])` with block counts `n`; there are `N!/∏ᵢ ((i+1)!)^{n_i} n_i!` of them.
* `lower_bound_of_estimates`: for a partition `π` of the profile `n`, the label symmetry
  (`setLIntegral_inter_eq_factorial_mul`), Lemma 4.18 (`MultipoleBKT.Hierarchical.lemma_4_18`) and
  the four estimates — the normalization (4.11), the block partition functions (4.143), the
  cluster sum ((4.145), in the form of `exists_log_disjointSum_ge`) and the profile
  asymptotics of the count, block partition functions and polymer gas (Stirling and the hypertree
  limit, `MultipoleBKT.PropFiveFortyFive.eventually_abs_log_count_mul_le`) — give
  `e^{N log N + log N! + (2-β) N log λ + N log 𝒵_β - N ℐ(γ) - C N δ} ≤ ∫_𝒜 e^{-βF_λ}`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace LowerBoundLDP

open Hierarchical PropFiveFortyFive

/-! ### The partitions of a profile -/

theorem mem_profilePartitions_iff {N p : ℕ} {n : Fin p → ℕ} {π : Finset (Finset ℕ)} :
    π ∈ profilePartitions N p n ↔ π ∈ boundedBlockPartitions N p ∧ blockCount p π = n := by
  rw [profilePartitions, boundedBlockPartitions_eq, mem_filter, mem_filter, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    rw [← h]
    rfl

theorem card_profilePartitions (N p : ℕ) (n : Fin p → ℕ) :
    (profilePartitions N p n).card = partitionCount N p n := by
  unfold partitionCount
  congr 1
  ext π
  rw [mem_profilePartitions_iff, mem_filter]

theorem profilePartitions_nonempty {N p : ℕ} {n : Fin p → ℕ}
    (hn : ∑ i : Fin p, ((i : ℕ) + 1) * n i = N) : (profilePartitions N p n).Nonempty := by
  rw [← card_pos, card_profilePartitions]
  exact partitionCount_pos hn

/-! ### The event `𝒜` depends only on the matched dipoles -/

/-- The event `{𝒩_1 = n_1, …, 𝒩_p = n_p} ∩ ⋂ᵢ {|x_i - y_{σ_N(i)}| ≤ h}` of (4.24) depends
only on the matched dipoles. -/
theorem eventA_invariant {N p : ℕ} (M lam h : ℝ) (n : Fin p → ℕ) (c c' : Fin N → ℂ × ℂ)
    (hc : matchedDipoles c = matchedDipoles c') :
    c ∈ {c : Fin N → ℂ × ℂ | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
        ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤ h} ↔
      c' ∈ {c : Fin N → ℂ × ℂ | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
        ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤ h} := by
  have hd : ∀ i, ((c i).1, (c (stableMatching c i)).2) =
      ((c' i).1, (c' (stableMatching c' i)).2) := fun i => congrFun hc i
  simp only [Set.mem_ofPred_eq, multipoleCount_eq_of_matchedDipoles_eq hc]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 := congrArg Prod.fst (hd i)
  have h2 := congrArg Prod.snd (hd i)
  simp only at h1 h2
  rw [h1, h2]

/-! ### The bookkeeping -/

/-- The real inequality behind the bookkeeping: with
`log #Π + log ∏𝖬 + log Ẑ + N ℐ ≥ -δN`, `log C ≥ ℓ - a₁ R`, `log 𝖬^- ≥ log ∏𝖬 - a₂ R N` and
`log Ξ ≥ log Ẑ - a₃ R N - C₂₇ N δ`, `R ≤ δ`, the logarithm of
`N! · #Π · (N C)^N 𝖬^- Ξ` is at least
`N log N + log N! + N ℓ - N ℐ - (a₁ + a₂ + a₃ + C₂₇ + 1) N δ`. -/
theorem log_bookkeeping {N lN lF lP lC lM lΞ lMz lZ ℓ I R δ a₁ a₂ a₃ C₂₇ : ℝ} (hN : 0 ≤ N)
    (hcount : -(δ * N) ≤ lP + (lMz + lZ) + N * I) (hC : ℓ - a₁ * R ≤ lC)
    (hM : lMz - a₂ * R * N ≤ lM) (hΞ : lZ - a₃ * R * N - C₂₇ * N * δ ≤ lΞ) (hRδ : R ≤ δ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) :
    N * lN + lF + N * ℓ - N * I - (a₁ + a₂ + a₃ + C₂₇ + 1) * N * δ ≤
      lF + (lP + (N * (lN + lC) + lM + lΞ)) := by
  have h1 : a₁ * R * N ≤ a₁ * δ * N := by
    have := mul_le_mul_of_nonneg_left hRδ ha₁
    exact mul_le_mul_of_nonneg_right this hN
  have h2 : a₂ * R * N ≤ a₂ * δ * N := by
    have := mul_le_mul_of_nonneg_left hRδ ha₂
    exact mul_le_mul_of_nonneg_right this hN
  have h3 : a₃ * R * N ≤ a₃ * δ * N := by
    have := mul_le_mul_of_nonneg_left hRδ ha₃
    exact mul_le_mul_of_nonneg_right this hN
  have hC' : N * (ℓ - a₁ * R) ≤ N * lC := mul_le_mul_of_nonneg_left hC hN
  nlinarith

open scoped Classical in
/-- **The bookkeeping at fixed `N` and profile** (proof of Proposition 4.62): for a
partition `π` of the profile `n` and the estimates (4.11), (4.143), (4.145) and the
profile asymptotics as hypotheses (see the module docstring),
`e^{N log N + log N! + (2-β) N log λ + N log 𝒵_β - N ℐ(n/N) - (a₁ + a₂ + a₃ + C₂₇ + 1) N δ}
≤ ∫_{(Λ²)^N ∩ 𝒜} e^{-βF_λ}`. -/
theorem lower_bound_of_estimates {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} {β lam M ε₀ L : ℝ}
    {N p : ℕ} {n : Fin p → ℕ} {π : Finset (Finset ℕ)} (hN : 1 ≤ N) (hlam : 0 < lam)
    (hβ : 0 ≤ β) (hε₀ : 0 < ε₀) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) (hL : β / 64 ≤ L)
    (hM : 1 ≤ M) (hπ : π ∈ profilePartitions N p n) {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ}
    {R δ a₁ a₂ a₃ C₂₇ : ℝ}
    (hCpos : 0 < cutoffDipoleNormalization χ N p₀ β lam ε₀)
    (hlogC : (2 - β) * Real.log lam + Real.log (dipoleConstant χ β) - a₁ * R ≤
      Real.log (cutoffDipoleNormalization χ N p₀ β lam ε₀))
    (hMpos : 0 < minusPartitionFunction χ N p₀ β lam M ε₀ L π)
    (hMzpos : 0 < ∏ S ∈ π, multipolePartitionFunction χ N β lam M (Finset.range S.card))
    (hlogM : Real.log (∏ S ∈ π, multipolePartitionFunction χ N β lam M (Finset.range S.card)) -
        a₂ * R * N ≤ Real.log (minusPartitionFunction χ N p₀ β lam M ε₀ L π))
    (hΞpos : 0 < disjointSum (minusActivity χ N p₀ β lam M ε₀ L) π)
    (hPpos : 0 < polymerSum p (multipoleActivity χ N β lam M) π)
    (hlogΞ : Real.log (polymerSum p (multipoleActivity χ N β lam M) π) - a₃ * R * N -
        C₂₇ * N * δ ≤ Real.log (disjointSum (minusActivity χ N p₀ β lam M ε₀ L) π))
    (hcount : |Real.log (partitionCount N p n) +
        Real.log ((∏ S ∈ π, multipolePartitionFunction χ N β lam M (Finset.range S.card)) *
          polymerSum p (multipoleActivity χ N β lam M) π) +
        N * rateFunction p msf kmult (fun i => (n i : ℝ) / N)| ≤ δ * N)
    (hRδ : R ≤ δ) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) :
    ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
        + (2 - β) * N * Real.log lam + N * Real.log (dipoleConstant χ β)
        - N * rateFunction p msf kmult (fun i => (n i : ℝ) / N)
        - (a₁ + a₂ + a₃ + C₂₇ + 1) * N * δ))
      ≤ ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
          {c | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
            ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
              ε₀ * truncationScale p₀ β lam},
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- label symmetry and Lemma 4.18
  rw [setLIntegral_inter_eq_factorial_mul χ β lam
    (eventA_invariant M lam (ε₀ * truncationScale p₀ β lam) n)]
  have h418 := lemma_4_18 (M := M) (L := L) hχ hlam hβ hε₀ hN hlamR hL hM p n hπ
  refine le_trans ?_ (mul_le_mul_right h418 _)
  -- the real inequality
  have hPc : (profilePartitions N p n).card = partitionCount N p n := card_profilePartitions N p n
  have hPcpos : (0 : ℝ) < (partitionCount N p n : ℝ) := by
    rw [← hPc]
    exact_mod_cast card_pos.2 ⟨π, hπ⟩
  have hNC : 0 < (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ := mul_pos hN0 hCpos
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hprod : 0 < (partitionCount N p n : ℝ) *
      (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
        minusPartitionFunction χ N p₀ β lam M ε₀ L π *
        disjointSum (minusActivity χ N p₀ β lam M ε₀ L) π) :=
    mul_pos hPcpos (mul_pos (mul_pos (pow_pos hNC N) hMpos) hΞpos)
  have hΞdef : disjointSum (minusActivity χ N p₀ β lam M ε₀ L) π =
      ∑' k : ℕ, 1 / (k.factorial : ℝ) *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => π.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∏ i, minusActivity χ N p₀ β lam M ε₀ L (Xs i) := rfl
  rw [← hΞdef, hPc, ← ENNReal.ofReal_natCast (N.factorial),
    ← ENNReal.ofReal_mul hfac.le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_log (mul_pos hfac hprod)]
  refine Real.exp_le_exp.mpr ?_
  rw [Real.log_mul hfac.ne' hprod.ne', Real.log_mul hPcpos.ne' (mul_pos (mul_pos (pow_pos hNC N)
      hMpos) hΞpos).ne',
    Real.log_mul (mul_pos (pow_pos hNC N) hMpos).ne' hΞpos.ne',
    Real.log_mul (pow_pos hNC N).ne' hMpos.ne',
    Real.log_pow, Real.log_mul hN0.ne' hCpos.ne']
  rw [Real.log_mul hMzpos.ne' hPpos.ne'] at hcount
  have hcount' := (abs_le.mp hcount).1
  have key := log_bookkeeping (N := (N : ℝ)) (lN := Real.log N) (lF := Real.log (N.factorial : ℝ))
    (ℓ := (2 - β) * Real.log lam + Real.log (dipoleConstant χ β)) hN0.le hcount' hlogC hlogM
    hlogΞ hRδ ha₁ ha₂ ha₃
  calc (N : ℝ) * Real.log N + Real.log (N.factorial : ℝ) + (2 - β) * N * Real.log lam +
        N * Real.log (dipoleConstant χ β) - N * rateFunction p msf kmult (fun i => (n i : ℝ) / N) -
        (a₁ + a₂ + a₃ + C₂₇ + 1) * N * δ
      = N * Real.log N + Real.log (N.factorial : ℝ) +
          N * ((2 - β) * Real.log lam + Real.log (dipoleConstant χ β)) -
          N * rateFunction p msf kmult (fun i => (n i : ℝ) / N) -
          (a₁ + a₂ + a₃ + C₂₇ + 1) * N * δ := by ring
    _ ≤ _ := key
    _ = _ := by ring

end LowerBoundLDP

end MultipoleBKT

end
