/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.StartLowEvent

/-!
# Lemma 4.18, summed over the partitions of a given profile

Lemma 4.18 and its proof (proof of Lemma 4.18).

* `profilePartitions N p n`: the partitions `π` of `[N]` with `n_k` blocks of size `k` for
  `k = 1, …, p` and no block of size `≥ p + 1` (eq. (4.25)), with `n i = n_{i+1}`;
* `lemma_4_18_sum`: Steps 1–8 without the relabeling of Step 1:
  `∑_{π} (N C_{β,λ,ε₀})^N 𝖬^-_{ε₀}(π) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) disjoint}
  ∏ₗ 𝖪^-_{ε₀}(Xₗ) ≤ ∫_{𝒜 ∩ \{σ_N = Id\}} e^{-β F_λ}`, the sum over `π ∈ profilePartitions N p n`
  and `𝒜` the event (4.24) in the form of the frozen Proposition 4.62. The events
  `{Π_mult = π, σ_N = Id}` of distinct `π` are disjoint and contained in `𝒜 ∩ {σ_N = Id}`
  (`MultipoleBKT.Hierarchical.startEvent_subset`, `eq_of_mem_startEvent`), and each is bounded
  below by `start_low_partition`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

open scoped Classical in
/-- The partitions `π` of `[N] = {0, …, N - 1}` with `n_{i+1} = n i` blocks of size `i + 1` for
`i < p` and no block of size `≥ p + 1` (eq. (4.25)). -/
noncomputable def profilePartitions (N p : ℕ) (n : Fin p → ℕ) : Finset (Finset (Finset ℕ)) :=
  (partitions (Finset.range N)).filter fun π =>
    (∀ S ∈ π, S.card ≤ p) ∧ ∀ i : Fin p, (π.filter fun S => S.card = (i : ℕ) + 1).card = n i

/-- A finite sum of lower integrals is at most the lower integral of the sum. -/
theorem sum_lintegral_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    simp_rw [Finset.sum_insert hb]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- **Lemma 4.18, summed over the partitions of the profile** (Steps 1–8, without the
relabeling of Step 1): for `λ > 0`, `λ ≤ ε₀ R̄`, `β ≥ 0`, `L ≥ β/64`, `N ≥ 1`,
`∑_{π} (N C_{β,λ,ε₀})^N 𝖬^-_{ε₀}(π) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) disjoint} ∏ₗ 𝖪^-_{ε₀}(Xₗ)
≤ ∫_{𝒜 ∩ \{σ_N = Id\}} e^{-β F_λ}`, the sum over the partitions `π` of `[N]` with `n_k` blocks of
size `k` (`k ≤ p`) and none larger. -/
theorem lemma_4_18_sum (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) (hL : β / 64 ≤ L) (p : ℕ)
    (n : Fin p → ℕ) :
    ∑ π ∈ profilePartitions N p n,
        ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
          minusPartitionFunction χ N p₀ β lam M ε₀ L π *
          ∑' k : ℕ, 1 / (k.factorial : ℝ) *
            ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => π.powerset).filter
                (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
              ∏ i, minusActivity χ N p₀ β lam M ε₀ L (Xs i)) ≤
      ∫⁻ c in ((Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
          {c | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
            ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
              ε₀ * truncationScale p₀ β lam}) ∩ {c | stableMatching c = Equiv.refl _},
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  set A := ((Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
    {c : Fin N → ℂ × ℂ | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
      ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤ ε₀ * truncationScale p₀ β lam}) ∩
    {c | stableMatching c = Equiv.refl _} with hA
  set f : (Fin N → ℂ × ℂ) → ℝ≥0∞ := fun c => ENNReal.ofReal (Real.exp (-β * energy χ lam c))
    with hf
  refine (Finset.sum_le_sum fun π hπ => start_low_partition (M := M) (L := L) hχ hlam hβ hε₀ hN
    hlamR hL (Finset.mem_filter.1 hπ).1).trans ?_
  refine (sum_lintegral_le _ _).trans ((lintegral_mono fun c => ?_).trans
    (lintegral_indicator_le f A))
  show (∑ π ∈ profilePartitions N p n, (startEvent N p₀ β lam M ε₀ π).indicator f c) ≤
    A.indicator f c
  by_cases hc : ∃ π ∈ profilePartitions N p n, c ∈ startEvent N p₀ β lam M ε₀ π
  · obtain ⟨π₀, hπ₀, hcπ₀⟩ := hc
    rw [Finset.sum_eq_single_of_mem π₀ hπ₀ fun π hπ hne => ?_]
    · rw [Set.indicator_of_mem hcπ₀]
      have hπ₀' := Finset.mem_filter.1 hπ₀
      rw [Set.indicator_of_mem (startEvent_subset hπ₀'.1 hπ₀'.2.2 hcπ₀)]
    · refine Set.indicator_of_notMem (fun hcπ => hne ?_) _
      exact eq_of_mem_startEvent (Finset.mem_filter.1 hπ).1 (Finset.mem_filter.1 hπ₀).1 hcπ hcπ₀
  · push Not at hc
    rw [Finset.sum_eq_zero fun π hπ => Set.indicator_of_notMem (hc π hπ) _]
    exact bot_le

end Hierarchical

end MultipoleBKT

end
