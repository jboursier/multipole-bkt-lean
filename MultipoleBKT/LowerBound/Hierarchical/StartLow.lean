/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Relabel

/-!
# Lemma 4.18

Lemma 4.18 and its proof (proof of Lemma 4.18),
in the form consumed by the proof of Proposition 4.62 (eq. (4.142)).

**Lemma 4.18** (`lemma_4_18`): let `β ≥ 0` (the paper has `β > 2`), `λ > 0` with `λ ≤ ε₀ R̄_{β,λ}`
(true for `λ` small, as (3.53) requires), `ε₀ > 0`, `N ≥ 1`, `M ≥ 1` (the paper has `M > 20`) and
`L ≥ β/64` (the constant of (3.53), `MultipoleBKT.exists_eq_b2`). For a profile
`n_1, …, n_p` and any partition `π` of `[N]` with `n_k` blocks of size `k` (`k ≤ p`) and no larger
block (eq. (4.25)),

`#{π' of profile n} · (N C_{β,λ,ε₀})^N 𝖬^-_{ε₀}(π) ∑_{n ≥ 0} (1/n!)
∑_{X₁, …, Xₙ ∈ 𝒫(π) disjoint} 𝖪^-_{ε₀}(X₁) ⋯ 𝖪^-_{ε₀}(Xₙ) ≤ ∫_{𝒜 ∩ \{σ_N = Id\}} e^{-β F_λ}`,

with `𝒜 = {𝒩_1 = n_1, …, 𝒩_p = n_p} ∩ ⋂ᵢ {|x_i - y_{σ_N(i)}| ≤ ε₀ R̄}` (eq. (4.24)) inside
`(Λ²)^N`, as in the frozen Proposition 4.62. The number of partitions of the profile is
`#{π'} = N! / (1^{n_1} (2!)^{n_2} ⋯ (p!)^{n_p} n_1! ⋯ n_p!)` (eq. (4.27)); it is stated here
as the cardinality of `profilePartitions N p n`.

* `unlinkedBondOf_comm`: the bond `e^{-β w} 𝟙_{𝒜} 𝟙_{𝓑^c} - 1` is symmetric for `w` symmetric and
  `M ≥ 1` (on `𝓑^c`, `𝒜` holds in both orders, Remark 4.6);
* `ModelHyp.clusterIntegralOf_image_perm`, `clusterIntegralOf_minus_eq_of_profile`: the cluster
  integral of Steps 4–8 depends only on the profile of `π` (relabeling, Step 1);
* `minusPartitionFunction_mul_tsum_eq`: `𝖬^-_{ε₀}(π) ∑ (1/n!) ∑ ∏ 𝖪^-_{ε₀}` is that cluster integral.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

/-! ### Symmetry of the bond -/

open scoped Classical in
/-- The bond `e^{-β w_ij} 𝟙_{𝒜_ij} 𝟙_{𝓑_ij^c} - 1` is symmetric in the two dipoles, for `w`
symmetric and `M ≥ 1`. -/
theorem unlinkedBondOf_comm {w : ℂ × ℂ → ℂ × ℂ → ℝ} (hM : 1 ≤ M) (hw : ∀ d e, w d e = w e d)
    (d e : ℂ × ℂ) : unlinkedBondOf β w M lam d e = unlinkedBondOf β w M lam e d := by
  unfold unlinkedBondOf stableWeight
  by_cases h : MultipoleLinked M lam d e
  · rw [ite_eq_left h, ite_eq_left (multipoleLinked_comm.1 h)]
  · have h' : ¬ MultipoleLinked M lam e d := fun h' => h (multipoleLinked_comm.1 h')
    rw [ite_eq_right h, ite_eq_right h', ite_eq_left (remark_4_6 hM h),
      ite_eq_left (remark_4_6 hM h'), hw]

/-! ### Relabeling the cluster integral -/

/-- **Relabeling the cluster integral** (Step 1): for a permutation `τ` increasing on each block of
`π'`, the cluster integrals of `π'` and `{τ(S) : S ∈ π'}` agree. -/
theorem ModelHyp.clusterIntegralOf_image_perm {ρ : Measure (ℂ × ℂ)} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)} (h : ModelHyp ρ β w ψ K) (hM : 1 ≤ M)
    (hw : ∀ d e, w d e = w e d) {π' : Finset (Finset ℕ)} (hπ' : IsSubpartition π')
    (τ : Equiv.Perm ℕ) (hτ : ∀ S ∈ π', StrictMonoOn τ S) :
    clusterIntegralOf ρ (blockWeightOf β w ψ M lam) (unlinkedBondOf β w M lam)
        (π'.image fun S => S.image τ) =
      clusterIntegralOf ρ (blockWeightOf β w ψ M lam) (unlinkedBondOf β w M lam) π' := by
  have := h.isProbabilityMeasure
  have hmp := measurePreserving_comp_perm (ρ := ρ) τ
  have hm := measurable_clusterWeight (h.measurable_blockWeightOf M lam)
    (h.measurable_unlinkedBondOf M lam) π'
  unfold clusterIntegralOf
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  exact (clusterWeight_comp β w ψ M lam τ hπ' hτ _ (unlinkedBondOf_comm hM hw) c).symm

/-- The cluster integral of the model `-` depends only on the profile of the partition. -/
theorem clusterIntegralOf_minus_eq_of_profile (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : 1 ≤ M)
    {p : ℕ} {n : Fin p → ℕ} {π π' : Finset (Finset ℕ)} (hπ : π ∈ profilePartitions N p n)
    (hπ' : π' ∈ profilePartitions N p n) :
    clusterIntegralOf (cutoffDipoleMeasure χ N p₀ β lam ε₀)
        (blockWeightOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
          (gaussianWeight p₀ β lam ε₀ L) M lam)
        (unlinkedBondOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) M lam) π =
      clusterIntegralOf (cutoffDipoleMeasure χ N p₀ β lam ε₀)
        (blockWeightOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
          (gaussianWeight p₀ β lam ε₀ L) M lam)
        (unlinkedBondOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) M lam)
        π' := by
  obtain ⟨τ, hτ, himg⟩ := exists_perm_of_profile hπ hπ'
  have hπs' := (mem_partitions.1 (Finset.mem_filter.1 hπ').1).1
  rw [← himg]
  exact (modelHyp_minus hχ hlam β hε₀ hN hlamR L).clusterIntegralOf_image_perm hM
    (fun d e => screenedInteraction_comm χ lam _ d e) hπs' τ hτ

/-- `𝖬^-_{ε₀}(π) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ π disjoint} ∏ₗ 𝖪^-_{ε₀}(Xₗ)` is the cluster integral
of the model `-` (Steps 4–8). -/
theorem minusPartitionFunction_mul_tsum_eq (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) {π : Finset (Finset ℕ)}
    (hπ : IsSubpartition π) :
    minusPartitionFunction χ N p₀ β lam M ε₀ L π *
        ∑' k : ℕ, 1 / (k.factorial : ℝ) *
          ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => π.powerset).filter
              (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
            ∏ i, minusActivity χ N p₀ β lam M ε₀ L (Xs i) =
      clusterIntegralOf (cutoffDipoleMeasure χ N p₀ β lam ε₀)
        (blockWeightOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
          (gaussianWeight p₀ β lam ε₀ L) M lam)
        (unlinkedBondOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) M lam) π := by
  rw [(modelHyp_minus hχ hlam β hε₀ hN hlamR L).clusterIntegralOf_eq_tsum (M := M) (lam := lam) hπ]
  unfold minusPartitionFunction minusActivity
  rfl

/-! ### Lemma 4.18 -/

/-- **Lemma 4.18** (Lemma 4.18; eq. (4.142)): for every
partition `π` of `[N]` with `n_k` blocks of size `k` (`k ≤ p`) and no larger block,
`#{π'} (N C_{β,λ,ε₀})^N 𝖬^-_{ε₀}(π) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) disjoint}
𝖪^-_{ε₀}(X₁) ⋯ 𝖪^-_{ε₀}(Xₙ) ≤ ∫_{𝒜 ∩ \{σ_N = Id\}} e^{-β F_λ}`, where `#{π'}` is the number of
partitions of the profile (`N!/(1^{n_1} (2!)^{n_2} ⋯ (p!)^{n_p} n_1! ⋯ n_p!)`, eq. (4.27)) and
`𝒜 = {𝒩_1 = n_1, …, 𝒩_p = n_p} ∩ ⋂ᵢ {|x_i - y_{σ_N(i)}| ≤ ε₀ R̄}` (eq. (4.24)), in `(Λ²)^N`. -/
theorem lemma_4_18 (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) (hL : β / 64 ≤ L) (hM : 1 ≤ M)
    (p : ℕ) (n : Fin p → ℕ) {π : Finset (Finset ℕ)} (hπ : π ∈ profilePartitions N p n) :
    ENNReal.ofReal ((profilePartitions N p n).card *
        (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
          minusPartitionFunction χ N p₀ β lam M ε₀ L π *
          ∑' k : ℕ, 1 / (k.factorial : ℝ) *
            ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => π.powerset).filter
                (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
              ∏ i, minusActivity χ N p₀ β lam M ε₀ L (Xs i))) ≤
      ∫⁻ c in ((Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
          {c | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
            ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
              ε₀ * truncationScale p₀ β lam}) ∩ {c | stableMatching c = Equiv.refl _},
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  refine le_trans (le_of_eq ?_) (lemma_4_18_sum (M := M) (L := L) hχ hlam hβ hε₀ hN hlamR hL p n)
  have hterm : ∀ π' ∈ profilePartitions N p n,
      ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
          minusPartitionFunction χ N p₀ β lam M ε₀ L π' *
          ∑' k : ℕ, 1 / (k.factorial : ℝ) *
            ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => π'.powerset).filter
                (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
              ∏ i, minusActivity χ N p₀ β lam M ε₀ L (Xs i) =
        ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
          minusPartitionFunction χ N p₀ β lam M ε₀ L π *
          ∑' k : ℕ, 1 / (k.factorial : ℝ) *
            ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => π.powerset).filter
                (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
              ∏ i, minusActivity χ N p₀ β lam M ε₀ L (Xs i) := by
    intro π' hπ'
    have hπs := (mem_partitions.1 (Finset.mem_filter.1 hπ).1).1
    have hπs' := (mem_partitions.1 (Finset.mem_filter.1 hπ').1).1
    rw [mul_assoc, mul_assoc, minusPartitionFunction_mul_tsum_eq hχ hlam hε₀ hN hlamR hπs',
      minusPartitionFunction_mul_tsum_eq hχ hlam hε₀ hN hlamR hπs,
      clusterIntegralOf_minus_eq_of_profile hχ hlam hε₀ hN hlamR hM hπ' hπ]
  rw [Finset.sum_congr rfl fun π' hπ' => by rw [hterm π' hπ'], Finset.sum_const, nsmul_eq_mul]
  set t := ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
    minusPartitionFunction χ N p₀ β lam M ε₀ L π *
    ∑' k : ℕ, 1 / (k.factorial : ℝ) *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => π.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∏ i, minusActivity χ N p₀ β lam M ε₀ L (Xs i)
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end Hierarchical

end MultipoleBKT

end
