/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.StartLowEnergy

/-!
# Lemma 4.18, Steps 2–8 for a fixed partition

The proof of Lemma 4.18,
Steps 2–8, for a fixed partition `π` of `[N]` (labels `{0, …, N - 1}`).

* `startEvent N p₀ β λ M ε₀ π`: the configurations of `(Λ²)^N` with all dipoles of length at most
  `ε₀ R̄`, all `𝒜_ij` (`i < j`, i.e. `σ_N = Id` by Lemma 4.3), every block `S ∈ π` connected by the
  multipole relation (`𝓑_S`) and no two dipoles of distinct blocks linked (`𝓑_ij^c`): the event
  `{Π_mult = π, σ_N = Id} ∩ {|x_i - y_i| ≤ ε₀ R̄ ∀ i}` written as in eq. (4.30).
* `clusterWeight_eq_prod`: the integrand of the cluster expansion of the model `-` is
  `𝟙_{𝓑_S}`'s times `𝟙_{𝓑_ij^c}`'s times `∏_{i<j} e^{-β ṽ_ij} 𝟙_{𝒜_ij} ∏ᵢ e^{-L r_i²/(ε₀ R̄)²}`.
* `startLowerDensity_le` (Steps 2–3): pointwise on `(Λ²)^N`,
  `∏ᵢ dμ_{β,λ,ε₀}/dx dy · (N C_{β,λ,ε₀})^N · (cluster integrand) ≤ 𝟙_{startEvent} e^{-β F_λ}`.
* `lintegral_startLowerDensity` (Steps 4–8): the integral of the left side is
  `(N C_{β,λ,ε₀})^N 𝖬^-_{ε₀}(π) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ π disjoint} ∏ₗ 𝖪^-_{ε₀}(Xₗ)`.
* `start_low_partition`: hence
  `(N C_{β,λ,ε₀})^N 𝖬^-_{ε₀}(π) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ π disjoint} ∏ₗ 𝖪^-_{ε₀}(Xₗ)
  ≤ ∫_{startEvent} e^{-β F_λ}`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

/-- The event of Steps 1–2 of Lemma 4.18 (eq. (4.30), with the short-dipole condition):
the configurations of `(Λ²)^N` whose dipoles have length at most `ε₀ R̄`, with all `𝒜_ij`
(`i < j`), every block of `π` connected by the multipole relation and no two dipoles of distinct
blocks linked. -/
def startEvent (N p₀ : ℕ) (β lam M ε₀ : ℝ) (π : Finset (Finset ℕ)) : Set (Fin N → ℂ × ℂ) :=
  {c | (∀ i, c i ∈ box N ×ˢ box N) ∧
    (∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * truncationScale p₀ β lam) ∧
    (∀ i j : Fin N, i < j → IsStableDipolePair (c i) (c j)) ∧
    (∀ S ∈ π, ConnOn S (linkedPairs M lam (finToLabels c) S)) ∧
    ∀ p ∈ interPairs π, ¬ MultipoleLinked M lam (finToLabels c p.1) (finToLabels c p.2)}

/-! ### The integrand of the cluster expansion -/

section Weight

open scoped Classical

variable (β M lam) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ)

/-- The pairs `i < j` of `[N]` are those inside the blocks of a partition `π` and those between
two blocks. -/
theorem prod_pairsOn_eq_prod_intra_mul_inter {π : Finset (Finset ℕ)} {U : Finset ℕ}
    (hπ : π ∈ partitions U) (f : ℕ × ℕ → ℝ) :
    ∏ p ∈ pairsOn U, f p = (∏ S ∈ π, ∏ p ∈ pairsOn S, f p) * ∏ p ∈ interPairs π, f p := by
  have hπs := (mem_partitions.1 hπ).1
  have hU : π.biUnion id = U := (mem_partitions.1 hπ).2
  have hpd : (π : Set (Finset ℕ)).PairwiseDisjoint pairsOn := fun S hS T hT hST =>
    disjoint_pairsOn_pairsOn (hπs.2 hS hT hST)
  rw [← Finset.prod_biUnion hpd, show π.biUnion pairsOn = intraPairs π from rfl,
    ← Finset.prod_union disjoint_interPairs_intraPairs.symm]
  congr 1
  rw [interPairs, hU, Finset.union_sdiff_of_subset]
  have := intraPairs_subset_pairsOn (X := π)
  rwa [hU] at this

/-- The integrand of the cluster expansion of a model over a partition `π` of `U`:
`(∏_{S ∈ π} 𝟙_{𝓑_S}) (∏_{ij ∈ ℰ^inter(π)} 𝟙_{𝓑_ij^c}) ∏_{i<j ∈ U} e^{-β w_ij} 𝟙_{𝒜_ij}
∏_{i ∈ U} ψ(c_i)`. -/
theorem clusterWeight_eq_prod {π : Finset (Finset ℕ)} {U : Finset ℕ} (hπ : π ∈ partitions U)
    (c : ℕ → ℂ × ℂ) :
    clusterWeight (blockWeightOf β w ψ M lam) (unlinkedBondOf β w M lam) π c =
      (∏ S ∈ π, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
        (∏ p ∈ interPairs π, if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) *
        (∏ p ∈ pairsOn U, stableWeight β w (c p.1) (c p.2)) * ∏ n ∈ U, ψ (c n) := by
  have hπs := (mem_partitions.1 hπ).1
  have hU : π.biUnion id = U := (mem_partitions.1 hπ).2
  unfold clusterWeight blockWeightOf unlinkedBondOf
  simp only [add_sub_cancel, Finset.prod_mul_distrib]
  have hinter : ∀ p ∈ interPairs π,
      (if MultipoleLinked M lam (c p.1) (c p.2) then 0 else stableWeight β w (c p.1) (c p.2)) =
        (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) *
          stableWeight β w (c p.1) (c p.2) := fun p _ => by
    split_ifs <;> ring
  rw [Finset.prod_congr rfl hinter, Finset.prod_mul_distrib,
    prod_pairsOn_eq_prod_intra_mul_inter hπ, ← hU,
    Finset.prod_biUnion (f := fun n => ψ (c n)) (by exact hπs.2)]
  simp only [id]
  ring

end Weight

/-! ### Steps 2–3: the pointwise lower bound -/

section Pointwise

open scoped Classical

/-- The density `dμ_{β,λ,ε₀}/dx dy` of the truncated dipole measure. -/
noncomputable def cutoffDensity (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ) (d : ℂ × ℂ) : ℝ :=
  (N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
    (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
      (fun w => Real.exp (β * smearedKernel χ lam w)) (d.1 - d.2)

theorem cutoffDensity_apply_nonneg (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
    (d : ℂ × ℂ) : 0 ≤ cutoffDensity χ N p₀ β lam ε₀ d :=
  mul_nonneg (inv_nonneg.2 (natCast_mul_cutoffDipoleNormalization_pos hχ hlam β hε₀ hN).le)
    (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)

/-- The integrand of Steps 4–8: `(N C)^N` times the cluster integrand of the model `-`. -/
noncomputable def startIntegrand (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ L : ℝ)
    (π : Finset (Finset ℕ)) (c : Fin N → ℂ × ℂ) : ℝ :=
  ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
    clusterWeight (blockWeightOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
        (gaussianWeight p₀ β lam ε₀ L) M lam)
      (unlinkedBondOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) M lam) π
      (finToLabels c)

/-- **Steps 2–3 of Lemma 4.18**, pointwise: on `(Λ²)^N`,
`∏ᵢ dμ_{β,λ,ε₀}/dx dy (c_i) · (N C)^N · (cluster integrand) ≤ 𝟙_{startEvent} e^{-β F_λ}`. -/
theorem startLowerDensity_le (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hL : β / 64 ≤ L) {π : Finset (Finset ℕ)} (hπ : π ∈ partitions (Finset.range N))
    (c : Fin N → ℂ × ℂ) (hc : ∀ i, c i ∈ box N ×ˢ box N) :
    (∏ i, cutoffDensity χ N p₀ β lam ε₀ (c i)) * startIntegrand χ N p₀ β lam M ε₀ L π c ≤
      (startEvent N p₀ β lam M ε₀ π).indicator (fun c => Real.exp (-β * energy χ lam c)) c := by
  set R := truncationScale p₀ β lam with hR
  set NC := (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ with hNC
  have hNC0 : 0 < NC := natCast_mul_cutoffDipoleNormalization_pos hχ hlam β hε₀ hN
  have hRHS : 0 ≤ (startEvent N p₀ β lam M ε₀ π).indicator
      (fun c => Real.exp (-β * energy χ lam c)) c :=
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  by_cases hr : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R
  swap
  · push Not at hr
    obtain ⟨i, hi⟩ := hr
    have h0 : cutoffDensity χ N p₀ β lam ε₀ (c i) = 0 := by
      unfold cutoffDensity
      rw [Set.indicator_of_notMem (by simpa [dist_eq_norm] using hi.not_ge), mul_zero]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]
    exact hRHS
  -- all dipoles are short
  have hD : ∀ i, cutoffDensity χ N p₀ β lam ε₀ (c i) =
      NC⁻¹ * Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) := fun i => by
    unfold cutoffDensity
    rw [Set.indicator_of_mem (by simpa [dist_eq_norm] using hr i)]
  have hprodD : (∏ i, cutoffDensity χ N p₀ β lam ε₀ (c i)) * NC ^ N =
      ∏ n ∈ Finset.range N, Real.exp (β * smearedKernel χ lam
        ((finToLabels c n).1 - (finToLabels c n).2)) := by
    simp_rw [hD, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [mul_comm, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hNC0.ne', one_pow, one_mul]
    rw [← Fin.prod_univ_eq_prod_range (fun n => Real.exp (β * smearedKernel χ lam
      ((finToLabels c n).1 - (finToLabels c n).2))) N]
    simp only [finToLabels_apply]
  unfold startIntegrand
  rw [← hNC, ← mul_assoc, hprodD, clusterWeight_eq_prod (β := β) (M := M) (lam := lam) _ _ hπ]
  by_cases hE : c ∈ startEvent N p₀ β lam M ε₀ π
  · rw [Set.indicator_of_mem hE]
    obtain ⟨-, hr', hA, hconn, hcross⟩ := hE
    rw [Finset.prod_eq_one fun S hS => ite_eq_left (hconn S hS),
      Finset.prod_eq_one fun p hp => ite_eq_right (hcross p hp), one_mul, one_mul]
    have hsw : ∀ p ∈ pairsOn (Finset.range N),
        stableWeight β (upperBoundInteraction χ lam ε₀ R) (finToLabels c p.1)
          (finToLabels c p.2) =
        Real.exp (-β * upperBoundInteraction χ lam ε₀ R (finToLabels c p.1)
          (finToLabels c p.2)) := by
      intro p hp
      obtain ⟨h1, h2, h12⟩ := mem_pairsOn.1 hp
      have h1' : p.1 < N := Finset.mem_range.1 h1
      have h2' : p.2 < N := Finset.mem_range.1 h2
      have hst := hA ⟨p.1, h1'⟩ ⟨p.2, h2'⟩ (Fin.mk_lt_mk.2 h12)
      unfold stableWeight
      rw [ite_eq_left (by simpa [finToLabels, h1', h2'] using hst)]
    rw [Finset.prod_congr rfl hsw]
    have := exp_neg_mul_energy_ge (p₀ := p₀) (ε₀ := ε₀) hχ c hlam hβ hlamR hL hr'
    rw [Finset.prod_mul_distrib] at this
    calc (∏ n ∈ Finset.range N, Real.exp (β * smearedKernel χ lam
            ((finToLabels c n).1 - (finToLabels c n).2))) *
          ((∏ p ∈ pairsOn (Finset.range N), Real.exp (-β * upperBoundInteraction χ lam ε₀ R
            (finToLabels c p.1) (finToLabels c p.2))) *
            ∏ n ∈ Finset.range N, gaussianWeight p₀ β lam ε₀ L (finToLabels c n))
        = (∏ n ∈ Finset.range N, Real.exp (β * smearedKernel χ lam
            ((finToLabels c n).1 - (finToLabels c n).2))) *
          (∏ n ∈ Finset.range N, gaussianWeight p₀ β lam ε₀ L (finToLabels c n)) *
          ∏ p ∈ pairsOn (Finset.range N), Real.exp (-β * upperBoundInteraction χ lam ε₀ R
            (finToLabels c p.1) (finToLabels c p.2)) := by ring
      _ ≤ Real.exp (-β * energy χ lam c) := this
  · rw [Set.indicator_of_notMem hE]
    have hzero : ((∏ S ∈ π, if ConnOn S (linkedPairs M lam (finToLabels c) S) then (1 : ℝ)
          else 0) *
        (∏ p ∈ interPairs π, if MultipoleLinked M lam (finToLabels c p.1) (finToLabels c p.2)
          then (0 : ℝ) else 1) *
        (∏ p ∈ pairsOn (Finset.range N), stableWeight β (upperBoundInteraction χ lam ε₀ R)
          (finToLabels c p.1) (finToLabels c p.2))) = 0 := by
      simp only [startEvent, Set.mem_ofPred_eq, not_and] at hE
      by_cases hA : ∀ i j : Fin N, i < j → IsStableDipolePair (c i) (c j)
      · by_cases hconn : ∀ S ∈ π, ConnOn S (linkedPairs M lam (finToLabels c) S)
        · have hcross := hE hc hr hA hconn
          push Not at hcross
          obtain ⟨p, hp, hlink⟩ := hcross
          rw [Finset.prod_eq_zero hp (by simp [hlink]), mul_zero, zero_mul]
        · push Not at hconn
          obtain ⟨S, hS, hnc⟩ := hconn
          rw [Finset.prod_eq_zero hS (by simp [hnc]), zero_mul, zero_mul]
      · push Not at hA
        obtain ⟨i, j, hij, hnst⟩ := hA
        have hp : ((i : ℕ), (j : ℕ)) ∈ pairsOn (Finset.range N) :=
          mem_pairsOn.2 ⟨Finset.mem_range.2 i.2, Finset.mem_range.2 j.2, hij⟩
        rw [Finset.prod_eq_zero hp (by
          unfold stableWeight
          rw [ite_eq_right (by simpa [finToLabels_apply] using hnst)]), mul_zero]
    rw [hzero, zero_mul, mul_zero]

end Pointwise

/-! ### Steps 4–8: integration -/

section Integration

open scoped Classical

theorem measurable_cutoffDensity_apply (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Measurable (cutoffDensity χ N p₀ β lam ε₀) :=
  (measurable_cutoffDensity hχ hlam β _).const_mul _

theorem clusterWeight_minus_nonneg {π : Finset (Finset ℕ)} {U : Finset ℕ} (hπ : π ∈ partitions U)
    (c : ℕ → ℂ × ℂ) :
    0 ≤ clusterWeight (blockWeightOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
        (gaussianWeight p₀ β lam ε₀ L) M lam)
      (unlinkedBondOf β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) M lam) π c := by
  rw [clusterWeight_eq_prod (β := β) (M := M) (lam := lam) _ _ hπ]
  refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
  · exact Finset.prod_nonneg fun S _ => by split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun p _ => by split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun p _ => stableWeight_nonneg _ _ _ _
  · exact Finset.prod_nonneg fun n _ => (Real.exp_pos _).le

/-- **Steps 4–8 of Lemma 4.18**: the integral over `(Λ²)^N` of
`∏ᵢ dμ_{β,λ,ε₀}/dx dy (c_i) · (N C)^N · (cluster integrand)` is
`(N C_{β,λ,ε₀})^N 𝖬^-_{ε₀}(π) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ π disjoint} ∏ₗ 𝖪^-_{ε₀}(Xₗ)`. -/
theorem lintegral_startLowerDensity (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) {π : Finset (Finset ℕ)}
    (hπ : π ∈ partitions (Finset.range N)) :
    ∫⁻ c, (Set.univ.pi fun _ : Fin N => box N ×ˢ box N).indicator (fun c => ENNReal.ofReal
        ((∏ i, cutoffDensity χ N p₀ β lam ε₀ (c i)) * startIntegrand χ N p₀ β lam M ε₀ L π c)) c =
      ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
        minusPartitionFunction χ N p₀ β lam M ε₀ L π *
        ∑' n : ℕ, 1 / (n.factorial : ℝ) *
          ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
              (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
            ∏ i, minusActivity χ N p₀ β lam M ε₀ L (Xs i)) := by
  have h := modelHyp_minus hχ hlam β hε₀ hN hlamR L
  have := h.isProbabilityMeasure
  have hπs := (mem_partitions.1 hπ).1
  have hU : π.biUnion id = Finset.range N := (mem_partitions.1 hπ).2
  set R := truncationScale p₀ β lam with hR
  set w := upperBoundInteraction χ lam ε₀ R with hw
  set ψ := gaussianWeight p₀ β lam ε₀ L with hψ
  set cw : (ℕ → ℂ × ℂ) → ℝ :=
    clusterWeight (blockWeightOf β w ψ M lam) (unlinkedBondOf β w M lam) π with hcw
  have hcwm : Measurable cw :=
    measurable_clusterWeight (h.measurable_blockWeightOf M lam) (h.measurable_unlinkedBondOf M lam) π
  have hcwd : DependsOn cw (Finset.range N : Set ℕ) := by
    have := dependsOn_clusterWeight (φ := unlinkedBondOf β w M lam)
      (dependsOn_blockWeightOf (β := β) (w := w) (ψ := ψ) M lam) π
    rwa [hU] at this
  have hcwb : BoundedOn (cutoffSet N p₀ β lam ε₀) cw :=
    boundedOn_clusterWeight (h.boundedOn_blockWeightOf M lam) (h.boundedOn_unlinkedBondOf M lam) π
  have hcw0 : ∀ c, 0 ≤ cw c := clusterWeight_minus_nonneg hπ
  have hmp := measurePreserving_finRestrict (ρ := cutoffDipoleMeasure χ N p₀ β lam ε₀) N
  -- integrability of the integrand against `μ_{β,λ,ε₀}^{⊗ N}`
  have hint : Integrable (fun c : Fin N → ℂ × ℂ => cw (finToLabels c))
      (Measure.pi fun _ : Fin N => cutoffDipoleMeasure χ N p₀ β lam ε₀) := by
    rw [← hmp.map_eq]
    refine (integrable_map_measure (g := fun c => cw (finToLabels c))
      (hcwm.comp (measurable_finToLabels N)).aestronglyMeasurable
      hmp.measurable.aemeasurable).2 ?_
    refine (integrable_of_boundedOn h.ae_mem hcwm hcwb).congr
      (Filter.Eventually.of_forall fun c => ?_)
    exact (finToLabels_restrict hcwd c).symm
  have hdens : Measurable fun c : Fin N → ℂ × ℂ =>
      ∏ i, ENNReal.ofReal (cutoffDensity χ N p₀ β lam ε₀ (c i)) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      ((measurable_cutoffDensity_apply hχ hlam).comp (measurable_pi_apply i))
  have hI : Measurable fun c : Fin N → ℂ × ℂ =>
      ENNReal.ofReal (startIntegrand χ N p₀ β lam M ε₀ L π c) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hcwm.comp (measurable_finToLabels N)))
  rw [lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_box_prod N)]
  have hpt : ∀ c : Fin N → ℂ × ℂ, ENNReal.ofReal
      ((∏ i, cutoffDensity χ N p₀ β lam ε₀ (c i)) * startIntegrand χ N p₀ β lam M ε₀ L π c) =
      (∏ i, ENNReal.ofReal (cutoffDensity χ N p₀ β lam ε₀ (c i))) *
        ENNReal.ofReal (startIntegrand χ N p₀ β lam M ε₀ L π c) := by
    intro c
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ =>
      cutoffDensity_apply_nonneg hχ hlam hε₀ hN _), ENNReal.ofReal_prod_of_nonneg fun i _ =>
      cutoffDensity_apply_nonneg hχ hlam hε₀ hN _]
  simp_rw [hpt]
  have hwd := lintegral_withDensity_eq_lintegral_mul
    (volume.restrict (Set.univ.pi fun _ : Fin N => box N ×ˢ box N)) hdens hI
  simp only [Pi.mul_apply] at hwd
  rw [← hwd]
  have hpi := pi_cutoffDipoleMeasure_eq (p₀ := p₀) hχ hlam β hε₀ hN (Fin N)
  rw [show (volume.restrict (Set.univ.pi fun _ : Fin N => box N ×ˢ box N)).withDensity
      (fun c => ∏ i, ENNReal.ofReal (cutoffDensity χ N p₀ β lam ε₀ (c i))) =
      Measure.pi fun _ : Fin N => cutoffDipoleMeasure χ N p₀ β lam ε₀ from hpi.symm]
  simp only [startIntegrand, ← hR, ← hw, ← hψ, ← hcw]
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (Filter.Eventually.of_forall fun c => mul_nonneg (pow_nonneg
      (natCast_mul_cutoffDipoleNormalization_pos hχ hlam β hε₀ hN).le _) (hcw0 _))]
  congr 1
  rw [integral_const_mul, integral_pi_fin_eq_integral_labelField hcwm hcwd]
  -- Steps 7–8: the directly grouped expansion and its component normalizations.
  have key := h.clusterIntegralOf_eq_tsum (M := M) (lam := lam) hπs
  unfold clusterIntegralOf at key
  rw [key]
  unfold minusPartitionFunction minusActivity
  ring

/-- **Lemma 4.18 for a fixed partition `π`** (Steps 2–8, proof of Lemma 4.18): for `λ > 0`,
`λ ≤ ε₀ R̄`, `β ≥ 0`, `L ≥ β/64`, `N ≥ 1` and a partition `π` of `[N]`,
`(N C_{β,λ,ε₀})^N 𝖬^-_{ε₀}(π) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ π disjoint} ∏ₗ 𝖪^-_{ε₀}(Xₗ)
≤ ∫_{\{Π_mult = π, σ_N = Id, |x_i - y_i| ≤ ε₀ R̄\}} e^{-β F_λ}`. -/
theorem start_low_partition (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) (hL : β / 64 ≤ L)
    {π : Finset (Finset ℕ)} (hπ : π ∈ partitions (Finset.range N)) :
    ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
        minusPartitionFunction χ N p₀ β lam M ε₀ L π *
        ∑' n : ℕ, 1 / (n.factorial : ℝ) *
          ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
              (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
            ∏ i, minusActivity χ N p₀ β lam M ε₀ L (Xs i)) ≤
      ∫⁻ c, (startEvent N p₀ β lam M ε₀ π).indicator
        (fun c => ENNReal.ofReal (Real.exp (-β * energy χ lam c))) c := by
  rw [← lintegral_startLowerDensity (M := M) (L := L) hχ hlam hε₀ hN hlamR hπ]
  refine lintegral_mono fun c => ?_
  by_cases hc : c ∈ Set.univ.pi fun _ : Fin N => box N ×ˢ box N
  · rw [Set.indicator_of_mem hc]
    have := startLowerDensity_le (M := M) hχ hlam hβ hε₀ hN hlamR hL hπ c
      (fun i => hc i (Set.mem_univ i))
    refine (ENNReal.ofReal_le_ofReal this).trans ?_
    by_cases hE : c ∈ startEvent N p₀ β lam M ε₀ π
    · rw [Set.indicator_of_mem hE, Set.indicator_of_mem hE]
    · rw [Set.indicator_of_notMem hE, Set.indicator_of_notMem hE, ENNReal.ofReal_zero]
  · rw [Set.indicator_of_notMem hc]
    exact bot_le

end Integration

end Hierarchical

end MultipoleBKT

end
