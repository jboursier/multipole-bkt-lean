/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Pointwise
public import MultipoleBKT.UpperBound.BoundedUpper.JMeasurable

/-!
# Integrating the separated pointwise bound

The paper: Proposition 5.18. The full separation product stays beside the reduced term until
replacement-tree tails have been proved in `RouteRaw.pointwise_separated_family_bound`.
The theorem `integral_abs_separatedReducedTerm_le` integrates that bound against
the hierarchical density. The shared density lemmas give positivity of dipole
lengths almost everywhere and the explicit product cutoff measure on the box.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)
open scoped ENNReal NNReal

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Multipole Parity

variable {χ : ℂ → ℝ}

/-- Almost every dipole of `μ_{β,λ,ε₀}` lies in `Λ² ∩ {r ≤ ε₀ R̄}` and has positive length. -/
theorem ae_cutoffDipoleMeasure_pos (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ) :
    ∀ᵐ p ∂cutoffDipoleMeasure χ N p₀ β lam ε₀,
      p ∈ supportSet N p₀ β lam ε₀ ∧ 0 < ‖p.1 - p.2‖ := by
  have h0 : (volume : Measure (ℂ × ℂ)) {p | p.1 - p.2 = 0} = 0 := by
    have hm : MeasurableSet {p : ℂ × ℂ | p.1 - p.2 = 0} :=
      (measurable_fst.sub measurable_snd) (measurableSet_singleton 0)
    rw [Measure.volume_eq_prod, Measure.prod_apply hm]
    have h1 : ∀ x : ℂ, Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 - p.2 = 0} = {x} := by
      intro x
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff, sub_eq_zero]
      exact eq_comm
    simp_rw [h1, measure_singleton, lintegral_zero]
  have hvol : ∀ᵐ p ∂(volume : Measure (ℂ × ℂ)), 0 < ‖p.1 - p.2‖ := by
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) h0
    simp only [Set.mem_ofPred_eq, not_lt, norm_le_zero_iff] at hp ⊢
    exact hp
  have h2 : ∀ᵐ p ∂cutoffDipoleMeasure χ N p₀ β lam ε₀, 0 < ‖p.1 - p.2‖ := by
    unfold cutoffDipoleMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_of_ae hvol)
  filter_upwards [ae_cutoffDipoleMeasure χ N p₀ β lam ε₀, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- **The density of `μ_{β,λ,ε₀}^{⊗ U}`**, for lower integrals of nonnegative functions. -/
theorem lintegral_pi_cutoff_eq (hχ : IsMollifier χ) {N p₀ : ℕ} {β lam ε₀ : ℝ} (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (U : Finset ℕ) {f : (U → ℂ × ℂ) → ℝ} (hf : Measurable f) :
    ∫⁻ y, ENNReal.ofReal (f y) ∂Measure.pi (fun _ : U => cutoffDipoleMeasure χ N p₀ β lam ε₀) =
      ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ U.card) *
        ∫⁻ y in Set.univ.pi (fun _ : U => box N ×ˢ box N), ENNReal.ofReal (f y *
          ∏ i : U, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
            (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator 1
              ((y i).1 - (y i).2))) := by
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  have hd : Measurable fun c : U → ℂ × ℂ =>
      ∏ i, ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      (((measurable_cutoffDensity hχ hlam β _).comp (measurable_pi_apply i)).const_mul _)
  have hfm : Measurable fun y => ENNReal.ofReal (f y) := ENNReal.measurable_ofReal.comp hf
  rw [pi_cutoffDipoleMeasure_eq hχ hlam β hε₀ hN U, lintegral_withDensity_eq_lintegral_mul _ hd hfm]
  have hdens : ∀ z : ℂ, (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
      (fun w => Real.exp (β * smearedKernel χ lam w)) z =
      Real.exp (β * smearedKernel χ lam z) *
        (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator 1 z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  have hpt : ∀ y : U → ℂ × ℂ,
      (∏ i, ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((y i).1 - (y i).2))) *
        ENNReal.ofReal (f y) =
      ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ U.card) *
        ENNReal.ofReal (f y *
          ∏ i : U, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
            (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator 1
              ((y i).1 - (y i).2))) := by
    intro y
    have hnn : ∀ i : U, 0 ≤ (N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((y i).1 - (y i).2) := fun i =>
      mul_nonneg (inv_nonneg.2 hC.le) (cutoffDensity_nonneg β _ _)
    have hP0 : 0 ≤ ∏ i : U, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
        (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator 1
          ((y i).1 - (y i).2)) := by
      refine prod_nonneg fun i _ => mul_nonneg (Real.exp_pos _).le ?_
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => hnn i,
      ← ENNReal.ofReal_mul (prod_nonneg fun i _ => hnn i),
      ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hC.le) _)]
    congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    simp_rw [hdens]
    ring
  simp_rw [Pi.mul_apply, hpt]
  refine lintegral_const_mul _ ?_
  refine ENNReal.measurable_ofReal.comp (hf.mul (Finset.measurable_prod _ fun i _ => ?_))
  have hsub : Measurable fun y : U → ℂ × ℂ => (y i).1 - (y i).2 :=
    (measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd
  exact ((measurable_exp_smearedKernel hχ hlam β).comp hsub).mul
    ((measurable_const.indicator Metric.isClosed_closedBall.measurableSet).comp hsub)

open scoped Classical in
/-- The raw reduced term, with full separation, is bounded by `J`.
The paper: Proposition 5.18.
Separation is removed inside the component estimate after replacement tails. -/
theorem integral_abs_separatedReducedTerm_le (hχ : IsMollifier χ) {β : ℝ} (hβ : 0 ≤ β) (p₀ : ℕ)
    (M L : ℝ) (hM3 : 3 ≤ M) (k : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      0 < lam → 0 < ε₀ → 1 ≤ N → lam ≤ ε₀ * truncationScale p₀ β lam →
      (3 : ℝ) ^ pBeta p₀ β ≤ M → V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ k →
      ∀ E ∈ relEdgeSets₀ X, ∀ E₁ ∈ E.powerset, ∀ V₁ ∈ (X.biUnion id).powerset,
      IsParityPair X E₁ V₁ →
      ∃ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), n ≤ k ∧ (∀ l, Xs l ⊆ X) ∧
        (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) ∧
        ∃ Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id),
          IsRelTree₀ (coarsen X (univ.image Xs)) Tb ∧
          ENNReal.ofReal ((∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) *
              ∫ y, (|reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ (extendConfig (X.biUnion id) y)| *
                RouteRaw.oddSeparation M lam X E₁ (extendConfig (X.biUnion id) y))
                ∂plusModel χ N p₀ β lam M ε₀ L V Z X) ≤
            ENNReal.ofReal (K₀ * ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^
                (X.biUnion id).card) *
              ∑ Ta ∈ (univ : Finset (∀ l, SimpleGraph ((Xs l).biUnion id))).filter
                  (fun Ta => ∀ l, IsRelTree (Xs l) (Ta l)),
                jIntegral M lam ε₀ (truncationScale p₀ β lam) χ N β X Xs Ta Tb := by
  obtain ⟨K₀, hK₀, hpt⟩ := RouteRaw.pointwise_separated_family_bound hχ hβ p₀ M L hM3 k
  refine ⟨K₀, hK₀, ?_⟩
  intro N lam ε₀ V Z hlam hε₀ hN hlamh hMp hVZ X hX hk E hE E₁ hE₁ V₁ hV₁ hpar
  obtain ⟨n, Xs, hnk, hXs, hdisj, Tb, hTb, hbound⟩ :=
    hpt lam ε₀ V Z hlam hlamh hMp hVZ X hX hk E hE E₁ hE₁ V₁ hV₁ hpar
  refine ⟨n, Xs, hnk, hXs, hdisj, Tb, hTb, ?_⟩
  set W := X.biUnion id with hW
  set R := truncationScale p₀ β lam with hR
  set μ := cutoffDipoleMeasure χ N p₀ β lam ε₀ with hμ
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  set rT := fun c => reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ c *
    RouteRaw.oddSeparation M lam X E₁ c with hrT
  have hmrT : Measurable rT := (measurable_reducedTerm hχ hlam X E E₁ V₁).mul
    (RouteRaw.measurable_oddSeparation M lam X E₁)
  have hdep : DependsOn rT (W : Set ℕ) :=
    by
    intro c c' hcc'
    dsimp only [rT]
    rw [(dependsOn_reducedTerm (mem_relEdgeSets₀.1 hE).1
      (Finset.mem_powerset.1 hE₁) (Finset.mem_powerset.1 hV₁)) hcc',
      RouteRaw.dependsOn_oddSeparation M lam X E₁ hcc']
  -- the density form
  have e1 := h.prod_mul_integral_modelHierarchical (M := M) (lam := lam) (X := X)
    (f := fun y => |rT (extendConfig W y)|)
    (continuous_abs.measurable.comp (hmrT.comp (measurable_extendConfig _)))
  set Φ : (ℕ → ℂ × ℂ) → ℝ := fun c =>
    (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) * |rT c| with hΦ
  have hΦm : Measurable Φ :=
    (Finset.measurable_prod _ fun B _ => h.measurable_blockWeightOf M lam B).mul
      (continuous_abs.measurable.comp hmrT)
  have hΦdep : DependsOn Φ (W : Set ℕ) := by
    intro c c' hcc'
    simp only [hΦ]
    rw [hdep hcc']
    congr 1
    refine Finset.prod_congr rfl fun B hB => dependsOn_blockWeightOf M lam B fun i hi =>
      hcc' i ?_
    exact Finset.mem_coe.2 (subset_biUnion_of_mem id hB (Finset.mem_coe.1 hi))
  have hΦ0 : ∀ c, 0 ≤ Φ c := fun c => mul_nonneg (prod_nonneg fun B _ =>
    blockWeightOf_nonneg M lam (fun _ => dipoleWeightZ_nonneg _) B c) (abs_nonneg _)
  have e2 : ∫ c, (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) * |rT (extendConfig W (W.restrict c))|
        ∂labelField μ = ∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ) := by
    rw [← integral_labelField_eq_pi hΦm hΦdep]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [hΦ]
    rw [apply_extendConfig_restrict hdep c]
  have hLHS : (∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) *
      ∫ y, |rT (extendConfig W y)| ∂plusModel χ N p₀ β lam M ε₀ L V Z X =
      ∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ) := e1.trans e2
  have hsepabs : ∀ c, |rT c| = |reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ c| *
      RouteRaw.oddSeparation M lam X E₁ c := fun c => by
    rw [hrT, abs_mul, abs_of_nonneg (RouteRaw.oddSeparation_nonneg M lam X E₁ c)]
  simp_rw [← hsepabs]
  rw [hLHS]
  -- the lower integral
  have hle1 : ENNReal.ofReal (∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ)) ≤
      ∫⁻ y, ENNReal.ofReal (Φ (extendConfig W y)) ∂Measure.pi (fun _ : W => μ) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hΦ0 _)
      (hΦm.comp (measurable_extendConfig _)).aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  refine hle1.trans ?_
  -- the pointwise bound, almost everywhere
  set ψ : (∀ l, SimpleGraph ((Xs l).biUnion id)) → (ℕ → ℂ × ℂ) → ℝ := fun Ta c =>
    jIntegrand M lam ε₀ R X Xs Ta Tb c *
      ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) with hψ
  set 𝒯 := (univ : Finset (∀ l, SimpleGraph ((Xs l).biUnion id))).filter
    (fun Ta => ∀ l, IsRelTree (Xs l) (Ta l)) with h𝒯
  have hψ0 : ∀ Ta c, 0 ≤ ψ Ta c := fun Ta c => mul_nonneg (jIntegrand_nonneg M lam ε₀ R X Xs Ta Tb c)
    (prod_nonneg fun S _ => by split_ifs <;> norm_num)
  have hψm : ∀ Ta, Measurable (ψ Ta) := fun Ta =>
    (measurable_jIntegrand M lam ε₀ R X Xs Ta Tb).mul (measurable_prod_connOn_indicator M lam X)
  have hae : ∀ᵐ y ∂Measure.pi (fun _ : W => μ), ENNReal.ofReal (Φ (extendConfig W y)) ≤
      ENNReal.ofReal (K₀ * ∑ Ta ∈ 𝒯, ψ Ta (extendConfig W y)) := by
    filter_upwards [ae_pi_mem (ρ := μ) (ι := W) (ae_cutoffDipoleMeasure_pos χ N p₀ β lam ε₀)]
      with y hy
    apply ENNReal.ofReal_le_ofReal
    simp only [hΦ, hsepabs]
    refine hbound (extendConfig W y) fun i hi => ?_
    have : extendConfig W y i = y ⟨i, hi⟩ := by simp [extendConfig, hi]
    rw [this]
    exact hy ⟨i, hi⟩
  refine (lintegral_mono_ae hae).trans ?_
  have hsum : ∀ y : W → ℂ × ℂ, ENNReal.ofReal (K₀ * ∑ Ta ∈ 𝒯, ψ Ta (extendConfig W y)) =
      ENNReal.ofReal K₀ * ∑ Ta ∈ 𝒯, ENNReal.ofReal (ψ Ta (extendConfig W y)) := by
    intro y
    rw [ENNReal.ofReal_mul hK₀.le, ENNReal.ofReal_sum_of_nonneg fun Ta _ => hψ0 Ta _]
  simp_rw [hsum]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum 𝒯 (f := fun Ta y => ENNReal.ofReal (ψ Ta (extendConfig W y)))
      fun Ta _ => ENNReal.measurable_ofReal.comp ((hψm Ta).comp (measurable_extendConfig _))]
  have hJ : ∀ Ta, ∫⁻ y, ENNReal.ofReal (ψ Ta (extendConfig W y)) ∂Measure.pi (fun _ : W => μ) =
      ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ W.card) *
        jIntegral M lam ε₀ R χ N β X Xs Ta Tb := by
    intro Ta
    exact lintegral_pi_cutoff_eq (p₀ := p₀) (β := β) hχ hlam hε₀ hN W
      (f := fun y => ψ Ta (extendConfig W y)) ((hψm Ta).comp (measurable_extendConfig _))
  simp_rw [hJ]
  rw [← Finset.mul_sum, ← mul_assoc, ← ENNReal.ofReal_mul hK₀.le]

end BoundedUpper

end UpperBound

end MultipoleBKT

end
