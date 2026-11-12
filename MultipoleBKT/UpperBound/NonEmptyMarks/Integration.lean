/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.NonEmptyMarks.PointwiseMarked
public import MultipoleBKT.UpperBound.NonEmptyMarks.Parity
public import MultipoleBKT.UpperBound.BoundedUpper.Integration
public import MultipoleBKT.UpperBound.BoundedUpper.LemmaA6Bridge
public import MultipoleBKT.UpperBound.BoundedUpper.JMeasurable

/-!
# Bounding a marked integral by `J_ext`

The paper: (5.106), and (A.18), (A.20) in Lemma A.4.

`integral_abs_markedTerm_le` writes the hierarchical expectation in
density form and integrates `pointwise_marked`. The input raw groups
are disjoint, so their separation factors remain available until the
replacement-family estimates. The output is a finite sum of `J_ext`
integrals with the block-connectivity indicators and dipole densities.

`jExtIntegral_le_integralJext` converts graph trees to edge sets and
matches the radius factors with the largest-block choices of
`SmallIntegral.integralJext`. The next step, in `Statement`, invokes
the logarithmic `lemma_A6_J2`.
-/

@[expose] public section

open MeasureTheory Finset SimpleGraph
open TwoComponentCoulomb (box)
open scoped ENNReal NNReal

namespace MultipoleBKT

namespace UpperBound

namespace NonEmptyMarks

open Hierarchical Multipole Parity Peeling Quadratic SetPartition BoundedUpper

variable {χ : ℂ → ℝ}

/-! ### The integrand of `J_ext` -/

section J

open scoped Classical in
/-- The integrand of `J_ext` (eq. (A.18)) on `(Λ²)^{V_X}`, in the form of the proof of
Proposition 5.18: `extGain · jIntegrandNT · ∏_{S ∈ X} 𝟙_{𝓑_S} · ∏_{i ∈ V_X} e^{β g_λ} 𝟙_{r_i ≤ ε₀ R̄}`. -/
noncomputable def jExtFullIntegrand (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ) {N : ℕ}
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id))
    (y : X.biUnion id → ℂ × ℂ) : ℝ :=
  (SmallIntegral.extGain p₀ β lam ε₀ V Z y *
      jIntegrandNT M lam ε₀ (truncationScale p₀ β lam) X Xs Ta Tb (extendConfig (X.biUnion id) y)) *
    (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
    ∏ i : X.biUnion id, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
      (Metric.closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator 1 ((y i).1 - (y i).2))

/-- **The integral `J_ext`** (eq. (A.18)) in the form of the proof of Proposition 5.18. -/
noncomputable def jExtIntegral (χ : ℂ → ℝ) (p₀ N : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) : ℝ≥0∞ :=
  ∫⁻ y in Set.univ.pi (fun _ : X.biUnion id => box N ×ˢ box N),
    ENNReal.ofReal (jExtFullIntegrand χ p₀ β lam M ε₀ V Z X Xs Ta Tb y)

/-- A fold of `max` from `0` of continuous functions is continuous. -/
theorem continuous_fold_max {W : Type*} {α : Type*} [TopologicalSpace α] (s : Finset W)
    (f : W → α → ℝ) (hf : ∀ i, Continuous (f i)) :
    Continuous fun z => s.fold max 0 fun i => f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.fold_empty]; exact continuous_const
  | insert j s hj ih =>
    simp only [Finset.fold_insert hj]
    exact (hf j).max ih

/-- A fold of `min` of continuous functions is continuous. -/
theorem continuous_fold_min {W : Type*} {α : Type*} [TopologicalSpace α] (s : Finset W) (b : ℝ)
    (f : W → α → ℝ) (hf : ∀ i, Continuous (f i)) :
    Continuous fun z => s.fold min b fun i => f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.fold_empty]; exact continuous_const
  | insert j s hj ih =>
    simp only [Finset.fold_insert hj]
    exact (hf j).min ih

theorem measurable_extGain {W : Type*} [Fintype W] {N p₀ : ℕ} {β lam ε₀ : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ} :
    Measurable (SmallIntegral.extGain (W := W) p₀ β lam ε₀ V Z) := by
  unfold SmallIntegral.extGain SmallIntegral.minBadDist
  have h1 : Continuous fun z : W → ℂ × ℂ => univ.fold max 0 fun i => dipoleLength (z i) :=
    continuous_fold_max _ (fun (i : W) (z : W → ℂ × ℂ) => dipoleLength (z i)) fun i => by
      unfold dipoleLength; fun_prop
  have h2 : Continuous fun z : W → ℂ × ℂ => univ.fold min (4 * (ε₀ * truncationScale p₀ β lam))
      fun i => badDistZ p₀ β lam ε₀ V Z (z i) :=
    continuous_fold_min _ _ (fun (i : W) (z : W → ℂ × ℂ) => badDistZ p₀ β lam ε₀ V Z (z i))
      fun i => (SmallIntegral.continuous_badDistZ' p₀ β lam ε₀ V Z).comp (continuous_apply i)
  exact ((h1.measurable.div h2.measurable).min measurable_const).pow_const 2

theorem measurable_jIntegrandNT (M lam ε₀ R : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) :
    Measurable (jIntegrandNT M lam ε₀ R X Xs Ta Tb) := by
  classical
  unfold jIntegrandNT
  refine ((Finset.measurable_prod _ fun l _ => measurable_radialExceptMax _).mul
    (Finset.measurable_prod _ fun l _ => Finset.measurable_prod _ fun e _ =>
      measurable_keptLift M lam ε₀ R e)).mul
    (Finset.measurable_prod _ fun e _ => measurable_absEvenLift M lam ε₀ R e)

theorem measurable_extGain_restrict {N p₀ : ℕ} {β lam ε₀ : ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} (X : Finset (Finset ℕ)) :
    Measurable fun c : ℕ → ℂ × ℂ =>
      SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) :=
  measurable_extGain.comp (measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℕ))

end J

/-! ### One marked term is bounded by `J_ext` -/

section Integration

open scoped Classical in
/-- **One marked term is bounded by `J_ext`** (the display before (A.20) in the proof of the
claim (5.106)), as an inequality in `[0, ∞]`. -/
theorem integral_abs_markedTerm_le (hχ : IsMollifier χ) {β : ℝ} (hβ : 0 ≤ β) (p₀ : ℕ)
    (M L : ℝ) (hM3 : 3 ≤ M) (k : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      0 < lam → 0 < ε₀ → 1 ≤ N → lam ≤ ε₀ * truncationScale p₀ β lam →
      (3 : ℝ) ^ pBeta p₀ β ≤ M → V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ k →
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
      ∀ U ⊆ X.biUnion id, U.Nonempty → ∀ E₁ ∈ (univ.biUnion Es).powerset, ∀ U₁ ∈ U.powerset,
      IsParityPair X E₁ U₁ →
      ∃ (m : ℕ) (Ys : Fin m → Finset (Finset ℕ)), m ≤ k ∧ (∀ l, Ys l ⊆ X) ∧
        (∀ l l', l ≠ l' → Disjoint (Ys l) (Ys l')) ∧
        ∃ Tb : SimpleGraph ((coarsen X (univ.image Ys)).biUnion id),
          IsRelTree₀ (coarsen X (univ.image Ys)) Tb ∧
          ENNReal.ofReal ((∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) *
              ∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁
                (extendConfig (X.biUnion id) y)| ∂plusModel χ N p₀ β lam M ε₀ L V Z X) ≤
            ENNReal.ofReal (K₀ * ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^
                (X.biUnion id).card) *
              ∑ Ta ∈ (univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter
                  (fun Ta => ∀ l, IsRelTree (Ys l) (Ta l)),
                jExtIntegral χ p₀ N β lam M ε₀ V Z X Ys Ta Tb := by
  obtain ⟨K₀, hK₀, hpt⟩ := pointwise_marked hχ hβ p₀ M L hM3 k
  refine ⟨K₀, hK₀, ?_⟩
  intro N lam ε₀ V Z hlam hε₀ hN hlamh hMp hVZ X hX hk n Xs hXs hXd Es hEs F hF U hU hUne E₁ hE₁ U₁
    hU₁ hpar
  obtain ⟨m, Ys, hm, hYs, hYd, Tb, hTb, hbound⟩ :=
    hpt lam ε₀ V Z hlam hlamh hMp hVZ X hX hk Xs hXs hXd Es hEs F hF U hU hUne E₁ hE₁ U₁ hU₁ hpar
  refine ⟨m, Ys, hm, hYs, hYd, Tb, hTb, ?_⟩
  set W := X.biUnion id with hW
  set R := truncationScale p₀ β lam with hR
  set μ := cutoffDipoleMeasure χ N p₀ β lam ε₀ with hμ
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  have hEs' : ∀ l, Es l ∈ relEdgeSets (Xs l) := Fintype.mem_piFinset.1 hEs
  have hEsi : ∀ l, Es l ⊆ interPairs (Xs l) := fun l => (mem_relEdgeSets.1 (hEs' l)).1
  have hFV : ∀ p ∈ F, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := by
    intro p hp
    have hpE := (mem_relEdgeSets₀.1 (union_mem_relEdgeSets₀ hX hXs hEs' hF)).1
      (Finset.mem_union_right _ hp)
    exact ⟨(mem_pairsOn.1 (interPairs_subset_pairsOn hpE)).1,
      (mem_pairsOn.1 (interPairs_subset_pairsOn hpE)).2.1⟩
  set mT := markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ with hmT
  have hmmT : Measurable mT := measurable_markedTerm hχ hlam Xs Es F U U₁ E₁
  have hdep : DependsOn mT (W : Set ℕ) :=
    dependsOn_markedTerm hXs hEsi hFV hU (Finset.mem_powerset.1 hU₁) (Finset.mem_powerset.1 hE₁)
  -- the density form
  have e1 := h.prod_mul_integral_modelHierarchical (M := M) (lam := lam) (X := X)
    (f := fun y => |mT (extendConfig W y)|)
    (continuous_abs.measurable.comp (hmmT.comp (measurable_extendConfig _)))
  set Φ : (ℕ → ℂ × ℂ) → ℝ := fun c =>
    (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) * |mT c| with hΦ
  have hΦm : Measurable Φ :=
    (Finset.measurable_prod _ fun B _ => h.measurable_blockWeightOf M lam B).mul
      (continuous_abs.measurable.comp hmmT)
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
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) * |mT (extendConfig W (W.restrict c))|
        ∂labelField μ = ∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ) := by
    rw [← integral_labelField_eq_pi hΦm hΦdep]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [hΦ]
    rw [apply_extendConfig_restrict hdep c]
  have hLHS : (∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) *
      ∫ y, |mT (extendConfig W y)| ∂plusModel χ N p₀ β lam M ε₀ L V Z X =
      ∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ) := e1.trans e2
  rw [hLHS]
  -- the lower integral
  have hle1 : ENNReal.ofReal (∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ)) ≤
      ∫⁻ y, ENNReal.ofReal (Φ (extendConfig W y)) ∂Measure.pi (fun _ : W => μ) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hΦ0 _)
      (hΦm.comp (measurable_extendConfig _)).aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  refine hle1.trans ?_
  -- the pointwise bound, almost everywhere
  set ψ : (∀ l, SimpleGraph ((Ys l).biUnion id)) → (ℕ → ℂ × ℂ) → ℝ := fun Ta c =>
    (SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) *
      jIntegrandNT M lam ε₀ R X Ys Ta Tb c) *
      ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) with hψ
  set 𝒯 := (univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter
    (fun Ta => ∀ l, IsRelTree (Ys l) (Ta l)) with h𝒯
  have hψ0 : ∀ Ta c, 0 ≤ ψ Ta c := fun Ta c => mul_nonneg (mul_nonneg (sq_nonneg _)
    (jIntegrandNT_nonneg M lam ε₀ R X Ys Ta Tb c))
    (prod_nonneg fun S _ => by split_ifs <;> norm_num)
  have hψm : ∀ Ta, Measurable (ψ Ta) := fun Ta =>
    ((measurable_extGain_restrict X).mul (measurable_jIntegrandNT M lam ε₀ R X Ys Ta Tb)).mul
      (measurable_prod_connOn_indicator M lam X)
  have hae : ∀ᵐ y ∂Measure.pi (fun _ : W => μ), ENNReal.ofReal (Φ (extendConfig W y)) ≤
      ENNReal.ofReal (K₀ * ∑ Ta ∈ 𝒯, ψ Ta (extendConfig W y)) := by
    filter_upwards [ae_pi_mem (ρ := μ) (ι := W) (ae_cutoffDipoleMeasure_pos χ N p₀ β lam ε₀)]
      with y hy
    refine ENNReal.ofReal_le_ofReal (hbound (extendConfig W y) fun i hi => ?_)
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
        jExtIntegral χ p₀ N β lam M ε₀ V Z X Ys Ta Tb := by
    intro Ta
    have hres : ∀ y : W → ℂ × ℂ, (fun i : W => extendConfig W y i) = y := fun y => by
      funext i
      exact extendConfig_apply_coe W y i
    have := lintegral_pi_cutoff_eq (p₀ := p₀) (β := β) hχ hlam hε₀ hN W
      (f := fun y => ψ Ta (extendConfig W y)) ((hψm Ta).comp (measurable_extendConfig _))
    rw [this]
    congr 1
    unfold jExtIntegral jExtFullIntegrand
    refine setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ =>
      (TwoComponentCoulomb.measurableSet_box N).prod (TwoComponentCoulomb.measurableSet_box N))
      fun y _ => ?_
    simp only [hψ]
    rw [hres y]
  simp_rw [hJ]
  rw [← Finset.mul_sum, ← mul_assoc, ← ENNReal.ofReal_mul hK₀.le]

end Integration

/-! ### The comparison with `SmallIntegral.integralJext` -/

section Bridge

open scoped Classical in
/-- **The pointwise comparison of the integrands of `J_ext`** (the form of the proof of the claim
(5.106) and the form `SmallIntegral.integrandJext` of Lemma A.4). -/
theorem jExtFullIntegrand_le_integrandJext {β lam M ε₀ : ℝ} (p₀ : ℕ) {N : ℕ}
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id))
    (hW : (coarsen X (Finset.univ.image Xs)).biUnion id = X.biUnion id)
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X)
    (hhat : ∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S ∈ (Xs l).subtype (· ∈ X),
      blockRadius hX (fun i => dipoleLength (z i)) S ≤
        blockRadius hX (fun i => dipoleLength (z i)) (hatS l z))
    (y : X.biUnion id → ℂ × ℂ) :
    jExtFullIntegrand χ p₀ β lam M ε₀ V Z X Xs Ta Tb y ≤
      SmallIntegral.integrandJext χ β lam M ε₀ p₀ V Z hX Xs (fun l => Multipole.edgesOf (Ta l))
        (Multipole.edgesOf Tb) hatS y := by
  set R := truncationScale p₀ β lam with hR
  set c := extendConfig (X.biUnion id) y with hc
  have hcy : ∀ i : (X.biUnion id), c i = y i := extendConfig_apply_coe (X.biUnion id) y
  -- the factors of the right side
  set U := univ.biUnion fun l => (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta l))).edgeFinset
    with hU
  set kw : Sym2 (X.biUnion id) → ℝ := keptWeight (dipoleDistOn y) (absIndicator M lam ε₀ R y) with hkw
  set KEPT' := ∏ e ∈ U, kw e with hKEPT'
  set RAD' := ∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hatS l y),
      blockRadius hX (fun i => dipoleLength (y i)) S ^ 2 with hRAD'
  set EVEN' := ∏ e ∈ (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf Tb)).edgeFinset,
      (absWeight (fun i => dipoleLength (y i)) (dipoleDistOn y)
        (absIndicator M lam ε₀ R y) e ^ 2 + SmallIntegral.linkE M lam y e) with hEVEN'
  set IND := ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) with hIND
  set DENS' := ∏ i, SmallIntegral.cutDens χ β lam (ε₀ * R) (y i) with hDENS'
  set GAIN := SmallIntegral.extGain p₀ β lam ε₀ V Z y with hGAIN
  have hRHS : SmallIntegral.integrandJext χ β lam M ε₀ p₀ V Z hX Xs
      (fun l => Multipole.edgesOf (Ta l)) (Multipole.edgesOf Tb) hatS y =
        GAIN * RAD' * KEPT' * EVEN' * IND * DENS' := rfl
  -- the factors of the left side
  set KEPT := ∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e with hKEPT
  set RAD := ∏ l, radialExceptMax c (Xs l) with hRAD
  set EVEN := ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e with hEVEN
  set DENS := ∏ i : (X.biUnion id), (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
      (Metric.closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((y i).1 - (y i).2)) with hDENS
  have hLHS : jExtFullIntegrand χ p₀ β lam M ε₀ V Z X Xs Ta Tb y =
      GAIN * (RAD * KEPT * EVEN) * IND * DENS := rfl
  rw [hLHS, hRHS]
  -- the densities
  have hdens : DENS = DENS' := by
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold SmallIntegral.cutDens Limits.pairDensity
    congr 1
    by_cases hz : ‖(y i).1 - (y i).2‖ ≤ ε₀ * R
    · rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_zero_right] using hz),
        Set.indicator_of_mem (show ‖(y i).1 - (y i).2‖ ∈ Set.Iic (ε₀ * R) from hz)]
      rfl
    · rw [Set.indicator_of_notMem (by simpa [Metric.mem_closedBall, dist_zero_right] using hz),
        Set.indicator_of_notMem (show ‖(y i).1 - (y i).2‖ ∉ Set.Iic (ε₀ * R) from hz)]
  -- the even weights
  have hTbW : Multipole.edgesOf Tb ⊆ pairsOn (X.biUnion id) := hW ▸ edgesOf_subset_pairsOn Tb
  have heven : EVEN = EVEN' := by
    have h1 := prod_graphPairs Tb (fun i j => absEvenWeight M lam ε₀ R (c i) (c j))
      fun i j => absEvenWeight_comm M lam ε₀ R _ _
    have h2 := prod_pairs_eq_prod_edgeFinset (W := X.biUnion id) hTbW
      (fun i j => absEvenWeight M lam ε₀ R (c i) (c j)) fun i j => absEvenWeight_comm M lam ε₀ R _ _
    rw [graphPairs_eq_edgesOf] at h1
    rw [hEVEN]
    refine (h1.symm.trans h2).trans (Finset.prod_congr rfl fun e _ => ?_)
    induction e using Sym2.ind with
    | h i j =>
      simp only [Sym2.lift_mk, hcy]
      have habs : absWeight (fun i => dipoleLength (y i)) (dipoleDistOn y)
          (absIndicator M lam ε₀ R y) s(i, j) = absOddWeight M lam ε₀ R (y i) (y j) := by
        unfold absOddWeight
        exact absWeight_on M lam ε₀ R y i j
      rw [habs]
      unfold absEvenWeight SmallIntegral.linkE
      rw [Limits.symmLift_mk]
  -- the kept weights
  have hkwf : ∀ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e =
      ∏ e ∈ (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta l))).edgeFinset, kw e := by
    intro l
    have hsub : Multipole.edgesOf (Ta l) ⊆ pairsOn (X.biUnion id) :=
      (edgesOf_subset_pairsOn (Ta l)).trans
        (pairsOn_mono (Finset.biUnion_subset_biUnion_of_subset_left _ (hXs l)))
    set f : ℕ → ℕ → ℝ := fun i j => ((if MultipoleLinked M lam (c i) (c j) then 0 else 1) *
        (if dipoleDist (c i) (c j) ≤ 17 * ε₀ * R then 1 else 0)) / dipoleDist (c i) (c j) ^ 2
      with hf
    have hfs : ∀ i j, f i j = f j i := by
      intro i j
      simp only [hf, dipoleDist_comm (c i) (c j), propext (Quadratic.multipoleLinked_comm (a := c i))]
    have h1 := prod_graphPairs (Ta l) f hfs
    have h2 := prod_pairs_eq_prod_edgeFinset (W := X.biUnion id) hsub f hfs
    rw [graphPairs_eq_edgesOf] at h1
    calc ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e
        = ∏ e ∈ (Ta l).edgeFinset, Sym2.lift ⟨fun i j : (Xs l).biUnion id => f i j,
            fun i j => hfs i j⟩ e := by
          refine Finset.prod_congr rfl fun e _ => ?_
          induction e using Sym2.ind with
          | h i j => rfl
      _ = ∏ e ∈ (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta l))).edgeFinset,
            Sym2.lift ⟨fun i j : (X.biUnion id) => f i j, fun i j => hfs i j⟩ e := h1.symm.trans h2
      _ = _ := by
          refine Finset.prod_congr rfl fun e _ => ?_
          induction e using Sym2.ind with
          | h i j =>
            simp only [Sym2.lift_mk, hf, hcy, hkw]
            rfl
  have hdisjE : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      fun l => (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta l))).edgeFinset := by
    intro l _ l' _ hll'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | h i j =>
      rw [mem_edgeFinset, mem_edgeSet] at he he'
      have hmem : ∀ m, (Multipole.graphOf (X.biUnion id) (Multipole.edgesOf (Ta m))).Adj i j →
          (i : ℕ) ∈ (Xs m).biUnion id := by
        intro m hadj
        rw [Multipole.graphOf, fromRel_adj] at hadj
        rcases hadj.2 with h | h
        · exact (mem_pairsOn.1 (edgesOf_subset_pairsOn (Ta m) h)).1
        · exact (mem_pairsOn.1 (edgesOf_subset_pairsOn (Ta m) h)).2.1
      exact Finset.disjoint_left.1 (BoundedUpper.disjoint_biUnion_of_disjoint hX (hXs l) (hXs l')
        (hdisj l l' hll')) (hmem l he) (hmem l' he')
  have hkept : KEPT = KEPT' := by
    rw [hKEPT, hKEPT', hU, Finset.prod_biUnion hdisjE]
    exact Finset.prod_congr rfl fun l _ => hkwf l
  -- nonnegativity
  have hkw0 : ∀ e, 0 ≤ kw e := fun e => div_nonneg (absIndicator_nonneg M lam ε₀ R y e) (sq_nonneg _)
  have hKEPT0 : 0 ≤ KEPT' := prod_nonneg fun e _ => hkw0 e
  have hEVEN0 : 0 ≤ EVEN := prod_nonneg fun e _ => absEvenLift_nonneg M lam ε₀ R c e
  have hIND0 : 0 ≤ IND := prod_nonneg fun S _ => by split_ifs <;> norm_num
  have hDENS0 : 0 ≤ DENS' := prod_nonneg fun i _ => SmallIntegral.cutDens_nonneg _ _
  have hRAD0 : 0 ≤ RAD := prod_nonneg fun l _ => radialExceptMax_nonneg c _
  have hRAD'0 : 0 ≤ RAD' := prod_nonneg fun l _ => prod_nonneg fun S _ => sq_nonneg _
  have hGAIN0 : 0 ≤ GAIN := sq_nonneg _
  rw [hkept, heven, hdens]
  by_cases hK0 : KEPT' = 0
  · rw [hK0]
    simp only [mul_zero, zero_mul, le_refl]
  -- the radial factors
  have hr : (fun i : (X.biUnion id) => dipoleLength (y i)) = fun i : (X.biUnion id) => ‖(c i).1 - (c i).2‖ := by
    funext i
    rw [hcy]
    rfl
  have hrad : RAD ≤ RAD' := by
    refine Finset.prod_le_prod₀ (fun l _ => radialExceptMax_nonneg c _) fun l _ => ?_
    set Y := Xs l
    obtain ⟨hmemS, hmax⟩ := hhat l y
    set Ŝ : X := hatS l y
    have hŜY : (Ŝ : Finset ℕ) ∈ Y := (Finset.mem_subtype.1 hmemS)
    have hbr : ∀ S : X, blockRadius hX (fun i => dipoleLength (y i)) S = blockRad c S := by
      intro S
      rw [hr]
      exact blockRadius_eq_blockRad hX c S
    have hŜmax : ∀ S : Y, blockRad c S ≤ blockRad c (Ŝ : Finset ℕ) := by
      intro S
      have := hmax ⟨S, hXs l S.2⟩ (Finset.mem_subtype.2 S.2)
      rwa [hbr, hbr] at this
    have hYeq : blockRad c (Ŝ : Finset ℕ) = blockRad c (Y.biUnion id) :=
      blockRad_biUnion_eq c (Ŝ := ⟨Ŝ, hŜY⟩) hŜmax
    rcases (blockRad_nonneg c (Ŝ : Finset ℕ)).eq_or_lt with h0 | hpos
    · unfold radialExceptMax
      rw [← hYeq, ← h0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      exact prod_nonneg fun S _ => sq_nonneg _
    · rw [radialExceptMax_eq hŜY hYeq hpos]
      refine le_of_eq (Eq.symm ?_)
      refine Finset.prod_bij (fun S _ => (S : Finset ℕ)) (fun S hS => ?_)
        (fun S _ S' _ h => Subtype.ext h) (fun T hT => ?_) (fun S _ => ?_)
      · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
        exact Finset.mem_erase.2 ⟨fun h => hne (Subtype.ext h), Finset.mem_subtype.1 hS⟩
      · obtain ⟨hne, hT⟩ := Finset.mem_erase.1 hT
        refine ⟨⟨T, hXs l hT⟩, Finset.mem_erase.2 ⟨fun h => hne (congrArg Subtype.val h),
          Finset.mem_subtype.2 hT⟩, rfl⟩
      · rw [hbr]
  -- assembling
  have h1 : GAIN * RAD ≤ GAIN * RAD' := mul_le_mul_of_nonneg_left hrad hGAIN0
  have hrest : 0 ≤ KEPT' * EVEN' * IND * DENS' := by
    rw [← heven]
    exact mul_nonneg (mul_nonneg (mul_nonneg hKEPT0 hEVEN0) hIND0) hDENS0
  calc GAIN * (RAD * KEPT' * EVEN') * IND * DENS'
      = (GAIN * RAD) * (KEPT' * EVEN' * IND * DENS') := by ring
    _ ≤ (GAIN * RAD') * (KEPT' * EVEN' * IND * DENS') := mul_le_mul_of_nonneg_right h1 hrest
    _ = GAIN * RAD' * KEPT' * EVEN' * IND * DENS' := by ring


open scoped Classical in
/-- **`J_ext` in the two forms**: the integral of the proof of the claim (5.106) is at most
`SmallIntegral.integralJext` (eq. (A.18) of Lemma A.4) for the trees read as edge sets and any
selection `hatS` of blocks of largest radius. -/
theorem jExtIntegral_le_integralJext {β lam M ε₀ : ℝ} (p₀ N : ℕ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id))
    (hW : (coarsen X (Finset.univ.image Xs)).biUnion id = X.biUnion id)
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X)
    (hhat : ∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S ∈ (Xs l).subtype (· ∈ X),
      blockRadius hX (fun i => dipoleLength (z i)) S ≤
        blockRadius hX (fun i => dipoleLength (z i)) (hatS l z)) :
    jExtIntegral χ p₀ N β lam M ε₀ V Z X Xs Ta Tb ≤
      SmallIntegral.integralJext χ β lam M ε₀ p₀ N V Z hX Xs (fun l => Multipole.edgesOf (Ta l))
        (Multipole.edgesOf Tb) hatS := by
  unfold jExtIntegral SmallIntegral.integralJext Limits.boxConfig
  exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal
    (jExtFullIntegrand_le_integrandJext p₀ V Z hX Xs hXs hdisj Ta Tb hW hatS hhat y)

end Bridge

end NonEmptyMarks

end UpperBound

end MultipoleBKT

end
