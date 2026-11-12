/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.IntegrandBound
public import MultipoleBKT.UpperBound.Hierarchical.Expansion

/-!
# The integral over the good dipoles (`W'(Z)`, Steps 4–5 of Lemma 5.16)

The paper: proof of Lemma 5.16:
for a frozen configuration `Z` of the bad dipoles of `V` and a partition `π` of the good labels,
the integral over the good dipoles `(x_i, y_i)_{i ∉ V} ∈ (Λ²)^{V_good}` of
`∏_{i ∉ V} e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R̄}` times the cluster weight of the good
dipoles is `(N C_{β,λ,ε₀})^{|V_good|} 𝖬̂^{+,Z}_{ε₀}(π) W(Z)` (`lintegral_good_eq`).

The good dipoles are indexed by `{i : Fin N // i ∉ V}` and read on the labels `ℕ` by `natGood`
(`= extendConfig` along `goodLabelEquiv`, `natGood_piCongrLeft`): the integral against Lebesgue
measure with the dipole densities is `(N C)^{|V_good|}` times the integral against
`μ_{β,λ,ε₀}^{⊗ V_good}` (`pi_cutoffDipoleMeasure_eq`), which is the integral against
`μ_{β,λ,ε₀}^{⊗ ℕ}` of the cluster weight, `𝖬̂^{+,Z}(π) W(Z)` by `clusterIntegralOf_hat_eq`.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace UpperBound

open Hierarchical Multipole SetPartition Parity

variable {N : ℕ}

/-! ### The good labels -/

section Labels

variable (V : Finset (Fin N))

/-- A configuration of the good labels `i ∉ V`, read on `ℕ` (by `0` off the good labels). -/
def natGood (g : {i : Fin N // i ∉ V} → ℂ × ℂ) : ℕ → ℂ × ℂ :=
  fun n => if h : n < N then (if h' : (⟨n, h⟩ : Fin N) ∉ V then g ⟨⟨n, h⟩, h'⟩ else 0) else 0

theorem mem_goodLabels {n : ℕ} :
    n ∈ (univ \ V).map Fin.valEmbedding ↔ ∃ h : n < N, (⟨n, h⟩ : Fin N) ∉ V := by
  simp only [Finset.mem_map, Finset.mem_sdiff, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, hi⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨n, h⟩, h', rfl⟩

/-- The good labels of `ℕ` and the good labels of `Fin N`. -/
def goodLabelEquiv : ((univ \ V).map Fin.valEmbedding : Finset ℕ) ≃ {i : Fin N // i ∉ V} where
  toFun n := ⟨⟨n.1, ((mem_goodLabels V).1 n.2).1⟩, ((mem_goodLabels V).1 n.2).2⟩
  invFun i := ⟨i.1.1, (mem_goodLabels V).2 ⟨i.1.2, i.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natGood_piCongrLeft (y : ((univ \ V).map Fin.valEmbedding : Finset ℕ) → ℂ × ℂ) :
    natGood V (MeasurableEquiv.piCongrLeft (fun _ => ℂ × ℂ) (goodLabelEquiv V) y) =
      extendConfig ((univ \ V).map Fin.valEmbedding) y := by
  funext n
  by_cases hn : n ∈ (univ \ V).map Fin.valEmbedding
  · obtain ⟨h, h'⟩ := (mem_goodLabels V).1 hn
    have he : (⟨⟨n, h⟩, h'⟩ : {i : Fin N // i ∉ V}) = goodLabelEquiv V ⟨n, hn⟩ := rfl
    simp only [natGood, h, h', dite_true, not_false_eq_true, extendConfig, hn]
    rw [he, MeasurableEquiv.piCongrLeft_apply_apply]
  · have hnot : ¬ ∃ h : n < N, (⟨n, h⟩ : Fin N) ∉ V := fun h => hn ((mem_goodLabels V).2 h)
    simp only [natGood, extendConfig, hn, dite_false]
    by_cases h : n < N
    · have h' : (⟨n, h⟩ : Fin N) ∈ V := by
        by_contra h'
        exact hnot ⟨h, h'⟩
      simp [h, h']
    · simp [h]

theorem measurable_natGood : Measurable (natGood V) := by
  refine measurable_pi_iff.2 fun n => ?_
  unfold natGood
  by_cases h : n < N
  · simp only [h, dite_true]
    by_cases h' : (⟨n, h⟩ : Fin N) ∉ V
    · simp only [h', not_false_eq_true, dite_true]
      exact measurable_pi_apply _
    · simp only [h', dite_false]
      exact measurable_const
  · simp only [h, dite_false]
    exact measurable_const

end Labels

/-! ### The integral -/

section Integral

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ}

theorem goodClusterWeight_nonneg (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (π : Finset (Finset ℕ))
    (c : ℕ → ℂ × ℂ) : 0 ≤ goodClusterWeight χ p₀ β lam M ε₀ L V Z π c := by
  unfold goodClusterWeight clusterWeight
  refine mul_nonneg (Finset.prod_nonneg fun B _ =>
    blockWeightOf_nonneg M lam hatDipoleWeightZ_nonneg B c) (Finset.prod_nonneg fun q _ => ?_)
  unfold unlinkedBondOf
  split_ifs
  · norm_num
  · linarith [stableWeight_nonneg β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c q.1) (c q.2)]

theorem cutoffDensity_nonneg' (q : ℂ × ℂ) : 0 ≤ cutoffDensity χ p₀ β lam ε₀ q :=
  Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam hε₀ hN

open scoped Classical in
/-- **The integral over the good dipoles**: for a partition `π` of the good labels and a frozen
configuration `Z`, `∫_{(Λ²)^{V_good}} ∏_{i ∉ V} e^{β g_λ(r_i)} 𝟙_{r_i ≤ ε₀ R̄} (cluster weight)
= (N C_{β,λ,ε₀})^{|V_good|} 𝖬̂^{+,Z}_{ε₀}(π) W(Z)`. -/
theorem lintegral_good_eq {V : Finset (Fin N)} {π : Finset (Finset ℕ)}
    (hπ : π ∈ partitions ((univ \ V).map Fin.valEmbedding)) (Z : Fin N → ℂ × ℂ) :
    ∫⁻ g : {i : Fin N // i ∉ V} → ℂ × ℂ,
        ENNReal.ofReal ((if ∀ i, g i ∈ box N ×ˢ box N then 1 else 0) *
          ((∏ i, cutoffDensity χ p₀ β lam ε₀ (g i)) *
            goodClusterWeight χ p₀ β lam M ε₀ L V Z π (natGood V g))) =
      ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^
          Fintype.card {i : Fin N // i ∉ V}) *
        ENNReal.ofReal (hatPartitionFunctions χ N p₀ β lam M ε₀ L V Z π *
          clusterSeriesW χ N p₀ β lam M ε₀ L V Z π) := by
  classical
  have h' := modelHyp_hat (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h'.isProbabilityMeasure
  set ρ := cutoffDipoleMeasure χ N p₀ β lam ε₀
  set C := (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ with hCdef
  have hC : 0 < C := natCast_mul_cutoffDipoleNormalization_pos hχ hlam β hε₀ hN
  set ι := {i : Fin N // i ∉ V}
  set G' := (univ \ V).map Fin.valEmbedding
  set Φ := goodClusterWeight χ p₀ β lam M ε₀ L V Z π
  have hΦm : Measurable Φ :=
    measurable_clusterWeight (fun B => h'.measurable_blockWeightOf M lam B)
      (h'.measurable_unlinkedBondOf M lam) π
  have hΦd : DependsOn Φ ((G' : Finset ℕ) : Set ℕ) := by
    have := dependsOn_clusterWeight
      (h := blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z) M lam)
      (φ := unlinkedBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam)
      (fun B => dependsOn_blockWeightOf (β := β) (w := interactionGoodZ χ p₀ β lam ε₀ V Z)
        (ψ := hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z) M lam B) π
    rwa [(mem_partitions.1 hπ).2] at this
  have hΦb : BoundedOn (supportSet N p₀ β lam ε₀) Φ :=
    boundedOn_clusterWeight (fun B => h'.boundedOn_blockWeightOf M lam B)
      (h'.boundedOn_unlinkedBondOf M lam) π
  have hΦ0 : ∀ c, 0 ≤ Φ c := goodClusterWeight_nonneg V Z π
  have hdm : Measurable fun q : ℂ × ℂ => cutoffDensity χ p₀ β lam ε₀ q :=
    measurable_cutoffDensity hχ hlam β _
  -- the density of `μ^{⊗ ι}`
  set D : (ι → ℂ × ℂ) → ENNReal := fun g =>
    ∏ i, ENNReal.ofReal (C⁻¹ * cutoffDensity χ p₀ β lam ε₀ (g i)) with hDdef
  have hDm : Measurable D := Finset.measurable_prod _ fun i _ =>
    ENNReal.measurable_ofReal.comp ((hdm.comp (measurable_pi_apply i)).const_mul _)
  have hpi : Measure.pi (fun _ : ι => ρ) =
      (volume.restrict (Set.univ.pi fun _ : ι => box N ×ˢ box N)).withDensity D :=
    pi_cutoffDipoleMeasure_eq hχ hlam β hε₀ hN ι
  have hbox : MeasurableSet (Set.univ.pi fun _ : ι => box N ×ˢ box N) :=
    MeasurableSet.univ_pi fun _ => measurableSet_box_prod N
  -- step 1: the indicator and the normalization
  have h1 : ∀ g : ι → ℂ × ℂ, ∀ _ : Decidable (∀ i, g i ∈ box N ×ˢ box N),
      ENNReal.ofReal ((if ∀ i, g i ∈ box N ×ˢ box N then 1 else 0) *
        ((∏ i, cutoffDensity χ p₀ β lam ε₀ (g i)) * Φ (natGood V g))) =
      (Set.univ.pi fun _ : ι => box N ×ˢ box N).indicator
        (fun g => ENNReal.ofReal (C ^ Fintype.card ι) *
          (D g * ENNReal.ofReal (Φ (natGood V g)))) g := by
    intro g _
    by_cases hg : ∀ i, g i ∈ box N ×ˢ box N
    · have hmem : g ∈ Set.univ.pi fun _ : ι => box N ×ˢ box N := fun i _ => hg i
      rw [ite_eq_left hg, one_mul, Set.indicator_of_mem hmem]
      simp only [hDdef]
      rw [← ENNReal.ofReal_prod_of_nonneg fun i _ =>
        mul_nonneg (inv_nonneg.2 hC.le) (cutoffDensity_nonneg' _),
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ =>
          mul_nonneg (inv_nonneg.2 hC.le) (cutoffDensity_nonneg' _)),
        ← ENNReal.ofReal_mul (pow_nonneg hC.le _)]
      congr 1
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, inv_pow, ← mul_assoc,
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hC.ne'), one_mul]
    · have hmem : g ∉ Set.univ.pi fun _ : ι => box N ×ˢ box N := fun h =>
        hg fun i => h i (Set.mem_univ i)
      rw [ite_eq_right hg, zero_mul, ENNReal.ofReal_zero, Set.indicator_of_notMem hmem]
  rw [lintegral_congr fun g => h1 g _]
  rw [lintegral_indicator hbox, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  -- step 2: the product measure
  have hΦg : Measurable fun g : ι → ℂ × ℂ => ENNReal.ofReal (Φ (natGood V g)) :=
    ENNReal.measurable_ofReal.comp (hΦm.comp (measurable_natGood V))
  have hwd := lintegral_withDensity_eq_lintegral_mul
    (volume.restrict (Set.univ.pi fun _ : ι => box N ×ˢ box N)) hDm hΦg
  simp only [Pi.mul_apply] at hwd
  rw [← hwd, ← hpi]
  -- step 3: relabelling by `ℕ`
  rw [(measurePreserving_piCongrLeft (fun _ : ι => ρ) (goodLabelEquiv V)).lintegral_map_equiv
    (fun g => ENNReal.ofReal (Φ (natGood V g)))]
  rw [lintegral_congr fun y => by rw [natGood_piCongrLeft V y]]
  rw [← lintegral_restrict_infinitePi (μ := fun _ : ℕ => ρ) (s := G')
    (f := fun y => ENNReal.ofReal (Φ (extendConfig G' y)))
    (ENNReal.measurable_ofReal.comp (hΦm.comp (measurable_extendConfig G')))]
  have hdep : ∀ c : ℕ → ℂ × ℂ, Φ (extendConfig G' (G'.restrict c)) = Φ c :=
    fun c => apply_extendConfig_restrict hΦd c
  simp only [hdep]
  -- Step 5: group both edge families with their marks, then normalize unused blocks.
  change ∫⁻ c, ENNReal.ofReal (Φ c) ∂labelField ρ = _
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_boundedOn h'.ae_mem hΦm hΦb)
    (Filter.Eventually.of_forall hΦ0)]
  congr 1
  exact clusterIntegralOf_hat_eq hχ hlam hε₀ hN (mem_partitions.1 hπ).1

end Integral

end UpperBound

end MultipoleBKT

end
