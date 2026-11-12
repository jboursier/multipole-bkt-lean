/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Nested
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteMerge.Normalization
public import MultipoleBKT.LowerBound.AbsoluteLower.LXi
public import MultipoleBKT.LowerBound.BoundedLowerEps.Activity
public import MultipoleBKT.UpperBound.AbsoluteUpper.Bounded

/-!
# The large clusters of `𝖪^-_{ε₀}` (Lemma 4.57 and Lemma 4.59 for `𝖪^-_{ε₀}`)

Lemma 4.57, and Lemma 4.58.

`lemma_simplification` assembles the complete inequality with the
`J_large` integrals and `𝖬⁰` normalization. Lemma 4.54 supplies the
outer expectations. The written Lemma 4.55 and Lemma 4.56 simplify the
Euler factors, with positive radii outside the diagonal null set.
The common merger records the former groups by marking the outer edges
of the merged even tree. The lower-model density gives the dipole
normalization, block indicators and Boltzmann densities in `J_large`.
Finally the bounded-block comparison replaces `𝖬⁻` by `𝖬⁰`.

`minus_large_bound` combines this assembled statement with `lemma_4_59`, which integrates and sums trees with the groups fixed,
then enumerates the groups.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open MeasureTheory Finset SimpleGraph Multipole SetPartition Limits SmallIntegral Parity
  Hierarchical
open scoped ENNReal

/-! ### The diagonal is null -/

theorem volume_diagonal : volume {p : ℂ × ℂ | p.1 = p.2} = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_eq_fun measurable_fst
    measurable_snd)]
  have : ∀ x : ℂ, (Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = p.2}) = {x} := fun x => by
    ext y
    simp [eq_comm]
  simp [this]

theorem ae_ne_diagonal {ι : Type*} [Fintype ι] :
    ∀ᵐ y : ι → ℂ × ℂ ∂volume, ∀ i, (y i).1 ≠ (y i).2 := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null (fun _ : ι => (volume : Measure (ℂ × ℂ))) volume_diagonal

/-! ### From `𝖯^{-,ε₀}_X` to Lebesgue measure -/

theorem restrict_extendConfig' (U : Finset ℕ) (y : U → ℂ × ℂ) :
    U.restrict (extendConfig U y) = y := by
  funext i
  simp [Finset.restrict, extendConfig, i.2]

open scoped Classical in
/-- The weight of one block on the cutoff set: `≤ 𝟙_{𝓑_S} (W_b^p Ψ)^{|S|}` for `|S| ≤ p`. -/
theorem blockWeightOf_le_of_cutoff {β M lam : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
    {K : Set (ℂ × ℂ)} {Wb Ψ : ℝ} (hWb : 1 ≤ Wb) (hΨ0 : ∀ d, 0 ≤ ψ d)
    (hstab : ∀ d ∈ K, ∀ e ∈ K, stableWeight β w d e ≤ Wb) (hψ : ∀ d ∈ K, ψ d ≤ Ψ)
    {S : Finset ℕ} {p : ℕ} (hSp : S.card ≤ p) (c : ℕ → ℂ × ℂ) (hc : ∀ i ∈ S, c i ∈ K) :
    blockWeightOf β w ψ M lam S c ≤
      (if ConnOn S (linkedPairs M lam c S) then 1 else 0) * (Wb ^ p * Ψ) ^ S.card := by
  unfold blockWeightOf
  have hI : (0 : ℝ) ≤ if ConnOn S (linkedPairs M lam c S) then 1 else 0 := by
    split_ifs <;> norm_num
  have hp : ∏ q ∈ pairsOn S, stableWeight β w (c q.1) (c q.2) ≤ Wb ^ (p * S.card) := by
    calc ∏ q ∈ pairsOn S, stableWeight β w (c q.1) (c q.2) ≤ ∏ _q ∈ pairsOn S, Wb :=
          prod_le_prod₀ (fun q _ => stableWeight_nonneg β w _ _) fun q hq =>
            hstab _ (hc _ (mem_pairsOn.1 hq).1) _ (hc _ (mem_pairsOn.1 hq).2.1)
      _ = Wb ^ (pairsOn S).card := prod_const _
      _ ≤ Wb ^ (p * S.card) := pow_le_pow_right₀ hWb ((BoundedLowerEps.card_pairsOn_le S).trans
          (by rw [sq]; exact Nat.mul_le_mul_right _ hSp))
  have hq : ∏ i ∈ S, ψ (c i) ≤ Ψ ^ S.card := by
    calc ∏ i ∈ S, ψ (c i) ≤ ∏ _i ∈ S, Ψ := prod_le_prod₀ (fun i _ => hΨ0 _) fun i hi =>
          hψ _ (hc i hi)
      _ = Ψ ^ S.card := prod_const _
  calc (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
        (∏ q ∈ pairsOn S, stableWeight β w (c q.1) (c q.2)) * ∏ i ∈ S, ψ (c i)
      ≤ (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) * Wb ^ (p * S.card) *
          Ψ ^ S.card := by
        gcongr
        exact prod_nonneg fun i _ => hΨ0 _
    _ = _ := by rw [mul_pow, pow_mul]; ring

open scoped Classical in
/-- **From `𝖯^{-,ε₀}_X` to Lebesgue measure** ("using the definition of `𝖯^{-,ε₀}_X`", proof of Lemma 4.57): if
`F ∏_S 𝟙_{𝓑_S} ∏_i e^{β g_λ} 𝟙_{r_i ≤ ε₀R̄} ≤ G` on the box, off the null set `{∃ i, r_i = 0}` and
on the cutoff set, then
`∫ F d𝖯^{-,ε₀}_X ≤ (N C_{β,λ,ε₀})^{-|V_X|} 𝖬^-_{ε₀}(X)^{-1} (W_b^p e^{|L|})^{|V_X|}
∫_{(Λ²)^{V_X}} G`. -/
theorem lintegral_minusModel_le {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ : ℝ} (hχ : IsMollifier χ)
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hlh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (L : ℝ) {Wb : ℝ} (hWb : 1 ≤ Wb)
    (hstab : ∀ d ∈ cutoffSet N p₀ β lam ε₀, ∀ e ∈ cutoffSet N p₀ β lam ε₀,
      stableWeight β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) d e ≤ Wb)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {p : ℕ} (hXp : ∀ S ∈ X, S.card ≤ p)
    (F G : (X.biUnion id → ℂ × ℂ) → ℝ)
    (hFG : ∀ y ∈ boxConfig (X.biUnion id) N, (∀ i, (y i).1 ≠ (y i).2) →
      (∀ i, ‖(y i).1 - (y i).2‖ ≤ ε₀ * truncationScale p₀ β lam) →
      F y * (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S)
          then (1 : ℝ) else 0) *
        ∏ i, SmallIntegral.cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (y i) ≤ G y) :
    ∫⁻ y, ENNReal.ofReal (F y) ∂minusModel χ N p₀ β lam M ε₀ L X ≤
      ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^
          (X.biUnion id).card * (minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ *
          (Wb ^ p * Real.exp |L|) ^ (X.biUnion id).card) *
        ∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal (G y) := by
  have h := modelHyp_minus (p₀ := p₀) hχ hlam β hε₀ hN hlh L
  have := h.isProbabilityMeasure
  set R := truncationScale p₀ β lam with hRdef
  set hcut := ε₀ * R with hhcut
  set ρ := cutoffDipoleMeasure χ N p₀ β lam ε₀ with hρ
  set w := upperBoundInteraction χ lam ε₀ R with hw
  set ψ := gaussianWeight p₀ β lam ε₀ L with hψ
  set Cn := (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ with hCn
  have hCn0 : 0 < Cn := natCast_mul_cutoffDipoleNormalization_pos hχ hlam β hε₀ hN
  set d₁ : ((X.biUnion id) → ℂ × ℂ) → ℝ≥0∞ := fun y => ∏ S ∈ X,
    ENNReal.ofReal ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
      hierBlockWeight β w ψ M lam X S y) with hd₁
  have hd₁m : Measurable d₁ := h.measurable_modelHierarchicalDensity X
  set d₂ : ((X.biUnion id) → ℂ × ℂ) → ℝ≥0∞ := fun y => ∏ i, ENNReal.ofReal (Cn⁻¹ *
    (Metric.closedBall (0 : ℂ) hcut).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
      ((y i).1 - (y i).2)) with hd₂
  have hd₂m : Measurable d₂ := Finset.measurable_prod _ fun i _ =>
    ENNReal.measurable_ofReal.comp (((measurable_cutoffDensity hχ hlam β _).comp
      (measurable_pi_apply i)).const_mul _)
  set Q := Cn⁻¹ ^ (X.biUnion id).card * (minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ *
    (Wb ^ p * Real.exp |L|) ^ (X.biUnion id).card with hQ
  have hM0 : ∀ S, 0 ≤ modelPartitionFunction ρ β w ψ M lam S := fun S =>
    h.modelPartitionFunction_nonneg (M := M) (lam := lam) S
  have hMX : minusPartitionFunction χ N p₀ β lam M ε₀ L X =
      ∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S := rfl
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ (minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ :=
      inv_nonneg.2 (prod_nonneg fun S _ => hM0 S)
    positivity
  -- the pointwise bound
  have hpt : ∀ᵐ y ∂(volume.restrict (boxConfig (X.biUnion id) N)),
      d₂ y * (d₁ y * ENNReal.ofReal (F y)) ≤ ENNReal.ofReal Q * ENNReal.ofReal (G y) := by
    filter_upwards [ae_restrict_mem (measurableSet_boxConfig (ι := (X.biUnion id)) N),
      ae_restrict_of_ae (ae_ne_diagonal (ι := (X.biUnion id)))] with y hyb hyd
    by_cases hall : ∀ i, ‖(y i).1 - (y i).2‖ ≤ hcut
    · have hd₂eq : d₂ y = ENNReal.ofReal (Cn⁻¹ ^ (X.biUnion id).card *
          ∏ i, SmallIntegral.cutDens χ β lam hcut (y i)) := by
        simp only [hd₂, BoundedLowerEps.indicator_exp_eq_cutDens]
        rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => mul_nonneg (inv_nonneg.2 hCn0.le)
          (cutDens_nonneg _ _), prod_mul_distrib, prod_const, card_univ, Fintype.card_coe]
      have hyK : ∀ i, y i ∈ cutoffSet N p₀ β lam ε₀ := fun i => ⟨hyb i (Set.mem_univ i), hall i⟩
      have hext : ∀ i (hi : i ∈ (X.biUnion id)), extendConfig (X.biUnion id) y i = y ⟨i, hi⟩ :=
          fun i hi => by
        simp only [extendConfig, hi, dite_true]
      have hblock : ∀ S ∈ X, hierBlockWeight β w ψ M lam X S y ≤
          (if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
            (Wb ^ p * Real.exp |L|) ^ S.card := by
        intro S hS
        have := hierBlockWeight_restrict (β := β) (w := w) (ψ := ψ) (M := M) (lam := lam) hS
          (extendConfig (X.biUnion id) y)
        rw [restrict_extendConfig'] at this
        rw [this]
        refine blockWeightOf_le_of_cutoff hWb h.nonneg_ψ hstab
          (fun d hd => BoundedLowerEps.gaussianWeight_le_exp_abs hlam hε₀ L hd) (hXp S hS) _
          fun i hi => ?_
        have hiV : i ∈ (X.biUnion id) := mem_biUnion.2 ⟨S, hS, hi⟩
        rw [hext i hiV]
        exact hyK _
      have hd₁le : d₁ y ≤ ENNReal.ofReal ((minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ *
          ((∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S)
            then (1 : ℝ) else 0) *
            (Wb ^ p * Real.exp |L|) ^ (X.biUnion id).card)) := by
        have hsum : ∑ S ∈ X, S.card = (X.biUnion id).card := BoundedLowerEps.sum_card_eq hX
        have hc0 : 0 ≤ Wb ^ p * Real.exp |L| := by positivity
        calc d₁ y ≤ ∏ S ∈ X, ENNReal.ofReal ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
              ((if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S)
                then (1 : ℝ) else 0) *
                (Wb ^ p * Real.exp |L|) ^ S.card)) :=
            prod_le_prod fun S hS => ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_left (hblock S hS) (inv_nonneg.2 (hM0 S)))
          _ = _ := by
            rw [← ENNReal.ofReal_prod_of_nonneg fun S _ => mul_nonneg (inv_nonneg.2 (hM0 S))
              (mul_nonneg (by split_ifs <;> norm_num) (by positivity))]
            congr 1
            rw [prod_mul_distrib, prod_mul_distrib, prod_inv_distrib, prod_pow_eq_pow_sum, hsum,
              hMX]
      have hI0 : (0 : ℝ) ≤ ∏ S ∈ X,
          if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S)
          then (1 : ℝ) else 0 := prod_nonneg fun S _ => by split_ifs <;> norm_num
      have hP0 : 0 ≤ ∏ i, SmallIntegral.cutDens χ β lam hcut (y i) :=
        prod_nonneg fun i _ => cutDens_nonneg _ _
      have hMinv : 0 ≤ (minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ :=
        inv_nonneg.2 (prod_nonneg fun S _ => hM0 S)
      rw [hd₂eq]
      calc ENNReal.ofReal (Cn⁻¹ ^ (X.biUnion id).card *
            ∏ i, SmallIntegral.cutDens χ β lam hcut (y i)) *
            (d₁ y * ENNReal.ofReal (F y))
          ≤ ENNReal.ofReal (Cn⁻¹ ^ (X.biUnion id).card *
              ∏ i, SmallIntegral.cutDens χ β lam hcut (y i)) *
            (ENNReal.ofReal ((minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ *
              ((∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S)
                then (1 : ℝ) else 0) * (Wb ^ p * Real.exp |L|) ^ (X.biUnion id).card)) *
              ENNReal.ofReal (F y)) := by gcongr
        _ = ENNReal.ofReal (Q * (F y * (∏ S ∈ X, if ConnOn S (linkedPairs M lam
              (extendConfig (X.biUnion id) y) S) then (1 : ℝ) else 0) *
                ∏ i, SmallIntegral.cutDens χ β lam hcut (y i))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [hQ]
            ring
        _ ≤ ENNReal.ofReal (Q * G y) := ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (hFG y hyb hyd hall) hQ0)
        _ = ENNReal.ofReal Q * ENNReal.ofReal (G y) := ENNReal.ofReal_mul hQ0
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have : d₂ y = 0 := by
        refine prod_eq_zero (mem_univ i) ?_
        rw [Set.indicator_of_notMem (by
          rw [Metric.mem_closedBall, dist_zero_right]; exact not_le.2 hi), mul_zero,
          ENNReal.ofReal_zero]
      rw [this, zero_mul]
      exact bot_le
  calc ∫⁻ y, ENNReal.ofReal (F y) ∂minusModel χ N p₀ β lam M ε₀ L X
      ≤ ∫⁻ y, (d₁ * fun y => ENNReal.ofReal (F y)) y ∂Measure.pi (fun _ : (X.biUnion id) => ρ) :=
        lintegral_withDensity_le_lintegral_mul _ hd₁m _
    _ ≤ ∫⁻ y, (d₂ * fun y => (d₁ * fun y => ENNReal.ofReal (F y)) y) y
          ∂(volume.restrict (boxConfig (X.biUnion id) N)) := by
        rw [hρ, pi_cutoffDipoleMeasure_eq hχ hlam β hε₀ hN (X.biUnion id)]
        exact lintegral_withDensity_le_lintegral_mul _ hd₂m _
    _ ≤ ∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal Q * ENNReal.ofReal (G y) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal Q * ∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal (G y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

/-! ### The product of the group majorants -/

open scoped Classical in
/-- **The product of the majorants of the outer groups** (Lemmas 4.55–4.56 for each group):
`∏_l 𝓛_{C₁}(X_l) ≤ K^{|V_X|} ∏_{i ∈ V_X} (ε₀R/r_i)^{C₀/M} ∏_l 𝓛'(X_l)` for `0 < r_i ≤ ε₀R`. -/
theorem prod_eulerMajorant_le {M lam ε₀ R C₁ C₀ K : ℝ} (hC₁ : 0 ≤ C₁) (hK1 : 1 ≤ K)
    (hC₀M : 0 ≤ C₀ / M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (hEM : ∀ Y ⊆ X, ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ Y.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      eulerMajorant M lam ε₀ R C₁ Y c ≤ K ^ (Y.biUnion id).card *
        (∏ i ∈ Y.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
          innerSeries M lam ε₀ R Y c)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXsX : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) (c : ℕ → ℂ × ℂ)
    (hpos : ∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) :
    ∏ l, eulerMajorant M lam ε₀ R C₁ (Xs l) c ≤ K ^ (X.biUnion id).card *
      (∏ i ∈ X.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
        ∏ l, sourceInnerSeries M lam ε₀ R (Xs l) c := by
  set t : ℕ → ℝ := fun i => (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) with ht
  have ht1 : ∀ i ∈ X.biUnion id, 1 ≤ t i := fun i hi =>
    Real.one_le_rpow ((one_le_div (hpos i hi).1).2 (hpos i hi).2) hC₀M
  have hVl : ∀ l, (Xs l).biUnion id ⊆ X.biUnion id := fun l =>
    biUnion_subset_biUnion_of_subset_left _ (hXsX l)
  have hVd : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint fun l => (Xs l).biUnion id :=
    fun l _ l' _ hll' => Hierarchical.disjoint_biUnion_of_disjoint hX (hXsX l)
      (hXsX l') (hdisj l l' hll')
  have hU : univ.biUnion (fun l => (Xs l).biUnion id) ⊆ X.biUnion id := biUnion_subset.2
    fun l _ => hVl l
  have hcard : ∑ l, ((Xs l).biUnion id).card ≤ (X.biUnion id).card := by
    rw [← card_biUnion hVd]
    exact card_le_card hU
  have hI0 : ∀ l, 0 ≤ sourceInnerSeries M lam ε₀ R (Xs l) c :=
    fun l => sourceInnerSeries_nonneg _ _ _ _ _ _
  calc ∏ l, eulerMajorant M lam ε₀ R C₁ (Xs l) c
      ≤ ∏ l, (K ^ ((Xs l).biUnion id).card * (∏ i ∈ (Xs l).biUnion id, t i) *
          sourceInnerSeries M lam ε₀ R (Xs l) c) :=
        prod_le_prod₀ (fun l _ => eulerMajorant_nonneg hC₁ _ _) fun l _ =>
          by
            by_cases hl : 2 ≤ (Xs l).card
            · rw [sourceInnerSeries, ite_eq_left hl]
              exact hEM (Xs l) (hXsX l) c fun i hi => hpos i (hVl l hi)
            · rw [eulerMajorant_eq_zero_of_card_le_one (by omega) c,
                sourceInnerSeries, ite_eq_right hl, mul_zero]
    _ = K ^ (∑ l, ((Xs l).biUnion id).card) *
          (∏ i ∈ univ.biUnion (fun l => (Xs l).biUnion id), t i) *
          ∏ l, sourceInnerSeries M lam ε₀ R (Xs l) c := by
        rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, prod_biUnion hVd]
    _ ≤ K ^ (X.biUnion id).card * (∏ i ∈ X.biUnion id, t i) *
          ∏ l, sourceInnerSeries M lam ε₀ R (Xs l) c := by
        have h1 : ∏ i ∈ univ.biUnion (fun l => (Xs l).biUnion id), t i ≤
            ∏ i ∈ X.biUnion id, t i := by
          rw [← prod_sdiff hU]
          exact le_mul_of_one_le_left (prod_nonneg fun i hi =>
            zero_le_one.trans (ht1 i (mem_biUnion.2 (by
              obtain ⟨l, -, hl⟩ := mem_biUnion.1 hi
              exact ⟨l, mem_univ _, hl⟩) |> fun h => hU h)))
            (one_le_prod₀ fun i hi => ht1 i (mem_sdiff.1 hi).1)
        have h2 : 0 ≤ ∏ i ∈ univ.biUnion (fun l => (Xs l).biUnion id), t i :=
          prod_nonneg fun i hi => zero_le_one.trans (ht1 i (hU hi))
        have h3 : K ^ (∑ l, ((Xs l).biUnion id).card) ≤ K ^ (X.biUnion id).card :=
          pow_le_pow_right₀ hK1 hcard
        gcongr
        exact prod_nonneg fun l _ => hI0 l

/-! ### The expectations of Lemma 4.54, integrated -/

open scoped Classical in
/-- **One expectation of Lemma 4.54**, bounded by the nested integrand: for `M > 20`, `λ ≤ ε₀R̄`
and blocks of size at most `p`,
`∫ ∏_l 𝓛_{C₁}(X_l) ∏_{T^b} b^abs d𝖯^{-,ε₀}_X ≤ Q K^{|V_X|} ∫_{(Λ²)^{V_X}} (nested integrand)`. -/
theorem lintegral_lemma454_term_le {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ C₁ C₀ K : ℝ}
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
    (hlh : lam ≤ ε₀ * truncationScale p₀ β lam) (L : ℝ) {Wb : ℝ} (hWb : 1 ≤ Wb)
    (hstab : ∀ d ∈ cutoffSet N p₀ β lam ε₀, ∀ e ∈ cutoffSet N p₀ β lam ε₀,
      stableWeight β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) d e ≤ Wb)
    (hC₁ : 0 ≤ C₁) (hK1 : 1 ≤ K) (hC₀M : 0 ≤ C₀ / M)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {p : ℕ} (hXp : ∀ S ∈ X, S.card ≤ p)
    (hEM : ∀ Y ⊆ X, ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ Y.biUnion id,
      0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * truncationScale p₀ β lam) →
      eulerMajorant M lam ε₀ (truncationScale p₀ β lam) C₁ Y c ≤ K ^ (Y.biUnion id).card *
        (∏ i ∈ Y.biUnion id, (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
          innerSeries M lam ε₀ (truncationScale p₀ β lam) Y c)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXsX : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) (Tb : Finset (ℕ × ℕ)) :
    ∫⁻ y, ENNReal.ofReal ((∏ l, eulerMajorant M lam ε₀ (truncationScale p₀ β lam) C₁ (Xs l)
        (extendConfig (X.biUnion id) y)) *
      ∏ q ∈ Tb, absEvenWeight M lam ε₀ (truncationScale p₀ β lam)
        (extendConfig (X.biUnion id) y q.1) (extendConfig (X.biUnion id) y q.2))
        ∂minusModel χ N p₀ β lam M ε₀ L X ≤
      ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^
          (X.biUnion id).card * (minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ *
          (Wb ^ p * Real.exp |L|) ^ (X.biUnion id).card) *
        (ENNReal.ofReal (K ^ (X.biUnion id).card) *
          ∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
            (nestedIntegrand χ p₀ β lam M ε₀ C₀ X Xs Tb (extendConfig (X.biUnion id) y))) := by
  set R := truncationScale p₀ β lam with hRdef
  have hR : 0 ≤ ε₀ * R := hlam.le.trans hlh
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [← ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans hK1) _)]
  refine lintegral_minusModel_le hχ hlam hε₀ hN hlh L hWb hstab hX hXp _ _ fun y hyb hyd hall => ?_
  set c := extendConfig (X.biUnion id) y with hc
  have hcy : ∀ i (hi : i ∈ X.biUnion id), c i = y ⟨i, hi⟩ := fun i hi => by
    simp only [hc, extendConfig, hi, dite_true]
  have hpos : ∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R :=
    fun i hi => by
      rw [hcy i hi]
      exact ⟨norm_pos_iff.2 (sub_ne_zero.2 (hyd ⟨i, hi⟩)), hall ⟨i, hi⟩⟩
  have h1 := prod_eulerMajorant_le hC₁ hK1 hC₀M hX hEM Xs hXsX hdisj c hpos
  have hb0 : 0 ≤ ∏ q ∈ Tb, absEvenWeight M lam ε₀ R (c q.1) (c q.2) :=
    prod_nonneg fun q _ => absEvenWeight_nonneg _ _ _ _ _ _
  have hI0 : (0 : ℝ) ≤ ∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then 1 else 0 :=
    prod_nonneg fun S _ => by split_ifs <;> norm_num
  have hP : ∏ i, SmallIntegral.cutDens χ β lam (ε₀ * R) (y i) =
      ∏ i ∈ X.biUnion id, SmallIntegral.cutDens χ β lam (ε₀ * R) (c i) := by
    rw [← prod_coe_sort (X.biUnion id)]
    exact prod_congr rfl fun i _ => by rw [hcy i i.2]
  have hP0 : 0 ≤ ∏ i ∈ X.biUnion id, SmallIntegral.cutDens χ β lam (ε₀ * R) (c i) :=
    prod_nonneg fun i _ => cutDens_nonneg _ _
  rw [hP]
  unfold nestedIntegrand
  rw [← hRdef]
  calc (∏ l, eulerMajorant M lam ε₀ R C₁ (Xs l) c) *
        (∏ q ∈ Tb, absEvenWeight M lam ε₀ R (c q.1) (c q.2)) *
        (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
        ∏ i ∈ X.biUnion id, SmallIntegral.cutDens χ β lam (ε₀ * R) (c i)
      ≤ (K ^ (X.biUnion id).card *
          (∏ i ∈ X.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
            ∏ l, sourceInnerSeries M lam ε₀ R (Xs l) c) *
        (∏ q ∈ Tb, absEvenWeight M lam ε₀ R (c q.1) (c q.2)) *
        (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
        ∏ i ∈ X.biUnion id, SmallIntegral.cutDens χ β lam (ε₀ * R) (c i) := by gcongr
    _ = K ^ (X.biUnion id).card * ((∏ l, sourceInnerSeries M lam ε₀ R (Xs l) c) *
          (∏ q ∈ Tb, absEvenWeight M lam ε₀ R (c q.1) (c q.2)) *
          (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
          ∏ i ∈ X.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) *
            SmallIntegral.cutDens χ β lam (ε₀ * R) (c i)) := by
        rw [prod_mul_distrib]
        ring

/-! ### The large clusters of `𝖪^-_{ε₀}` -/

/-- The integrand of one term of Lemma 4.54: `∏_l 𝓛_{C₁}(X_l) ∏_{T^b} b^abs`. -/
noncomputable def lxIntegrand (M lam ε₀ R C₁ : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Tb : Finset (ℕ × ℕ)) (y : X.biUnion id → ℂ × ℂ) : ℝ :=
  (∏ l, eulerMajorant M lam ε₀ R C₁ (Xs l) (extendConfig (X.biUnion id) y)) *
    ∏ q ∈ Tb, absEvenWeight M lam ε₀ R
      (extendConfig (X.biUnion id) y q.1) (extendConfig (X.biUnion id) y q.2)

open scoped Classical in
/-- The series of Lemma 4.54, simplified and merged,
proof of Lemma 4.57. The paper's cutoff removes
small outer groups before applying the common merger. The density
factor is independent of the group and tree indices. -/
theorem lemma454_series_merged_le {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ C₁ C₀ K : ℝ}
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
    (hlh : lam ≤ ε₀ * truncationScale p₀ β lam) (L : ℝ) {Wb : ℝ} (hWb : 1 ≤ Wb)
    (hstab : ∀ d ∈ cutoffSet N p₀ β lam ε₀, ∀ e ∈ cutoffSet N p₀ β lam ε₀,
      stableWeight β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) d e ≤ Wb)
    (hC₁ : 0 ≤ C₁) (hK1 : 1 ≤ K) (hC₀M : 0 ≤ C₀ / M)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {p : ℕ} (hXp : ∀ S ∈ X, S.card ≤ p)
    (hEM : ∀ Y ⊆ X, ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ Y.biUnion id,
      0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * truncationScale p₀ β lam) →
      eulerMajorant M lam ε₀ (truncationScale p₀ β lam) C₁ Y c ≤ K ^ (Y.biUnion id).card *
        (∏ i ∈ Y.biUnion id, (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
          innerSeries M lam ε₀ (truncationScale p₀ β lam) Y c)
    :
    ENNReal.ofReal (∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
            ∫ y, lxIntegrand M lam ε₀ (truncationScale p₀ β lam) C₁ X Xs Tb y
              ∂minusModel χ N p₀ β lam M ε₀ L X) ≤
      ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^
        (X.biUnion id).card * (minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ *
        (Wb ^ p * Real.exp |L|) ^ (X.biUnion id).card) *
        ENNReal.ofReal (K ^ (X.biUnion id).card) * ENNReal.ofReal ((2 : ℝ) ^ X.card) *
        treeSeries χ N p₀ β lam M ε₀ C₀ X := by
  set R := truncationScale p₀ β lam with hRdef
  set P := minusModel χ N p₀ β lam M ε₀ L X with hP
  set Q := ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ (X.biUnion id).card *
    (minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ *
    (Wb ^ p * Real.exp |L|) ^ (X.biUnion id).card with hQ
  have hmodel := modelHyp_minus (p₀ := p₀) hχ hlam β hε₀ hN hlh L
  have hCn0 : 0 < (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ :=
    natCast_mul_cutoffDipoleNormalization_pos hχ hlam β hε₀ hN
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ (minusPartitionFunction χ N p₀ β lam M ε₀ L X)⁻¹ :=
      inv_nonneg.2 (prod_nonneg fun S _ => hmodel.modelPartitionFunction_nonneg (M := M)
        (lam := lam) S)
    positivity
  have hF0 : ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Tb : Finset (ℕ × ℕ))
      (y : X.biUnion id → ℂ × ℂ), 0 ≤ lxIntegrand M lam ε₀ R C₁ X Xs Tb y := fun Xs Tb y =>
    mul_nonneg (prod_nonneg fun l _ => eulerMajorant_nonneg hC₁ _ _)
      (prod_nonneg fun q _ => absEvenWeight_nonneg _ _ _ _ _ _)
  have hI0 : ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Tb : Finset (ℕ × ℕ)),
      0 ≤ ∫ y, lxIntegrand M lam ε₀ R C₁ X Xs Tb y ∂P := fun Xs Tb =>
    integral_nonneg fun y => hF0 Xs Tb y
  -- the terms with more than `|X|` groups vanish
  have hvan : ∀ n ∉ range (X.card + 1), 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
          ∫ y, lxIntegrand M lam ε₀ R C₁ X Xs Tb y ∂P = 0 := by
    intro n hn
    rw [mem_range, not_lt] at hn
    refine mul_eq_zero_of_right _ (sum_eq_zero fun Xs hXs => sum_eq_zero fun Tb _ => ?_)
    obtain ⟨hXs1, hXs2⟩ := mem_filter.1 hXs
    have hXsX : ∀ l, Xs l ⊆ X := fun l => mem_powerset.1 (Fintype.mem_piFinset.1 hXs1 l)
    obtain ⟨l, hl⟩ : ∃ l, Xs l = ∅ := by
      by_contra h
      push Not at h
      have := card_le_of_disjoint_nonempty hXsX hXs2 h
      omega
    have h0 : (fun y => lxIntegrand M lam ε₀ R C₁ X Xs Tb y) = fun _ => 0 := by
      funext y
      unfold lxIntegrand
      have he : eulerMajorant M lam ε₀ R C₁ (Xs l) (extendConfig (X.biUnion id) y) = 0 := by
        rw [hl]
        exact eulerMajorant_eq_zero_of_card_le_one (by simp) _
      rw [prod_eq_zero (mem_univ l) he, zero_mul]
    simp only [h0, integral_zero]
  rw [tsum_eq_sum hvan]
  have hrestrict (n : ℕ) :
      (∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
          ∫ y, lxIntegrand M lam ε₀ R C₁ X Xs Tb y ∂P) =
      ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesT X n,
        ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
          ∫ y, lxIntegrand M lam ε₀ R C₁ X Xs Tb y ∂P := by
    symm
    apply sum_subset (UpperBound.SimplifiedUpper.tuplesT_subset_tuplesD X n)
    intro Xs hD hT
    obtain ⟨hs, hd⟩ := mem_filter.mp hD
    have hsmall : ∃ l, (Xs l).card ≤ 1 := by
      by_contra h
      push Not at h
      exact hT (UpperBound.SimplifiedUpper.mem_tuplesT.mpr
        ⟨fun l => mem_powerset.mp (Fintype.mem_piFinset.mp hs l), hd, fun l => by
          have := h l
          omega⟩)
    obtain ⟨l, hl⟩ := hsmall
    apply sum_eq_zero
    intro Tb _
    have hz : (fun y => lxIntegrand M lam ε₀ R C₁ X Xs Tb y) = fun _ => 0 := by
      funext y
      unfold lxIntegrand
      rw [prod_eq_zero (mem_univ l) (eulerMajorant_eq_zero_of_card_le_one hl _), zero_mul]
    rw [hz, integral_zero]
  simp_rw [hrestrict]
  have hfin := sum_nonneg fun n (_ : n ∈ range (X.card + 1)) => mul_nonneg
    (by positivity : (0 : ℝ) ≤ 1 / (n.factorial : ℝ)) (sum_nonneg fun Xs (_ : Xs ∈
      UpperBound.SimplifiedUpper.tuplesT X n) => sum_nonneg fun Tb
          (_ : Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs))) => hI0 Xs Tb)
  calc ENNReal.ofReal (∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesT X n,
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
            ∫ y, lxIntegrand M lam ε₀ R C₁ X Xs Tb y ∂P)
      = ∑ n ∈ range (X.card + 1), ((n.factorial : ℝ≥0∞))⁻¹ *
          ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesT X n,
            ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
              ENNReal.ofReal (∫ y, lxIntegrand M lam ε₀ R C₁ X Xs Tb y ∂P) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun n _ => mul_nonneg (by positivity) (sum_nonneg
          fun Xs _ => sum_nonneg fun Tb _ => hI0 Xs Tb)]
        refine sum_congr rfl fun n _ => ?_
        rw [ENNReal.ofReal_mul (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun Xs _ => sum_nonneg
            fun Tb _ => hI0 Xs Tb]
        congr 1
        exact sum_congr rfl fun Xs _ => ENNReal.ofReal_sum_of_nonneg fun Tb _ => hI0 Xs Tb
    _ ≤ ∑ n ∈ range (X.card + 1), ((n.factorial : ℝ≥0∞))⁻¹ *
          ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesT X n,
            ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
              ENNReal.ofReal Q * (ENNReal.ofReal (K ^ (X.biUnion id).card) *
                ∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
                  (nestedIntegrand χ p₀ β lam M ε₀ C₀ X Xs Tb
                    (extendConfig (X.biUnion id) y))) := by
        refine sum_le_sum fun n _ => mul_le_mul_right (sum_le_sum fun Xs hXs => sum_le_sum
          fun Tb _ => ?_) _
        obtain ⟨hXs1, hXs2, _⟩ := UpperBound.SimplifiedUpper.mem_tuplesT.mp hXs
        exact (ofReal_integral_le_lintegral (hF0 Xs Tb)).trans
          (lintegral_lemma454_term_le hχ hlam hε₀ hN hlh L hWb hstab hC₁ hK1 hC₀M hX hXp hEM Xs
            hXs1 hXs2 Tb)
    _ = ENNReal.ofReal Q * ENNReal.ofReal (K ^ (X.biUnion id).card) *
          nestedSeries χ N p₀ β lam M ε₀ C₀ X := by
        unfold nestedSeries
        simp only [mul_sum]
        refine sum_congr rfl fun n _ => sum_congr rfl fun Xs _ => sum_congr rfl fun Tb _ => ?_
        ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_right (nestedSeries_le_merged hχ hlam hε₀ hX)
        (ENNReal.ofReal Q * ENNReal.ofReal (K ^ (X.biUnion id).card))

open scoped Classical in
/-- The complete lower simplification inequality,
Lemma 4.57.
The factorials remove orderings, the marked outer edges record the former
groups, and the lower density produces exactly `J_large`. The exponent
`C₀` is chosen before `M`. -/
theorem lemma_simplification {χ : ℂ → ℝ} {p₀ : ℕ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (L : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ M : ℝ, 20 < M → ∃ C : ℝ, 0 < C ∧
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₁ : ℝ, 0 < lam₁ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₁ → ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X →
            (∀ S ∈ X, S.card ≤ pBeta p₀ β) →
            ENNReal.ofReal |minusActivity χ N p₀ β lam M ε₀ L X| ≤
              UpperBound.AbsoluteUpper.simplifiedMajorant χ N p₀ β lam M ε₀ C₀ C X := by
  have hβ0 : 0 ≤ β := by linarith
  set p := pBeta p₀ β with hp
  obtain ⟨C₁, hC₁1, h454⟩ := lemma_4_54 hχ β
  obtain ⟨C₀, hC₀, hEMM⟩ := eulerMajorant_le_innerSeries p hC₁1
  -- the Boltzmann factors of the blocks
  obtain ⟨Cd, hCd0, hCd⟩ := dipoleBond_le hχ
  obtain ⟨C3, hC3, h310⟩ := lemma_3_10 hχ
  have h310' : ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
      |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
        C3 * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / τ ^ 2 := fun lam τ hlam d e hd he =>
    (h310 lam τ hlam d e hd he).1
  set Wb := Real.exp (β * (C3 / 64)) * Real.exp (β * Cd) with hWb
  have hWb1 : 1 ≤ Wb := one_le_mul_of_one_le_of_one_le
    (Real.one_le_exp (mul_nonneg hβ0 (by positivity))) (Real.one_le_exp (mul_nonneg hβ0 hCd0))
  obtain ⟨Cc, hCc, hcomp⟩ := BoundedLowerEps.minus_zero_comparison hχ
  have hZ := dipoleConstant_pos hχ hβ
  set Z := dipoleConstant χ β with hZdef
  set c₂ := β * (Cc / 64) * p + |L| with hc₂
  refine ⟨C₀, hC₀, fun M hM20 => ?_⟩
  have hM1 : 1 ≤ M := by linarith
  obtain ⟨K, hK1, hEM⟩ := hEMM hM20
  let D := max 1 (Real.exp c₂ * C₁ * (2 / Z) * (Wb ^ p * Real.exp |L|) * K * 2)
  have hD : 1 ≤ D := le_max_left _ _
  let C := Real.log D + 1
  have hC : 0 < C := by
    have := Real.log_nonneg hD
    dsimp only [C]
    linarith
  refine ⟨C, hC, fun ε₀ hε₀ hε₀1 => ?_⟩
  obtain ⟨lamL, hlamL, hL411⟩ := lem411_lower hχ hβ hε₀
  refine ⟨min lamL (min (ε₀ / 2) 1), lt_min hlamL (lt_min (by linarith) one_pos),
    fun lam hlam hlt => ?_⟩
  have hltL : lam < lamL := hlt.trans_le (min_le_left _ _)
  have hlamε : lam ≤ ε₀ / 2 := (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hlh : lam ≤ ε₀ * truncationScale p₀ β lam := by
    have := BoundedLowerEps.two_mul_le_cutoff hβ hlam hlam1 hε₀ hlamε p₀
    linarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (hL411 p₀ lam hlam hltL)
  refine ⟨max N₀ 1, fun N hN X hX hXp => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hCn := hN₀ N ((le_max_left _ _).trans hN)
  set k := (X.biUnion id).card with hkdef
  set R := truncationScale p₀ β lam with hRdef
  set Cnorm := cutoffDipoleNormalization χ N p₀ β lam ε₀ with hCnorm
  have hl : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hC0 : 0 < Cnorm := lt_of_lt_of_le (by positivity) hCn
  have hmodel := modelHyp_minus (p₀ := p₀) hχ hlam β hε₀ hN1 hlh L
  set Mm := minusPartitionFunction χ N p₀ β lam M ε₀ L X with hMm
  set Z0 := zeroPartitionFunction χ N p₀ β lam M ε₀ X with hZ0
  have hMS0 : ∀ S, 0 ≤ modelPartitionFunction (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
      (upperBoundInteraction χ lam ε₀ R) (gaussianWeight p₀ β lam ε₀ L) M lam S := fun S =>
    hmodel.modelPartitionFunction_nonneg (M := M) (lam := lam) S
  have hMm0 : 0 ≤ Mm := prod_nonneg fun S _ => hMS0 S
  have hZ00 : 0 ≤ Z0 := UpperBound.AbsoluteUpper.zeroPartitionFunction_nonneg χ N p₀ β lam M ε₀ X
  -- `𝖬^0_{ε₀}(X) ≤ e^{c₂ |V_X|} 𝖬^-_{ε₀}(X)`, block by block
  have hZM : Z0 ≤ Real.exp (c₂ * k) * Mm := by
    have hS : ∀ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
        Real.exp (c₂ * S.card) * minusPartitionFunction χ N p₀ β lam M ε₀ L {S} := by
      intro S hS
      obtain ⟨hlow, -⟩ := hcomp N p₀ β lam M ε₀ L hβ0 hlam hε₀ hN1 hlh {S}
      simp only [sum_singleton] at hlow
      set a := β * (Cc / 64) * (S.card : ℝ) ^ 2 + |L| * S.card with ha
      have hle : a ≤ c₂ * S.card := by
        have hSp : (S.card : ℝ) ≤ p := by exact_mod_cast hXp S hS
        have hsq : (S.card : ℝ) ^ 2 ≤ p * S.card := by
          rw [sq]
          exact mul_le_mul_of_nonneg_right hSp (Nat.cast_nonneg _)
        have h1 : β * (Cc / 64) * (S.card : ℝ) ^ 2 ≤ β * (Cc / 64) * (p * S.card) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        rw [ha, hc₂]
        nlinarith
      have hM0S : 0 ≤ minusPartitionFunction χ N p₀ β lam M ε₀ L {S} := by
        rw [minusPartitionFunction, prod_singleton]
        exact hMS0 S
      calc zeroPartitionFunction χ N p₀ β lam M ε₀ {S}
          = Real.exp a * (Real.exp (-a) * zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) := by
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp a * minusPartitionFunction χ N p₀ β lam M ε₀ L {S} :=
            mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
        _ ≤ Real.exp (c₂ * S.card) * minusPartitionFunction χ N p₀ β lam M ε₀ L {S} :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hle) hM0S
    have hsum : ∑ S ∈ X, S.card = k := BoundedLowerEps.sum_card_eq hX
    calc Z0 = ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
          rw [hZ0, zeroPartitionFunction]
          exact prod_congr rfl fun S _ => (prod_singleton _ S).symm
      _ ≤ ∏ S ∈ X, (Real.exp (c₂ * S.card) * minusPartitionFunction χ N p₀ β lam M ε₀ L {S}) :=
          prod_le_prod₀ (fun S _ => UpperBound.AbsoluteUpper.zeroPartitionFunction_nonneg χ N p₀ β
            lam M ε₀ {S}) hS
      _ = Real.exp (c₂ * k) * Mm := by
          rw [prod_mul_distrib, ← Real.exp_sum, ← mul_sum, ← hsum]
          push_cast
          congr 1
          rw [hMm, minusPartitionFunction]
          exact prod_congr rfl fun S _ => prod_singleton _ S
  -- the series of Lemma 4.54
  have hstab : ∀ d ∈ cutoffSet N p₀ β lam ε₀, ∀ e ∈ cutoffSet N p₀ β lam ε₀,
      stableWeight β (upperBoundInteraction χ lam ε₀ R) d e ≤ Wb := fun d hd e he =>
    ((BoundedLowerEps.stableWeight_comparison hβ0 hC3 h310' hlam hlh hd.2 he.2).1).trans
      (mul_le_mul_of_nonneg_left (by unfold stableWeight; exact hCd β hβ0 lam hlam d e)
        (Real.exp_pos _).le)
  have hEM' : ∀ Y ⊆ X, ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ Y.biUnion id,
      0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      eulerMajorant M lam ε₀ R C₁ Y c ≤ K ^ (Y.biUnion id).card *
        (∏ i ∈ Y.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
          innerSeries M lam ε₀ R Y c := fun Y hY c hc =>
    hEM lam ε₀ R hlam (SmallIntegral.isSubpartition_of_subset hX hY)
      (fun S hS => hXp S (hY hS)) c hc
  let Q := ((N : ℝ) * Cnorm)⁻¹ ^ k * Mm⁻¹ * (Wb ^ p * Real.exp |L|) ^ k
  have hQ : 0 ≤ Q := by positivity
  have hser := lemma454_series_merged_le (C₀ := C₀) hχ hlam hε₀ hN1 hlh L hWb1 hstab
    (by linarith : (0 : ℝ) ≤ C₁) hK1 (div_nonneg hC₀.le (by linarith)) hX hXp hEM'
  have h54 := ENNReal.ofReal_le_ofReal (h454 N p₀ lam M ε₀ L hlam hε₀ hN1 hlh hM1 hX)
  rw [ENNReal.ofReal_mul (by positivity)] at h54
  have hraw : ENNReal.ofReal |minusActivity χ N p₀ β lam M ε₀ L X| ≤
      ENNReal.ofReal (C₁ ^ k * Q * K ^ k * (2 : ℝ) ^ X.card) *
        treeSeries χ N p₀ β lam M ε₀ C₀ X := by
    refine (h54.trans (mul_le_mul_right hser _)).trans_eq ?_
    change ENNReal.ofReal (C₁ ^ k) * (ENNReal.ofReal Q * ENNReal.ofReal (K ^ k) *
      ENNReal.ofReal ((2 : ℝ) ^ X.card) * treeSeries χ N p₀ β lam M ε₀ C₀ X) = _
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by positivity) hQ) (by positivity)),
      ENNReal.ofReal_mul (mul_nonneg (by positivity) hQ),
      ENNReal.ofReal_mul (by positivity : 0 ≤ C₁ ^ k)]
    ring
  -- Compare the normalization coefficients before multiplying by the series.
  have hcoeff : ENNReal.ofReal (C₁ ^ k * Q * K ^ k * (2 : ℝ) ^ X.card) ≤
      ENNReal.ofReal (Real.exp (C * k)) /
        ENNReal.ofReal (((N : ℝ) * lam ^ (2 - β)) ^ k * Z0) := by
    apply RouteMerge.coefficient_le (card_le_card_biUnion hX.2 hX.1)
      hNR hlam hC0 hMm0 hZ00 (zero_le_one.trans hC₁1) (zero_le_one.trans hK1)
      (by positivity) hZ hZM
    · rw [div_le_div_iff₀ hC0 hZ]
      linarith only [hCn]
    · calc
        _ ≤ D := (le_of_eq (by ring)).trans (le_max_right _ _)
        _ ≤ Real.exp C := by
          have hDpos : 0 < D := zero_lt_one.trans_le hD
          dsimp only [C]
          rw [Real.exp_add, Real.exp_log hDpos]
          exact le_mul_of_one_le_right hDpos.le (Real.one_le_exp (by norm_num))
  exact hraw.trans (mul_le_mul_left hcoeff _)

open scoped Classical in
/-- The large-cluster estimate (4.127),
(4.126), from the complete
simplification lemma and the written integration and group sums. -/
theorem minus_large_bound {χ : ℂ → ℝ} {p₀ : ℕ} {β : ℝ} (hχ : IsMollifier χ) (hβ : 2 < β)
    (hp₀ : 1 ≤ p₀) (L : ℝ) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∃ B : ℝ, 1 ≤ B ∧
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₁ : ℝ, 0 < lam₁ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₁ →
        ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ X : Finset (Finset ℕ), IsSubpartition X →
          (∀ S ∈ X, S.card ≤ pBeta p₀ β) → largeThreshold p₀ β < (X.biUnion id).card →
          zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ ((X.biUnion id).card - 1) *
              |minusActivity χ N p₀ β lam M ε₀ L X| ≤
            B ^ (X.biUnion id).card * ((X.card.factorial : ℝ) *
              (ε₀ ^ (2 * alphaExponent β * (X.biUnion id).card - 2) * errorRate p₀ β lam)) := by
  obtain ⟨C₀, hC₀, hsimp⟩ := lemma_simplification (p₀ := p₀) hχ hβ L
  obtain ⟨M₀, hM₀, h459⟩ := lemma_4_59 (χ := χ) hχ hβ hp₀ hC₀
  refine ⟨M₀, hM₀, fun M hM => ?_⟩
  have hM20 : 20 < M := hM₀.trans_le hM
  obtain ⟨C, hC, hS⟩ := hsimp M hM20
  obtain ⟨Bs, hBs, htree⟩ := h459 M hM
  let B := max 1 (Real.exp C * Bs)
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B, hB, fun ε₀ hε₀ hε₀1 => ?_⟩
  obtain ⟨l, hl, hbound⟩ := hS ε₀ hε₀ hε₀1
  refine ⟨min l (min (ε₀ / 2) (min 1 (ε₀ ^ 2))),
    lt_min hl (lt_min (by positivity) (lt_min one_pos (by positivity))), fun lam hlam hlt => ?_⟩
  have hll : lam < l := hlt.trans_le (min_le_left _ _)
  have hlamε : lam ≤ ε₀ / 2 := (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hlam1 : lam ≤ 1 :=
    (hlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hlamε2 : lam ≤ ε₀ ^ 2 :=
    (hlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hlh : lam ≤ ε₀ * truncationScale p₀ β lam := by
    have := BoundedLowerEps.two_mul_le_cutoff hβ hlam hlam1 hε₀ hlamε p₀
    linarith
  obtain ⟨N₀, hN₀⟩ := hbound lam hlam hll
  refine ⟨max N₀ 1, fun N hN X hX hXp hk => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  let k := (X.biUnion id).card
  let Z0 := zeroPartitionFunction χ N p₀ β lam M ε₀ X
  have hZ0 : 0 ≤ Z0 := UpperBound.AbsoluteUpper.zeroPartitionFunction_nonneg χ N p₀ β lam M ε₀ X
  let E := ε₀ ^ (2 * alphaExponent β * k - 2) * errorRate p₀ β lam
  have hE : 0 ≤ E := mul_nonneg (Real.rpow_nonneg hε₀.le _) (TheoremTwo.errorRate_pos hβ hlam).le
  have hRHS : 0 ≤ B ^ k * ((X.card.factorial : ℝ) * E) := by positivity
  rcases hZ0.eq_or_lt with hz | hz
  · change Z0 * _ * _ ≤ _
    rw [← hz, zero_mul, zero_mul]
    exact hRHS
  have hden : 0 < ((N : ℝ) * lam ^ (2 - β)) ^ k * Z0 := by positivity
  have hS' := hN₀ N ((le_max_left _ _).trans hN) X hX hXp
  rw [simplifiedMajorant_eq, ← ENNReal.ofReal_div_of_pos hden] at hS'
  have ht := htree ε₀ lam hε₀ hε₀1.le hlam hlh (fun _ => hlamε2) N X hX hXp hk
  have hact := hS'.trans (mul_le_mul_right ht _)
  rw [← ENNReal.ofReal_mul (by positivity)] at hact
  have hδ := (TheoremTwo.errorRate_pos (p₀ := p₀) hβ hlam).le
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hact
  have hk1 : 1 ≤ k := by omega
  have hNk : (N : ℝ) ^ (k - 1) * N = (N : ℝ) ^ k := by
    rw [← pow_succ]
    congr 1
    omega
  have hlamk : lam ^ ((2 - β) * (k : ℝ)) = (lam ^ (2 - β)) ^ k :=
    Real.rpow_mul_natCast hlam.le _ _
  calc
    _ ≤ Z0 * (N : ℝ) ^ (k - 1) *
        (Real.exp (C * k) / (((N : ℝ) * lam ^ (2 - β)) ^ k * Z0) *
          ((N : ℝ) * Bs ^ k * (X.card.factorial : ℝ) *
            (ε₀ ^ (2 * alphaExponent β * k - 2) * lam ^ ((2 - β) * k) * errorRate p₀ β lam))) :=
      mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = (Real.exp C * Bs) ^ k * ((X.card.factorial : ℝ) * E) := by
      rw [hlamk, show Real.exp (C * k) = Real.exp C ^ k by rw [← Real.exp_nat_mul, mul_comm]]
      dsimp only [E]
      simp only [mul_pow]
      field_simp
      rw [← hNk]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (le_max_right _ _) k) (by positivity)

end AbsoluteLower

end MultipoleBKT

end
