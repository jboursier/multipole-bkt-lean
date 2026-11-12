/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.NearTree

/-!
# The limits of the multipole partition functions

See Lemma 4.26, first
assertion (4.52): for `1 ≤ |S| ≤ p*(β)`, `N^{|S|-1} 𝖬_{β,λ}(S)` converges, with
proof in equations (4.83) and (4.84).

We write `𝖬(S) = (N C_{β,λ})^{-|S|} ∫_{(Λ²)^S} Φ_S` (`multipolePartitionFunction_eq_box`), where
`Φ_S = 𝟙_{𝓑_S} ∏_{i<j} e^{-β v_ij} 𝟙_{𝒜_ij} ∏ᵢ e^{β g_λ(xᵢ - yᵢ)}` is translation invariant, and
`𝟙_{[0,1]²}(x_{i₀}) Φ_S` is integrable by the tree bound (`integrable_anchor_multipoleBox`). By
`tendsto_boxAverage` and `C_{β,λ} → λ^{2-β} 𝒵_β`:

* `tendsto_multipolePartitionFunction`:
  `N^{|S|-1} 𝖬(S) → (∫ 𝟙_{[0,1]²}(x_{i₀}) Φ_S) / (λ^{2-β} 𝒵_β)^{|S|}`;
* `multipolePartitionFunction_congr_card`: `𝖬(S)` depends on `S` only through `|S|`;
* `exists_tendsto_multipolePartitionFunction`: the form used by Theorem 2 (1).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

/-! ### The box integrand of `𝖬(S)` -/

section General

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

open scoped Classical in
/-- `Φ = 𝟙_{𝓑} ∏_{i<j} e^{-β v_ij} 𝟙_{𝒜_ij} ∏ᵢ e^{β g_λ(xᵢ - yᵢ)}` on configurations `ι → ℂ²`. -/
noncomputable def multipoleBox (χ : ℂ → ℝ) (β lam M : ℝ) (c : ι → ℂ × ℂ) : ℝ :=
  (if (nearGraph M lam c).Connected then 1 else 0) *
    (∏ i, ∏ j, if i < j then stablePairWeight χ β lam (c i) (c j) else 1) *
    ∏ i, pairDensity χ β lam (c i)

theorem multipoleBox_nonneg (χ : ℂ → ℝ) (β lam M : ℝ) (c : ι → ℂ × ℂ) :
    0 ≤ multipoleBox χ β lam M c := by
  unfold multipoleBox
  refine mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => ?_)) (Finset.prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le)
  split_ifs
  · exact stablePairWeight_nonneg χ β lam _ _
  · exact zero_le_one

theorem measurable_multipoleBox (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) :
    Measurable (multipoleBox (ι := ι) χ β lam M) := by
  classical
  unfold multipoleBox
  refine (Measurable.mul (Measurable.ite
    (measurableSet_setOf_fromRel_multipoleLinked M lam (fun G => G.Connected))
    measurable_const measurable_const) ?_).mul (Finset.measurable_prod _ fun i _ =>
      (measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i))
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  by_cases h : i < j
  · simp only [h, ite_true]
    exact measurable_stablePairWeight_apply hχ hlam β i j
  · simp only [h, ite_false]
    exact measurable_const

theorem multipoleBox_translate (a : ℂ) (c : ι → ℂ × ℂ) :
    multipoleBox χ β lam M (translate a c) = multipoleBox χ β lam M c := by
  classical
  unfold multipoleBox translate
  have hG : nearGraph M lam (fun i => c i + (a, a)) = nearGraph M lam c := by
    ext i j
    simp only [nearGraph_adj, multipoleLinked_translate]
  simp only [hG, stablePairWeight_translate, pairDensity_translate]

theorem translationInvariant_multipoleBox :
    TranslationInvariant (multipoleBox (ι := ι) χ β lam M) :=
  fun a c => multipoleBox_translate a c

open scoped Classical in
/-- The tree bound for `Φ`: `Φ ≤ B 𝟙_{𝓑} ∏ e^{β g_λ}` with `B = e^{β C |ι|²}`. -/
theorem multipoleBox_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : ι → ℂ × ℂ, multipoleBox χ β lam M c ≤
      B * ((if (nearGraph M lam c).Connected then 1 else 0) * ∏ i, pairDensity χ β lam (c i)) := by
  obtain ⟨C, hC0, hC⟩ := dipoleBond_le hχ
  set W := Real.exp (β * C)
  have hW1 : 1 ≤ W := Real.one_le_exp (mul_nonneg hβ hC0)
  refine ⟨W ^ (Fintype.card ι * Fintype.card ι), by positivity, fun c => ?_⟩
  unfold multipoleBox
  have hP : (∏ i, ∏ j, if i < j then stablePairWeight χ β lam (c i) (c j) else 1) ≤
      W ^ (Fintype.card ι * Fintype.card ι) := by
    have := abs_prod_prod_le (fun i j => if i < j then stablePairWeight χ β lam (c i) (c j) else 1)
      (W := W) fun i j => by
        split_ifs
        · rw [abs_of_nonneg (stablePairWeight_nonneg χ β lam _ _)]
          exact hC β hβ lam hlam _ _
        · rw [abs_one]; exact hW1
    exact (le_abs_self _).trans this
  have h0 : 0 ≤ ∏ i, pairDensity χ β lam (c i) :=
    Finset.prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le
  have h1 : (0 : ℝ) ≤ if (nearGraph M lam c).Connected then 1 else 0 := by split_ifs <;> norm_num
  calc (if (nearGraph M lam c).Connected then (1 : ℝ) else 0) *
        (∏ i, ∏ j, if i < j then stablePairWeight χ β lam (c i) (c j) else 1) *
        ∏ i, pairDensity χ β lam (c i)
      ≤ (if (nearGraph M lam c).Connected then 1 else 0) * W ^ (Fintype.card ι * Fintype.card ι) *
          ∏ i, pairDensity χ β lam (c i) := by gcongr
    _ = _ := by ring

open scoped Classical in
/-- **Integrability of the multipole integrand** for `|ι| ≤ p*(β)` (the untruncated tree bound
(A.13) of the paper). -/
theorem integrable_anchor_multipoleBox (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hM : 0 ≤ M) [Nonempty ι] (hk : (Fintype.card ι : ℕ∞) ≤ pStar β) (i₀ : ι) :
    Integrable fun c : ι → ℂ × ℂ => anchorR i₀ c * multipoleBox χ β lam M c := by
  have hk1 : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hks := two_sub_two_div_lt_of_le_pStar hk1 hk
  obtain ⟨B, hB0, hB⟩ := multipoleBox_le (ι := ι) (β := β) (M := M) hχ (by linarith) hlam
  refine ⟨((measurable_anchorR i₀).mul (measurable_multipoleBox hχ hlam β M)).aestronglyMeasurable,
    ?_⟩
  unfold HasFiniteIntegral
  have hpt : ∀ c : ι → ℂ × ℂ, ‖anchorR i₀ c * multipoleBox χ β lam M c‖ₑ ≤
      ENNReal.ofReal B * (anchor i₀ c * treeSum (nearGraph M lam c) *
        ∏ i, ENNReal.ofReal (pairDensity χ β lam (c i))) := by
    intro c
    rw [enorm_anchorR_mul, Real.enorm_eq_ofReal (multipoleBox_nonneg χ β lam M c)]
    have h1 := indicator_connected_le (nearGraph M lam c)
    have h2 : ENNReal.ofReal (multipoleBox χ β lam M c) ≤ ENNReal.ofReal B *
        ((if (nearGraph M lam c).Connected then 1 else 0 : ℝ≥0∞) *
          ∏ i, ENNReal.ofReal (pairDensity χ β lam (c i))) := by
      refine (ENNReal.ofReal_le_ofReal (hB c)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul hB0, ENNReal.ofReal_mul (by split_ifs <;> norm_num),
        ENNReal.ofReal_prod_of_nonneg fun i _ => (pairDensity_pos _ _ _ _).le]
      congr 2
      split_ifs <;> simp
    calc anchor i₀ c * ENNReal.ofReal (multipoleBox χ β lam M c)
        ≤ anchor i₀ c * (ENNReal.ofReal B *
            ((if (nearGraph M lam c).Connected then 1 else 0 : ℝ≥0∞) *
              ∏ i, ENNReal.ofReal (pairDensity χ β lam (c i)))) := mul_le_mul_right h2 _
      _ ≤ anchor i₀ c * (ENNReal.ofReal B * (treeSum (nearGraph M lam c) *
              ∏ i, ENNReal.ofReal (pairDensity χ β lam (c i)))) :=
          mul_le_mul_right (mul_le_mul_right (mul_le_mul_left h1 _) _) _
      _ = _ := by ring
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  unfold treeSum
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [lintegral_finsetSum' _ fun T _ => ?_]
  · exact ENNReal.sum_lt_top.2 fun T hT =>
      lintegral_tree_near_lt_top hχ hβ hlam hM hks (mem_filter.1 hT).2 i₀
  · exact ((measurable_anchor i₀).mul (Finset.measurable_prod _ fun e _ =>
      measurable_edgeInd_nearGraph M lam e)).mul
      (Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
        ((measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i))) |>.aemeasurable

end General

/-! ### `𝖬(S)` as a box integral and its limit -/

theorem multipolePartitionFunctionIntegrand_eq (S : Finset ℕ) (c : S → ℂ × ℂ) :
    multipolePartitionFunctionIntegrand χ β lam M c * ∏ i, pairDensity χ β lam (c i) =
      multipoleBox χ β lam M c := by
  unfold multipolePartitionFunctionIntegrand multipoleBox
  rfl

/-- `𝖬(S) = (N C_{β,λ})^{-|S|} ∫_{(Λ²)^S} Φ_S`. -/
theorem multipolePartitionFunction_eq_box (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    (S : Finset ℕ) :
    multipolePartitionFunction χ N β lam M S =
      ((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ ^ S.card *
        ∫ c in boxConfig S N, multipoleBox χ β lam M c := by
  rw [multipolePartitionFunction_eq_integral, integral_pi_dipoleMeasure hχ hlam β hN,
    Fintype.card_coe]
  simp_rw [multipolePartitionFunctionIntegrand_eq]

/-- `λ^{2-β} 𝒵_β > 0`, the limit of `C_{β,λ}`. -/
theorem limNormalization_pos (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam) :
    0 < lam ^ (2 - β) * dipoleConstant χ β :=
  mul_pos (Real.rpow_pos_of_pos hlam _) (dipoleConstant_pos hχ hβ)

/-- **Lemma 4.26, equation (4.52)**: for `1 ≤ |S| ≤ p*(β)`,
`N^{|S|-1} 𝖬(S) → (∫ 𝟙_{[0,1]²}(x_{i₀}) Φ_S) / (λ^{2-β} 𝒵_β)^{|S|}`. -/
theorem tendsto_multipolePartitionFunction (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hM : 0 ≤ M) {S : Finset ℕ} (i₀ : S) (hS : (S.card : ℕ∞) ≤ pStar β) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S)
      atTop (𝓝 ((∫ c, anchorR i₀ c * multipoleBox χ β lam M c) /
        (lam ^ (2 - β) * dipoleConstant χ β) ^ S.card)) := by
  have hne : Nonempty S := ⟨i₀⟩
  have hk : (Fintype.card S : ℕ∞) ≤ pStar β := by rwa [Fintype.card_coe]
  have hS1 : 1 ≤ S.card := Finset.card_pos.2 ⟨i₀, i₀.2⟩
  have hbox := tendsto_boxAverage i₀ (measurable_multipoleBox hχ hlam β M)
    translationInvariant_multipoleBox (integrable_anchor_multipoleBox hχ hβ hlam hM hk i₀)
  have hc := limNormalization_pos hχ hβ hlam
  have hC := tendsto_dipoleNormalization hχ hβ hlam
  have hinv : Tendsto (fun N : ℕ => (dipoleNormalization χ N β lam)⁻¹ ^ S.card) atTop
      (𝓝 ((lam ^ (2 - β) * dipoleConstant χ β)⁻¹ ^ S.card)) :=
    (hC.inv₀ hc.ne').pow _
  have h := hinv.mul hbox
  rw [inv_pow, ← div_eq_inv_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [multipolePartitionFunction_eq_box hχ hlam hN]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mul_inv, mul_pow, inv_pow, inv_pow]
  have hpow : (N : ℝ) ^ (S.card - 1) * ((N : ℝ) ^ S.card)⁻¹ = 1 / N := by
    rw [← Nat.sub_add_cancel hS1, pow_succ, Nat.add_sub_cancel]
    field_simp
  calc ((dipoleNormalization χ N β lam) ^ S.card)⁻¹ *
        (1 / (N : ℝ) * ∫ c in boxConfig S N, multipoleBox χ β lam M c)
      = (N : ℝ) ^ (S.card - 1) * ((N : ℝ) ^ S.card)⁻¹ *
          ((dipoleNormalization χ N β lam) ^ S.card)⁻¹ *
          ∫ c in boxConfig S N, multipoleBox χ β lam M c := by rw [hpow]; ring
    _ = _ := by ring

/-! ### `𝖬(S)` depends only on `|S|` -/

/-- An order isomorphism of label sets preserves `𝖬`. -/
theorem multipolePartitionFunction_congr_orderIso (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hN : 1 ≤ N) {S S' : Finset ℕ} (e : S ≃o S') :
    multipolePartitionFunction χ N β lam M S = multipolePartitionFunction χ N β lam M S' := by
  classical
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  rw [multipolePartitionFunction_eq_integral, multipolePartitionFunction_eq_integral]
  have hmp := measurePreserving_piCongrLeft (fun _ : S' => dipoleMeasure χ N β lam)
    e.toEquiv
  refine Eq.trans ?_ (hmp.integral_comp' (multipolePartitionFunctionIntegrand χ β lam M))
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only
  have happ : ∀ s : S', MeasurableEquiv.piCongrLeft (fun _ => ℂ × ℂ) e.toEquiv c s =
      c (e.symm s) := fun s => by
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  unfold multipolePartitionFunctionIntegrand
  simp_rw [happ]
  congr 1
  · have hiso : (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)) ≃g
        (SimpleGraph.fromRel fun i j : S' =>
          MultipoleLinked M lam (c (e.symm i)) (c (e.symm j))) :=
      { toEquiv := e.toEquiv
        map_rel_iff' := by
          intro a b
          simp [fromRel_adj] }
    rw [hiso.connected_iff]
  · refine Fintype.prod_equiv e.toEquiv _ _ fun i => ?_
    refine Fintype.prod_equiv e.toEquiv _ _ fun j => ?_
    simp [e.lt_iff_lt]

/-- `𝖬(S)` depends only on `|S|`. -/
theorem multipolePartitionFunction_congr_card (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hN : 1 ≤ N) {S S' : Finset ℕ} (h : S.card = S'.card) :
    multipolePartitionFunction χ N β lam M S = multipolePartitionFunction χ N β lam M S' :=
  multipolePartitionFunction_congr_orderIso hχ hlam hN ((S.orderIsoOfFin rfl).symm.trans
    (S'.orderIsoOfFin h.symm))

/-- **Lemma 4.26 (𝗆), in the form of Theorem 2 (1).** For `β > 2`, `λ > 0`, `M ≥ 0` and
`1 ≤ k ≤ p*(β)`, there is `m` with `N^{|S|-1} 𝖬(S) → m` for every `S` with `|S| = k`. -/
theorem exists_tendsto_multipolePartitionFunction (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 0 ≤ M) {k : ℕ} (hk : 1 ≤ k) (hkp : (k : ℕ∞) ≤ pStar β) :
    ∃ m : ℝ, ∀ S : Finset ℕ, S.card = k →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S)
        atTop (𝓝 m) := by
  have hr : (Finset.range k).card = k := Finset.card_range k
  set i₀ : Finset.range k := ⟨0, Finset.mem_range.2 hk⟩
  refine ⟨(∫ c, anchorR i₀ c * multipoleBox χ β lam M c) /
    (lam ^ (2 - β) * dipoleConstant χ β) ^ (Finset.range k).card, fun S hS => ?_⟩
  have := tendsto_multipolePartitionFunction (χ := χ) (M := M) hχ hβ hlam hM i₀
    (by rwa [hr])
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [hr, hS, multipolePartitionFunction_congr_card hχ hlam hN (hS.trans hr.symm)]

end Limits

end MultipoleBKT

end
