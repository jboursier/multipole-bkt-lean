/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Gibbs.Activities
public import MultipoleBKT.Potential.DipoleConstant
public import TwoComponentCoulomb.Gibbs.Basic
public import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Box averages of translation-invariant integrands

See the proof of Lemma 4.26,
claim (4.82).

The paper writes an integrand of `k` points of `Λ = [0, √N]²` that only depends on the
differences to the first point as `G(z₂ - z₁, …, z_k - z₁)` and proves
`(1/N) ∫_{Λ^k} G(z₂ - z₁, …) → ∫ G` by dominated convergence, the normalized area `V_N` of
`Λ ∩ (Λ - y₂) ∩ ⋯` tending to `1`. We avoid relative coordinates: for a function `Φ` of a
configuration `c : ι → ℂ × ℂ` that is invariant under translating all the points, the role of
`G` is played by `𝟙_{[0,1]²}(x_{i₀}) Φ(c)` (the reference point `x_{i₀}` is integrated against the unit
square instead of being fixed), and

* `lintegral_boxConfig_eq`: `∫_{(Λ²)^ι} F = ∫ 𝟙_{[0,1]²}(x_{i₀}) F(c) |{a : c + a ∈ (Λ²)^ι}| dc`
  for `F ≥ 0` translation invariant;
* `tendsto_boxAverage`: if `𝟙_{[0,1]²}(x_{i₀}) Φ` is integrable, then
  `(1/N) ∫_{(Λ²)^ι} Φ → ∫ 𝟙_{[0,1]²}(x_{i₀}) Φ`.

We also write integrals against `μ^{⊗ ι}` as box integrals (`integral_pi_dipoleMeasure`).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Filter Topology Set
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {ι : Type*}

/-- Translation of all the points of a configuration by `a`. -/
def translate (a : ℂ) (c : ι → ℂ × ℂ) : ι → ℂ × ℂ := fun i => c i + (a, a)

/-- A function of configurations is translation invariant. -/
def TranslationInvariant {α : Type*} (Φ : (ι → ℂ × ℂ) → α) : Prop :=
  ∀ a c, Φ (translate a c) = Φ c

/-- The set `(Λ²)^ι` of configurations with all points in `Λ = [0, √N]²`. -/
def boxConfig (ι : Type*) (N : ℕ) : Set (ι → ℂ × ℂ) := Set.univ.pi fun _ => box N ×ˢ box N

/-- The area `|{a ∈ ℂ : c + a ∈ (Λ²)^ι}|` of the translations keeping `c` in the box. -/
noncomputable def overlap (N : ℕ) (c : ι → ℂ × ℂ) : ℝ≥0∞ :=
  volume {a : ℂ | translate a c ∈ boxConfig ι N}

/-- The indicator of the unit square `[0, 1]²` at the reference point. -/
noncomputable def anchor (i₀ : ι) (c : ι → ℂ × ℂ) : ℝ≥0∞ := (box 1).indicator 1 (c i₀).1

/-- The real indicator of the unit square at the reference point. -/
noncomputable def anchorR (i₀ : ι) (c : ι → ℂ × ℂ) : ℝ := (box 1).indicator 1 (c i₀).1

theorem measurable_translate (a : ℂ) : Measurable (translate (ι := ι) a) :=
  measurable_pi_iff.2 fun i => (measurable_pi_apply i).add_const _

theorem measurable_uncurry_translate [Fintype ι] :
    Measurable fun p : ℂ × (ι → ℂ × ℂ) => translate p.1 p.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  exact ((measurable_pi_apply i).comp measurable_snd).add
    (measurable_fst.prodMk measurable_fst)

theorem measurableSet_boxConfig [Countable ι] (N : ℕ) : MeasurableSet (boxConfig ι N) :=
  MeasurableSet.univ_pi fun _ => measurableSet_box_prod N

theorem measurable_anchor (i₀ : ι) : Measurable (anchor i₀) :=
  (measurable_const.indicator (TwoComponentCoulomb.measurableSet_box 1)).comp
    (measurable_fst.comp (measurable_pi_apply i₀))

theorem measurable_anchorR (i₀ : ι) : Measurable (anchorR i₀) :=
  (measurable_const.indicator (TwoComponentCoulomb.measurableSet_box 1)).comp
    (measurable_fst.comp (measurable_pi_apply i₀))

theorem anchorR_nonneg (i₀ : ι) (c : ι → ℂ × ℂ) : 0 ≤ anchorR i₀ c := by
  unfold anchorR
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem anchorR_le_one (i₀ : ι) (c : ι → ℂ × ℂ) : anchorR i₀ c ≤ 1 := by
  unfold anchorR
  exact Set.indicator_le_self' (fun _ _ => zero_le_one) _

theorem ofReal_anchorR (i₀ : ι) (c : ι → ℂ × ℂ) :
    ENNReal.ofReal (anchorR i₀ c) = anchor i₀ c := by
  unfold anchorR anchor
  by_cases h : (c i₀).1 ∈ box 1 <;> simp [h]

/-- `∫ 𝟙_{[0,1]²}(x - a) da = 1`. -/
theorem lintegral_indicator_box_one_sub (x : ℂ) :
    ∫⁻ a : ℂ, (box 1).indicator 1 (x - a) = 1 := by
  rw [lintegral_sub_left_eq_self (fun a => (box 1).indicator (1 : ℂ → ℝ≥0∞) a) x,
    lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box 1),
    TwoComponentCoulomb.volume_box]
  simp

section Fintype

variable [Fintype ι]

theorem measurePreserving_translate (a : ℂ) :
    MeasurePreserving (translate (ι := ι) a) volume volume := by
  have : (volume : Measure (ℂ × ℂ)).IsAddRightInvariant :=
    Measure.prod.instIsAddRightInvariant
  exact measurePreserving_pi (fun _ : ι => (volume : Measure (ℂ × ℂ)))
    (fun _ : ι => (volume : Measure (ℂ × ℂ))) fun _ => measurePreserving_add_right _ (a, a)

/-- **Box averages.** For `F ≥ 0` measurable and translation invariant,
`∫_{(Λ²)^ι} F = ∫ 𝟙_{[0,1]²}(x_{i₀}) F(c) |{a : c + a ∈ (Λ²)^ι}| dc`. -/
theorem lintegral_boxConfig_eq (N : ℕ) (i₀ : ι) {F : (ι → ℂ × ℂ) → ℝ≥0∞}
    (hF : Measurable F) (hinv : TranslationInvariant F) :
    ∫⁻ c in boxConfig ι N, F c = ∫⁻ c, anchor i₀ c * F c * overlap N c := by
  have hB := measurableSet_boxConfig (ι := ι) N
  have hx : Measurable fun c : ι → ℂ × ℂ => (c i₀).1 := measurable_fst.comp (measurable_pi_apply i₀)
  have hg : Measurable fun x : ℂ => (box 1).indicator (1 : ℂ → ℝ≥0∞) x :=
    measurable_const.indicator (TwoComponentCoulomb.measurableSet_box 1)
  -- insert `1 = ∫ 𝟙(x_{i₀} - a) da`
  have h1 : ∫⁻ c in boxConfig ι N, F c =
      ∫⁻ c, ∫⁻ a : ℂ, (box 1).indicator 1 ((c i₀).1 - a) * (boxConfig ι N).indicator F c := by
    rw [← lintegral_indicator hB]
    refine lintegral_congr fun c => ?_
    have := lintegral_mul_const (μ := volume) ((boxConfig ι N).indicator F c)
      (f := fun a : ℂ => (box 1).indicator (1 : ℂ → ℝ≥0∞) ((c i₀).1 - a))
      (hg.comp (measurable_const.sub measurable_id))
    rw [this, lintegral_indicator_box_one_sub, one_mul]
  have hmeas : Measurable (Function.uncurry fun (c : ι → ℂ × ℂ) (a : ℂ) =>
      (box 1).indicator (1 : ℂ → ℝ≥0∞) ((c i₀).1 - a) * (boxConfig ι N).indicator F c) :=
    (hg.comp ((hx.comp measurable_fst).sub measurable_snd)).mul
      ((hF.indicator hB).comp measurable_fst)
  rw [h1, lintegral_lintegral_swap hmeas.aemeasurable]
  -- translate the configuration by `a`
  have h2 : ∀ a : ℂ, ∫⁻ c, (box 1).indicator 1 ((c i₀).1 - a) * (boxConfig ι N).indicator F c =
      ∫⁻ c, (box 1).indicator 1 (c i₀).1 * {c | translate a c ∈ boxConfig ι N}.indicator 1 c *
        F c := by
    intro a
    have key := (measurePreserving_translate (ι := ι) a).lintegral_comp
      (f := fun c => (box 1).indicator (1 : ℂ → ℝ≥0∞) ((c i₀).1 - a) *
        (boxConfig ι N).indicator F c)
      ((hg.comp (hx.sub measurable_const)).mul (hF.indicator hB))
    rw [← key]
    refine lintegral_congr fun c => ?_
    have e1 : (translate a c i₀).1 - a = (c i₀).1 := by simp [translate]
    rw [e1]
    by_cases h : translate a c ∈ boxConfig ι N
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show c ∈ {c | translate a c ∈
        boxConfig ι N} from h), hinv a c]
      simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show c ∉ {c | translate a c ∈
        boxConfig ι N} from h)]
      simp
  simp_rw [h2]
  have hset : MeasurableSet {p : ℂ × (ι → ℂ × ℂ) | translate p.1 p.2 ∈ boxConfig ι N} :=
    measurable_uncurry_translate hB
  have hmeas2 : Measurable (Function.uncurry fun (a : ℂ) (c : ι → ℂ × ℂ) =>
      (box 1).indicator (1 : ℂ → ℝ≥0∞) (c i₀).1 *
        {c | translate a c ∈ boxConfig ι N}.indicator 1 c * F c) := by
    have : Measurable fun p : ℂ × (ι → ℂ × ℂ) =>
        {p : ℂ × (ι → ℂ × ℂ) | translate p.1 p.2 ∈ boxConfig ι N}.indicator
          (1 : ℂ × (ι → ℂ × ℂ) → ℝ≥0∞) p := measurable_const.indicator hset
    refine ((hg.comp (hx.comp measurable_snd)).mul ?_).mul (hF.comp measurable_snd)
    convert this using 1
    rfl
  rw [lintegral_lintegral_swap hmeas2.aemeasurable]
  refine lintegral_congr fun c => ?_
  have hc : MeasurableSet {a : ℂ | translate a c ∈ boxConfig ι N} :=
    (measurable_uncurry_translate.comp (measurable_id.prodMk measurable_const)) hB
  have : ∀ a : ℂ, (box 1).indicator (1 : ℂ → ℝ≥0∞) (c i₀).1 *
      {c | translate a c ∈ boxConfig ι N}.indicator 1 c * F c =
      (box 1).indicator 1 (c i₀).1 * F c *
        {a : ℂ | translate a c ∈ boxConfig ι N}.indicator 1 a := by
    intro a
    by_cases h : translate a c ∈ boxConfig ι N
    · rw [Set.indicator_of_mem (show c ∈ {c | translate a c ∈ boxConfig ι N} from h),
        Set.indicator_of_mem (show a ∈ {a : ℂ | translate a c ∈ boxConfig ι N} from h)]
      simp only [Pi.one_apply]
      ring
    · rw [Set.indicator_of_notMem (show c ∉ {c | translate a c ∈ boxConfig ι N} from h),
        Set.indicator_of_notMem (show a ∉ {a : ℂ | translate a c ∈ boxConfig ι N} from h)]
      ring
  simp_rw [this]
  rw [lintegral_const_mul _ (measurable_one.indicator hc), lintegral_indicator_one hc]
  rfl

omit [Fintype ι] in
/-- The overlap area is at most `|Λ| = N`. -/
theorem overlap_le [Nonempty ι] (N : ℕ) (c : ι → ℂ × ℂ) : overlap N c ≤ N := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsub : {a : ℂ | translate a c ∈ boxConfig ι N} ⊆ (fun a => a + (c i₀).1) ⁻¹' box N := by
    intro a ha
    have := (ha i₀ (Set.mem_univ _)).1
    simpa [translate, add_comm] using this
  calc overlap N c ≤ volume ((fun a => a + (c i₀).1) ⁻¹' box N) := measure_mono hsub
    _ = N := by rw [measure_preimage_add_right, TwoComponentCoulomb.volume_box]

omit [Fintype ι] in
theorem overlap_ne_top [Nonempty ι] (N : ℕ) (c : ι → ℂ × ℂ) : overlap N c ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (overlap_le N c)

omit [Fintype ι] in
/-- A square of translations keeping all the points of `c` in the box. -/
theorem reProdIm_subset_overlap (N : ℕ) (c : ι → ℂ × ℂ) {R : ℝ}
    (hR : ∀ i, |(c i).1.re| ≤ R ∧ |(c i).1.im| ≤ R ∧ |(c i).2.re| ≤ R ∧ |(c i).2.im| ≤ R) :
    Complex.reProdIm (Icc R (√(N : ℝ) - R)) (Icc R (√(N : ℝ) - R)) ⊆
      {a : ℂ | translate a c ∈ boxConfig ι N} := by
  intro a ha
  rw [Complex.mem_reProdIm] at ha
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ha
  intro i _
  obtain ⟨r1, r2, r3, r4⟩ := hR i
  rw [abs_le] at r1 r2 r3 r4
  obtain ⟨r1, r1'⟩ := r1
  obtain ⟨r2, r2'⟩ := r2
  obtain ⟨r3, r3'⟩ := r3
  obtain ⟨r4, r4'⟩ := r4
  simp only [translate, Prod.fst_add, Prod.snd_add, Set.mem_prod, box, Complex.mem_reProdIm,
    Complex.add_re, Complex.add_im, Set.mem_Icc]
  refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The normalized overlap tends to `1`. -/
theorem tendsto_overlap_toReal_div [Nonempty ι] (c : ι → ℂ × ℂ) :
    Tendsto (fun N : ℕ => (overlap N c).toReal / N) atTop (𝓝 1) := by
  set R : ℝ := ∑ i, (‖(c i).1‖ + ‖(c i).2‖)
  have hR : ∀ i, |(c i).1.re| ≤ R ∧ |(c i).1.im| ≤ R ∧ |(c i).2.re| ≤ R ∧ |(c i).2.im| ≤ R := by
    intro i
    have hi : ‖(c i).1‖ + ‖(c i).2‖ ≤ R :=
      Finset.single_le_sum (f := fun i => ‖(c i).1‖ + ‖(c i).2‖)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have a1 := Complex.abs_re_le_norm (c i).1
    have a2 := Complex.abs_im_le_norm (c i).1
    have a3 := Complex.abs_re_le_norm (c i).2
    have a4 := Complex.abs_im_le_norm (c i).2
    have n1 := norm_nonneg (c i).1
    have n2 := norm_nonneg (c i).2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hlow : Tendsto (fun N : ℕ => (max (1 - (2 * R) / √(N : ℝ)) 0) ^ 2) atTop (𝓝 1) := by
    simpa using (tendsto_max_one_sub_div_sqrt (2 * R)).pow 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN'
    have hss : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN'.le
    have hvol : ENNReal.ofReal (√(N : ℝ) - 2 * R) * ENNReal.ofReal (√(N : ℝ) - 2 * R) ≤
        overlap N c := by
      have := measure_mono (μ := volume) (reProdIm_subset_overlap N c hR)
      rwa [TwoComponentCoulomb.volume_reProdIm_Icc_Icc,
        show √(N : ℝ) - R - R = √(N : ℝ) - 2 * R by ring] at this
    have ht : (max (√(N : ℝ) - 2 * R) 0) ^ 2 ≤ (overlap N c).toReal := by
      have := ENNReal.toReal_mono (overlap_ne_top N c) hvol
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ← sq] at this
    have e : max (√(N : ℝ) - 2 * R) 0 = √(N : ℝ) * max (1 - 2 * R / √(N : ℝ)) 0 := by
      rw [mul_max_of_nonneg _ _ hs.le, mul_zero, mul_sub, mul_one, mul_div_cancel₀ _ hs.ne']
    rw [e, mul_pow, sq (√(N : ℝ)), hss] at ht
    rw [le_div_iff₀ hN', mul_comm]
    exact ht
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_one hN']
    have := overlap_le N c
    exact (ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg N) (by simpa using this))

omit [Fintype ι] in
theorem enorm_anchorR_mul (i₀ : ι) (Φ : (ι → ℂ × ℂ) → ℝ) (c : ι → ℂ × ℂ) :
    ‖anchorR i₀ c * Φ c‖ₑ = anchor i₀ c * ‖Φ c‖ₑ := by
  unfold anchorR anchor
  by_cases h : (c i₀).1 ∈ box 1 <;> simp [h]

omit [Fintype ι] in
theorem ofReal_anchorR_mul_mul (i₀ : ι) (x : ℝ) {t : ℝ≥0∞} (ht : t ≠ ∞) (c : ι → ℂ × ℂ) :
    ENNReal.ofReal (anchorR i₀ c * x * t.toReal) = anchor i₀ c * ENNReal.ofReal x * t := by
  unfold anchorR anchor
  by_cases h : (c i₀).1 ∈ box 1
  · simp only [h, Set.indicator_of_mem, Pi.one_apply, one_mul]
    rw [mul_comm x, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ht, mul_comm]
  · simp [h]

/-- **Box averages, real-valued form.** If `Φ` is measurable, translation invariant and
`𝟙_{[0,1]²}(x_{i₀}) Φ` is integrable, then `Φ` is integrable on `(Λ²)^ι` and
`∫_{(Λ²)^ι} Φ = ∫ 𝟙_{[0,1]²}(x_{i₀}) Φ(c) |{a : c + a ∈ (Λ²)^ι}| dc`. -/
theorem integral_boxConfig_eq [Nonempty ι] (N : ℕ) (i₀ : ι) {Φ : (ι → ℂ × ℂ) → ℝ}
    (hΦ : Measurable Φ) (hinv : TranslationInvariant Φ)
    (hint : Integrable (fun c => anchorR i₀ c * Φ c)) :
    IntegrableOn Φ (boxConfig ι N) ∧
      ∫ c in boxConfig ι N, Φ c = ∫ c, anchorR i₀ c * Φ c * (overlap N c).toReal := by
  have hov : Measurable (overlap (ι := ι) N) := by
    have hset : MeasurableSet {p : (ι → ℂ × ℂ) × ℂ | translate p.2 p.1 ∈ boxConfig ι N} :=
      (measurable_uncurry_translate.comp measurable_swap) (measurableSet_boxConfig N)
    exact measurable_measure_prodMk_left hset
  have hinvE : TranslationInvariant fun c => ‖Φ c‖ₑ := fun a c => by
    simp only [hinv a c]
  have hinvP : TranslationInvariant fun c => ENNReal.ofReal (Φ c) := fun a c => by
    simp only [hinv a c]
  have hinvN : TranslationInvariant fun c => ENNReal.ofReal (-Φ c) := fun a c => by
    simp only [hinv a c]
  have hfin : ∫⁻ c, anchor i₀ c * ‖Φ c‖ₑ < ∞ := by
    have := hint.2
    unfold HasFiniteIntegral at this
    simpa only [enorm_anchorR_mul] using this
  have hint1 : IntegrableOn Φ (boxConfig ι N) := by
    refine ⟨hΦ.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_boxConfig_eq N i₀ hΦ.enorm hinvE]
    calc ∫⁻ c, anchor i₀ c * ‖Φ c‖ₑ * overlap N c ≤ ∫⁻ c, anchor i₀ c * ‖Φ c‖ₑ * N :=
          lintegral_mono fun c => by gcongr; exact overlap_le N c
      _ = (∫⁻ c, anchor i₀ c * ‖Φ c‖ₑ) * N :=
          lintegral_mul_const _ ((measurable_anchor i₀).mul hΦ.enorm)
      _ < ∞ := ENNReal.mul_lt_top hfin (ENNReal.natCast_lt_top N)
  have hH : Integrable (fun c => anchorR i₀ c * Φ c * (overlap N c).toReal) := by
    refine Integrable.mono' (hint.norm.const_mul (N : ℝ))
      (((measurable_anchorR i₀).mul hΦ).mul hov.ennreal_toReal).aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg N) (by simpa using overlap_le N c)
  refine ⟨hint1, ?_⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hH,
    lintegral_boxConfig_eq (F := fun c => ENNReal.ofReal (Φ c)) N i₀
      (ENNReal.measurable_ofReal.comp hΦ) hinvP,
    lintegral_boxConfig_eq (F := fun c => ENNReal.ofReal (-Φ c)) N i₀
      (ENNReal.measurable_ofReal.comp hΦ.neg) hinvN]
  congr 2
  · refine lintegral_congr fun c => ?_
    rw [ofReal_anchorR_mul_mul i₀ (Φ c) (overlap_ne_top N c)]
  · refine lintegral_congr fun c => ?_
    rw [show -(anchorR i₀ c * Φ c * (overlap N c).toReal) =
      anchorR i₀ c * (-Φ c) * (overlap N c).toReal by ring,
      ofReal_anchorR_mul_mul i₀ (-Φ c) (overlap_ne_top N c)]

/-- **Claim (4.82)** of the proof of Lemma 4.26: if `Φ` is
measurable and translation invariant and `𝟙_{[0,1]²}(x_{i₀}) Φ` is integrable, then
`(1/N) ∫_{(Λ²)^ι} Φ → ∫ 𝟙_{[0,1]²}(x_{i₀}) Φ`. -/
theorem tendsto_boxAverage [Nonempty ι] (i₀ : ι) {Φ : (ι → ℂ × ℂ) → ℝ}
    (hΦ : Measurable Φ) (hinv : TranslationInvariant Φ)
    (hint : Integrable (fun c => anchorR i₀ c * Φ c)) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∫ c in boxConfig ι N, Φ c) atTop
      (𝓝 (∫ c, anchorR i₀ c * Φ c)) := by
  have hov : ∀ N : ℕ, Measurable (overlap (ι := ι) N) := by
    intro N
    have hset : MeasurableSet {p : (ι → ℂ × ℂ) × ℂ | translate p.2 p.1 ∈ boxConfig ι N} :=
      (measurable_uncurry_translate.comp measurable_swap) (measurableSet_boxConfig N)
    exact measurable_measure_prodMk_left hset
  have h := tendsto_integral_of_dominated_convergence (fun c => ‖anchorR i₀ c * Φ c‖)
    (F := fun (N : ℕ) c => anchorR i₀ c * Φ c * ((overlap N c).toReal / N))
    (fun N => (((measurable_anchorR i₀).mul hΦ).mul
      ((hov N).ennreal_toReal.div_const _)).aestronglyMeasurable) hint.norm
    (fun N => Eventually.of_forall fun c => by
      rw [norm_mul, Real.norm_eq_abs ((overlap N c).toReal / N)]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [abs_of_nonneg (by positivity)]
      rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).eq_or_lt with h0 | h0
      · rw [← h0, div_zero]
        exact zero_le_one
      · rw [div_le_one h0]
        exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg N) (by simpa using overlap_le N c))
    (Eventually.of_forall fun c => by
      simpa using (tendsto_const_nhds (x := anchorR i₀ c * Φ c)).mul
        (tendsto_overlap_toReal_div c))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [(integral_boxConfig_eq N i₀ hΦ hinv hint).2, ← integral_const_mul]
  congr 1
  funext c
  ring

end Fintype

end Limits

end MultipoleBKT

end
