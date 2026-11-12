/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Gibbs.Activities
public import MultipoleBKT.Potential.BondBound
public import MultipoleBKT.Potential.DipoleConstant
public import MultipoleBKT.Appendix.MultipoleIntegral.TreeIntegral
public import MultipoleBKT.Multipole.Transport

/-!
# The multipole integral `I^0_{mult,∞}(S)` and its ingredients

See Appendix A,
(A.4) and Lemma A.3.
The definition includes the true-interaction model `(v, ∞, 0, ∅)` with
infinite cutoff. Its upper proof is assembled in `RouteOrdered/`.

* `multipoleIntegral χ N β λ M S = I^0_{mult,∞}(S) = ∫_{(Λ²)^S} 𝟙_{𝓑_S} ∏_{i<j} e^{-β v_ij} 𝟙_{𝒜_ij}
  ∏_i e^{β g_λ(x_i - y_i)} dx_i dy_i`.
* `multipolePartitionFunction_eq_multipoleIntegral`: the identity
  `I^0_{mult,∞}(S) = (N C_{β,λ})^{|S|} 𝖬_{β,λ}(S)` (A.4), as
  `𝖬_{β,λ}(S) = ((N C_{β,λ})⁻¹)^{|S|} I^0_{mult,∞}(S)`; `multipoleIntegral_eq_toReal_lintegral`,
  `lintegral_multipoleIntegrand_ne_top`: the integral as a finite Lebesgue integral.
* `linkSet`, `sub_mem_linkSet`, `volume_linkSet_le`: if the dipoles
  `(a + u, a)` and `(b + v, b)` (negative charges `a`, `b`, dipole vectors `u`, `v`) are linked,
  then `a - b` lies in a union of four discs of radius `M min(max(|u|, λ), max(|v|, λ))`, of total
  area at most `4π M² max(|u|, λ)²` (the bound on `B_ij` used in (A.11)).
* `prod_erase_sq_le_prod_rpow`: if `m_r` is the largest of the `k` positive numbers `m_c`, then
  `∏_{c ≠ r} m_c² ≤ ∏_c m_c^{2 - 2/k}` on a largest-radius sector. The connected proof uses
  the literal ordered integral first and uses this inequality only for numerical compatibility
  with the prescribed `upperConst`.
* `integrable_max_norm_rpow`, `integral_max_norm_rpow`: `∫_ℂ max(|w|, λ)^e dw = λ^{e+2} K_e` with
  `K_e = ∫_ℂ max(|w|, 1)^e dw < ∞` for `e < -2`; `exp_smearedKernel_le`,
  `lintegral_dipoleWeight_le`: `∫_ℂ max(|w|, λ)^a e^{β g_λ(w)} dw ≤ e^{β c_χ} K_{a-β} λ^{a-β+2}`
  for `a - β < -2`.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box logKernel)

variable {χ : ℂ → ℝ} {lam β M : ℝ} {N : ℕ}

/-! ### The multipole integral -/

/-- **The multipole integral** `I^0_{mult,∞}(S) = I_{mult,∞}(S; v, ∞, 0, ∅)` (equation (A.4), for the true interaction `v`,
`τ = ∞`, `L = 0`, `Z = ∅` and the cutoff `ε₀ = ∞`. Then `I_good^∅ = [N]`
and `e^{L r_i²/τ_i²} = 1`):
`∫_{(Λ²)^{|S|}} 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij} ∏_{i ∈ S} e^{β g_λ(x_i - y_i)} dx_i dy_i`.
The factor `𝟙_{𝓑_S} ∏_{i<j} e^{-β v_ij} 𝟙_{𝒜_ij}` is the integrand of the frozen
`multipolePartitionFunction` (`multipolePartitionFunctionIntegrand`). -/
noncomputable def multipoleIntegral (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ) (S : Finset ℕ) : ℝ :=
  ∫ c in Set.univ.pi (fun _ : S => box N ×ˢ box N),
    multipolePartitionFunctionIntegrand χ β lam M c *
      ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))

namespace MultipoleIntegral

/-- `∫ ∏ᵢ fᵢ(xᵢ) d(⊗ᵢ μᵢ) = ∏ᵢ ∫ fᵢ dμᵢ` for `x : ι → α`, `α` inhabited. -/
theorem lintegral_pi_prod_eq' {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    [MeasurableSpace α] (a : α) (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (f : ι → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → α, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i := by
  rw [lintegral_eq_lmarginal_univ (fun _ => a), lmarginal_prod_eq f hf]

end MultipoleIntegral

open MultipoleIntegral

/-- The finite powers of the dipole measure, as a density with respect to Lebesgue measure on
`(Λ²)^ι`. -/
theorem pi_dipoleMeasure_eq_withDensity (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => dipoleMeasure χ N β lam) =
      (volume.restrict (Set.univ.pi fun _ : ι => box N ×ˢ box N)).withDensity fun c =>
        ∏ i, ENNReal.ofReal ((N * dipoleNormalization χ N β lam)⁻¹ *
          Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) := by
  classical
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  have hd : Measurable fun p : ℂ × ℂ => ENNReal.ofReal ((N * dipoleNormalization χ N β lam)⁻¹ *
      Real.exp (β * smearedKernel χ lam (p.1 - p.2))) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_exp_smearedKernel_sub hχ hlam β).measurable.const_mul _)
  refine Measure.pi_eq (μ := fun _ : ι => dipoleMeasure χ N β lam) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    Measure.restrict_restrict (MeasurableSet.univ_pi hs), ← Set.pi_inter_distrib,
    volume_pi, Measure.restrict_pi_pi, lintegral_pi_prod_eq' ((0 : ℂ), (0 : ℂ))
      (fun i => (volume : Measure (ℂ × ℂ)).restrict (s i ∩ box N ×ˢ box N)) _ (fun _ => hd)]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold dipoleMeasure
  rw [withDensity_apply _ (hs i), Measure.restrict_restrict (hs i)]

/-- **The normalization identity** (equation (A.4), model `0`, `ε₀ = ∞`):
`𝖬_{β,λ}(S) = ((N C_{β,λ})⁻¹)^{|S|} I^0_{mult,∞}(S)`, for `λ > 0` and `N ≥ 1`. -/
theorem multipolePartitionFunction_eq_multipoleIntegral (hχ : IsMollifier χ) (hlam : 0 < lam)
    (β M : ℝ) (hN : 1 ≤ N) (S : Finset ℕ) :
    multipolePartitionFunction χ N β lam M S =
      ((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ ^ S.card * multipoleIntegral χ N β lam M S := by
  have hC := natCast_mul_dipoleNormalization_pos hχ hlam β hN
  have hd : Measurable fun c : S → ℂ × ℂ =>
      ∏ i, ENNReal.ofReal ((N * dipoleNormalization χ N β lam)⁻¹ *
        Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      (((continuous_exp_smearedKernel_sub hχ hlam β).measurable.comp
        (measurable_pi_apply i)).const_mul _)
  rw [multipolePartitionFunction_eq_integral, pi_dipoleMeasure_eq_withDensity hχ hlam β hN,
    integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall fun c => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top),
    multipoleIntegral, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_prod]
  have : ∀ i, (ENNReal.ofReal ((N * dipoleNormalization χ N β lam)⁻¹ *
      Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))).toReal =
      (N * dipoleNormalization χ N β lam)⁻¹ *
        Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) := fun i =>
    ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hC.le) (Real.exp_pos _).le)
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  ring

/-- The integrand of `multipoleIntegral` is nonnegative. -/
theorem multipoleIntegrand_nonneg {S : Finset ℕ} (c : S → ℂ × ℂ) :
    0 ≤ multipolePartitionFunctionIntegrand χ β lam M c *
      ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) :=
  mul_nonneg (multipolePartitionFunctionIntegrand_nonneg χ β lam M c)
    (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)

theorem measurable_multipoleIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ)
    {S : Finset ℕ} :
    Measurable fun c : S → ℂ × ℂ => multipolePartitionFunctionIntegrand χ β lam M c *
      ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) :=
  (measurable_multipolePartitionFunctionIntegrand hχ hlam β M).mul
    (Finset.measurable_prod _ fun i _ =>
      (continuous_exp_smearedKernel_sub hχ hlam β).measurable.comp (measurable_pi_apply i))

/-- `I^0_{mult,∞}(S)` as a Lebesgue integral. -/
theorem multipoleIntegral_eq_toReal_lintegral (hχ : IsMollifier χ) (hlam : 0 < lam)
    (N : ℕ) (β M : ℝ) (S : Finset ℕ) :
    multipoleIntegral χ N β lam M S =
      (∫⁻ c in Set.univ.pi (fun _ : S => box N ×ˢ box N),
        ENNReal.ofReal (multipolePartitionFunctionIntegrand χ β lam M c *
          ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall multipoleIntegrand_nonneg)
    (measurable_multipoleIntegrand hχ hlam β M).aestronglyMeasurable

/-- The Lebesgue integral defining `I^0_{mult,∞}(S)` is finite (the integrand is bounded on the
compact set `(Λ²)^S`). -/
theorem lintegral_multipoleIntegrand_ne_top (hχ : IsMollifier χ) (hlam : 0 < lam)
    (N : ℕ) (β M : ℝ) (S : Finset ℕ) :
    ∫⁻ c in Set.univ.pi (fun _ : S => box N ×ˢ box N),
      ENNReal.ofReal (multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) ≠ ⊤ := by
  obtain ⟨B₁, hB₁⟩ := exists_bound_multipolePartitionFunctionIntegrand (S := S) hχ hlam β M N
  obtain ⟨B₂, hB₂⟩ := (isCompact_box_prod N).exists_bound_of_continuousOn
    (continuous_exp_smearedKernel_sub hχ hlam β).continuousOn
  have hle : ∀ c ∈ Set.univ.pi (fun _ : S => box N ×ˢ box N),
      ENNReal.ofReal (multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) ≤
      ENNReal.ofReal (B₁ * B₂ ^ Fintype.card S) := by
    intro c hc
    rw [Set.mem_univ_pi] at hc
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hB₁ c hc
    have h2 : ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) ≤
        B₂ ^ Fintype.card S := by
      calc ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))
          ≤ ∏ _i : S, B₂ := Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i _ => by
            have := hB₂ (c i) (hc i)
            rwa [Real.norm_of_nonneg (Real.exp_pos _).le] at this
        _ = B₂ ^ Fintype.card S := by rw [Finset.prod_const, Finset.card_univ]
    have h0 := Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) =>
      (Real.exp_pos (β * smearedKernel χ lam ((c i).1 - (c i).2))).le
    calc _ ≤ |multipolePartitionFunctionIntegrand χ β lam M c| *
          ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ B₁ * B₂ ^ Fintype.card S := mul_le_mul h1 h2 h0 ((abs_nonneg _).trans h1)
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono measurable_const hle)
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_pi_box_prod_lt_top N).ne

/-! ### The geometry of a link -/

namespace MultipoleIntegral

/-- The relative positions `a - b` of the negative charges for which the dipoles `(a + u, a)` and
`(b + v, b)` can be linked: four closed discs of radius `M min(max(|u|, λ), max(|v|, λ))`. -/
def linkSet (M lam : ℝ) (u v : ℂ) : Set ℂ :=
  Metric.closedBall 0 (M * min (max ‖u‖ lam) (max ‖v‖ lam)) ∪
    Metric.closedBall (v - u) (M * min (max ‖u‖ lam) (max ‖v‖ lam)) ∪
    Metric.closedBall (-u) (M * min (max ‖u‖ lam) (max ‖v‖ lam)) ∪
    Metric.closedBall v (M * min (max ‖u‖ lam) (max ‖v‖ lam))

theorem measurableSet_linkSet (M lam : ℝ) (u v : ℂ) : MeasurableSet (linkSet M lam u v) :=
  ((measurableSet_closedBall.union measurableSet_closedBall).union measurableSet_closedBall).union
    measurableSet_closedBall

/-- If the dipoles `(a + u, a)` and `(b + v, b)` are linked, then `a - b ∈ linkSet M λ u v`. -/
theorem sub_mem_linkSet {a b u v : ℂ} (h : MultipoleLinked M lam (a + u, a) (b + v, b)) :
    a - b ∈ linkSet M lam u v := by
  unfold MultipoleLinked at h
  simp only [add_sub_cancel_left] at h
  set ρ := M * min (max ‖u‖ lam) (max ‖v‖ lam)
  simp only [linkSet, Set.mem_union, Metric.mem_closedBall, dist_eq_norm]
  rcases min_le_iff.1 h with h1 | h1 <;> rcases min_le_iff.1 h1 with h2 | h2
  · left; left; right
    rwa [show a - b - (v - u) = a + u - (b + v) by ring]
  · left; right
    rwa [show a - b - -u = a + u - b by ring]
  · right
    rwa [show a - b - v = a - (b + v) by ring]
  · left; left; left
    rwa [sub_zero]

/-- The area of `linkSet M λ u v` is at most `4π M² max(|u|, λ)²`, for `M ≥ 0` and `λ ≥ 0`. -/
theorem volume_linkSet_le (hM : 0 ≤ M) (hlam : 0 ≤ lam) (u v : ℂ) :
    volume (linkSet M lam u v) ≤
      ENNReal.ofReal (4 * Real.pi * (M * max ‖u‖ lam) ^ 2) := by
  set ρ := M * min (max ‖u‖ lam) (max ‖v‖ lam)
  have hρ0 : 0 ≤ ρ := mul_nonneg hM (le_min (le_max_of_le_right hlam) (le_max_of_le_right hlam))
  have hρ : ρ ≤ M * max ‖u‖ lam := mul_le_mul_of_nonneg_left (min_le_left _ _) hM
  have hball : ∀ z : ℂ, volume (Metric.closedBall z ρ) ≤
      ENNReal.ofReal (Real.pi * (M * max ‖u‖ lam) ^ 2) := by
    intro z
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hρ0, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_comm]
    gcongr
  calc volume (linkSet M lam u v)
      ≤ volume (Metric.closedBall (0 : ℂ) ρ) + volume (Metric.closedBall (v - u) ρ) +
          volume (Metric.closedBall (-u) ρ) + volume (Metric.closedBall v ρ) := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.pi * (M * max ‖u‖ lam) ^ 2) +
          ENNReal.ofReal (Real.pi * (M * max ‖u‖ lam) ^ 2) +
          ENNReal.ofReal (Real.pi * (M * max ‖u‖ lam) ^ 2) +
          ENNReal.ofReal (Real.pi * (M * max ‖u‖ lam) ^ 2) := by
        gcongr <;> exact hball _
    _ = ENNReal.ofReal (4 * Real.pi * (M * max ‖u‖ lam) ^ 2) := by
        have h0 : 0 ≤ Real.pi * (M * max ‖u‖ lam) ^ 2 := by positivity
        rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0,
          ← ENNReal.ofReal_add (by positivity) h0]
        congr 1
        ring

/-! ### Ordering the radii -/

/-- If `m_r` is the largest of the positive numbers `m_c`, `c ∈ ι`, `|ι| = k`, then
`∏_{c ≠ r} m_c² ≤ ∏_c m_c^{2 - 2/k}`. -/
theorem prod_erase_sq_le_prod_rpow {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (r : ι) (hr : ∀ i, m i ≤ m r) :
    ∏ c ∈ univ.erase r, m c ^ 2 ≤ ∏ c, m c ^ (2 - 2 / (Fintype.card ι : ℝ)) := by
  set k : ℝ := (Fintype.card ι : ℝ)
  have hk1 : (1 : ℝ) ≤ k := by
    have : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨r⟩
    simp only [k]
    exact_mod_cast this
  have hk0 : 0 < k := by linarith
  set a : ℝ := 2 - 2 / k
  set b : ℝ := 2 / k
  have hb0 : 0 ≤ b := by positivity
  have hsplit : ∀ c, m c ^ 2 = m c ^ a * m c ^ b := by
    intro c
    rw [← Real.rpow_add (hm c), show a + b = 2 by ring]
    norm_cast
  have hcard : ((univ.erase r).card : ℝ) = k - 1 := by
    rw [card_erase_of_mem (mem_univ r), card_univ, Nat.cast_sub (Fintype.card_pos_iff.2 ⟨r⟩)]
    simp [k]
  have hb : ∏ c ∈ univ.erase r, m c ^ b ≤ m r ^ a := by
    calc ∏ c ∈ univ.erase r, m c ^ b ≤ ∏ _c ∈ univ.erase r, m r ^ b :=
          prod_le_prod₀ (fun c _ => (Real.rpow_pos_of_pos (hm c) b).le)
            fun c _ => Real.rpow_le_rpow (hm c).le (hr c) hb0
      _ = m r ^ a := by
          rw [prod_const, ← Real.rpow_natCast, ← Real.rpow_mul (hm r).le, hcard]
          congr 1
          simp only [a, b]
          field_simp
  calc ∏ c ∈ univ.erase r, m c ^ 2
      = (∏ c ∈ univ.erase r, m c ^ a) * ∏ c ∈ univ.erase r, m c ^ b := by
        rw [← prod_mul_distrib]
        exact prod_congr rfl fun c _ => hsplit c
    _ ≤ (∏ c ∈ univ.erase r, m c ^ a) * m r ^ a :=
        mul_le_mul_of_nonneg_left hb (prod_nonneg fun c _ => (Real.rpow_pos_of_pos (hm c) a).le)
    _ = ∏ c, m c ^ a := prod_erase_mul _ _ (mem_univ r)

/-! ### The one-dipole integral -/

/-- `w ↦ max(|w|, λ)^e` is integrable on `ℂ` for `λ > 0` and `e < -2`. -/
theorem integrable_max_norm_rpow (hlam : 0 < lam) {e : ℝ} (he : e < -2) :
    Integrable fun w : ℂ => max ‖w‖ lam ^ e := by
  refine (integrable_fun_norm_complex_iff fun r : ℝ => max r lam ^ e).2 ?_
  have hc : Continuous fun r : ℝ => max r lam ^ e * r :=
    ((continuous_id.max continuous_const).rpow_const
      fun r => Or.inl (lt_max_of_lt_right hlam).ne').mul continuous_id
  rw [← Ioc_union_Ioi_eq_Ioi hlam.le]
  refine IntegrableOn.union ?_ ?_
  · exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · have h := integrableOn_Ioi_rpow_of_lt (by linarith : e + 1 < -1) hlam
    refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hr0 : 0 < r := hlam.trans hr
    show r ^ (e + 1) = max r lam ^ e * r
    rw [max_eq_left (le_of_lt hr), Real.rpow_add_one hr0.ne']

/-- Scaling: `∫_ℂ max(|w|, λ)^e dw = λ^{e+2} ∫_ℂ max(|w|, 1)^e dw` for `λ > 0`. -/
theorem integral_max_norm_rpow (hlam : 0 < lam) (e : ℝ) :
    ∫ w : ℂ, max ‖w‖ lam ^ e = lam ^ (e + 2) * ∫ w : ℂ, max ‖w‖ 1 ^ e := by
  have hcv := Measure.integral_comp_smul (volume : Measure ℂ) (fun w : ℂ => max ‖w‖ lam ^ e) lam
  rw [Complex.finrank_real_complex] at hcv
  have hpt : ∀ v : ℂ, max ‖lam • v‖ lam ^ e = lam ^ e * max ‖v‖ 1 ^ e := by
    intro v
    rw [norm_smul, Real.norm_of_nonneg hlam.le, ← Real.mul_rpow hlam.le
      (le_max_of_le_right zero_le_one), mul_max_of_nonneg _ _ hlam.le, mul_one]
  simp_rw [hpt] at hcv
  rw [integral_const_mul, smul_eq_mul, abs_of_pos (by positivity)] at hcv
  have h2 : lam ^ (e + 2) = lam ^ 2 * lam ^ e := by
    rw [Real.rpow_add hlam, Real.rpow_two, mul_comm]
  rw [h2, mul_assoc, hcv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- The constant `c_χ = max(∫ g dδ₀^{(1)}, 0)` of the bound `g_λ ≤ -log max(|w|, λ) + c_χ`. -/
noncomputable def kernelConst (χ : ℂ → ℝ) : ℝ :=
  max (∫ y, logKernel y ∂smearedCharge χ 0 1) 0

theorem kernelConst_nonneg (χ : ℂ → ℝ) : 0 ≤ kernelConst χ := le_max_right _ _

/-- `e^{β g_λ(w)} ≤ e^{β c_χ} max(|w|, λ)^{-β}` for `β ≥ 0`, `λ > 0`. -/
theorem exp_smearedKernel_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam) (w : ℂ) :
    Real.exp (β * smearedKernel χ lam w) ≤
      Real.exp (β * kernelConst χ) * max ‖w‖ lam ^ (-β) := by
  have hm : 0 < max ‖w‖ lam := lt_max_of_lt_right hlam
  have h := smearedKernel_le_neg_log_max hχ hlam w
  rw [Real.rpow_def_of_pos hm, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left h hβ
  unfold kernelConst
  nlinarith

/-- **The one-dipole integral.** For `β ≥ 0`, `λ > 0` and `a - β < -2`,
`∫_ℂ max(|w|, λ)^a e^{β g_λ(w)} dw ≤ e^{β c_χ} K_{a-β} λ^{a-β+2}` with
`K_e = ∫_ℂ max(|w|, 1)^e dw`. -/
theorem lintegral_dipoleWeight_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam) {a : ℝ}
    (ha : a - β < -2) :
    ∫⁻ w : ℂ, ENNReal.ofReal (max ‖w‖ lam ^ a * Real.exp (β * smearedKernel χ lam w)) ≤
      ENNReal.ofReal (Real.exp (β * kernelConst χ) * (∫ v : ℂ, max ‖v‖ 1 ^ (a - β)) *
        lam ^ (a - β + 2)) := by
  have hint := (integrable_max_norm_rpow hlam ha).const_mul (Real.exp (β * kernelConst χ))
  have hpt : ∀ w : ℂ, max ‖w‖ lam ^ a * Real.exp (β * smearedKernel χ lam w) ≤
      Real.exp (β * kernelConst χ) * max ‖w‖ lam ^ (a - β) := by
    intro w
    have hm : 0 < max ‖w‖ lam := lt_max_of_lt_right hlam
    calc max ‖w‖ lam ^ a * Real.exp (β * smearedKernel χ lam w)
        ≤ max ‖w‖ lam ^ a * (Real.exp (β * kernelConst χ) * max ‖w‖ lam ^ (-β)) :=
          mul_le_mul_of_nonneg_left (exp_smearedKernel_le hχ hβ hlam w)
            (Real.rpow_pos_of_pos hm a).le
      _ = Real.exp (β * kernelConst χ) * max ‖w‖ lam ^ (a - β) := by
          rw [sub_eq_add_neg, Real.rpow_add hm]
          ring
  calc ∫⁻ w : ℂ, ENNReal.ofReal (max ‖w‖ lam ^ a * Real.exp (β * smearedKernel χ lam w))
      ≤ ∫⁻ w : ℂ, ENNReal.ofReal (Real.exp (β * kernelConst χ) * max ‖w‖ lam ^ (a - β)) :=
        lintegral_mono fun w => ENNReal.ofReal_le_ofReal (hpt w)
    _ = ENNReal.ofReal (∫ w : ℂ, Real.exp (β * kernelConst χ) * max ‖w‖ lam ^ (a - β)) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w =>
          mul_nonneg (Real.exp_pos _).le
            (Real.rpow_pos_of_pos (lt_max_of_lt_right hlam) _).le)).symm
    _ = ENNReal.ofReal (Real.exp (β * kernelConst χ) * (∫ v : ℂ, max ‖v‖ 1 ^ (a - β)) *
          lam ^ (a - β + 2)) := by
        rw [integral_const_mul, integral_max_norm_rpow hlam]
        ring_nf

end MultipoleIntegral

end MultipoleBKT

end
