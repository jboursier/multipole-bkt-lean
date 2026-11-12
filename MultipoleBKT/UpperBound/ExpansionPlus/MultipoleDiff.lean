/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.FrozenModel
public import MultipoleBKT.Appendix.MultipoleIntegral.CutoffModel
public import MultipoleBKT.LowerBound.Hierarchical.Instances

/-!
# Proposition 5.19, eq. (5.68) for `𝖬^{+,Z}_{ε₀}`

The paper: Proposition 5.19,
eq. (5.68); proof.

The proof first compares with `𝖬^0_∞(S)`, then uses the triangle inequality as in
Proposition 5.19. Both `𝖬^{+,Z}_{ε₀}(S)` and `𝖬^0_{ε₀}(S)` carry the same normalization
`(N C_{β,λ,ε₀})^{-|S|}`, so the comparison at the same cutoff follows from

`|I^{+,Z}_{mult,ε₀}(S) - I^0_{mult,ε₀}(S)| ≤ |I^{+,Z}_{mult,ε₀}(S) - I^0_{mult,∞}(S)|
  + |I^0_{mult,∞}(S) - I^0_{mult,ε₀}(S)|`,

Lemma A.6 (`GeneralExpansion.multipoleIntegralPlus_sub_le`) for the first term and
eq. (A.47) (from eq. (A.46), `GeneralExpansion.lintegral_cutoff_tail_le`) for the second, then
`C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β}/2` (Lemma 4.12, `lem411_lower`).

* `zeroPartitionFunction_singleton_eq_cut`: the normalization identity
  `𝖬^0_{ε₀}(S) = (N C_{β,λ,ε₀})^{-|S|} I^0_{mult,ε₀}(S)`;
* `multipoleIntegralCut_sub_le_unif`: **eq. (A.47)**,
  `|I^0_{mult,ε₀}(S) - I^0_{mult,∞}(S)| ≤ C_{ε₀} N λ^{(2-β)|S|} R̄^{-2}`;
* `multipoleIntegralPlus_sub_cut_le`: `|I^{+,Z}_{mult,ε₀}(S) - I^0_{mult,ε₀}(S)| ≤ λ^{(2-β)k} (C_{ε₀} N R̄^{-2} + C ε₀^{α(β)k} |V_bad|)`, with `C` independent of `ε₀`;
* `plusPartitionFunction_sub_le`: **eq. (5.68) for `𝖬^{+,Z}_{ε₀}`**,
  `|𝖬^{+,Z}_{ε₀}(S) - 𝖬^0_{ε₀}(S)| ≤ N^{1-|S|} (C_{ε₀} R̄^{-2} + C ε₀^{α(β)|S|} |V_bad|/N)`.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace ExpansionPlus

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open Hierarchical MultipoleIntegral GeneralExpansion

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ : ℝ}

/-! ### The normalization identity for `𝖬^0_{ε₀}` -/

open scoped Classical in
/-- **The normalization identity** (equation (4.17)):
`𝖬^0_{ε₀}(S) = (N C_{β,λ,ε₀})^{-|S|} I^0_{mult,ε₀}(S)`, for `λ > 0`, `ε₀ > 0`, `N ≥ 1`. -/
theorem zeroPartitionFunction_singleton_eq_cut (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (S : Finset ℕ) :
    zeroPartitionFunction χ N p₀ β lam M ε₀ {S} =
      ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ S.card *
        multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S := by
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  set R := truncationScale p₀ β lam
  have hd : Measurable fun c : S → ℂ × ℂ =>
      ∏ i, ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      (((measurable_cutoffDensity hχ hlam β _).comp (measurable_pi_apply i)).const_mul _)
  rw [zeroPartitionFunction, Finset.prod_singleton, modelPartitionFunction,
    pi_cutoffDipoleMeasure_eq hχ hlam β hε₀ hN,
    integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall fun c => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top),
    multipoleIntegralCut, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_prod]
  have hti : ∀ i, (ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
      (closedBall (0 : ℂ) (ε₀ * R)).indicator
        (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2))).toReal =
      (N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2) := fun i =>
    ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hC.le) (cutoffDensity_nonneg β _ _))
  simp_rw [hti]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hdip : ∀ i : S, (closedBall (0 : ℂ) (ε₀ * R)).indicator
      (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2) =
      Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2) := by
    intro i
    by_cases hm : (c i).1 - (c i).2 ∈ closedBall (0 : ℂ) (ε₀ * R)
    · rw [indicator_of_mem hm, indicator_of_mem hm, Pi.one_apply, mul_one]
    · rw [indicator_of_notMem hm, indicator_of_notMem hm, mul_zero]
  rw [prod_congr rfl fun i _ => hdip i]
  simp only [Finset.prod_const_one, mul_one, multipolePartitionFunctionIntegrand]
  simp only [R]
  have key : ∀ a P Q D : ℝ, a * D * (P * Q) = a * (P * Q * D) := fun _ _ _ _ => by ring
  convert key _ _ _ _ using 3
  simp only [stablePairWeight]

/-! ### Eq. (A.47): the cutoff of the multipole integral -/

open scoped Classical in
/-- The pointwise bound of Step 3 of Lemma A.6: on `(Λ²)^S`, the `v`-integrand without and with
the length cutoff `h` differ by at most `W^{k²} ∑_{i₀} 𝟙_{𝓑} ∏_i e^{β g_λ(r_i)} 𝟙_{r_{i₀} > h}`. -/
theorem abs_multipoleIntegrand_sub_cut_le {W : ℝ} (hW : 1 ≤ W)
    (hbond : ∀ d e : ℂ × ℂ, stablePairWeight χ β lam d e ≤ W) (h : ℝ) {S : Finset ℕ}
    {c : S → ℂ × ℂ} (hc : c ∈ Set.univ.pi fun _ : S => box N ×ˢ box N) :
    ENNReal.ofReal |multipolePartitionFunctionIntegrand χ β lam M c *
          ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
            (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) -
        multipolePartitionFunctionIntegrand χ β lam M c *
          ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))| ≤
      ENNReal.ofReal (W ^ (S.card * S.card)) *
        ∑ i₀ : S, (Set.univ.pi fun _ : S => box N ×ˢ box N).indicator
            (fun c => connInd M lam c *
              ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
          {u : ℂ | h < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2) := by
  classical
  set m := multipolePartitionFunctionIntegrand χ β lam M c with hm_def
  have hm0 : 0 ≤ m := multipolePartitionFunctionIntegrand_nonneg χ β lam M c
  have hE0 : 0 ≤ ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) :=
    prod_nonneg fun _ _ => (Real.exp_pos _).le
  by_cases hall : ∀ i : S, (c i).1 - (c i).2 ∈ Metric.closedBall (0 : ℂ) h
  · have : ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
        (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) =
        ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) :=
      prod_congr rfl fun i _ => by rw [indicator_of_mem (hall i), Pi.one_apply, mul_one]
    rw [this, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  simp only [not_forall] at hall
  obtain ⟨i₀, hi₀⟩ := hall
  have hzero : ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
      (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) = 0 :=
    prod_eq_zero (mem_univ i₀) (by rw [indicator_of_notMem hi₀, mul_zero])
  rw [hzero, mul_zero, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg hm0 hE0)]
  have hgt : h < ‖(c i₀).1 - (c i₀).2‖ := by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hi₀
    exact hi₀
  have hmle := multipolePartitionFunctionIntegrand_le (M := M) hW hbond c
  refine le_trans ?_ (mul_le_mul' le_rfl (Finset.single_le_sum (f := fun i₀ : S =>
    (Set.univ.pi fun _ : S => box N ×ˢ box N).indicator
      (fun c => connInd M lam c *
        ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
      {u : ℂ | h < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2)) (fun _ _ => zero_le) (mem_univ i₀)))
  rw [indicator_of_mem hc, indicator_of_mem (show (c i₀).1 - (c i₀).2 ∈ {u : ℂ | h < ‖u‖} from hgt),
    Pi.one_apply, mul_one]
  have hW0 : 0 ≤ W ^ (S.card * S.card) := pow_nonneg (zero_le_one.trans hW) _
  refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hmle hE0)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hW0, mul_assoc,
    ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le]
  congr 2
  unfold connInd
  split_ifs <;> simp

/-- The bond bound: `e^{-β v_ij} 𝟙_{𝒜_ij} ≤ e^{β C_b}` for `β ≥ 0`, `C_b` the constant of
`neg_le_dipoleInteraction`. -/
theorem stablePairWeight_le_exp (hβ : 0 ≤ β) {Cb : ℝ}
    (hCb : ∀ d e : ℂ × ℂ, IsStableDipolePair d e → -Cb ≤ dipoleInteraction χ lam d e)
    (d e : ℂ × ℂ) : stablePairWeight χ β lam d e ≤ Real.exp (β * Cb) := by
  unfold stablePairWeight
  split_ifs with h
  · refine Real.exp_le_exp.2 ?_
    have := hCb d e h
    nlinarith
  · exact (Real.exp_pos _).le

/-- **Eq. (A.47)** (proof of Lemma A.6, from eq. (A.46)): for `β > 2`,
`1 ≤ k ≤ p*(β)`, `M ≥ 0` and `p₀`, there is `C > 0` (depending on `χ, β, M, k, p₀`) such that for
`ε₀ > 0`, `0 < λ ≤ 1` with `λ ≤ ε₀ R̄`, every `N` and every `S` with `|S| = k`,
`|I^0_{mult,ε₀}(S) - I^0_{mult,∞}(S)| ≤ C ε₀^x N λ^{(2-β)k} R̄^{-2}`, `x = tailExp p₀ β k`. -/
theorem multipoleIntegralCut_sub_le_unif (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (p₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε₀ lam : ℝ), 0 < ε₀ → 0 < lam → lam ≤ 1 →
      lam ≤ ε₀ * truncationScale p₀ β lam → ∀ (N : ℕ) (S : Finset ℕ), S.card = k →
        |multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S -
            multipoleIntegral χ N β lam M S| ≤
          C * ε₀ ^ tailExp p₀ β k * N *
            (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  classical
  have hβ0 : 0 ≤ β := by linarith
  have hkp' : (4 - β) * k - 2 < 0 :=
    (Appendix.transitionBeta_lt_iff hk β).1 ((Appendix.le_pStar_iff hk).1 hkp)
  obtain ⟨Cb, hCb0, hCb⟩ := neg_le_dipoleInteraction hχ
  obtain ⟨CT, hCT0, htail⟩ := lintegral_cutoff_tail_le (M := M) hχ hβ hk hkp' hM p₀
  set W := Real.exp (β * Cb)
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg hβ0 hCb0)
  refine ⟨W ^ (k * k) * k * CT, by positivity, fun ε₀ lam hε₀ hlam hlam1 hlh N S hS => ?_⟩
  set h := ε₀ * truncationScale p₀ β lam
  set T : ℝ := lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hT : 0 ≤ T := by positivity
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  set P : Set (S → ℂ × ℂ) := Set.univ.pi fun _ : S => box N ×ˢ box N
  set F₂ : S → (S → ℂ × ℂ) → ℝ≥0∞ := fun i₀ c => P.indicator (fun c => connInd M lam c *
      ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
    {u : ℂ | h < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2)
  have hF₂m : ∀ i₀, Measurable (F₂ i₀) := by
    intro i₀
    refine (Measurable.indicator ((measurable_connInd M lam).mul
      (Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp ((measurable_exp_smearedKernel hχ hlam β).comp
        ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd))))
      (measurableSet_pi_box_prod N)).mul ?_
    exact (measurable_one.indicator (measurableSet_lt measurable_const measurable_norm)).comp
      ((measurable_pi_apply i₀).fst.sub (measurable_pi_apply i₀).snd)
  have hlint : ∫⁻ c in P, ENNReal.ofReal |multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
          (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) -
      multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))| ≤
      ENNReal.ofReal (W ^ (k * k) * k * CT * ε₀ ^ tailExp p₀ β k * N * T) := by
    calc _ ≤ ∫⁻ c in P, ENNReal.ofReal (W ^ (k * k)) * ∑ i₀, F₂ i₀ c :=
          setLIntegral_mono' (measurableSet_pi_box_prod N) fun c hc => by
            have := abs_multipoleIntegrand_sub_cut_le (M := M) hW
              (stablePairWeight_le_exp hβ0 (hCb lam hlam)) h hc
            rw [hS] at this
            exact this
      _ ≤ ∫⁻ c, ENNReal.ofReal (W ^ (k * k)) * ∑ i₀, F₂ i₀ c := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (W ^ (k * k)) * ∑ i₀, ∫⁻ c, F₂ i₀ c := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_finsetSum _ fun i₀ _ => hF₂m i₀]
      _ ≤ ENNReal.ofReal (W ^ (k * k)) *
            ∑ _i₀ : S, ENNReal.ofReal (CT * ε₀ ^ tailExp p₀ β k * N * T) :=
          mul_le_mul' le_rfl (sum_le_sum fun i₀ _ => htail ε₀ lam hε₀ hlam hlam1 hlh N S hS i₀)
      _ = ENNReal.ofReal (W ^ (k * k) * k * CT * ε₀ ^ tailExp p₀ β k * N * T) := by
          rw [sum_const, card_univ, hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hmain := abs_setIntegral_sub_le (μ := volume) (P := P)
    (measurable_cutIntegrand hχ hlam β M h) (integrableOn_multipoleIntegrand hχ hlam N S)
    (by positivity) hlint
  exact hmain.2.trans (le_of_eq (by simp only [T]))

/-! ### `I^{+,Z}_{mult,ε₀}` versus `I^0_{mult,ε₀}` -/

/-- **`|I^{+,Z}_{mult,ε₀}(S) - I^0_{mult,ε₀}(S)|`** (Lemma A.6, with eq. (A.47)): for
`1 ≤ k ≤ p*(β)`, `M ≥ 0`, `L`, `p₀`, there is `C > 0` (depending on `χ, β, M, L, k, p₀`, not on
`ε₀`) such that for every `ε₀ ∈ (0, 1]` there is `C_{ε₀} > 0` with
`|I^{+,Z}_{mult,ε₀}(S) - I^0_{mult,ε₀}(S)| ≤ λ^{(2-β)k} (C_{ε₀} N R̄^{-2} + C ε₀^{α(β)k} |V_bad|)`
for all `λ ∈ (0, ε₀]`, `N`, frozen configurations `(V, Z)` (when `3^{p(β)} ≤ M`) and `|S| = k`. -/
theorem multipoleIntegralPlus_sub_cut_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (L : ℝ) (p₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ∃ Cε : ℝ, 0 < Cε ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ ε₀ → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ (N : ℕ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ S : Finset ℕ, S.card = k →
        |multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S -
            multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S| ≤
          lam ^ ((2 - β) * k) * (Cε * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * ε₀ ^ (alphaExponent β * k) * V.card) := by
  obtain ⟨C, hC, hA7⟩ := multipoleIntegralPlus_sub_le (χ := χ) hχ hβ hk hkp hM L p₀
  obtain ⟨C₂, hC₂, hcut⟩ := multipoleIntegralCut_sub_le_unif (χ := χ) hχ hβ hk hkp hM p₀
  refine ⟨C, hC, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨Cε, hCε, h7⟩ := hA7 ε₀ hε₀ hε₁
  refine ⟨Cε + C₂ * ε₀ ^ tailExp p₀ β k, by positivity,
    fun lam hlam hlε hM3 N V Z hV S hS => ?_⟩
  have hlam1 : lam ≤ 1 := hlε.trans hε₁
  have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
  have hlh : lam ≤ ε₀ * truncationScale p₀ β lam :=
    hlε.trans (le_mul_of_one_le_right hε₀.le hR1)
  have h1 := h7 lam hlam hlε hM3 N V Z hV S hS
  have h2 := hcut ε₀ lam hε₀ hlam hlam1 hlh N S hS
  calc _ ≤ |multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S - multipoleIntegral χ N β lam M S| +
        |multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S -
          multipoleIntegral χ N β lam M S| := by
        rw [abs_sub_comm (multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S)]
        exact abs_sub_le _ _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-! ### Eq. (5.68) for `𝖬^{+,Z}_{ε₀}` -/

/-- The scaling of the normalization: if `C_n ≥ (Z/2) λ^{2-β}`, `N > 0`, `X ≥ 0`, then
`(N C_n)^{-k} λ^{(2-β)k} X ≤ (2/Z)^k X / N^k`. -/
theorem normalization_scaling_le {Cn Zc X : ℝ} {N : ℝ} (hN : 0 < N) (hlam : 0 < lam)
    (hZ : 0 < Zc) (hCn : 1 / 2 * Zc * lam ^ (2 - β) ≤ Cn) (hX : 0 ≤ X) (k : ℕ) :
    (N * Cn)⁻¹ ^ k * (lam ^ ((2 - β) * k) * X) ≤ (2 / Zc) ^ k * X / N ^ k := by
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hD : 0 < N * (1 / 2 * Zc * lam ^ (2 - β)) := by positivity
  have hA : (N * Cn)⁻¹ ≤ (N * (1 / 2 * Zc * lam ^ (2 - β)))⁻¹ :=
    inv_anti₀ hD (mul_le_mul_of_nonneg_left hCn hN.le)
  have hA0 : 0 ≤ (N * Cn)⁻¹ := inv_nonneg.2 (hD.le.trans (mul_le_mul_of_nonneg_left hCn hN.le))
  have hΛ : lam ^ ((2 - β) * (k : ℝ)) = (lam ^ (2 - β)) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
  calc (N * Cn)⁻¹ ^ k * (lam ^ ((2 - β) * k) * X)
      ≤ (N * (1 / 2 * Zc * lam ^ (2 - β)))⁻¹ ^ k * (lam ^ ((2 - β) * k) * X) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA0 hA k) (by positivity)
    _ = (2 / Zc) ^ k * X / N ^ k := by
        rw [hΛ, inv_pow, mul_pow, mul_pow]
        field_simp
        rw [mul_comm _ X, mul_assoc, ← mul_pow, show Zc / 2 * (2 / Zc) = 1 by field_simp, one_pow,
          mul_one]

/-- **Eq. (5.68) for `𝖬^{+,Z}_{ε₀}`, against `𝖬^0_{ε₀}`** (Proposition 5.19, proof, with the comparison made at the same cutoff, see the module docstring): for
`1 ≤ k ≤ p*(β)`, `M ≥ 0`, `L`, `p₀`, there is `C > 0` (depending on `χ, β, M, L, k, p₀`, not on
`ε₀`) such that for every `ε₀ ∈ (0, 1)` there are `C_{ε₀} > 0` and `λ₀ > 0` such that for every
`λ ∈ (0, λ₀)` there is `N₀` with
`|𝖬^{+,Z}_{ε₀}(S) - 𝖬^0_{ε₀}(S)| ≤ (C_{ε₀} R̄^{-2} + C ε₀^{α(β)k} |V_bad|/N) / N^{k-1}`
for `N ≥ N₀`, every frozen configuration `(V, Z)` (when `3^{p(β)} ≤ M`) and `|S| = k`. -/
theorem plusPartitionFunction_sub_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (L : ℝ) (p₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ S : Finset ℕ, S.card = k →
        |plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
          (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / (N : ℝ) ^ (k - 1) := by
  obtain ⟨C, hC, hI⟩ := multipoleIntegralPlus_sub_cut_le (χ := χ) hχ hβ hk hkp hM L p₀
  set Zc := dipoleConstant χ β
  have hZ : 0 < Zc := dipoleConstant_pos hχ hβ
  refine ⟨(2 / Zc) ^ k * C, by positivity, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨Cε, hCε, hIε⟩ := hI ε₀ hε₀ hε₁.le
  obtain ⟨laml, hlaml, hlow⟩ := lem411_lower hχ hβ hε₀
  refine ⟨(2 / Zc) ^ k * Cε, by positivity, min laml ε₀, lt_min hlaml hε₀,
    fun lam hlam hlt => ?_⟩
  have hltl : lam < laml := hlt.trans_le (min_le_left _ _)
  have hlε : lam ≤ ε₀ := (hlt.trans_le (min_le_right _ _)).le
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hlow p₀ lam hlam hltl)
  refine ⟨max N₁ 1, fun N hN hM3 V Z hV S hS => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hCN := hN₁ N (le_trans (le_max_left _ _) hN)
  have hε0 : 0 < ε₀ := hε₀
  rw [plusPartitionFunction_eq_multipoleIntegralPlus hχ hlam hε₀ hN1 S,
    zeroPartitionFunction_singleton_eq_cut hχ hlam hε₀ hN1 S, ← mul_sub, abs_mul,
    abs_of_nonneg (pow_nonneg (inv_nonneg.2
      (natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN1).le) _), hS]
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set X : ℝ := Cε * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
    C * ε₀ ^ (alphaExponent β * k) * V.card
  have hX : 0 ≤ X := by positivity
  have hA0 : 0 ≤ ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ k :=
    pow_nonneg (inv_nonneg.2
      (natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN1).le) _
  calc ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ k *
        |multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S -
          multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S|
      ≤ ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ k *
          (lam ^ ((2 - β) * k) * X) :=
        mul_le_mul_of_nonneg_left (hIε lam hlam hlε hM3 N V Z hV S hS) hA0
    _ ≤ (2 / Zc) ^ k * X / (N : ℝ) ^ k := normalization_scaling_le hNpos hlam hZ hCN hX k
    _ = _ := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]
        simp only [X]
        field_simp
        ring

end ExpansionPlus

end UpperBound

end MultipoleBKT

end
