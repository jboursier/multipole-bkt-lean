/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RootBound
import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.WeightedRoot
import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.SquareMoment
public import MultipoleBKT.Appendix.GeneralExpansion.Pointwise
public import MultipoleBKT.Appendix.MultipoleIntegral.MinusModel
import TwoComponentCoulomb.Gibbs.Basic

/-!
# The screened multipole error

See Lemma A.6, with empty frozen data. The pointwise expansion bounds the
short-dipole defect by `C ∑ r_i²/h²`. The actual-tree position integration
leaves the cut square-weighted radial moment. Logarithmic integration evaluates that moment below,
at and above four. Only then is it compared with the normalization retained
by `cut_power_le`. The long-dipole term uses the three ordered cutoff tails.
The same argument includes a singleton.
-/

@[expose] public section

namespace MultipoleBKT

namespace GeneralExpansion

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral

variable {χ : ℂ → ℝ} {β M lam : ℝ}

/-! ### Plumbing -/

/-- If `∫_P |f - g| ≤ B` (as a lower integral), `f` is measurable and `g` integrable on `P`,
then `f` is integrable on `P` and `|∫_P f - ∫_P g| ≤ B`. -/
theorem abs_setIntegral_sub_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {P : Set X}
    {f g : X → ℝ} (hfm : Measurable f) (hg : IntegrableOn g P μ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ x in P, ENNReal.ofReal |f x - g x| ∂μ ≤ ENNReal.ofReal B) :
    IntegrableOn f P μ ∧ |∫ x in P, f x ∂μ - ∫ x in P, g x ∂μ| ≤ B := by
  have hint : IntegrableOn (fun x => f x - g x) P μ := by
    refine ⟨hfm.aestronglyMeasurable.sub hg.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs]
    exact h.trans_lt ENNReal.ofReal_lt_top
  have hf : IntegrableOn f P μ :=
    (hint.add hg).congr (Filter.Eventually.of_forall fun x => by simp)
  refine ⟨hf, ?_⟩
  rw [← integral_sub hf hg]
  refine abs_integral_le_integral_abs.trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (hint.aestronglyMeasurable.norm.congr (Filter.Eventually.of_forall fun x => by
      simp [Real.norm_eq_abs]))]
  exact ENNReal.toReal_le_of_le_ofReal hB h

/-- `I^0_{mult,∞}` has an integrable integrand on `(Λ²)^S`. -/
theorem integrableOn_multipoleIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (N : ℕ)
    (S : Finset ℕ) :
    IntegrableOn (fun c : S → ℂ × ℂ => multipolePartitionFunctionIntegrand χ β lam M c *
      ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))
      (Set.univ.pi fun _ : S => box N ×ˢ box N) := by
  refine ⟨(measurable_multipoleIntegrand hχ hlam β M).aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs]
  have := lintegral_multipoleIntegrand_ne_top (χ := χ) hχ hlam N β M S
  refine lt_of_le_of_lt (le_of_eq ?_) this.lt_top
  refine lintegral_congr fun c => ?_
  rw [abs_of_nonneg (multipoleIntegrand_nonneg c)]

/-! ### Step 1: the pointwise expansion -/

/-- The constant of Step 1 for the model `(ṽ, τ̃)`: with `W = e^{β(C_b + C₁/64)}`,
`W^{k²} (e^{k|L|} (2k K₁ + K₂) + 1)`, `K₁ = W β C₁/128`, `K₂ = e^{|L|} |L|`. -/
noncomputable def minusK (β L Cb C₁ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (β * (Cb + C₁ / 64)) ^ (k * k) *
    (Real.exp |L| ^ k * (2 * k * (Real.exp (β * (Cb + C₁ / 64)) * β * C₁ / 128) +
      Real.exp |L| * |L|) + 1)

theorem minusK_nonneg {β L Cb C₁ : ℝ} (hβ : 0 ≤ β) (hC₁ : 0 ≤ C₁) (k : ℕ) :
    0 ≤ minusK β L Cb C₁ k := by
  unfold minusK
  positivity

open scoped Classical in
/-- **Step 1 for the model `(ṽ, τ̃)`**: for a configuration `c ∈ (Λ²)^S`, with
`h = ε₀ R`, `C_b` the bond bound (`v_ij ≥ -C_b` on `𝒜_ij`) and `C₁` the constant of Lemma 3.10,
`|ṽ-integrand - v-integrand| ≤ K (∑_{i₀} 𝟙_{𝓑} ∏_i e^{β g_λ(r_i)} 𝟙_{r_i ≤ h} r_{i₀}²/h²
+ ∑_{i₀} 𝟙_{𝓑} ∏_i e^{β g_λ(r_i)} 𝟙_{r_{i₀} > h})`, `K = minusK`. -/
theorem minus_pointwise_le (hβ : 0 ≤ β) (hlam : 0 < lam) {ε₀ R L : ℝ}
    (hlh : lam ≤ ε₀ * R) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hCb : ∀ d e : ℂ × ℂ, IsStableDipolePair d e → -Cb ≤ dipoleInteraction χ lam d e)
    {C₁ : ℝ} (hC₁0 : 0 < C₁)
    (hC₁ : ∀ d e : ℂ × ℂ, 8 * max ‖d.2 - d.1‖ lam ≤ 8 * ε₀ * R →
      8 * max ‖e.2 - e.1‖ lam ≤ 8 * ε₀ * R →
      |screenedInteraction χ lam (8 * ε₀ * R) d e - dipoleInteraction χ lam d e| ≤
        C₁ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / (8 * ε₀ * R) ^ 2)
    {N : ℕ} {S : Finset ℕ} {c : S → ℂ × ℂ}
    (hc : c ∈ Set.univ.pi fun _ : S => box N ×ˢ box N) :
    ENNReal.ofReal |minusIntegrand χ β lam M L ε₀ R c -
        multipolePartitionFunctionIntegrand χ β lam M c *
          ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))| ≤
      ENNReal.ofReal (minusK β L Cb C₁ S.card) *
        (∑ i₀ : S, connInd M lam c *
            ((∏ i, cutWeight χ β lam (ε₀ * R) ((c i).1 - (c i).2)) *
              ((box N).indicator (1 : ℂ → ℝ≥0∞) (c i₀).2 *
                ENNReal.ofReal (‖(c i₀).1 - (c i₀).2‖ ^ 2 / (ε₀ * R) ^ 2))) +
          ∑ i₀ : S, (Set.univ.pi fun _ : S => box N ×ˢ box N).indicator
              (fun c => connInd M lam c *
                ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
            {u : ℂ | ε₀ * R < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2)) := by
  set h := ε₀ * R with hh_def
  have hh0 : 0 < h := hlam.trans_le hlh
  set k := S.card
  have hcard : Fintype.card S = k := Fintype.card_coe S
  set W := Real.exp (β * (Cb + C₁ / 64))
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg hβ (by positivity))
  set Ψ := Real.exp |L|
  have hΨ : 1 ≤ Ψ := Real.one_le_exp (abs_nonneg L)
  set K₁ := W * β * C₁ / 128
  have hK₁ : 0 ≤ K₁ := by positivity
  set K₂ := Ψ * |L|
  set E : ℝ := ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))
  have hE0 : 0 ≤ E := prod_nonneg fun i _ => (Real.exp_pos _).le
  set RHS := ∑ i₀ : S, connInd M lam c *
            ((∏ i, cutWeight χ β lam (ε₀ * R) ((c i).1 - (c i).2)) *
              ((box N).indicator (1 : ℂ → ℝ≥0∞) (c i₀).2 *
                ENNReal.ofReal (‖(c i₀).1 - (c i₀).2‖ ^ 2 / (ε₀ * R) ^ 2))) +
          ∑ i₀ : S, (Set.univ.pi fun _ : S => box N ×ˢ box N).indicator
              (fun c => connInd M lam c *
                ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
            {u : ℂ | ε₀ * R < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2)
  -- the stable-pair weights are bounded by `W`
  have hstab : ∀ d e : ℂ × ℂ, stablePairWeight χ β lam d e ≤ W := by
    intro d e
    unfold stablePairWeight
    split_ifs with hst
    · exact Real.exp_le_exp.2 (by nlinarith [hCb d e hst])
    · linarith
  have hstab0 : ∀ d e : ℂ × ℂ, 0 ≤ stablePairWeight χ β lam d e := fun d e => by
    unfold stablePairWeight; split_ifs <;> positivity
  have hPb : multipolePartitionFunctionIntegrand χ β lam M c ≤ W ^ (k * k) := by
    have h1 := multipolePartitionFunctionIntegrand_le (M := M) hW hstab c
    refine h1.trans ?_
    have : (if (SimpleGraph.fromRel fun i j : S =>
        MultipoleLinked M lam (c i) (c j)).Connected then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    calc W ^ (S.card * S.card) * (if (SimpleGraph.fromRel fun i j : S =>
          MultipoleLinked M lam (c i) (c j)).Connected then (1 : ℝ) else 0)
        ≤ W ^ (S.card * S.card) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = W ^ (k * k) := mul_one _
  have hRHS0 : 0 ≤ RHS := zero_le
  have hmK : minusK β L Cb C₁ k = W ^ (k * k) * (Ψ ^ k * (2 * k * K₁ + K₂) + 1) := rfl
  have hWk : 0 ≤ W ^ (k * k) := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  have hX : 0 ≤ Ψ ^ k * (2 * k * K₁ + K₂) := by positivity
  have hK : W ^ (k * k) * Ψ ^ k * (2 * k * K₁ + K₂) ≤ minusK β L Cb C₁ k := by
    rw [hmK]
    nlinarith
  have hKW : W ^ (k * k) ≤ minusK β L Cb C₁ k := by
    rw [hmK]
    nlinarith
  by_cases hconn : (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
  · have hci : connInd M lam c = 1 := by unfold connInd; simp only [hconn, ↓reduceIte]
    by_cases hall : ∀ i : S, ‖(c i).1 - (c i).2‖ ≤ h
    · -- all dipoles are shorter than the cutoff: the expansion
      have hmem : ∀ i : S, (c i).1 - (c i).2 ∈ closedBall (0 : ℂ) (ε₀ * R) := fun i => by
        rw [mem_closedBall_zero_iff]; exact hall i
      set a : S → S → ℝ := fun i j =>
        if i < j then minusPairWeight χ β lam ε₀ R (c i) (c j) else 1 with ha_def
      set b : S → S → ℝ := fun i j => if i < j then stablePairWeight χ β lam (c i) (c j) else 1
        with hb_def
      set ψ : S → ℝ := fun i => Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2)
        with hψ_def
      set ρ : S → ℝ := fun i => ‖(c i).1 - (c i).2‖ ^ 2 / h ^ 2 with hρ_def
      have hρ0 : ∀ i, 0 ≤ ρ i := fun i => by rw [hρ_def]; positivity
      have hρ1 : ∀ i, ρ i ≤ 1 := fun i => by
        rw [hρ_def]
        rw [div_le_one (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hall i) 2
      have hdip : ∏ i : S, (Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
          Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
            (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2)) = (∏ i, ψ i) * E := by
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun i _ => ?_
        rw [indicator_of_mem (hmem i), Pi.one_apply, mul_one]
      have hrwm : minusIntegrand χ β lam M L ε₀ R c = (∏ i, ∏ j, a i j) * (∏ i, ψ i) * E := by
        unfold minusIntegrand
        simp only [hconn, ↓reduceIte, one_mul]
        rw [hdip, ha_def]
        ring
      have hrwi : multipolePartitionFunctionIntegrand χ β lam M c = ∏ i, ∏ j, b i j := by
        unfold multipolePartitionFunctionIntegrand
        simp only [hconn, ↓reduceIte, one_mul, hb_def]
      -- the interaction difference
      have hv : ∀ i j : S, IsStableDipolePair (c i) (c j) →
          |upperBoundInteraction χ lam ε₀ R (c i) (c j) - dipoleInteraction χ lam (c i) (c j)| ≤
            C₁ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / (64 * h ^ 2) := by
        intro i j _
        have h8 : ∀ l : S, 8 * max ‖(c l).2 - (c l).1‖ lam ≤ 8 * ε₀ * R := fun l => by
          rw [norm_sub_rev, show 8 * ε₀ * R = 8 * h by rw [hh_def]; ring]
          exact mul_le_mul_of_nonneg_left (max_le (hall l) hlh) (by norm_num)
        have := hC₁ (c i) (c j) (h8 i) (h8 j)
        rw [show (8 * ε₀ * R) ^ 2 = 64 * h ^ 2 by rw [hh_def]; ring] at this
        exact this
      have hvC : ∀ i j : S, IsStableDipolePair (c i) (c j) →
          |upperBoundInteraction χ lam ε₀ R (c i) (c j) - dipoleInteraction χ lam (c i) (c j)| ≤
            C₁ / 64 := by
        intro i j hst
        refine (hv i j hst).trans ?_
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have := mul_le_mul (hall i) (hall j) (norm_nonneg _) hh0.le
        nlinarith
      have hab : ∀ i j, |a i j - b i j| ≤ K₁ * (ρ i + ρ j) := by
        intro i j
        rw [ha_def, hb_def]
        by_cases hij : i < j
        · simp only [hij, ↓reduceIte]
          unfold minusPairWeight stablePairWeight
          by_cases hst : IsStableDipolePair (c i) (c j)
          · simp only [hst, ↓reduceIte]
            refine (abs_exp_sub_exp_le _ _).trans ?_
            have h1 := hv i j hst
            have h2 := hvC i j hst
            have h3 := hCb (c i) (c j) hst
            rw [abs_le] at h2
            have hmax : max (-β * upperBoundInteraction χ lam ε₀ R (c i) (c j))
                (-β * dipoleInteraction χ lam (c i) (c j)) ≤ β * (Cb + C₁ / 64) :=
              max_le (by nlinarith) (by nlinarith)
            have hexp : Real.exp (max (-β * upperBoundInteraction χ lam ε₀ R (c i) (c j))
                (-β * dipoleInteraction χ lam (c i) (c j))) ≤ W := Real.exp_le_exp.2 hmax
            have hdiff : |-β * upperBoundInteraction χ lam ε₀ R (c i) (c j) -
                -β * dipoleInteraction χ lam (c i) (c j)| ≤
                β * (C₁ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / (64 * h ^ 2)) := by
              rw [show -β * upperBoundInteraction χ lam ε₀ R (c i) (c j) -
                -β * dipoleInteraction χ lam (c i) (c j) =
                -(β * (upperBoundInteraction χ lam ε₀ R (c i) (c j) -
                  dipoleInteraction χ lam (c i) (c j))) by ring, abs_neg, abs_mul, abs_of_nonneg hβ]
              exact mul_le_mul_of_nonneg_left h1 hβ
            have hρij : C₁ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / (64 * h ^ 2) ≤
                C₁ * (ρ i + ρ j) / 128 := by
              rw [hρ_def]
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]
              have hsq := two_mul_le_add_sq ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖
              have hh2 : 0 < h ^ 2 := by positivity
              field_simp
              nlinarith
            calc Real.exp (max (-β * upperBoundInteraction χ lam ε₀ R (c i) (c j))
                  (-β * dipoleInteraction χ lam (c i) (c j))) *
                  |-β * upperBoundInteraction χ lam ε₀ R (c i) (c j) -
                    -β * dipoleInteraction χ lam (c i) (c j)|
                ≤ W * (β * (C₁ * (ρ i + ρ j) / 128)) :=
                  mul_le_mul hexp (hdiff.trans (mul_le_mul_of_nonneg_left hρij hβ))
                    (abs_nonneg _) (by positivity)
              _ = K₁ * (ρ i + ρ j) := by simp only [K₁]; ring
          · simp only [hst, ↓reduceIte, sub_zero, abs_zero]
            exact mul_nonneg hK₁ (add_nonneg (hρ0 i) (hρ0 j))
        · simp only [hij, ↓reduceIte, sub_self, abs_zero]
          exact mul_nonneg hK₁ (add_nonneg (hρ0 i) (hρ0 j))
      have ha0 : ∀ i j, 0 ≤ a i j := fun i j => by
        simp only [ha_def]
        split_ifs
        · exact minusPairWeight_nonneg β lam ε₀ R _ _
        · exact zero_le_one
      have haW : ∀ i j, a i j ≤ W := fun i j => by
        simp only [ha_def]
        split_ifs
        · unfold minusPairWeight
          split_ifs with hst
          · refine Real.exp_le_exp.2 ?_
            have h2 := hvC i j hst
            have h3 := hCb (c i) (c j) hst
            rw [abs_le] at h2
            nlinarith
          · linarith
        · exact hW
      have hb0 : ∀ i j, 0 ≤ b i j := fun i j => by
        simp only [hb_def]
        split_ifs
        · exact hstab0 _ _
        · exact zero_le_one
      have hbW : ∀ i j, b i j ≤ W := fun i j => by
        simp only [hb_def]
        split_ifs
        · exact hstab _ _
        · exact hW
      have hψ0 : ∀ i, 0 ≤ ψ i := fun i => by rw [hψ_def]; exact (Real.exp_pos _).le
      have hψarg : ∀ i, |-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2| = |L| * ρ i := fun i => by
        rw [hρ_def, hh_def]
        rw [mul_div_assoc, abs_mul, abs_neg, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2)]
      have hψΨ : ∀ i, ψ i ≤ Ψ := fun i => by
        rw [hψ_def]
        refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
        rw [hψarg]
        exact mul_le_of_le_one_right (abs_nonneg L) (hρ1 i)
      have hψ1 : ∀ i, |ψ i - 1| ≤ K₂ * ρ i := fun i => by
        rw [hψ_def]
        have := abs_exp_sub_exp_le (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) 0
        rw [Real.exp_zero, sub_zero, hψarg] at this
        refine this.trans ?_
        have hmax : max (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) 0 ≤ |L| := by
          refine max_le ((le_abs_self _).trans ?_) (abs_nonneg L)
          rw [hψarg]
          exact mul_le_of_le_one_right (abs_nonneg L) (hρ1 i)
        calc Real.exp (max (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) 0) * (|L| * ρ i)
            ≤ Ψ * (|L| * ρ i) := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hmax)
              (mul_nonneg (abs_nonneg L) (hρ0 i))
          _ = K₂ * ρ i := by simp only [K₂]; ring
      have hexp := abs_pairs_mul_sub_le hW hΨ hK₁ ha0 haW hb0 hbW hψ0 hψΨ hρ0 hab hψ1
      rw [hcard] at hexp
      have hreal : |minusIntegrand χ β lam M L ε₀ R c -
          multipolePartitionFunctionIntegrand χ β lam M c * E| ≤
          minusK β L Cb C₁ k * ∑ i₀, E * ρ i₀ := by
        rw [hrwm, hrwi, show (∏ i, ∏ j, a i j) * (∏ i, ψ i) * E - (∏ i, ∏ j, b i j) * E =
          ((∏ i, ∏ j, a i j) * (∏ i, ψ i) - ∏ i, ∏ j, b i j) * E by ring, abs_mul,
          abs_of_nonneg hE0, ← mul_sum]
        calc |(∏ i, ∏ j, a i j) * (∏ i, ψ i) - ∏ i, ∏ j, b i j| * E
            ≤ W ^ (k * k) * Ψ ^ k * (2 * k * K₁ + K₂) * (∑ i, ρ i) * E :=
              mul_le_mul_of_nonneg_right hexp hE0
          _ ≤ minusK β L Cb C₁ k * (∑ i, ρ i) * E := by
              gcongr
          _ = minusK β L Cb C₁ k * (E * ∑ i, ρ i) := by ring
      refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
      rw [ENNReal.ofReal_mul (minusK_nonneg hβ hC₁0.le k)]
      gcongr
      refine le_trans ?_ (le_add_of_nonneg_right zero_le)
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg hE0 (hρ0 i)]
      refine sum_le_sum fun i₀ _ => le_of_eq ?_
      rw [hci, one_mul, indicator_of_mem (Set.mem_univ_pi.1 hc i₀).2, Pi.one_apply, one_mul,
        ENNReal.ofReal_mul hE0, ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
      congr 1
      refine prod_congr rfl fun i _ => ?_
      unfold cutWeight
      rw [indicator_of_mem (hmem i)]
    · -- some dipole is longer than the cutoff
      push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have h1 : minusIntegrand χ β lam M L ε₀ R c = 0 := by
        unfold minusIntegrand
        have hz : ∏ i : S, (Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
            Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
              (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2)) = 0 := by
          refine prod_eq_zero (mem_univ i₀) ?_
          have hnot : (c i₀).1 - (c i₀).2 ∉ closedBall (0 : ℂ) (ε₀ * R) := by
            rw [mem_closedBall_zero_iff]; exact not_le.2 hi₀
          rw [indicator_of_notMem hnot, mul_zero]
        rw [hz, mul_zero]
      rw [h1, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg
        (multipolePartitionFunctionIntegrand_nonneg χ β lam M c) hE0)]
      have hreal : multipolePartitionFunctionIntegrand χ β lam M c * E ≤
          minusK β L Cb C₁ k * E := mul_le_mul_of_nonneg_right (hPb.trans hKW) hE0
      refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
      rw [ENNReal.ofReal_mul (minusK_nonneg hβ hC₁0.le k)]
      gcongr
      refine le_trans ?_ (le_add_of_nonneg_left zero_le)
      refine le_trans (le_of_eq ?_) (single_le_sum (fun j _ => zero_le) (mem_univ i₀))
      rw [indicator_of_mem hc, hci, one_mul,
        indicator_of_mem (show (c i₀).1 - (c i₀).2 ∈ {u : ℂ | ε₀ * R < ‖u‖} from hi₀),
        Pi.one_apply, mul_one, ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
  · have h1 : minusIntegrand χ β lam M L ε₀ R c = 0 := by
      unfold minusIntegrand
      simp only [hconn, ↓reduceIte, zero_mul]
    have h2 : multipolePartitionFunctionIntegrand χ β lam M c = 0 := by
      unfold multipolePartitionFunctionIntegrand
      simp only [hconn, ↓reduceIte, zero_mul]
    rw [h1, h2, zero_mul, sub_zero, abs_zero, ENNReal.ofReal_zero]
    exact zero_le

/-! ### Step 2 for the model `(ṽ, τ̃)`: the term `r_{i₀}²/h²` -/

/-- **Step 2 for the model `(ṽ, τ̃)`** (the term `C N/h²` of eq. (A.41) with
`τ̃ = 8h`): for `1 ≤ k`, `M ≥ 0`, `p₀`, there is `C ≥ 0` (depending on `χ, β, M, k, p₀`) such that
for `ε₀ > 0`, `0 < λ ≤ 1` with `λ ≤ h = ε₀ R̄`, every `N`, `S` with `|S| = k` and `i₀ ∈ S`,
`∫ 𝟙_{𝓑_S} ∏_i e^{β g_λ(r_i)} 𝟙_{r_i ≤ h} 𝟙_Λ(y_{i₀}) r_{i₀}²/h² ≤
C ε₀^{σk-2} N λ^{(2-β)k} R̄^{-2}`, `σ = tailSigma p₀ β k`. -/
theorem lintegral_minus_root_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hM : 0 ≤ M) (p₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε₀ lam : ℝ), 0 < ε₀ → 0 < lam → lam ≤ 1 →
      lam ≤ ε₀ * truncationScale p₀ β lam → ∀ (N : ℕ) (S : Finset ℕ), S.card = k → ∀ i₀ : S,
        ∫⁻ c : S → ℂ × ℂ, connInd M lam c *
            ((∏ i, cutWeight χ β lam (ε₀ * truncationScale p₀ β lam) ((c i).1 - (c i).2)) *
              ((box N).indicator (1 : ℂ → ℝ≥0∞) (c i₀).2 *
                ENNReal.ofReal (‖(c i₀).1 - (c i₀).2‖ ^ 2 /
                  (ε₀ * truncationScale p₀ β lam) ^ 2))) ≤
          ENNReal.ofReal (C * ε₀ ^ (tailSigma p₀ β k * k - 2) * N *
            (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ))) := by
  classical
  have hβ0 : 0 ≤ β := by linarith
  set σ := tailSigma p₀ β k with hσ_def
  have hσ : 0 < σ := zero_lt_tailSigma hk
  have hσβ : 4 - β ≤ σ := four_sub_le_tailSigma hk
  obtain ⟨J, hJ, hmoment⟩ := internal_cut_square_mul_power hχ hβ hσ hσβ
  set K₀ := J
  have hK₀ : 0 < K₀ := hJ
  set A₀ : ℝ := 1
  have hA₀ : 0 ≤ A₀ := by positivity
  set C := ((k ^ k : ℕ) : ℝ) * (4 * Real.pi * M ^ 2 * K₀ * A₀) ^ (k - 1) * (K₀ * A₀)
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, fun ε₀ lam hε₀ hlam hlam1 hlh N S hS i₀ => ?_⟩
  set h := ε₀ * truncationScale p₀ β lam with hh_def
  have hh0 : 0 < h := hlam.trans_le hlh
  have hmax : max h lam = h := max_eq_left hlh
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  set G : ℂ → ℂ → ℝ≥0∞ := fun w y =>
    (box N).indicator (1 : ℂ → ℝ≥0∞) y * ENNReal.ofReal (‖w‖ ^ 2 / h ^ 2)
  have hG : Measurable (Function.uncurry G) :=
    ((measurable_const.indicator (TwoComponentCoulomb.measurableSet_box N)).comp measurable_snd).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))
  have hroot := lintegral_rooted_weighted_power_le (ι := S) hM hlam.le i₀ (cutWeight χ β lam h)
    (measurable_cutWeight hχ hlam β h) G hG
  refine hroot.trans ?_
  -- the non-root factors
  have hedge : ∫⁻ w, cutWeight χ β lam h w *
      ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2) ≤
      ENNReal.ofReal (4 * Real.pi * M ^ 2 * K₀ * (lam ^ (4 - β - σ) * (A₀ * h ^ σ))) := by
    have := hmoment lam h hlam hlh (4 * Real.pi * M ^ 2)
      (by positivity) (fun w => ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2))
      (fun w => le_of_eq (by congr 1; ring))
    simpa only [A₀, one_mul] using this
  -- the root factor
  have hGint : ∀ w, ∫⁻ y, G w y = (N : ℝ≥0∞) * ENNReal.ofReal (‖w‖ ^ 2 / h ^ 2) := by
    intro w
    simp only [G]
    rw [lintegral_mul_const _ (measurable_one.indicator (TwoComponentCoulomb.measurableSet_box N)),
      lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box N),
      TwoComponentCoulomb.volume_box]
  have hrootf : ∫⁻ w, cutWeight χ β lam h w * ∫⁻ y, G w y ≤
      ENNReal.ofReal (N / h ^ 2 * K₀ * (lam ^ (4 - β - σ) * (A₀ * h ^ σ))) := by
    simp_rw [hGint]
    have := hmoment lam h hlam hlh (N / h ^ 2) (by positivity)
      (fun w => (N : ℝ≥0∞) * ENNReal.ofReal (‖w‖ ^ 2 / h ^ 2)) (fun w => by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_mul_eq_mul_div]
        gcongr
        exact le_max_left _ _)
    simpa only [A₀, one_mul] using this
  rw [hcard]
  calc ((k ^ k : ℕ) : ℝ≥0∞) * ((∫⁻ w, cutWeight χ β lam h w *
        ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2)) ^ (k - 1) *
        ∫⁻ w, cutWeight χ β lam h w * ∫⁻ y, G w y)
      ≤ ((k ^ k : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (4 * Real.pi * M ^ 2 * K₀ * (lam ^ (4 - β - σ) * (A₀ * h ^ σ))) ^ (k - 1) *
          ENNReal.ofReal (N / h ^ 2 * K₀ * (lam ^ (4 - β - σ) * (A₀ * h ^ σ)))) := by
        gcongr
    _ = ENNReal.ofReal (C * N * (lam ^ ((4 - β - σ) * k) * h ^ (σ * k - 2))) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        have hlp : lam ^ ((4 - β - σ) * ((m + 1 : ℕ) : ℝ)) = (lam ^ (4 - β - σ)) ^ (m + 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
        have hhp : h ^ (σ * ((m + 1 : ℕ) : ℝ) - 2) = (h ^ σ) ^ (m + 1) / h ^ 2 := by
          rw [Real.rpow_sub hh0, ← Real.rpow_natCast (h ^ σ), ← Real.rpow_mul hh0.le]
          norm_num
        rw [hlp, hhp]
        simp only [C, Nat.add_sub_cancel]
        field_simp
        ring_nf
    _ ≤ ENNReal.ofReal (C * ε₀ ^ (σ * k - 2) * N *
          (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hp := cut_power_le (p₀ := p₀) (β := β) hk hlam hlam1 hε₀
        rw [← hσ_def, ← hh_def] at hp
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        calc C * N * (lam ^ ((4 - β - σ) * k) * h ^ (σ * k - 2))
            ≤ C * N * (ε₀ ^ (σ * k - 2) *
                (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ))) := by gcongr
          _ = _ := by ring

/-! ### Lemma A.6 for the model `(ṽ, τ̃)` -/

/-- **Lemma A.6 for the model `(ṽ, τ̃)`** (with
`Z = ∅`, as used for eq. (4.75) in the proof of Proposition 4.24): for
`1 ≤ k ≤ p*(β)`, `M ≥ 0`, `L ∈ ℝ`, `p₀` and `ε₀ > 0` there is `C > 0` such that for every
`0 < λ ≤ 1` with `λ ≤ ε₀ R̄`, every `N` and every `S` with `|S| = k`,
`|I^-_{mult,ε₀}(S) - I^0_{mult,∞}(S)| ≤ C N λ^{(2-β)k} R̄^{-2}`. -/
theorem multipoleIntegralMinus_sub_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (L : ℝ) (p₀ : ℕ) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      lam ≤ ε₀ * truncationScale p₀ β lam → ∀ (N : ℕ) (S : Finset ℕ), S.card = k →
        |multipoleIntegralMinus χ N β lam M L ε₀ (truncationScale p₀ β lam) S -
            multipoleIntegral χ N β lam M S| ≤
          C * N * (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  classical
  have hβ0 : 0 ≤ β := by linarith
  have hkp' : (4 - β) * k - 2 < 0 :=
    (Appendix.transitionBeta_lt_iff hk β).1 ((Appendix.le_pStar_iff hk).1 hkp)
  obtain ⟨Cb, hCb0, hCb⟩ := neg_le_dipoleInteraction hχ
  obtain ⟨C₁, hC₁0, hC₁⟩ := lemma_3_10 hχ
  obtain ⟨CR, hCR0, hroot⟩ := lintegral_minus_root_le (χ := χ) hχ hβ hk hM p₀
  obtain ⟨CT, hCT0, htail⟩ := lintegral_cutoff_tail_le (M := M) hχ hβ hk hkp' hM p₀
  intro ε₀ hε₀
  set K := minusK β L Cb C₁ k
  have hK : 0 ≤ K := minusK_nonneg hβ0 hC₁0.le k
  set D := CR * ε₀ ^ (tailSigma p₀ β k * k - 2) + CT * ε₀ ^ tailExp p₀ β k
  have hD : 0 ≤ D := by positivity
  refine ⟨K * k * D + 1, by positivity, fun lam hlam hlam1 hlh N S hS => ?_⟩
  set R := truncationScale p₀ β lam
  set h := ε₀ * R
  set T : ℝ := lam ^ ((2 - β) * k) * R ^ (-2 : ℝ)
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hT : 0 ≤ T := by positivity
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  set P : Set (S → ℂ × ℂ) := Set.univ.pi fun _ : S => box N ×ˢ box N
  -- the integrands of Step 2 and Step 3
  set F₁ : S → (S → ℂ × ℂ) → ℝ≥0∞ := fun i₀ c => connInd M lam c *
    ((∏ i, cutWeight χ β lam h ((c i).1 - (c i).2)) *
      ((box N).indicator (1 : ℂ → ℝ≥0∞) (c i₀).2 * ENNReal.ofReal (‖(c i₀).1 - (c i₀).2‖ ^ 2 / h ^ 2)))
  set F₂ : S → (S → ℂ × ℂ) → ℝ≥0∞ := fun i₀ c => P.indicator (fun c => connInd M lam c *
      ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
    {u : ℂ | h < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2)
  have hF₁m : ∀ i₀, Measurable (F₁ i₀) := by
    intro i₀
    refine (measurable_connInd M lam).mul ((Finset.measurable_prod _ fun i _ =>
      (measurable_cutWeight hχ hlam β h).comp
        ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd)).mul
      (((measurable_one.indicator (TwoComponentCoulomb.measurableSet_box N)).comp
        (measurable_pi_apply i₀).snd).mul (ENNReal.measurable_ofReal.comp ?_)))
    exact ((((measurable_pi_apply i₀).fst.sub (measurable_pi_apply i₀).snd).norm.pow_const 2).div_const _)
  have hF₂m : ∀ i₀, Measurable (F₂ i₀) := by
    intro i₀
    refine (Measurable.indicator ((measurable_connInd M lam).mul (Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp ((measurable_exp_smearedKernel hχ hlam β).comp
        ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd))))
      (measurableSet_pi_box_prod N)).mul ?_
    exact (measurable_one.indicator (measurableSet_lt measurable_const measurable_norm)).comp
      ((measurable_pi_apply i₀).fst.sub (measurable_pi_apply i₀).snd)
  -- the bound on the integral of the difference
  have hlint : ∫⁻ c in P, ENNReal.ofReal |minusIntegrand χ β lam M L ε₀ R c -
      (multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))| ≤
      ENNReal.ofReal (K * k * D * N * T) := by
    calc _ ≤ ∫⁻ c in P, ENNReal.ofReal K * ((∑ i₀, F₁ i₀ c) + ∑ i₀, F₂ i₀ c) :=
          setLIntegral_mono' (measurableSet_pi_box_prod N) fun c hc => by
            have := minus_pointwise_le (M := M) (L := L) hβ0 hlam hlh hCb0 (hCb lam hlam) hC₁0
              (fun d e hd he => (hC₁ lam (8 * ε₀ * R) hlam d e hd he).1) hc
            rw [hS] at this
            exact this
      _ ≤ ∫⁻ c, ENNReal.ofReal K * ((∑ i₀, F₁ i₀ c) + ∑ i₀, F₂ i₀ c) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal K * ((∑ i₀, ∫⁻ c, F₁ i₀ c) + ∑ i₀, ∫⁻ c, F₂ i₀ c) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left (f := fun c => ∑ i₀, F₁ i₀ c)
              (Finset.measurable_sum _ fun i₀ _ => hF₁m i₀),
            lintegral_finsetSum _ fun i₀ _ => hF₁m i₀, lintegral_finsetSum _ fun i₀ _ => hF₂m i₀]
      _ ≤ ENNReal.ofReal K *
            ((∑ _i₀ : S, ENNReal.ofReal (CR * ε₀ ^ (tailSigma p₀ β k * k - 2) * N * T)) +
              ∑ _i₀ : S, ENNReal.ofReal (CT * ε₀ ^ tailExp p₀ β k * N * T)) := by
          refine mul_le_mul' le_rfl (add_le_add (sum_le_sum fun i₀ _ => ?_)
            (sum_le_sum fun i₀ _ => ?_))
          · exact hroot ε₀ lam hε₀ hlam hlam1 hlh N S hS i₀
          · exact htail ε₀ lam hε₀ hlam hlam1 hlh N S hS i₀
      _ = ENNReal.ofReal (K * k * D * N * T) := by
          rw [sum_const, sum_const, card_univ, hcard, nsmul_eq_mul, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add (by positivity)
              (by positivity), ← ENNReal.ofReal_mul hK]
          congr 1
          simp only [D]
          ring
  have hmain := abs_setIntegral_sub_le (μ := volume) (P := P)
    (measurable_minusIntegrand hχ hlam β M L ε₀ R) (integrableOn_multipoleIntegrand hχ hlam N S)
    (by positivity) hlint
  refine hmain.2.trans ?_
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : 0 ≤ N * T := by positivity
  calc K * k * D * N * T = (K * k * D) * (N * T) := by ring
    _ ≤ (K * k * D + 1) * (N * T) := by nlinarith
    _ = (K * k * D + 1) * N * (lam ^ ((2 - β) * k) * R ^ (-2 : ℝ)) := by ring

end GeneralExpansion

end MultipoleBKT

end
