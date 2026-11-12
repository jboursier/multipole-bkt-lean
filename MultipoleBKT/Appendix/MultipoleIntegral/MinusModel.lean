/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.UpperBound
public import MultipoleBKT.Appendix.MultipoleIntegral.LowerBound
public import MultipoleBKT.Energy.ScreenedError
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Lemma A.3 for the model `(ṽ, τ̃)`: the multipole integral `I^-_{mult,ε₀}(S)`

See (A.4) and Lemma A.3. The integral is
`I^-_{mult,ε₀}(S) = I_{mult,ε₀}(S; ṽ, τ̃, -64L, ∅)`, where `ṽ_ij` is the screened interaction
with screening radius `τ₀ = 8 ε₀ R̄` (`upperBoundInteraction`).
* `measurable_screenedInteraction`: `(d, e) ↦ ṽ(d, e)` is measurable (needed for the integral to
  be meaningful; omitted in the paper);
* `minusIntegrand`, `multipoleIntegralMinus`: the integrand and the integral `I^-_{mult,ε₀}(S)`,
  with the cutoff `ε₀ R` (`R` stands for `R̄_{β,λ}`) and the damping constant `L` as parameters;
* `multipoleIntegralMinus_two_sided`: (A.5) for this model, for `1 < k ≤ p*(β)`, `M > 20` and every
  `L ∈ ℝ`, uniformly in the cutoff `ε₀ R ≥ 2λ` (the paper's "λ small enough"), with `C` depending
  on `χ, β, M, L, k`.

**Proof.** Lemma 3.10 gives `|ṽ_ij - v_ij| ≤ C/64` on the cutoff
support. For the lower bound, the Hessian estimate bounds `v_ij` on the paper's event
`𝒞`, so `ṽ_ij ≤ 12πB + C/64` there. The exact endpoint-ball chain lies in `𝒞`, satisfies all
stable and linked constraints, and has radii below `2λ ≤ ε₀ R`. Its weighted volume gives
(A.15). The empty frozen configuration makes the bad loss zero.
The damping factor is at least `exp(-|L|)` per dipole. This argument works for every `λ > 0`
allowed by the statement.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {lam β M : ℝ}

/-! ### Measurability of `ṽ` -/

theorem measurable_screenedImageField_joint (τ : ℝ) :
    Measurable fun p : ℂ × ℂ × ℂ => screenedImageField p.1 τ p.2.1 p.2.2 := by
  unfold screenedImageField
  fun_prop

/-- The screened dipole field is jointly measurable in the dipole and the point. -/
theorem measurable_uncurry_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam) (τ : ℝ) :
    Measurable (Function.uncurry (screenedField χ lam τ)) := by
  have h1 := continuous_smearedField hχ hlam
  have h2 := measurable_screenedImageField_joint τ
  unfold Function.uncurry screenedField dipoleField screenedCorrectionField
  refine Measurable.add (by fun_prop) (Measurable.sub ?_ ?_)
  · exact h2.comp (f := fun p : (ℂ × ℂ) × ℂ => (dipoleMidpoint p.1, p.1.1, p.2))
      (by unfold dipoleMidpoint; fun_prop)
  · exact h2.comp (f := fun p : (ℂ × ℂ) × ℂ => (dipoleMidpoint p.1, p.1.2, p.2))
      (by unfold dipoleMidpoint; fun_prop)

theorem measurable_inner_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam) (τ : ℝ) :
    Measurable fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ =>
      inner ℝ (screenedField χ lam τ p.1.1 p.2) (screenedField χ lam τ p.1.2 p.2) := by
  have hF := measurable_uncurry_screenedField hχ hlam τ
  have h1 : Measurable fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ =>
      Function.uncurry (screenedField χ lam τ) (p.1.1, p.2) :=
    hF.comp (measurable_fst.fst.prodMk measurable_snd)
  have h2 : Measurable fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ =>
      Function.uncurry (screenedField χ lam τ) (p.1.2, p.2) :=
    hF.comp (measurable_fst.snd.prodMk measurable_snd)
  exact Measurable.inner h1 h2

/-- **`ṽ` is measurable**: `(d, e) ↦ ṽ(d, e)` (`screenedInteraction`, eq. (3.18)) is a
measurable function of the two dipoles. -/
theorem measurable_screenedInteraction (hχ : IsMollifier χ) (hlam : 0 < lam) (τ : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => screenedInteraction χ lam τ q.1 q.2 := by
  classical
  have hi := measurable_inner_screenedField hχ hlam τ
  have hs : MeasurableSet {p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ |
      p.2 ∈ ball (dipoleMidpoint p.1.1) τ ∩ ball (dipoleMidpoint p.1.2) τ} := by
    have h1 : Measurable fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => dist p.2 (dipoleMidpoint p.1.1) := by
      unfold dipoleMidpoint; fun_prop
    have h2 : Measurable fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => dist p.2 (dipoleMidpoint p.1.2) := by
      unfold dipoleMidpoint; fun_prop
    exact (measurableSet_lt h1 measurable_const).inter (measurableSet_lt h2 measurable_const)
  have hG : Measurable fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ =>
      (ball (dipoleMidpoint p.1.1) τ ∩ ball (dipoleMidpoint p.1.2) τ).indicator
        (fun w => inner ℝ (screenedField χ lam τ p.1.1 w) (screenedField χ lam τ p.1.2 w)) p.2 := by
    have : (fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ =>
        (ball (dipoleMidpoint p.1.1) τ ∩ ball (dipoleMidpoint p.1.2) τ).indicator
          (fun w => inner ℝ (screenedField χ lam τ p.1.1 w) (screenedField χ lam τ p.1.2 w)) p.2) =
        {p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ |
          p.2 ∈ ball (dipoleMidpoint p.1.1) τ ∩ ball (dipoleMidpoint p.1.2) τ}.indicator
          (fun p => inner ℝ (screenedField χ lam τ p.1.1 p.2) (screenedField χ lam τ p.1.2 p.2)) := by
      funext p
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [this]
    exact hi.indicator hs
  have hint : (fun q : (ℂ × ℂ) × (ℂ × ℂ) => screenedInteraction χ lam τ q.1 q.2) =
      fun q => (2 * Real.pi)⁻¹ * ∫ w, (ball (dipoleMidpoint q.1) τ ∩
        ball (dipoleMidpoint q.2) τ).indicator
          (fun w => inner ℝ (screenedField χ lam τ q.1 w) (screenedField χ lam τ q.2 w)) w := by
    funext q
    unfold screenedInteraction
    rw [integral_indicator (measurableSet_ball.inter measurableSet_ball)]
  rw [hint]
  exact ((hG.stronglyMeasurable.integral_prod_right
    (ν := (volume : Measure ℂ))).measurable).const_mul _

/-! ### The integral `I^-_{mult,ε₀}(S)` -/

open scoped Classical in
/-- The pair factor `e^{-β ṽ_ij} 𝟙_{𝒜_ij}` of `I^-_{mult,ε₀}` (eq. (4.72)), with
`ṽ = upperBoundInteraction χ λ ε₀ R` (screening radius `8 ε₀ R`). -/
noncomputable def minusPairWeight (χ : ℂ → ℝ) (β lam ε₀ R : ℝ) (d e : ℂ × ℂ) : ℝ :=
  if IsStableDipolePair d e then Real.exp (-β * upperBoundInteraction χ lam ε₀ R d e) else 0

open scoped Classical in
/-- The integrand of `I^-_{mult,ε₀}(S)` (eq. (4.72)): with `h = ε₀ R` and
`r_i = |x_i - y_i|`,
`𝟙_{𝓑_S} ∏_{i<j} e^{-β ṽ_ij} 𝟙_{𝒜_ij} ∏_i e^{-L r_i²/h²} e^{β g_λ(x_i - y_i)} 𝟙_{r_i ≤ h}`, where
`ṽ = upperBoundInteraction χ λ ε₀ R` has screening radius `τ₀ = 8 ε₀ R`. -/
noncomputable def minusIntegrand (χ : ℂ → ℝ) (β lam M L ε₀ R : ℝ) {S : Finset ℕ}
    (c : S → ℂ × ℂ) : ℝ :=
  ((if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
      then 1 else 0) *
    ∏ i : S, ∏ j : S, if i < j then minusPairWeight χ β lam ε₀ R (c i) (c j) else 1) *
    ∏ i : S, (Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
      Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2))

/-- **The multipole integral of the `-` model** `I^-_{mult,ε₀}(S) = I_{mult,ε₀}(S; ṽ, τ̃, -64L, ∅)`
(equations (4.72) and (A.4)), with `R` standing for `R̄_{β,λ}`:
`∫_{(Λ²)^{|S|}} 𝟙_{𝓑_S} ∏_{i<j} e^{-β ṽ_ij} 𝟙_{𝒜_ij} ∏_i e^{-L r_i²/(ε₀R)²} e^{β g_λ(x_i - y_i)}
𝟙_{r_i ≤ ε₀ R} dx_i dy_i`. -/
noncomputable def multipoleIntegralMinus (χ : ℂ → ℝ) (N : ℕ) (β lam M L ε₀ R : ℝ)
    (S : Finset ℕ) : ℝ :=
  ∫ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), minusIntegrand χ β lam M L ε₀ R c

namespace MultipoleIntegral

theorem minusPairWeight_nonneg (β lam ε₀ R : ℝ) (d e : ℂ × ℂ) :
    0 ≤ minusPairWeight χ β lam ε₀ R d e := by
  unfold minusPairWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem measurable_minusPairWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β ε₀ R : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => minusPairWeight χ β lam ε₀ R q.1 q.2 := by
  have hv : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => upperBoundInteraction χ lam ε₀ R q.1 q.2 :=
    measurable_screenedInteraction hχ hlam (8 * ε₀ * R)
  unfold minusPairWeight
  exact Measurable.ite measurableSet_isStableDipolePair
    (Real.measurable_exp.comp (hv.const_mul (-β))) measurable_const

theorem minusDipoleWeight_nonneg (β lam L ε₀ R : ℝ) (p : ℂ × ℂ) :
    0 ≤ Real.exp (-L * ‖p.1 - p.2‖ ^ 2 / (ε₀ * R) ^ 2) *
      Real.exp (β * smearedKernel χ lam (p.1 - p.2)) *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 (p.1 - p.2) :=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem minusIntegrand_nonneg (β lam M L ε₀ R : ℝ) {S : Finset ℕ} (c : S → ℂ × ℂ) :
    0 ≤ minusIntegrand χ β lam M L ε₀ R c := by
  classical
  unfold minusIntegrand
  refine mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (prod_nonneg fun i _ =>
    prod_nonneg fun j _ => ?_)) (prod_nonneg fun i _ => minusDipoleWeight_nonneg β lam L ε₀ R _)
  split_ifs
  · exact minusPairWeight_nonneg β lam ε₀ R _ _
  · exact zero_le_one

theorem measurable_minusIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (β M L ε₀ R : ℝ)
    {S : Finset ℕ} : Measurable (minusIntegrand (S := S) χ β lam M L ε₀ R) := by
  classical
  have hpair := measurable_minusPairWeight hχ hlam β ε₀ R
  have hdip : Measurable fun p : ℂ × ℂ => Real.exp (-L * ‖p.1 - p.2‖ ^ 2 / (ε₀ * R) ^ 2) *
      Real.exp (β * smearedKernel χ lam (p.1 - p.2)) *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 (p.1 - p.2) :=
    ((by fun_prop : Measurable fun p : ℂ × ℂ => Real.exp (-L * ‖p.1 - p.2‖ ^ 2 / (ε₀ * R) ^ 2)).mul
      (continuous_exp_smearedKernel_sub hχ hlam β).measurable).mul
      ((measurable_const.indicator measurableSet_closedBall).comp
        (measurable_fst.sub measurable_snd))
  have hconn : Measurable fun c : S → ℂ × ℂ =>
      (if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
        then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_setOf_fromRel_multipoleLinked M lam (fun G => G.Connected))
      measurable_const measurable_const
  have hpairs : Measurable fun c : S → ℂ × ℂ => ∏ i : S, ∏ j : S, (if i < j then
      minusPairWeight χ β lam ε₀ R (c i) (c j) else 1) := by
    refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    by_cases h : i < j
    · simp only [h, ↓reduceIte]
      have hm := hpair.comp (f := fun c : S → ℂ × ℂ => (c i, c j))
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact hm
    · simp only [h, ↓reduceIte]
      exact measurable_const
  have hdips : Measurable fun c : S → ℂ × ℂ =>
      ∏ i : S, (Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
        Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
          (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2)) :=
    Finset.measurable_prod _ fun i _ => hdip.comp (measurable_pi_apply i)
  exact (hconn.mul hpairs).mul hdips

/-- The comparison `|ṽ_ij - v_ij| ≤ C/64` (Lemma 3.10) when `r_i, r_j, λ ≤ ε₀ R`. -/
theorem abs_upperBoundInteraction_sub_le {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
      |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
        C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / τ ^ 2)
    (hlam : 0 < lam) {ε₀ R : ℝ} (hh : lam ≤ ε₀ * R) {d e : ℂ × ℂ} (hd : ‖d.1 - d.2‖ ≤ ε₀ * R)
    (he : ‖e.1 - e.2‖ ≤ ε₀ * R) :
    |upperBoundInteraction χ lam ε₀ R d e - dipoleInteraction χ lam d e| ≤ C / 64 := by
  have hh0 : 0 < ε₀ * R := hlam.trans_le hh
  have hτ : 8 * ε₀ * R = 8 * (ε₀ * R) := by ring
  have hd' : 8 * max ‖d.2 - d.1‖ lam ≤ 8 * ε₀ * R := by
    rw [hτ, norm_sub_rev]; exact mul_le_mul_of_nonneg_left (max_le hd hh) (by norm_num)
  have he' : 8 * max ‖e.2 - e.1‖ lam ≤ 8 * ε₀ * R := by
    rw [hτ, norm_sub_rev]; exact mul_le_mul_of_nonneg_left (max_le he hh) (by norm_num)
  refine (hC lam _ hlam d e hd' he').trans ?_
  rw [hτ, div_le_iff₀ (by positivity)]
  have h1 : ‖d.1 - d.2‖ * ‖e.1 - e.2‖ ≤ (ε₀ * R) * (ε₀ * R) :=
    mul_le_mul hd he (norm_nonneg _) hh0.le
  have h2 : C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) ≤ C * ((ε₀ * R) * (ε₀ * R)) :=
    mul_le_mul_of_nonneg_left h1 hC0.le
  nlinarith

/-- The damping factor `e^{-L r²/h²}` lies in `[e^{-|L|}, e^{|L|}]` for `r ≤ h`. -/
theorem abs_damping_le {L r h : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ h) :
    |-L * r ^ 2 / h ^ 2| ≤ |L| := by
  rcases (hr0.trans hrh).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  have hq : r ^ 2 / h ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact pow_le_pow_left₀ hr0 hrh 2
  rw [mul_div_assoc, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ r ^ 2 / h ^ 2)]
  exact mul_le_of_le_one_right (abs_nonneg L) hq

end MultipoleIntegral

open MultipoleIntegral

/-- **Lemma A.3 for the model `(ṽ, τ̃)`** (with `I^-_{mult,ε₀}` of (A.4)): for `1 < k ≤ p*(β)`, `M > 20` and `L ∈ ℝ` there is `C > 0`
(depending on `χ, β, M, L, k`) such that for every `λ > 0` there is `N₀` with
`C⁻¹ N λ^{(2-β)k} λ^{2(k-1)} ≤ I^-_{mult,ε₀}(S) ≤ C N λ^{(2-β)k} λ^{2(k-1)}` for all `N ≥ N₀`, all
cutoffs `ε₀ R ≥ 2λ` and all `S` with `|S| = k`. -/
theorem multipoleIntegralMinus_two_sided (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 < k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 20 < M) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ ε₀ R : ℝ, 2 * lam ≤ ε₀ * R → ∀ S : Finset ℕ, S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤
            multipoleIntegralMinus χ N β lam M L ε₀ R S ∧
          multipoleIntegralMinus χ N β lam M L ε₀ R S ≤
            C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  classical
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨Cb, hCb0, hCb⟩ := neg_le_dipoleInteraction hχ
  obtain ⟨C₁, hC₁0, hC₁⟩ := lemma_3_10 hχ
  have hC₁' : ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
      |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
        C₁ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / τ ^ 2 := fun lam τ hlam d e hd he =>
    (hC₁ lam τ hlam d e hd he).1
  -- constants
  set W : ℝ := Real.exp (β * (Cb + C₁ / 64))
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg hβ0 (by positivity))
  set K : ℝ := W ^ (k * k) * Real.exp |L| ^ k
  have hK : 0 ≤ K := by positivity
  obtain ⟨B, hB⟩ := hχ.exists_bound
  have hB0 := hχ.nonneg_of_le hB
  set E : ℝ := Real.exp (-β * (12 * Real.pi * B + C₁ / 64))
  set A : ℝ := E ^ (k * k) * Real.exp (-|L|) ^ k
  have hA : 0 ≤ A := by positivity
  set c₀ : ℝ := A * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 256) ^ (2 * k - 1) / 4
  have hc₀ : 0 < c₀ := by positivity
  set Cu : ℝ := K * upperConst χ β M k
  have hCu : 0 ≤ Cu := mul_nonneg hK (upperConst_nonneg χ β M k)
  set C : ℝ := max (Cu + 1) c₀⁻¹
  have hC : 0 < C := lt_max_of_lt_left (by linarith)
  refine ⟨C, hC, fun lam hlam => ⟨lowerN₀ lam k, fun N hN ε₀ R hh S hS => ?_⟩⟩
  have hh0 : 0 < ε₀ * R := by linarith
  have hlh : lam ≤ ε₀ * R := by linarith
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  -- the pointwise upper bound
  have hup : ∀ c : S → ℂ × ℂ, minusIntegrand χ β lam M L ε₀ R c ≤ K *
      ((if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
          then 1 else 0) * ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) := by
    intro c
    have hR0 : 0 ≤ ((if (SimpleGraph.fromRel fun i j : S =>
        MultipoleLinked M lam (c i) (c j)).Connected then 1 else 0 : ℝ)) := by
      split_ifs <;> norm_num
    by_cases hall : ∀ i : S, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R
    · -- the pair factors
      have hpair : ∏ i : S, ∏ j : S, (if i < j then
          minusPairWeight χ β lam ε₀ R (c i) (c j) else 1) ≤
          W ^ (k * k) := by
        have h := abs_prod_prod_le (fun i j : S => if i < j then
          minusPairWeight χ β lam ε₀ R (c i) (c j) else 1)
          (W := W) (fun i j => by
            split_ifs with hij
            · unfold minusPairWeight
              split_ifs with hst
              · rw [abs_of_nonneg (Real.exp_pos _).le]
                refine Real.exp_le_exp.2 ?_
                have h1 := abs_upperBoundInteraction_sub_le hC₁0 hC₁' hlam hlh (hall i) (hall j)
                have h2 := hCb lam hlam (c i) (c j) hst
                rw [abs_le] at h1
                nlinarith
              · rw [abs_zero]; linarith
            · rw [abs_one]; exact hW)
        rw [hcard] at h
        exact (le_abs_self _).trans h
      -- the dipole factors
      have hdip : ∀ i : S, Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
          Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
            (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2) ≤
          Real.exp |L| * Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) := by
        intro i
        have hmem : (c i).1 - (c i).2 ∈ closedBall (0 : ℂ) (ε₀ * R) := by
          rw [mem_closedBall_zero_iff]; exact hall i
        rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        exact (le_abs_self _).trans (abs_damping_le (norm_nonneg _) (hall i))
      have hdips : ∏ i : S, (Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
          Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
            (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2)) ≤
          Real.exp |L| ^ k * ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) := by
        calc _ ≤ ∏ i : S, (Real.exp |L| * Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) :=
              prod_le_prod₀ (fun i _ => minusDipoleWeight_nonneg β lam L ε₀ R _) fun i _ => hdip i
          _ = _ := by rw [prod_mul_distrib, prod_const, card_univ, hcard]
      unfold minusIntegrand
      have hP0 : 0 ≤ ∏ i : S, ∏ j : S, (if i < j then
          minusPairWeight χ β lam ε₀ R (c i) (c j) else 1) :=
        prod_nonneg fun i _ => prod_nonneg fun j _ => by
          split_ifs
          · exact minusPairWeight_nonneg β lam ε₀ R _ _
          · exact zero_le_one
      calc _ ≤ ((if (SimpleGraph.fromRel fun i j : S =>
            MultipoleLinked M lam (c i) (c j)).Connected then 1 else 0) * W ^ (k * k)) *
            (Real.exp |L| ^ k * ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpair hR0) hdips
              (prod_nonneg fun i _ => minusDipoleWeight_nonneg β lam L ε₀ R _)
              (mul_nonneg hR0 (by positivity))
        _ = _ := by simp only [K]; ring
    · -- some dipole is longer than the cutoff: the integrand vanishes
      push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hz : ∏ i : S, (Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
          Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
            (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2)) = 0 := by
        refine prod_eq_zero (mem_univ i₀) ?_
        have hnot : (c i₀).1 - (c i₀).2 ∉ closedBall (0 : ℂ) (ε₀ * R) := by
          rw [mem_closedBall_zero_iff]; exact not_le.2 hi₀
        rw [Set.indicator_of_notMem hnot, mul_zero]
      unfold minusIntegrand
      rw [hz, mul_zero]
      exact mul_nonneg hK (mul_nonneg hR0 (prod_nonneg fun i _ => (Real.exp_pos _).le))
  constructor
  · -- the lower bound
    set σ : S ≃ Fin k := Fintype.equivFinOfCardEq hcard
    have hr₀ : (σ (σ.symm ⟨0, hk.le⟩) : ℕ) = 0 := by simp
    have hfin : ∫⁻ c in Set.univ.pi (fun _ : S => box N ×ˢ box N),
        ENNReal.ofReal (minusIntegrand χ β lam M L ε₀ R c) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (lintegral_le_of_le_connected (M := M) hχ hβ hk.le hkp (by linarith) hlam N hS hK
          fun c _ => hup c)
    refine le_trans ?_ (le_setIntegral_of_chain (β := β) hlam hk.le
      (by
        have := sqrt_ge_of_lowerN₀_le hlam hN
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith) σ (measurable_minusIntegrand hχ hlam β M L ε₀ R)
      (minusIntegrand_nonneg β lam M L ε₀ R) hfin hA fun c hc => ?_)
    · have : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
      calc C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
          = C⁻¹ * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by ring
        _ ≤ c₀ * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
            refine mul_le_mul_of_nonneg_right ?_ this
            rw [inv_le_comm₀ hC hc₀]
            exact le_max_right _ _
        _ = _ := by simp only [c₀]; ring
    · -- The Hessian estimate on `𝒞`, the screened correction and the chain give (A.15).
      have hr : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R := fun i => by
        linarith [(hc.radii hlam hr₀ i).2.le]
      have hconn : (SimpleGraph.fromRel fun i j : S =>
          MultipoleLinked M lam (c i) (c j)).Connected := by
        refine connected_of_chain σ (by omega) fun i j hij => ?_
        have hne : i ≠ j := fun h => by rw [h] at hij; omega
        exact (SimpleGraph.fromRel_adj _ _ _).2
          ⟨hne, Or.inl (hc.linked hlam hr₀ (by linarith) hij)⟩
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      have hE1 : E ≤ 1 := by
        refine Real.exp_le_one_iff.2 ?_
        have : 0 ≤ 12 * Real.pi * B + C₁ / 64 := by positivity
        nlinarith
      have hpair : ∀ i j : S, E ≤ (if i < j then
          minusPairWeight χ β lam ε₀ R (c i) (c j) else 1) := by
        intro i j
        split_ifs with hij
        · have hst := hc.stable hlam hr₀ hij.ne
          unfold minusPairWeight
          simp only [hst, ↓reduceIte]
          refine Real.exp_le_exp.2 ?_
          have h1 := abs_upperBoundInteraction_sub_le hC₁0 hC₁' hlam hlh (hr i) (hr j)
          have h2 := (abs_le.mp ((hc.event hlam hr₀).abs_interaction_le hχ hB hlam i j)).2
          rw [abs_le] at h1
          nlinarith
        · exact hE1
      have hpairs : E ^ (k * k) ≤ ∏ i : S, ∏ j : S, (if i < j then
          minusPairWeight χ β lam ε₀ R (c i) (c j) else 1) := by
        calc E ^ (k * k) = ∏ _i : S, ∏ _j : S, E := by
              rw [prod_const, prod_const, card_univ, hcard, ← pow_mul]
          _ ≤ _ := prod_le_prod₀ (fun i _ => prod_nonneg fun j _ => hE0) fun i _ =>
              prod_le_prod₀ (fun j _ => hE0) fun j _ => hpair i j
      have h4 : 0 < 4 * lam := by positivity
      have hdip : ∀ i : S, Real.exp (-|L|) * (4 * lam) ^ (-β) ≤
          Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
            Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
              (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2) := by
        intro i
        have hmem : (c i).1 - (c i).2 ∈ closedBall (0 : ℂ) (ε₀ * R) := by
          rw [mem_closedBall_zero_iff]; exact hr i
        rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
        refine mul_le_mul (Real.exp_le_exp.2 ?_) ?_ (Real.rpow_pos_of_pos h4 _).le
          (Real.exp_pos _).le
        · have := abs_damping_le (L := L) (norm_nonneg ((c i).1 - (c i).2)) (hr i)
          rw [abs_le] at this
          linarith
        · have h1 := neg_log_add_le_smearedKernel hχ hlam ((c i).1 - (c i).2)
          have h2 := (hc.radii hlam hr₀ i).2.le
          have h3 : Real.log (‖(c i).1 - (c i).2‖ + 2 * lam) ≤ Real.log (4 * lam) :=
            Real.log_le_log (by positivity) (by linarith)
          rw [Real.rpow_def_of_pos h4]
          refine Real.exp_le_exp.2 ?_
          nlinarith
      have hdips : Real.exp (-|L|) ^ k * ((4 * lam) ^ (-β)) ^ k ≤
          ∏ i : S, (Real.exp (-L * ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2) *
            Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
              (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c i).1 - (c i).2)) := by
        calc Real.exp (-|L|) ^ k * ((4 * lam) ^ (-β)) ^ k
            = ∏ _i : S, (Real.exp (-|L|) * (4 * lam) ^ (-β)) := by
              rw [prod_const, card_univ, hcard, mul_pow]
          _ ≤ _ := prod_le_prod₀ (fun i _ => mul_nonneg (Real.exp_pos _).le
              (Real.rpow_pos_of_pos h4 _).le) fun i _ => hdip i
      unfold minusIntegrand
      simp only [hconn, ↓reduceIte, one_mul]
      calc A * ((4 * lam) ^ (-β)) ^ k
          = E ^ (k * k) * (Real.exp (-|L|) ^ k * ((4 * lam) ^ (-β)) ^ k) := by
            simp only [A]; ring
        _ ≤ _ := mul_le_mul hpairs hdips (by positivity)
            (prod_nonneg fun i _ => prod_nonneg fun j _ => le_trans hE0 (hpair i j))
  · -- the upper bound
    refine (setIntegral_le_of_le_connected (M := M) hχ hβ hk.le hkp (by linarith) hlam N hS
      (measurable_minusIntegrand hχ hlam β M L ε₀ R) (minusIntegrand_nonneg β lam M L ε₀ R) hK
      fun c _ => hup c).trans ?_
    have : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
    calc K * upperConst χ β M k * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
        = Cu * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by simp only [Cu]; ring
      _ ≤ C * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
          refine mul_le_mul_of_nonneg_right ?_ this
          exact (le_max_left _ _).trans' (by linarith)
      _ = C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by ring

end MultipoleBKT

end
