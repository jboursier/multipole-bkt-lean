/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.UpperBound
public import MultipoleBKT.Appendix.MultipoleIntegral.LowerBound

/-!
# The multipole integral with a length cutoff, `I^0_{mult,ε₀}(S)`

See (A.4), for the model
`(w, τ, L, Z) = (v, ∞, 0, ∅)` with a finite cutoff: `I^0_{mult,ε₀}(S) = I_{mult,ε₀}(S; v, ∞, 0, ∅)`, the unnormalized version of `𝖬^0_{ε₀}(S)` in (4.17). The truncation length
`h = ε₀ R̄_{β,λ}` is a parameter.

* `multipoleIntegralCut χ N β λ M h S = ∫_{(Λ²)^{|S|}} 𝟙_{𝓑_S} ∏_{i<j} e^{-β v_ij} 𝟙_{𝒜_ij}
  ∏_i e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ h} dx_i dy_i`;
* `multipoleIntegralCut_two_sided`: the two-sided bound (A.5) for this model, for `1 < k ≤ p*(β)`
  and `M > 20`, uniformly in the truncation length `h ≥ 2λ` (the paper's "λ small enough",
  `λ ≤ ε₀ R̄/2`), with `C` depending on `χ, β, M, k`.

The lower bound uses the event `𝒞`, its Hessian interaction estimate and the exact chain of
Lemma A.3. For this empty-frozen-data model the bad loss is zero.
Every chain radius is below `2λ`, so the cutoff leaves the chain unchanged.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {lam β M : ℝ}

open MultipoleIntegral

/-- **The multipole integral with cutoff** `I^0_{mult,ε₀}(S) = I_{mult,ε₀}(S; v, ∞, 0, ∅)`
(A.4), with the truncation length `h = ε₀ R̄_{β,λ}`
as a parameter:
`∫_{(Λ²)^{|S|}} 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij} ∏_{i ∈ S} e^{β g_λ(x_i - y_i)}
𝟙_{|x_i - y_i| ≤ h} dx_i dy_i`. -/
noncomputable def multipoleIntegralCut (χ : ℂ → ℝ) (N : ℕ) (β lam M h : ℝ) (S : Finset ℕ) : ℝ :=
  ∫ c in Set.univ.pi (fun _ : S => box N ×ˢ box N),
    multipolePartitionFunctionIntegrand χ β lam M c *
      ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
        (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2))

namespace MultipoleIntegral

theorem cutFactor_le (lam h : ℝ) {S : Finset ℕ} (c : S → ℂ × ℂ) :
    ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
        (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) ≤
      ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) := by
  refine prod_le_prod₀ (fun i _ => mul_nonneg (Real.exp_pos _).le
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) fun i _ => ?_
  refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
  by_cases hi : (c i).1 - (c i).2 ∈ Metric.closedBall (0 : ℂ) h
  · rw [Set.indicator_of_mem hi]; rfl
  · rw [Set.indicator_of_notMem hi]; exact zero_le_one

theorem cutIntegrand_nonneg (lam h : ℝ) {S : Finset ℕ} (c : S → ℂ × ℂ) :
    0 ≤ multipolePartitionFunctionIntegrand χ β lam M c *
      ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
        (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) :=
  mul_nonneg (multipolePartitionFunctionIntegrand_nonneg χ β lam M c)
    (prod_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _))

theorem cutIntegrand_le (lam h : ℝ) {S : Finset ℕ} (c : S → ℂ × ℂ) :
    multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
          (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) ≤
      multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) :=
  mul_le_mul_of_nonneg_left (cutFactor_le lam h c)
    (multipolePartitionFunctionIntegrand_nonneg χ β lam M c)

theorem measurable_cutIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (β M h : ℝ)
    {S : Finset ℕ} :
    Measurable fun c : S → ℂ × ℂ => multipolePartitionFunctionIntegrand χ β lam M c *
      ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
        (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) :=
  (measurable_multipolePartitionFunctionIntegrand hχ hlam β M).mul
    (Finset.measurable_prod _ fun i _ =>
      ((continuous_exp_smearedKernel_sub hχ hlam β).measurable.comp
        (measurable_pi_apply i)).mul
      ((measurable_const.indicator measurableSet_closedBall).comp
        ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd)))

end MultipoleIntegral

namespace MultipoleIntegral.RouteChain

/-- The written chain lower estimate with any cutoff `h ≥ 2λ`.
See Lemma A.3. -/
theorem le_multipoleIntegralCut_chain (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ}
    (hk : 1 ≤ k) (hM : 9 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h : ℝ, 2 * lam ≤ h → ∀ S : Finset ℕ, S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤
          multipoleIntegralCut χ N β lam M h S := by
  obtain ⟨B, hB⟩ := hχ.exists_bound
  let E := Real.exp (-β * (12 * Real.pi * B))
  let c₀ := E ^ (k * k) * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 256) ^ (2 * k - 1) / 4
  have hc₀ : 0 < c₀ := by positivity
  refine ⟨c₀⁻¹, inv_pos.mpr hc₀, fun lam hlam => ⟨lowerN₀ lam k, fun N hN h hh S hS => ?_⟩⟩
  classical
  let σ : S ≃ Fin k := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hS])
  have hr : (σ (σ.symm ⟨0, hk⟩) : ℕ) = 0 := by simp
  have hgeom : 4 * (5 * k * lam) ≤ Real.sqrt N := by
    have := sqrt_ge_of_lowerN₀_le hlam hN
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hfin : ∫⁻ c in univ.pi (fun _ : S => box N ×ˢ box N),
      ENNReal.ofReal (multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
          (Metric.closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2))) ≠ ⊤ :=
    ne_top_of_le_ne_top (lintegral_multipoleIntegrand_ne_top hχ hlam N β M S)
      (lintegral_mono fun c => ENNReal.ofReal_le_ofReal (cutIntegrand_le lam h c))
  have hlow := le_setIntegral_of_chain (β := β) hlam hk hgeom σ
    (measurable_cutIntegrand hχ hlam β M h) (cutIntegrand_nonneg lam h) hfin
    (A := E ^ (k * k)) (by positivity) fun c hc => by
      have hp := le_multipoleIntegrand_of_chain (β := β) hχ hB (by linarith) hlam hM σ hr hc
      refine hp.trans_eq ?_
      congr 1
      apply prod_congr rfl
      intro i _
      have hi : (c i).1 - (c i).2 ∈ Metric.closedBall (0 : ℂ) h := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact ((hc.radii hlam hr i).2.le).trans hh
      rw [indicator_of_mem hi, Pi.one_apply, mul_one]
  simpa only [inv_inv, c₀, multipoleIntegralCut] using hlow

end MultipoleIntegral.RouteChain

/-- **Lemma A.3 for the model `(v, ∞, 0, ∅)` with a finite cutoff** (with the zero model of (A.4)): for `1 < k ≤ p*(β)` and `M > 20` there is
`C > 0` (depending on `χ, β, M, k`) such that for every `λ > 0` there is `N₀` with
`C⁻¹ N λ^{(2-β)k} λ^{2(k-1)} ≤ I^0_{mult,ε₀}(S) ≤ C N λ^{(2-β)k} λ^{2(k-1)}` for all `N ≥ N₀`,
all truncation lengths `h = ε₀ R̄ ≥ 2λ` and all `S` with `|S| = k`. -/
theorem multipoleIntegralCut_two_sided (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 < k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 20 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ h : ℝ, 2 * lam ≤ h →
      ∀ S : Finset ℕ, S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤
            multipoleIntegralCut χ N β lam M h S ∧
          multipoleIntegralCut χ N β lam M h S ≤
            C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  obtain ⟨Cb, hCb0, hCb⟩ := dipoleBond_le hχ
  set W : ℝ := Real.exp (β * Cb)
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg (by linarith) hCb0)
  obtain ⟨Cl, hCl, hlower⟩ := RouteChain.le_multipoleIntegralCut_chain (M := M) hχ hβ hk.le (by linarith)
  set Cu : ℝ := W ^ (k * k) * upperConst χ β M k
  have hCu : 0 ≤ Cu := mul_nonneg (by positivity) (upperConst_nonneg χ β M k)
  set C : ℝ := max (Cu + 1) Cl
  have hC : 0 < C := lt_max_of_lt_left (by linarith)
  refine ⟨C, hC, fun lam hlam => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hlower lam hlam
  refine ⟨N₀, fun N hN h hh S hS => ⟨?_, ?_⟩⟩
  · -- The finite cutoff contains the paper chain since every radius is below `2λ`.
    refine le_trans ?_ (hN₀ N hN h hh S hS)
    have hscale : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
    calc C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
        = C⁻¹ * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by ring
      _ ≤ Cl⁻¹ * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hCl (le_max_right _ _)) hscale
      _ = _ := by ring
  · -- the upper bound
    have hbond : ∀ d e : ℂ × ℂ, stablePairWeight χ β lam d e ≤ W := fun d e =>
      hCb β (by linarith) lam hlam d e
    refine (setIntegral_le_of_le_connected (M := M) hχ hβ hk.le hkp (by linarith) hlam N hS
      (measurable_cutIntegrand hχ hlam β M h) (cutIntegrand_nonneg lam h)
      (K := W ^ (k * k)) (by positivity) fun c _ => ?_).trans ?_
    · have h1 := multipolePartitionFunctionIntegrand_le (M := M) hW hbond c
      rw [hS] at h1
      refine (cutIntegrand_le lam h c).trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 (prod_nonneg fun i _ => (Real.exp_pos _).le)
    · have : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
      calc W ^ (k * k) * upperConst χ β M k * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
          = Cu * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by simp only [Cu]; ring
        _ ≤ C * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
            refine mul_le_mul_of_nonneg_right ?_ this
            exact (le_max_left _ _).trans' (by linarith)
        _ = C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by ring

end MultipoleBKT

end
