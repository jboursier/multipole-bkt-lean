/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegralZ.Basic
public import MultipoleBKT.Appendix.MultipoleIntegralZ.LowerBound
public import MultipoleBKT.Appendix.MultipoleIntegral.UpperBound
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Subtraction
public import MultipoleBKT.Appendix.MultipoleIntegralZ.RouteSingleton.Integration

/-!
# Lemma A.3 for the frozen-bad-point interaction

See Lemma A.3. The singleton lower proof uses the disk construction of Proposition 5.18. For sizes at least two the lower proof follows
the full weighted-event argument.
For these sizes, `le_multipoleIntegralPlus_written` combines the Hessian interaction bound,
the specified chain mass (A.15), the weighted bad-neighbourhood estimate
(A.16) and its absorption using `|V_bad| ≤ N`.

`multipoleIntegralPlus_two_sided` holds on a wider explicit
scale interval. Its small-scale branch uses the written proof. The
`IsGood` comparison covers the rest of that interval.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral UpperBound Hierarchical MultipoleIntegralZ

variable {χ : ℂ → ℝ} {β M : ℝ}

namespace MultipoleIntegralZ

/-- The one-body factor on the support: `e^{L r²/(τ^Z)²} 𝟙_{I_good^Z} e^{β g_λ} 𝟙_{r ≤ ε₀ R̄} ≤
e^{16|L|} e^{β g_λ}`, under the hypotheses of eq. (5.9). -/
theorem plusDipole_le {N p₀ : ℕ} {lam ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hlam : 0 < lam) (hlamh : lam ≤ 4 * (ε₀ * truncationScale p₀ β lam))
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V) (e : ℂ × ℂ) :
    dipoleWeightZ p₀ β lam M ε₀ L V Z e *
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) (e.1 - e.2) ≤
      Real.exp (16 * |L|) * Real.exp (β * smearedKernel χ lam (e.1 - e.2)) := by
  classical
  set h := ε₀ * truncationScale p₀ β lam
  by_cases hr : ‖e.1 - e.2‖ ≤ h
  · have hmem : e.1 - e.2 ∈ closedBall (0 : ℂ) h := by rwa [mem_closedBall_zero_iff]
    rw [indicator_of_mem hmem]
    unfold dipoleWeightZ
    by_cases hg : IsGoodZ p₀ β lam M ε₀ V Z e
    · simp only [hg, ↓reduceIte, mul_one]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      have hτ := goodRadiusZ_ge hlam hlamh hM hV hg (by linarith)
      have hτ0 : 0 < goodRadiusZ p₀ β lam ε₀ V Z e := goodRadiusZ_pos hlam e
      have hq : ‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e ≤ 4 := by
        rw [div_le_iff₀ hτ0]
        have := le_max_left ‖e.1 - e.2‖ lam
        linarith
      have hq0 : 0 ≤ ‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e := by positivity
      have hsq : (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2 ≤ 16 := by nlinarith
      calc L * (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2
          ≤ |L| * (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2 :=
            mul_le_mul_of_nonneg_right (le_abs_self L) (sq_nonneg _)
        _ ≤ |L| * 16 := mul_le_mul_of_nonneg_left hsq (abs_nonneg L)
        _ = 16 * |L| := by ring
    · simp only [hg, ↓reduceIte, mul_zero, zero_mul]
      positivity
  · have hmem : e.1 - e.2 ∉ closedBall (0 : ℂ) h := by
      rwa [mem_closedBall_zero_iff]
    rw [indicator_of_notMem hmem, mul_zero]
    positivity

/-- A dipole outside the support (`r > ε₀ R̄` or outside `I_good^Z`) kills the one-body factor. -/
theorem plusDipole_eq_zero {N p₀ : ℕ} {lam ε₀ L : ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} {e : ℂ × ℂ}
    (he : ¬ (‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam ∧ IsGoodZ p₀ β lam M ε₀ V Z e)) :
    dipoleWeightZ p₀ β lam M ε₀ L V Z e *
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) (e.1 - e.2) = 0 := by
  classical
  rw [not_and_or] at he
  rcases he with hr | hg
  · have hmem : e.1 - e.2 ∉ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam) := by
      rwa [mem_closedBall_zero_iff]
    rw [indicator_of_notMem hmem, mul_zero]
  · unfold dipoleWeightZ
    simp only [hg, ↓reduceIte, mul_zero, zero_mul]

end MultipoleIntegralZ

/-- **Lemma A.3 for `(v^Z, τ^Z, L, Z)`, upper bound** (eq. (A.5)): for `1 ≤ k ≤ p*(β)`, `M ≥ 0` and `L ∈ ℝ` there is `C > 0` (depending on
`χ, β, M, L, k`) such that for every `λ > 0`, every `N`, `p₀`, `ε₀` with `2λ ≤ ε₀ R̄`
and `3^{p(β)} ≤ M`, every frozen configuration `(V, Z)` with `I_bad^V(Z) = V` and every `S` with
`|S| = k`, `I^{+,Z}_{mult,ε₀}(S) ≤ C N λ^{(2-β)k} λ^{2(k-1)}`. -/
theorem multipoleIntegralPlus_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ (N p₀ : ℕ) (ε₀ : ℝ),
      2 * lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ S : Finset ℕ, S.card = k →
        multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S ≤
          C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  classical
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨Cb, hCb0, hCb⟩ := neg_le_dipoleInteraction hχ
  obtain ⟨C₃, hC₃, hC₃'⟩ := abs_interactionGoodZ_sub_le hχ
  set W : ℝ := Real.exp (β * (Cb + 16 * C₃))
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg hβ0 (by positivity))
  set K : ℝ := W ^ (k * k) * Real.exp (16 * |L|) ^ k
  have hK : 0 ≤ K := by positivity
  refine ⟨K * (upperConst χ β M k + 1), mul_pos (by positivity)
    (by linarith [upperConst_nonneg χ β M k]),
    fun lam hlam N p₀ ε₀ hh hM3 V Z hV S hS => ?_⟩
  set h := ε₀ * truncationScale p₀ β lam with hh_def
  have hh0 : 0 ≤ h := by linarith
  have hlamh : lam ≤ 4 * h := by linarith
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  -- the pair bound on the support
  have hpair : ∀ d e : ℂ × ℂ, ‖d.1 - d.2‖ ≤ h → IsGoodZ p₀ β lam M ε₀ V Z d →
      ‖e.1 - e.2‖ ≤ h → IsGoodZ p₀ β lam M ε₀ V Z e →
      |(if IsStableDipolePair d e then
        Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z d e) else 0)| ≤ W := by
    intro d e hd hdg he heg
    split_ifs with hst
    · rw [abs_of_nonneg (Real.exp_pos _).le]
      refine Real.exp_le_exp.2 ?_
      have hτd := goodRadiusZ_ge hlam hlamh hM3 hV hdg (by linarith)
      have hτe := goodRadiusZ_ge hlam hlamh hM3 hV heg (by linarith)
      set a := goodRadiusZ p₀ β lam ε₀ V Z d
      set b := goodRadiusZ p₀ β lam ε₀ V Z e
      have ha0 : 0 < a := goodRadiusZ_pos hlam d
      have hm0 : 0 < max a b := lt_max_of_lt_left ha0
      have hrd : ‖d.1 - d.2‖ ≤ 4 * max a b := by
        have := le_max_left ‖d.1 - d.2‖ lam
        have := le_max_left a b
        linarith
      have hre : ‖e.1 - e.2‖ ≤ 4 * max a b := by
        have := le_max_left ‖e.1 - e.2‖ lam
        have := le_max_right a b
        linarith
      have hprod : ‖d.1 - d.2‖ * ‖e.1 - e.2‖ ≤ 16 * max a b ^ 2 := by
        have := mul_le_mul hrd hre (norm_nonneg _) (by positivity)
        nlinarith
      have hdiff := hC₃' p₀ β lam ε₀ V Z hlam d e
      have hq : C₃ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / max a b ^ 2 ≤ 16 * C₃ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have hv := hCb lam hlam d e hst
      rw [abs_le] at hdiff
      nlinarith
    · rw [abs_zero]; linarith
  refine (setIntegral_le_of_le_connected (M := M) hχ hβ hk hkp hM hlam N hS
    (measurable_plusIntegrand hχ hlam) plusIntegrand_nonneg hK fun c _ => ?_).trans ?_
  · -- the pointwise bound
    have hdipK : ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
        (closedBall (0 : ℂ) h).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
          ((c i).1 - (c i).2)) ≤
        Real.exp (16 * |L|) ^ k * ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) := by
      calc _ ≤ ∏ i : S, (Real.exp (16 * |L|) *
            Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) :=
            prod_le_prod₀ (fun i _ => plusDipole_nonneg _) fun i _ =>
              plusDipole_le hlam hlamh hM3 hV (c i)
        _ = _ := by rw [prod_mul_distrib, prod_const, card_univ, hcard]
    have hG0 : 0 ≤ ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) :=
      prod_nonneg fun i _ => (Real.exp_pos _).le
    unfold plusIntegrand
    by_cases hall : ∀ i : S, ‖(c i).1 - (c i).2‖ ≤ h ∧ IsGoodZ p₀ β lam M ε₀ V Z (c i)
    · have hP : ∏ i : S, ∏ j : S, (if i < j then
          (if IsStableDipolePair (c i) (c j) then
            Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) ≤
          W ^ (k * k) := by
        have hb := abs_prod_prod_le (fun i j : S => if i < j then
          (if IsStableDipolePair (c i) (c j) then
            Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1)
          (W := W) (fun i j => by
            by_cases hij : i < j
            · simp only [hij, ↓reduceIte]
              exact hpair _ _ (hall i).1 (hall i).2 (hall j).1 (hall j).2
            · simp only [hij, ↓reduceIte, abs_one]
              exact hW)
        rw [hcard] at hb
        exact (le_abs_self _).trans hb
      have hP0 : 0 ≤ ∏ i : S, ∏ j : S, (if i < j then
          (if IsStableDipolePair (c i) (c j) then
            Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) :=
        prod_nonneg fun i _ => prod_nonneg fun j _ => by
          by_cases hij : i < j
          · simp only [hij, ↓reduceIte]
            exact plusPair_nonneg _ _
          · simp only [hij, ↓reduceIte]
            exact zero_le_one
      by_cases hconn : (SimpleGraph.fromRel fun i j : S =>
          MultipoleLinked M lam (c i) (c j)).Connected
      · simp only [hconn, ↓reduceIte, one_mul]
        calc _ ≤ W ^ (k * k) * (Real.exp (16 * |L|) ^ k *
              ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) :=
              mul_le_mul hP hdipK (prod_nonneg fun i _ => plusDipole_nonneg _) (by positivity)
          _ = _ := by simp only [K]; ring
      · simp only [hconn, ↓reduceIte, zero_mul, mul_zero]
        exact le_rfl
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hz : ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
          (closedBall (0 : ℂ) h).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
            ((c i).1 - (c i).2)) = 0 :=
        prod_eq_zero (mem_univ i₀) (plusDipole_eq_zero (fun h' => absurd h'.2 (hi₀ h'.1)))
      rw [hz, mul_zero]
      refine mul_nonneg hK (mul_nonneg (by split_ifs <;> norm_num) hG0)
  · have hU := upperConst_nonneg χ β M k
    have : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
    calc K * upperConst χ β M k * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
        = K * upperConst χ β M k * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by ring
      _ ≤ K * (upperConst χ β M k + 1) * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
          gcongr
          linarith
      _ = K * (upperConst χ β M k + 1) * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
          ring

namespace MultipoleIntegralZ

/-- The integral defining `I^{+,Z}_{mult,ε₀}(S)` is finite: the integrand is bounded on `(Λ²)^S`. -/
theorem lintegral_plusIntegrand_ne_top (hχ : IsMollifier χ) (hβ : 0 ≤ β) {N p₀ : ℕ}
    {lam ε₀ L : ℝ} (hlam : 0 < lam) (hε₀ : 0 < ε₀) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (S : Finset ℕ) :
    ∫⁻ c in Set.univ.pi (fun _ : S => box N ×ˢ box N),
      ENNReal.ofReal (plusIntegrand χ p₀ β lam M ε₀ L V Z c) ≠ ⊤ := by
  classical
  obtain ⟨B, hB⟩ := exists_abs_interactionGoodZ_le (N := N) (p₀ := p₀) (β := β) (ε₀ := ε₀)
    (V := V) (Z := Z) hχ hlam
  set h := ε₀ * truncationScale p₀ β lam
  set W : ℝ := Real.exp (|β| * B) + 1
  set D : ℝ := Real.exp (|L| * (h / lam) ^ 2) * (Real.exp (β * MultipoleIntegral.kernelConst χ) * lam ^ (-β))
  have hD0 : 0 ≤ D := by positivity
  set T : ℝ := W ^ (S.card * S.card) * D ^ S.card
  have hbound : ∀ c ∈ Set.univ.pi (fun _ : S => box N ×ˢ box N),
      plusIntegrand χ p₀ β lam M ε₀ L V Z c ≤ T := by
    intro c hc
    rw [Set.mem_univ_pi] at hc
    unfold plusIntegrand
    by_cases hall : ∀ i : S, ‖(c i).1 - (c i).2‖ ≤ h
    · have hsupp : ∀ i : S, c i ∈ supportSet N p₀ β lam ε₀ := fun i => ⟨hc i, hall i⟩
      have hP : ∏ i : S, ∏ j : S, (if i < j then
          (if IsStableDipolePair (c i) (c j) then
            Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) ≤
          W ^ (S.card * S.card) := by
        have hb := abs_prod_prod_le (fun i j : S => if i < j then
          (if IsStableDipolePair (c i) (c j) then
            Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1)
          (W := W) (fun i j => by
            by_cases hij : i < j
            · simp only [hij, ↓reduceIte]
              split_ifs
              · rw [abs_of_nonneg (Real.exp_pos _).le]
                have h1 : -β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) ≤ |β| * B := by
                  calc _ ≤ |-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)| := le_abs_self _
                    _ = |β| * |interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)| := by
                        rw [abs_mul, abs_neg]
                    _ ≤ |β| * B := mul_le_mul_of_nonneg_left (hB _ (hsupp i) _ (hsupp j))
                        (abs_nonneg β)
                have := Real.exp_le_exp.2 h1
                linarith
              · rw [abs_zero]; positivity
            · simp only [hij, ↓reduceIte, abs_one]
              have := Real.exp_pos (|β| * B)
              linarith)
        rw [Fintype.card_coe] at hb
        exact (le_abs_self _).trans hb
      have hdip : ∀ i : S, dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
          (closedBall (0 : ℂ) h).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
            ((c i).1 - (c i).2) ≤ D := by
        intro i
        refine mul_le_mul (dipoleWeightZ_le hlam hε₀ (hsupp i)) ?_ (cutoffDensity_nonneg β _ _)
          (Real.exp_pos _).le
        refine (cutoffDensity_le β _ (c i)).trans ?_
        refine (exp_smearedKernel_le hχ hβ hlam _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact Real.rpow_le_rpow_of_nonpos hlam (le_max_right _ _) (by linarith)
      have hdips : ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
          (closedBall (0 : ℂ) h).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
            ((c i).1 - (c i).2)) ≤ D ^ S.card := by
        calc _ ≤ ∏ _i : S, D := prod_le_prod₀ (fun i _ => plusDipole_nonneg _) fun i _ => hdip i
          _ = D ^ S.card := by rw [prod_const, card_univ, Fintype.card_coe]
      have hP0 : 0 ≤ ∏ i : S, ∏ j : S, (if i < j then
          (if IsStableDipolePair (c i) (c j) then
            Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) :=
        prod_nonneg fun i _ => prod_nonneg fun j _ => by
          by_cases hij : i < j
          · simp only [hij, ↓reduceIte]
            exact plusPair_nonneg _ _
          · simp only [hij, ↓reduceIte]
            exact zero_le_one
      have hconn : (if (SimpleGraph.fromRel fun i j : S =>
          MultipoleLinked M lam (c i) (c j)).Connected then (1 : ℝ) else 0) ≤ 1 := by
        split_ifs <;> norm_num
      have hconn0 : (0 : ℝ) ≤ (if (SimpleGraph.fromRel fun i j : S =>
          MultipoleLinked M lam (c i) (c j)).Connected then (1 : ℝ) else 0) := by
        split_ifs <;> norm_num
      calc _ ≤ (1 * W ^ (S.card * S.card)) * D ^ S.card :=
            mul_le_mul (mul_le_mul hconn hP hP0 zero_le_one) hdips
              (prod_nonneg fun i _ => plusDipole_nonneg _) (by positivity)
        _ = T := by simp only [T]; ring
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hz : ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
          (closedBall (0 : ℂ) h).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
            ((c i).1 - (c i).2)) = 0 :=
        prod_eq_zero (mem_univ i₀) (plusDipole_eq_zero (fun h' => absurd h'.1 (not_le.2 hi₀)))
      rw [hz, mul_zero]
      positivity
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono measurable_const fun c hc =>
    ENNReal.ofReal_le_ofReal (hbound c hc))
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_pi_box_prod_lt_top N).ne

end MultipoleIntegralZ

namespace MultipoleIntegralZ

/-- **The integrand on good clusters inside `I_good^Z`**: on a good cluster
(root `r₀`, `σ r₀ = 0`, `k = |S|` dipoles) all of whose dipoles are in `I_good^Z`, with
`2λ ≤ ε₀ R̄`, `M ≥ 9` and eq. (A.35) with constant `C₃`,
`I^{+,Z}`'s integrand is at least `E^{k²} e^{-4k|L|} ((4λ)^{-β})^k`,
`E = e^{-β(2 c_χ + 2 log(8k) + 4 C₃)}`. -/
theorem le_plusIntegrand_of_isGood (hχ : IsMollifier χ) (hβ : 0 ≤ β) {lam : ℝ} (hlam : 0 < lam)
    (hM : 9 ≤ M) {S : Finset ℕ} {N p₀ k : ℕ} (σ : S ≃ Fin k) {r₀ : S}
    (hr₀ : ((σ r₀ : ℕ) : ℝ) = 0) {ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hh : 2 * lam ≤ ε₀ * truncationScale p₀ β lam) {C₃ : ℝ} (hC₃ : 0 < C₃)
    (hC₃' : ∀ d e : ℂ × ℂ,
      |interactionGoodZ χ p₀ β lam ε₀ V Z d e - dipoleInteraction χ lam d e| ≤
        C₃ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
          max (goodRadiusZ p₀ β lam ε₀ V Z d) (goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2)
    {c : S → ℂ × ℂ} (hc : IsGood N lam σ r₀ c) (hgoodZ : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)) :
    Real.exp (-β * (2 * MultipoleIntegral.kernelConst χ + 2 * Real.log (8 * k) + 4 * C₃)) ^
        (k * k) * Real.exp (-(4 * |L|)) ^ k * ((4 * lam) ^ (-β)) ^ k ≤
      plusIntegrand χ p₀ β lam M ε₀ L V Z c := by
  classical
  have hcard : Fintype.card S = k := by simpa using Fintype.card_congr σ
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) (σ r₀).2
  set V₀ : ℝ := 2 * MultipoleIntegral.kernelConst χ + 2 * Real.log (8 * k)
  have hV₀ : 0 ≤ V₀ := by
    have : (1 : ℝ) ≤ 8 * k := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have := Real.log_nonneg this
    have := kernelConst_nonneg χ
    positivity
  set E : ℝ := Real.exp (-β * (V₀ + 4 * C₃))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hr : ∀ i, ‖(c i).1 - (c i).2‖ < 7 * lam / 4 := fun i => hc.norm_fst_sub_snd i hlam
  have hconn : (SimpleGraph.fromRel fun i j : S =>
      MultipoleLinked M lam (c i) (c j)).Connected := by
    refine connected_of_chain σ hk fun i j hij => ?_
    have hne : i ≠ j := fun h => by rw [h] at hij; omega
    exact (SimpleGraph.fromRel_adj _ _ _).2
      ⟨hne, Or.inl (hc.multipoleLinked hlam hr₀ hM hij)⟩
  -- the pair factors
  have hpair : ∀ i j : S, E ≤ (if i < j then
      (if IsStableDipolePair (c i) (c j) then
        Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) := by
    intro i j
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      have hst := hc.isStableDipolePair hlam hr₀ hij.ne
      simp only [hst, ↓reduceIte]
      refine Real.exp_le_exp.2 ?_
      have hv := hc.dipoleInteraction_le hχ hlam hr₀ i j
      have hdiff := hC₃' (c i) (c j)
      set a := goodRadiusZ p₀ β lam ε₀ V Z (c i)
      set b := goodRadiusZ p₀ β lam ε₀ V Z (c j)
      have ha : lam ≤ a := lam_le_goodRadiusZ _
      have hm : lam ≤ max a b := ha.trans (le_max_left _ _)
      have hm0 : 0 < max a b := hlam.trans_le hm
      have hri := hr i
      have hrj := hr j
      have hprod : ‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖ ≤ 4 * max a b ^ 2 := by
        have h1 : ‖(c i).1 - (c i).2‖ ≤ 2 * max a b := by linarith
        have h2 : ‖(c j).1 - (c j).2‖ ≤ 2 * max a b := by linarith
        have := mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
        nlinarith
      have hq : C₃ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max a b ^ 2 ≤ 4 * C₃ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      rw [abs_le] at hdiff
      nlinarith
    · simp only [hij, ↓reduceIte]
      exact hE1
  have hpairs : E ^ (k * k) ≤ ∏ i : S, ∏ j : S, (if i < j then
      (if IsStableDipolePair (c i) (c j) then
        Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) := by
    calc E ^ (k * k) = ∏ _i : S, ∏ _j : S, E := by
          rw [prod_const, prod_const, card_univ, hcard, ← pow_mul]
      _ ≤ _ := prod_le_prod₀ (fun i _ => prod_nonneg fun j _ => hE0) fun i _ =>
          prod_le_prod₀ (fun j _ => hE0) fun j _ => hpair i j
  -- the dipole factors
  have h4 : 0 < 4 * lam := by positivity
  have hdip : ∀ i : S, Real.exp (-(4 * |L|)) * (4 * lam) ^ (-β) ≤
      dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2) := by
    intro i
    have hmem : (c i).1 - (c i).2 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam) := by
      rw [mem_closedBall_zero_iff]
      linarith [hr i]
    rw [indicator_of_mem hmem]
    unfold dipoleWeightZ
    simp only [hgoodZ i, ↓reduceIte, mul_one]
    refine mul_le_mul (Real.exp_le_exp.2 ?_) ?_ (Real.rpow_pos_of_pos h4 _).le
      (Real.exp_pos _).le
    · have hτ : lam ≤ goodRadiusZ p₀ β lam ε₀ V Z (c i) := lam_le_goodRadiusZ _
      have hτ0 : 0 < goodRadiusZ p₀ β lam ε₀ V Z (c i) := hlam.trans_le hτ
      set q := ‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (c i)
      have hq : q ≤ 2 := by
        simp only [q]
        rw [div_le_iff₀ hτ0]
        linarith [hr i]
      have hq0 : 0 ≤ q := by positivity
      have hsq : q ^ 2 ≤ 4 := by nlinarith
      have : -|L| ≤ L := neg_abs_le L
      nlinarith [abs_nonneg L, sq_nonneg q]
    · have h1 := neg_log_add_le_smearedKernel hχ hlam ((c i).1 - (c i).2)
      have h3 : Real.log (‖(c i).1 - (c i).2‖ + 2 * lam) ≤ Real.log (4 * lam) :=
        Real.log_le_log (by positivity) (by linarith [hr i])
      rw [Real.rpow_def_of_pos h4]
      refine Real.exp_le_exp.2 ?_
      nlinarith
  have hdips : Real.exp (-(4 * |L|)) ^ k * ((4 * lam) ^ (-β)) ^ k ≤
      ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) := by
    have heq : Real.exp (-(4 * |L|)) ^ k * ((4 * lam) ^ (-β)) ^ k =
        ∏ _i : S, (Real.exp (-(4 * |L|)) * (4 * lam) ^ (-β)) := by
      rw [prod_const, card_univ, hcard, mul_pow]
    rw [heq]
    exact prod_le_prod₀ (fun i _ => mul_nonneg (Real.exp_pos _).le
      (Real.rpow_pos_of_pos h4 _).le) fun i _ => hdip i
  unfold plusIntegrand
  rw [ite_eq_left hconn, one_mul, mul_assoc]
  exact mul_le_mul hpairs hdips (by positivity)
    (prod_nonneg fun i _ => prod_nonneg fun j _ => le_trans hE0 (hpair i j))

/-- Internal comparison on the full written event, using the Hessian estimate.
See Lemma A.3. -/
theorem internal_le_plusIntegrand_of_event (hχ : IsMollifier χ) {B : ℝ} (hB : ∀ x, χ x ≤ B) (hβ : 0 ≤ β) {lam : ℝ} (hlam : 0 < lam)
    (hM : 9 ≤ M) {S : Finset ℕ} {N p₀ k : ℕ} (σ : S ≃ Fin k) {r₀ : S}
    {ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hh : 2 * lam ≤ ε₀ * truncationScale p₀ β lam) {C₃ : ℝ} (hC₃ : 0 < C₃)
    (hC₃' : ∀ d e : ℂ × ℂ,
      |interactionGoodZ χ p₀ β lam ε₀ V Z d e - dipoleInteraction χ lam d e| ≤
        C₃ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
          max (goodRadiusZ p₀ β lam ε₀ V Z d) (goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2)
    {c : S → ℂ × ℂ} (hc : RouteChain.Event lam σ c) (hstable : RouteChain.Stable c) (hgoodZ : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)) :
    Real.exp (-β * (12 * Real.pi * B + 4 * C₃)) ^ (k * k) * Real.exp (-(4 * |L|)) ^ k *
        (∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) ≤
      plusIntegrand χ p₀ β lam M ε₀ L V Z c := by
  classical
  have hcard : Fintype.card S = k := by simpa using Fintype.card_congr σ
  set V₀ : ℝ := 12 * Real.pi * B
  have hB0 := hχ.nonneg_of_le hB
  have hV₀ : 0 ≤ V₀ := by positivity
  set E : ℝ := Real.exp (-β * (V₀ + 4 * C₃))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hr : ∀ i, ‖(c i).1 - (c i).2‖ < 2 * lam := fun i => (hc.1 i).2
  have hconn : (SimpleGraph.fromRel fun i j : S =>
      MultipoleLinked M lam (c i) (c j)).Connected := hc.connected hlam (by linarith) r₀
  -- the pair factors
  have hpair : ∀ i j : S, E ≤ (if i < j then
      (if IsStableDipolePair (c i) (c j) then
        Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) := by
    intro i j
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      have hst := hstable i j hij
      simp only [hst, ↓reduceIte]
      refine Real.exp_le_exp.2 ?_
      have hv := hc.abs_interaction_le hχ hB hlam i j
      have hv' := le_abs_self (dipoleInteraction χ lam (c i) (c j))
      have hdiff := hC₃' (c i) (c j)
      set a := goodRadiusZ p₀ β lam ε₀ V Z (c i)
      set b := goodRadiusZ p₀ β lam ε₀ V Z (c j)
      have ha : lam ≤ a := lam_le_goodRadiusZ _
      have hm : lam ≤ max a b := ha.trans (le_max_left _ _)
      have hm0 : 0 < max a b := hlam.trans_le hm
      have hri := hr i
      have hrj := hr j
      have hprod : ‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖ ≤ 4 * max a b ^ 2 := by
        have h1 : ‖(c i).1 - (c i).2‖ ≤ 2 * max a b := by linarith
        have h2 : ‖(c j).1 - (c j).2‖ ≤ 2 * max a b := by linarith
        have := mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
        nlinarith
      have hq : C₃ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max a b ^ 2 ≤ 4 * C₃ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      rw [abs_le] at hdiff
      nlinarith
    · simp only [hij, ↓reduceIte]
      exact hE1
  have hpairs : E ^ (k * k) ≤ ∏ i : S, ∏ j : S, (if i < j then
      (if IsStableDipolePair (c i) (c j) then
        Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) := by
    calc E ^ (k * k) = ∏ _i : S, ∏ _j : S, E := by
          rw [prod_const, prod_const, card_univ, hcard, ← pow_mul]
      _ ≤ _ := prod_le_prod₀ (fun i _ => prod_nonneg fun j _ => hE0) fun i _ =>
          prod_le_prod₀ (fun j _ => hE0) fun j _ => hpair i j
  -- the dipole factors
  have hdip : ∀ i : S, Real.exp (-(4 * |L|)) * Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) ≤
      dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2) := by
    intro i
    have hmem : (c i).1 - (c i).2 ∈ closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam) := by
      rw [mem_closedBall_zero_iff]
      linarith [hr i]
    rw [indicator_of_mem hmem]
    unfold dipoleWeightZ
    simp only [hgoodZ i, ↓reduceIte, mul_one]
    refine mul_le_mul (Real.exp_le_exp.2 ?_) le_rfl (Real.exp_pos _).le (Real.exp_pos _).le
    have hτ : lam ≤ goodRadiusZ p₀ β lam ε₀ V Z (c i) := lam_le_goodRadiusZ _
    have hτ0 : 0 < goodRadiusZ p₀ β lam ε₀ V Z (c i) := hlam.trans_le hτ
    set q := ‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (c i)
    have hq : q ≤ 2 := by
      simp only [q]
      rw [div_le_iff₀ hτ0]
      linarith [hr i]
    have hq0 : 0 ≤ q := by positivity
    have hsq : q ^ 2 ≤ 4 := by nlinarith
    have : -|L| ≤ L := neg_abs_le L
    nlinarith [abs_nonneg L, sq_nonneg q]
  have hdips : Real.exp (-(4 * |L|)) ^ k *
      (∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) ≤
      ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
        (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) := by
    have hp : Real.exp (-(4 * |L|)) ^ k = ∏ _i : S, Real.exp (-(4 * |L|)) := by
      rw [prod_const, card_univ, hcard]
    rw [hp, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun i _ => by positivity) fun i _ => hdip i
  unfold plusIntegrand
  rw [ite_eq_left hconn, one_mul, mul_assoc]
  exact mul_le_mul hpairs hdips (by positivity)
    (prod_nonneg fun i _ => prod_nonneg fun j _ => le_trans hE0 (hpair i j))

end MultipoleIntegralZ

/-- The singleton lower bound by the disk construction of Proposition 5.18.
See Proposition 5.18.
Remove a boundary layer and the `(M+1)λ` disks around bad endpoints, then
integrate the displacement over `r ≤ λ`. -/
theorem le_multipoleIntegralPlus_singleton_written (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 0 ≤ M) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (p₀ : ℕ) (ε₀ : ℝ),
      2 * lam ≤ ε₀ * truncationScale p₀ β lam →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (S : Finset ℕ), S.card = 1 →
        C⁻¹ * N * lam ^ (2 - β) ≤ multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S := by
  let a : ℝ := Real.exp (-|L|) * (3 : ℝ) ^ (-β) * Real.pi / 8
  have ha : 0 < a := by positivity
  refine ⟨a⁻¹, by positivity, (16 * (M + 1))⁻¹, by positivity,
    fun lam hlam hsmall => ⟨lowerN₀ lam 1, fun N hN p₀ ε₀ hh V Z S hS => ?_⟩⟩
  let B := innerBox N (2 * lam) \ badNbhd V Z ((M + 1) * lam)
  have hBm : MeasurableSet B := (measurableSet_innerBox N _).diff (measurableSet_badNbhd V Z _)
  have harea : ENNReal.ofReal (N / 8) ≤ volume B :=
    RouteSingleton.root_area hlam hM hsmall (by
      have := sqrt_ge_of_lowerN₀_le hlam hN
      norm_num at this
      linarith) V Z
  have hε₀ : 0 < ε₀ := by
    have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hR.le
    linarith
  have hpoint (c : S → ℂ × ℂ) (hc : ∀ i, (c i).1 ∈ B ∧ ‖(c i).1 - (c i).2‖ ≤ lam) :
      Real.exp (-|L|) * (3 * lam) ^ (-β) ≤ plusIntegrand χ p₀ β lam M ε₀ L V Z c :=
    RouteSingleton.le_plusIntegrand_of_disk hχ (by linarith) hlam hS hM (by linarith)
      (fun i => (hc i).2) (fun i => (hc i).1.2)
  have hi := RouteSingleton.le_integral_of_disk hS hlam hBm Set.sdiff_subset
    (by positivity : (0 : ℝ) ≤ N / 8) (by positivity : 0 ≤ Real.exp (-|L|) * (3 * lam) ^ (-β))
    harea (measurable_plusIntegrand hχ hlam) plusIntegrand_nonneg
    (lintegral_plusIntegrand_ne_top hχ (by linarith) hlam hε₀ V Z S) hpoint
  unfold multipoleIntegralPlus
  refine le_trans (le_of_eq ?_) hi
  rw [inv_inv, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hlam.le]
  have hp : lam ^ (2 - β) = lam ^ (-β) * lam ^ 2 := by
    rw [← Real.rpow_natCast lam 2, ← Real.rpow_add hlam]
    congr 1
    ring
  rw [hp]
  dsimp [a]
  ring

/-- The paper lower bound for the frozen model, assembled from the
singleton disk when `k = 1`, and otherwise the full weighted event and its
weighted bad-neighbourhood loss. See (A.15), (A.16). -/
theorem le_multipoleIntegralPlus_written (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ}
    (hk : 1 ≤ k) (hM : 9 ≤ M) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (p₀ : ℕ) (ε₀ : ℝ),
      2 * lam ≤ ε₀ * truncationScale p₀ β lam →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (S : Finset ℕ), S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤
          multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S := by
  classical
  by_cases hsingleton : k = 1
  · subst k
    simpa using le_multipoleIntegralPlus_singleton_written hχ hβ (by linarith) L
  obtain ⟨B, hB⟩ := hχ.exists_bound
  obtain ⟨C₃, hC₃, hC₃'⟩ := abs_interactionGoodZ_sub_le hχ
  let A : ℝ := Real.exp (-β * (12 * Real.pi * B + 4 * C₃)) ^ (k * k) * Real.exp (-(4 * |L|)) ^ k
  let a := RouteChain.lowerCoefficient β k
  let b := RouteChain.lossCoefficient χ β M k
  have ha : 0 < a := RouteChain.lowerCoefficient_pos β k
  have hb : 0 ≤ b := by dsimp [b, RouteChain.lossCoefficient]; positivity
  have hA : 0 < A := by positivity
  let lam₀ := min 1 (a / (2 * (b + 1)))
  have hl0 : 0 < lam₀ := lt_min one_pos (by positivity)
  refine ⟨(A * (a / 2))⁻¹, by positivity, lam₀, hl0, fun lam hlam hsmall =>
    ⟨lowerN₀ lam k, fun N hN p₀ ε₀ hh V Z S hS => ?_⟩⟩
  have hsmall' : b * lam ^ 2 ≤ a / 2 := by
    have h1 : lam ≤ 1 := hsmall.trans (min_le_left _ _)
    have h2 : lam ≤ a / (2 * (b + 1)) := hsmall.trans (min_le_right _ _)
    have h3 := (le_div_iff₀ (by positivity : 0 < 2 * (b + 1))).mp h2
    have h4 : lam ^ 2 ≤ lam := by nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4 hb
    nlinarith
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hε₀ : 0 < ε₀ := by
    by_contra hn
    have : ε₀ * truncationScale p₀ β lam ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hR.le
    linarith
  let σ : S ≃ Fin k := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hS])
  let root : S := σ.symm ⟨0, hk⟩
  let W : (S → ℂ × ℂ) → ℝ≥0∞ :=
    {c | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)}.indicator (RouteChain.supportWeight χ N β lam σ)
  have hgeom : 4 * (5 * k * lam) ≤ Real.sqrt N := by
    have := sqrt_ge_of_lowerN₀_le hlam hN
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hmass := RouteChain.good_mass_lower (p₀ := p₀) (ε₀ := ε₀) hχ (by linarith) hlam (by linarith) hk V Z σ hgeom hsmall'
  have hpoint (c : S → ℂ × ℂ) : ENNReal.ofReal A * W c ≤
      (univ.pi (fun _ : S => box N ×ˢ box N)).indicator (fun c => ENNReal.ofReal
        (plusIntegrand χ p₀ β lam M ε₀ L V Z c)) c := by
    by_cases hg : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)
    · change ENNReal.ofReal A * ({c | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)}.indicator
        (RouteChain.supportWeight χ N β lam σ) c) ≤ _
      rw [indicator_of_mem (show c ∈ {c | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)} from hg)]
      by_cases hc : c ∈ univ.pi (fun _ : S => box N ×ˢ box N) ∧ RouteChain.Event lam σ c ∧ RouteChain.Stable c
      · rw [RouteChain.supportWeight, indicator_of_mem (show c ∈ {c | c ∈ univ.pi
          (fun _ : S => box N ×ˢ box N) ∧ RouteChain.Event lam σ c ∧ RouteChain.Stable c} from hc),
          indicator_of_mem hc.1]
        have hp := internal_le_plusIntegrand_of_event (L := L) (r₀ := root) hχ hB (by linarith) hlam hM σ hh hC₃
          (hC₃' p₀ β lam ε₀ V Z hlam) hc.2.1 hc.2.2 hg
        change ENNReal.ofReal A * (∏ i : S, ENNReal.ofReal
          (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) ≤ _
        rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
          ← ENNReal.ofReal_mul hA.le]
        exact ENNReal.ofReal_le_ofReal (by simpa only [A, mul_assoc] using hp)
      · rw [RouteChain.supportWeight, indicator_of_notMem (show c ∉ {c | c ∈ univ.pi
          (fun _ : S => box N ×ˢ box N) ∧ RouteChain.Event lam σ c ∧ RouteChain.Stable c} from hc), mul_zero]
        exact zero_le
    · have hz : W c = 0 := indicator_of_notMem (show c ∉ {c | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)} from hg) _
      rw [hz, mul_zero]
      exact zero_le
  have hlint : ENNReal.ofReal (A * (a / 2) * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) ≤
      ∫⁻ c in univ.pi (fun _ : S => box N ×ˢ box N), ENNReal.ofReal (plusIntegrand χ p₀ β lam M ε₀ L V Z c) := by
    rw [← lintegral_indicator (measurableSet_pi_box_prod N)]
    calc _ = ENNReal.ofReal A * ENNReal.ofReal
          (a / 2 * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
          rw [← ENNReal.ofReal_mul hA.le]
          congr 1
          ring
      _ ≤ ENNReal.ofReal A * ∫⁻ c, W c := mul_le_mul' le_rfl hmass
      _ = ∫⁻ c, ENNReal.ofReal A * W c := (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ _ := lintegral_mono hpoint
  unfold multipoleIntegralPlus
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall plusIntegrand_nonneg)
    (measurable_plusIntegrand hχ hlam).aestronglyMeasurable, inv_inv]
  exact (ENNReal.ofReal_le_iff_le_toReal
    (lintegral_plusIntegrand_ne_top hχ (by linarith) hlam hε₀ V Z S)).mp hlint

/-- **Lemma A.3 for `(v^Z, τ^Z, L, Z)`, lower bound** (eq. (A.5)): for `k ≥ 1`, `M ≥ 9` and `L ∈ ℝ` there is `C > 0` (depending on
`χ, β, M, L, k`) such that for every `λ ∈ (0, (16 (6k + 2M))⁻¹]` there is `N₀` with
`C⁻¹ N λ^{(2-β)k} λ^{2(k-1)} ≤ I^{+,Z}_{mult,ε₀}(S)` for all `N ≥ N₀`, `p₀`, `ε₀` with
`2λ ≤ ε₀ R̄`, every frozen configuration `(V, Z)` and every `S` with `|S| = k`. -/
theorem internal_le_multipoleIntegralPlus_compat (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hM : 9 ≤ M) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ (16 * (6 * k + 2 * M))⁻¹ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (p₀ : ℕ) (ε₀ : ℝ), 2 * lam ≤ ε₀ * truncationScale p₀ β lam →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (S : Finset ℕ), S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤
          multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S := by
  classical
  have hβ0 : 0 ≤ β := by linarith
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨C₃, hC₃, hC₃'⟩ := abs_interactionGoodZ_sub_le hχ
  set V₀ : ℝ := 2 * MultipoleIntegral.kernelConst χ + 2 * Real.log (8 * k)
  have hV₀ : 0 ≤ V₀ := by
    have : (1 : ℝ) ≤ 8 * k := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have := Real.log_nonneg this
    have := kernelConst_nonneg χ
    positivity
  set E : ℝ := Real.exp (-β * (V₀ + 4 * C₃))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set A : ℝ := E ^ (k * k) * Real.exp (-(4 * |L|)) ^ k
  have hA : 0 ≤ A := by positivity
  set c₀ : ℝ := A * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 16) ^ (2 * k - 1) / 8
  have hc₀ : 0 < c₀ := by positivity
  refine ⟨c₀⁻¹, inv_pos.2 hc₀, fun lam hlam hlam₀ => ⟨lowerN₀ lam k,
    fun N hN p₀ ε₀ hh V Z S hS => ?_⟩⟩
  rw [inv_inv]
  set h := ε₀ * truncationScale p₀ β lam with hh_def
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hε₀ : 0 < ε₀ := by
    by_contra hneg
    push Not at hneg
    have : ε₀ * truncationScale p₀ β lam ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hR.le
    linarith
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  set σ : S ≃ Fin k := Fintype.equivFinOfCardEq hcard
  set r₀ : S := σ.symm ⟨0, hk⟩
  have hr₀ : ((σ r₀ : ℕ) : ℝ) = 0 := by simp [r₀]
  set ρ : ℝ := (6 * k + 2 * M) * lam
  have hρ0 : 0 ≤ ρ := by positivity
  set B : Set ℂ := innerBox N (6 * lam * k) \ badNbhd V Z ρ
  have hBm : MeasurableSet B :=
    (measurableSet_innerBox N _).diff (measurableSet_badNbhd V Z ρ)
  -- the measure of the allowed roots
  have hVN : (V.card : ℝ) ≤ N := by
    have := Finset.card_le_univ V
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hρsq : 16 * Real.pi * ρ ^ 2 ≤ 1 := by
    have h6 : 0 < 6 * (k : ℝ) + 2 * M := by positivity
    have hρ1 : ρ ≤ 1 / 16 := by
      simp only [ρ]
      calc (6 * k + 2 * M) * lam ≤ (6 * k + 2 * M) * (16 * (6 * k + 2 * M))⁻¹ :=
            mul_le_mul_of_nonneg_left hlam₀ h6.le
        _ = 1 / 16 := by field_simp
    have := Real.pi_le_four
    nlinarith
  have hvol : ENNReal.ofReal (N / 8) ≤ volume B := by
    have hbox := ofReal_quarter_le_volume_innerBox (N := N) (D := 6 * lam * k) (by positivity)
      (sqrt_ge_of_lowerN₀_le hlam hN)
    have hbad : volume (badNbhd V Z ρ) ≤ ENNReal.ofReal (N / 8) := by
      refine (volume_badNbhd_le V Z hρ0).trans (ENNReal.ofReal_le_ofReal ?_)
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : 2 * (V.card : ℝ) * Real.pi * ρ ^ 2 ≤ 2 * N * Real.pi * ρ ^ 2 := by gcongr
      nlinarith
    calc ENNReal.ofReal (N / 8) = ENNReal.ofReal (N / 4) - ENNReal.ofReal (N / 8) := by
          rw [← ENNReal.ofReal_sub _ (by positivity)]
          congr 1
          ring
      _ ≤ volume (innerBox N (6 * lam * k)) - volume (badNbhd V Z ρ) := tsub_le_tsub hbox hbad
      _ ≤ volume B := le_measure_sdiff
  -- the integrand on good clusters away from the bad charges
  have hF : ∀ c : S → ℂ × ℂ, IsGood N lam σ r₀ c → (c r₀).2 ∈ B →
      A * ((4 * lam) ^ (-β)) ^ k ≤ plusIntegrand χ p₀ β lam M ε₀ L V Z c := by
    intro c hc hroot
    have hgoodZ : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i) :=
      isGoodZ_of_isGood hlam hM0 hr₀ hc (Set.notMem_of_mem_sdiff hroot)
    have := le_plusIntegrand_of_isGood (L := L) hχ hβ0 hlam hM σ hr₀ hh hC₃
      (hC₃' p₀ β lam ε₀ V Z hlam) hc hgoodZ
    simpa only [A, E, V₀, hcard] using this
  have hmain := le_setIntegral_of_isGoodOn (β := β) hlam hk σ hBm Set.sdiff_subset
    (by positivity : (0 : ℝ) ≤ N / 8) hvol (measurable_plusIntegrand hχ hlam)
    plusIntegrand_nonneg (lintegral_plusIntegrand_ne_top hχ hβ0 hlam hε₀ V Z S) hA hF
  unfold multipoleIntegralPlus
  refine le_trans (le_of_eq ?_) hmain
  simp only [c₀]
  ring

/-- The lower bound holds throughout the explicit scale interval.
For sufficiently small `λ`, use the singleton disk at `k = 1` and the written
weighted subtraction at `k ≥ 2`. The remaining compact scale interval uses the `IsGood` comparison. -/
theorem le_multipoleIntegralPlus (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hM : 9 ≤ M) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ (16 * (6 * k + 2 * M))⁻¹ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (p₀ : ℕ) (ε₀ : ℝ), 2 * lam ≤ ε₀ * truncationScale p₀ β lam →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (S : Finset ℕ), S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤
          multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S := by
  obtain ⟨Cw, hCw, lam₀, _, hw⟩ := le_multipoleIntegralPlus_written hχ hβ hk hM L
  obtain ⟨Cc, hCc, hc⟩ := internal_le_multipoleIntegralPlus_compat hχ hβ hk hM L
  refine ⟨max Cw Cc, lt_max_of_lt_left hCw, fun lam hlam hlim => ?_⟩
  have lower (C : ℝ) (hC : 0 < C) (hCle : C ≤ max Cw Cc) (N : ℕ) :
      (max Cw Cc)⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
    have hi := inv_anti₀ hC hCle
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg N)) (by positivity)) (by positivity)
  by_cases hs : lam ≤ lam₀
  · obtain ⟨N₀, hN₀⟩ := hw lam hlam hs
    exact ⟨N₀, fun N hN p₀ ε₀ hh V Z S hS =>
      (lower Cw hCw (le_max_left _ _) N).trans (hN₀ N hN p₀ ε₀ hh V Z S hS)⟩
  · obtain ⟨N₀, hN₀⟩ := hc lam hlam hlim
    exact ⟨N₀, fun N hN p₀ ε₀ hh V Z S hS =>
      (lower Cc hCc (le_max_right _ _) N).trans (hN₀ N hN p₀ ε₀ hh V Z S hS)⟩

/-- **Lemma A.3 for the model with frozen bad points** `(v^Z, τ^Z, L, Z)` (eq. (A.5)): for `1 ≤ k ≤ p*(β)`, `M ≥ 9` and `L ∈ ℝ` there is `C > 0`
(depending on `χ, β, M, L, k`) such that for every `λ ∈ (0, (16 (6k + 2M))⁻¹]` there is `N₀` with
`C⁻¹ N λ^{(2-β)k} λ^{2(k-1)} ≤ I^{+,Z}_{mult,ε₀}(S) ≤ C N λ^{(2-β)k} λ^{2(k-1)}` for all
`N ≥ N₀`, all `p₀`, `ε₀` with `2λ ≤ ε₀ R̄` and `3^{p(β)} ≤ M`, every frozen configuration
`(V, Z)` with `I_bad^V(Z) = V`  and every `S` with `|S| = k`. -/
theorem multipoleIntegralPlus_two_sided (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 9 ≤ M) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ (16 * (6 * k + 2 * M))⁻¹ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (p₀ : ℕ) (ε₀ : ℝ), 2 * lam ≤ ε₀ * truncationScale p₀ β lam →
      (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ S : Finset ℕ, S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤
            multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S ∧
          multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S ≤
            C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  obtain ⟨Cu, hCu, hup⟩ := multipoleIntegralPlus_le (χ := χ) hχ hβ hk hkp (M := M) (by linarith) L
  obtain ⟨Cl, hCl, hlow⟩ := le_multipoleIntegralPlus (χ := χ) hχ hβ hk hM L
  refine ⟨max Cu Cl, lt_max_of_lt_left hCu, fun lam hlam hlam₀ => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hlow lam hlam hlam₀
  refine ⟨N₀, fun N hN p₀ ε₀ hh hM3 V Z hV S hS =>
    ⟨le_trans ?_ (hN₀ N hN p₀ ε₀ hh V Z S hS), (hup lam hlam N p₀ ε₀ hh hM3 V Z hV S hS).trans ?_⟩⟩
  · have : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
    have h := inv_anti₀ hCl (le_max_right Cu Cl)
    calc (max Cu Cl)⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
        = (max Cu Cl)⁻¹ * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by ring
      _ ≤ Cl⁻¹ * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) :=
          mul_le_mul_of_nonneg_right h this
      _ = Cl⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by ring
  · have : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
    calc Cu * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
        = Cu * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by ring
      _ ≤ max Cu Cl * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = max Cu Cl * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by ring

end MultipoleBKT

end
