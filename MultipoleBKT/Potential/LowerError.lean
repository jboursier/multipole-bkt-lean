/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteLocal.RadiusChange

/-!
# Errors from the lower bound (Lemma 3.9)

Lemma 3.9 of the paper and its proof, equations (3.39)–(3.46). Here `χ` is an admissible mollifier, `g_λ = smearedKernel χ λ`,
`K_{α,η} = g * δ₀^{(α)} * δ₀^{(η)} = twoRadiusKernel χ α η`, `c : Fin N → ℂ × ℂ` is a dipole
configuration with `c i = (x_i, y_i)`, `r_i = |x_i - y_i|`, and the radii `τ_i^± ≥ λ` are
`τp i`, `τm i`. The objects of the lemma are:

* `v'_{i,j,+} = UpperBound.halfInteractionPlus χ λ τp τm c i j` (equation (3.39)),
  `v'_{i,j,-} = UpperBound.halfInteractionMinus χ λ τp τm c i j` (equation (3.40)),
  `v'_ij = ballGrowthInteraction χ λ τp τm c i j` (equation (3.6)).
* `v_{i,j,+} = g_λ(x_i - x_j) - g_λ(y_i - x_j)`, `v_{i,j,-} = g_λ(x_i - y_j) - g_λ(y_i - y_j)`,
  `v_ij = dipoleInteraction χ λ (c i) (c j)` (Definition 3.6).
* `d_{i,j}^+ = min(|x_i - x_j|, |y_i - x_j|)`, `d_{i,j}^- = min(|x_i - y_j|, |y_i - y_j|)`
  (equation (3.33)), `d_ij = dipoleDist (c i) (c j)`.

Indicators `𝟙_P · A` are written `if P then A else 0`.

**The hypothesis `σ₂[(x_i, x_j), (y_i, y_j)] = Id` of the paper is omitted**: no step of the proof
uses it (it enters only through Lemma 3.7, whose items (2)–(3) hold for all positions,
`abs_dipoleInteraction_le`, `lemma_3_7_3`), so the statements below are stronger than the
the paper's. The points need not lie in `Λ`.

Main results (each with a constant `C > 0` depending only on `χ`):

* `lemma_3_9_1`: **item (1)**, equations (3.41)–(3.42), for `v'_{i,j,+}` and
  `v'_{i,j,-}`.
* `lemma_3_9_2`: **item (2)**, equations (3.43)–(3.44), when `τ_i^+ = τ_i^-`.
* `lemma_3_9_3`: **item (3)**, equations (3.45)–(3.46), and the bound
  `|v'_ij - v_ij| ≤ C r_i r_j / max(τ_i, τ_j)²` without `d_ij ≥ min(r_i, r_j)` (the sentence
  after (3.46)). The latter is `abs_ballGrowthInteraction_sub_le` and needs neither
  `d_ij ≥ min(r_i, r_j)` nor `r_i ≤ 2(τ_i^+ + τ_i^-)`.

Item (1) inserts the common-radius charge `δ_{y_i}^{(τ_i^+)}` as in the
written proof. `RouteLocal.common_radius_insertion` gives the exact split,
`RouteLocal.abs_translation_le` integrates the gradient estimate for the singly
smoothed potential, and `RouteLocal.abs_radius_change_le` uses Taylor expansion
at the common centre. The comparison interface
`abs_twoRadiusKernel_sub_smearedPotential_le_sq` is provided by
`Potential/RouteLocal/RadiusChange.lean`. The mixed second difference behind
(3.49) is `abs_mixed_le_of_lipschitz`.
-/

@[expose] public section

open MeasureTheory Metric

namespace MultipoleBKT

open UpperBound

variable {χ : ℂ → ℝ} {lam : ℝ}

/-! ### Kernel estimates -/

section Kernel

/-- `K_{α,η}` is `√(π M) / max(α, η)`-Lipschitz (Lemma 3.1 and the symmetry `K_{α,η} = K_{η,α}`; "`∇f` is as regular as `∇g * δ₀^{(max(τ_i, τ_j^+))}`"). -/
theorem abs_twoRadiusKernel_sub_le_max (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (a b : ℂ) :
    |twoRadiusKernel χ α η a - twoRadiusKernel χ α η b| ≤
      Real.sqrt (Real.pi * M) / max α η * ‖a - b‖ := by
  rcases le_total α η with h | h
  · rw [max_eq_right h]
    exact abs_twoRadiusKernel_sub_le hχ hM hα hη a b
  · rw [max_eq_left h, twoRadiusKernel_comm hχ α η a, twoRadiusKernel_comm hχ α η b]
    exact abs_twoRadiusKernel_sub_le hχ hM hη hα a b

/-- **Mixed second difference** of a function with an `L`-Lipschitz gradient:
`|f(a + h + k) - f(a + h) - f(a + k) + f(a)| ≤ L |h| |k|` (equation (3.49)). -/
theorem abs_mixed_le_of_lipschitz {f : ℂ → ℝ} (hf : Differentiable ℝ f) {L : ℝ}
    (hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖) (a h k : ℂ) :
    |f (a + h + k) - f (a + h) - f (a + k) + f a| ≤ L * ‖h‖ * ‖k‖ := by
  have hφ : ∀ p, HasFDerivAt (fun p => f (p + k) - f p) (fderiv ℝ f (p + k) - fderiv ℝ f p) p :=
    fun p => by
      have h1 := (hf (p + k)).hasFDerivAt.comp p ((hasFDerivAt_id p).add_const k)
      rw [ContinuousLinearMap.comp_id] at h1
      exact h1.sub (hf p).hasFDerivAt
  have hbound : ∀ z ∈ Set.univ, ‖fderiv ℝ f (z + k) - fderiv ℝ f z‖ ≤ L * ‖k‖ := fun z _ => by
    have := hL (z + k) z
    rwa [add_sub_cancel_left] at this
  have hmv := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hφ z).hasFDerivWithinAt) hbound (Set.mem_univ a) (Set.mem_univ (a + h))
  rw [add_sub_cancel_left, Real.norm_eq_abs] at hmv
  calc |f (a + h + k) - f (a + h) - f (a + k) + f a|
      = |f (a + h + k) - f (a + h) - (f (a + k) - f a)| := by ring_nf
    _ ≤ L * ‖k‖ * ‖h‖ := hmv
    _ = L * ‖h‖ * ‖k‖ := by ring

/-- The mixed second difference of `K_{α,η}`:
`|K(a + h + k) - K(a + h) - K(a + k) + K(a)| ≤ 3 π M |h| |k| / max(α, η)²` (equation (3.49) with
the bound `|D² g * δ₀^{(max(τ_i, τ_j))}| ≤ C / max(τ_i, τ_j)²`). -/
theorem abs_twoRadiusKernel_mixed_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (a h k : ℂ) :
    |twoRadiusKernel χ α η (a + h + k) - twoRadiusKernel χ α η (a + h) -
        twoRadiusKernel χ α η (a + k) + twoRadiusKernel χ α η a| ≤
      3 * (Real.pi * M / max α η ^ 2) * ‖h‖ * ‖k‖ := by
  rcases le_total α η with hle | hle
  · rw [max_eq_right hle]
    exact abs_mixed_le_of_lipschitz (differentiable_twoRadiusKernel hχ hα hη)
      (norm_fderiv_twoRadiusKernel_sub_le hχ hM hα hη) a h k
  · rw [max_eq_left hle]
    have e : twoRadiusKernel χ α η = twoRadiusKernel χ η α :=
      funext fun z => twoRadiusKernel_comm hχ α η z
    rw [e]
    exact abs_mixed_le_of_lipschitz (differentiable_twoRadiusKernel hχ hη hα)
      (norm_fderiv_twoRadiusKernel_sub_le hχ hM hη hα) a h k

end Kernel

/-! ### Items (1)–(2): the half-interactions

For a dipole `(a, b) = (x_i, y_i)`, a charge `w` (`x_j` for `+`, `y_j` for `-`) and radii
`α = τ_i^+`, `α' = τ_i^-`, `η = τ_j^±`, the half-interaction is
`H = (g_λ - K_{α,η})(a - w) - (g_λ - K_{α',η})(b - w)` and the true half-interaction is
`V = g_λ(a - w) - g_λ(b - w)`. `v'_{i,j,±}` is `H` by definition. -/

section Half

/-- Far range (proof of Lemma 3.9, Newton's theorem): if
`dist({a, b}, w) > max(α, α') + η`, the half-interaction vanishes. -/
theorem halfCore_eq_zero (hχ : IsMollifier χ) (hlam : 0 < lam) {α α' η : ℝ} (hα : lam ≤ α)
    (hα' : lam ≤ α') (hη : lam ≤ η) {a b w : ℂ} (hfar : max α α' + η < min ‖a - w‖ ‖b - w‖) :
    (smearedKernel χ lam (a - w) - twoRadiusKernel χ α η (a - w)) -
        (smearedKernel χ lam (b - w) - twoRadiusKernel χ α' η (b - w)) = 0 := by
  have h1 : α + η ≤ ‖a - w‖ := by
    have := min_le_left ‖a - w‖ ‖b - w‖
    have := le_max_left α α'
    linarith
  have h2 : α' + η ≤ ‖b - w‖ := by
    have := min_le_right ‖a - w‖ ‖b - w‖
    have := le_max_right α α'
    linarith
  rw [smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam hα hη h1,
    smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam hα' hη h2, sub_zero]

/-- Near range, general radii (proof of equation (3.42)):
`|V - H| ≤ √(π M) r / η + 6 π M max(α, α')² / η²`. -/
theorem abs_halfCore_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) {α α' η : ℝ}
    (hα : 0 < α) (hα' : 0 < α') (hη : 0 < η) (a b w : ℂ) :
    |(smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
        ((smearedKernel χ lam (a - w) - twoRadiusKernel χ α η (a - w)) -
          (smearedKernel χ lam (b - w) - twoRadiusKernel χ α' η (b - w)))| ≤
      Real.sqrt (Real.pi * M) * ‖a - b‖ / η + 6 * Real.pi * M * max α α' ^ 2 / η ^ 2 := by
  have he : (smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
      ((smearedKernel χ lam (a - w) - twoRadiusKernel χ α η (a - w)) -
        (smearedKernel χ lam (b - w) - twoRadiusKernel χ α' η (b - w))) =
      twoRadiusKernel χ α η (a - w) - twoRadiusKernel χ α' η (b - w) := by ring
  rw [he, RouteLocal.common_radius_insertion hχ]
  exact (abs_add_le _ _).trans (add_le_add
    (RouteLocal.abs_translation_le hχ hM hα hη a b w)
    (RouteLocal.abs_radius_change_le hχ hM hα hα' hη b w))

/-- Near range, equal radii `α = α' = τ` (proof of equation (3.44)):
`|V - H| ≤ √(π M) r / max(τ, η)`. -/
theorem abs_halfCore_sub_le_of_eq (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) {τ η : ℝ}
    (hτ : 0 < τ) (hη : 0 < η) (a b w : ℂ) :
    |(smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
        ((smearedKernel χ lam (a - w) - twoRadiusKernel χ τ η (a - w)) -
          (smearedKernel χ lam (b - w) - twoRadiusKernel χ τ η (b - w)))| ≤
      Real.sqrt (Real.pi * M) * ‖a - b‖ / max τ η := by
  have h := abs_twoRadiusKernel_sub_le_max hχ hM hτ hη (a - w) (b - w)
  rw [show a - w - (b - w) = a - b by ring] at h
  rw [show (smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
      ((smearedKernel χ lam (a - w) - twoRadiusKernel χ τ η (a - w)) -
        (smearedKernel χ lam (b - w) - twoRadiusKernel χ τ η (b - w))) =
      twoRadiusKernel χ τ η (a - w) - twoRadiusKernel χ τ η (b - w) by ring]
  calc _ ≤ Real.sqrt (Real.pi * M) / max τ η * ‖a - b‖ := h
    _ = Real.sqrt (Real.pi * M) * ‖a - b‖ / max τ η := by ring

/-- **Item (1)** for the half-interaction, explicit constant `C = 2(1 + 2√(πM)) + √(πM) + 6πM`
(equations (3.41), (3.42)), with `D = dist({a, b}, w) ≥ r = |a - b|`. -/
theorem halfCore_item_one (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam)
    {α α' η : ℝ} (hα : lam ≤ α) (hα' : lam ≤ α') (hη : lam ≤ η) {a b w : ℂ}
    (hr : ‖a - b‖ ≤ min ‖a - w‖ ‖b - w‖) :
    |(smearedKernel χ lam (a - w) - twoRadiusKernel χ α η (a - w)) -
        (smearedKernel χ lam (b - w) - twoRadiusKernel χ α' η (b - w))| ≤
      (if min ‖a - w‖ ‖b - w‖ ≤ max α α' + η then
        (2 * (1 + 2 * Real.sqrt (Real.pi * M)) + Real.sqrt (Real.pi * M) + 6 * Real.pi * M) *
          (‖a - b‖ / max (min ‖a - w‖ ‖b - w‖) lam + ‖a - b‖ / η + max α α' ^ 2 / η ^ 2)
      else 0) ∧
    |(smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
        ((smearedKernel χ lam (a - w) - twoRadiusKernel χ α η (a - w)) -
          (smearedKernel χ lam (b - w) - twoRadiusKernel χ α' η (b - w)))| ≤
      (if min ‖a - w‖ ‖b - w‖ ≤ max α α' + η then
        (2 * (1 + 2 * Real.sqrt (Real.pi * M)) + Real.sqrt (Real.pi * M) + 6 * Real.pi * M) *
          (‖a - b‖ / η + max α α' ^ 2 / η ^ 2)
      else 0) +
      (if max α α' + η < min ‖a - w‖ ‖b - w‖ then
        (2 * (1 + 2 * Real.sqrt (Real.pi * M)) + Real.sqrt (Real.pi * M) + 6 * Real.pi * M) *
          ‖a - b‖ / max (min ‖a - w‖ ‖b - w‖) lam
      else 0) := by
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  set Kv := 2 * (1 + 2 * Real.sqrt (Real.pi * M)) with hKv
  set Ks := Real.sqrt (Real.pi * M) with hKs
  set C := Kv + Ks + 6 * Real.pi * M with hC
  set D := min ‖a - w‖ ‖b - w‖ with hD
  set r := ‖a - b‖ with hrdef
  have hKs0 : 0 ≤ Ks := Real.sqrt_nonneg _
  have hKv0 : 0 ≤ Kv := by positivity
  have hq0 : 0 ≤ 6 * Real.pi * M := by positivity
  have hη0 : 0 < η := hlam.trans_le hη
  have hX : 0 < max D lam := lt_max_of_lt_right hlam
  have hr0 : 0 ≤ r := norm_nonneg _
  -- Lemma 3.7 (3) for `V`
  have hV : |smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)| ≤ Kv * r / max D lam :=
    abs_smearedKernel_sub_sub_le hχ hM hlam (d := (a, b)) (x := w) hr
  have hdiff := abs_halfCore_sub_le hχ hM (lam := lam) (hlam.trans_le hα) (hlam.trans_le hα')
    hη0 a b w
  have t1 : 0 ≤ r / max D lam := div_nonneg hr0 hX.le
  have t2 : 0 ≤ r / η := div_nonneg hr0 hη0.le
  have t3 : 0 ≤ max α α' ^ 2 / η ^ 2 := by positivity
  by_cases hnear : D ≤ max α α' + η
  · have hfar : ¬ max α α' + η < D := not_lt.2 hnear
    rw [ite_eq_left hnear, ite_eq_left hnear, ite_eq_right hfar, add_zero]
    have hdiff' : |(smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
        ((smearedKernel χ lam (a - w) - twoRadiusKernel χ α η (a - w)) -
          (smearedKernel χ lam (b - w) - twoRadiusKernel χ α' η (b - w)))| ≤
        C * (r / η + max α α' ^ 2 / η ^ 2) := by
      refine hdiff.trans ?_
      have e1 : Ks * r / η = Ks * (r / η) := by ring
      have e2 : 6 * Real.pi * M * max α α' ^ 2 / η ^ 2 =
          6 * Real.pi * M * (max α α' ^ 2 / η ^ 2) := by ring
      rw [e1, e2]
      nlinarith
    refine ⟨?_, hdiff'⟩
    have htri : |(smearedKernel χ lam (a - w) - twoRadiusKernel χ α η (a - w)) -
        (smearedKernel χ lam (b - w) - twoRadiusKernel χ α' η (b - w))| ≤
        |smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)| +
          |(smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
            ((smearedKernel χ lam (a - w) - twoRadiusKernel χ α η (a - w)) -
              (smearedKernel χ lam (b - w) - twoRadiusKernel χ α' η (b - w)))| := by
      have := abs_sub (smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w))
        ((smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
          ((smearedKernel χ lam (a - w) - twoRadiusKernel χ α η (a - w)) -
            (smearedKernel χ lam (b - w) - twoRadiusKernel χ α' η (b - w))))
      rwa [sub_sub_cancel] at this
    refine htri.trans ?_
    have e3 : Kv * r / max D lam = Kv * (r / max D lam) := by ring
    rw [e3] at hV
    nlinarith
  · have hfar : max α α' + η < D := not_le.1 hnear
    rw [ite_eq_right hnear, ite_eq_right hnear, ite_eq_left hfar, zero_add]
    have hzero := halfCore_eq_zero hχ hlam hα hα' hη hfar
    rw [hzero, abs_zero, sub_zero]
    refine ⟨le_rfl, hV.trans ?_⟩
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) t1

/-- **Item (2)** for the half-interaction (`α = α' = τ`), explicit constant
`C = 2(1 + 2√(πM)) + 2√(πM)` (equations (3.43), (3.44)). -/
theorem halfCore_item_two (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam)
    {τ η : ℝ} (hτ : lam ≤ τ) (hη : lam ≤ η) {a b w : ℂ} (hr : ‖a - b‖ ≤ min ‖a - w‖ ‖b - w‖) :
    |(smearedKernel χ lam (a - w) - twoRadiusKernel χ τ η (a - w)) -
        (smearedKernel χ lam (b - w) - twoRadiusKernel χ τ η (b - w))| ≤
      (if min ‖a - w‖ ‖b - w‖ ≤ τ + η then
        (2 * (1 + 2 * Real.sqrt (Real.pi * M)) + 2 * Real.sqrt (Real.pi * M)) * ‖a - b‖ /
          max (min ‖a - w‖ ‖b - w‖) lam
      else 0) ∧
    |(smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
        ((smearedKernel χ lam (a - w) - twoRadiusKernel χ τ η (a - w)) -
          (smearedKernel χ lam (b - w) - twoRadiusKernel χ τ η (b - w)))| ≤
      (if min ‖a - w‖ ‖b - w‖ ≤ τ + η then
        (2 * (1 + 2 * Real.sqrt (Real.pi * M)) + 2 * Real.sqrt (Real.pi * M)) * ‖a - b‖ /
          max τ η
      else 0) +
      (if τ + η < min ‖a - w‖ ‖b - w‖ then
        (2 * (1 + 2 * Real.sqrt (Real.pi * M)) + 2 * Real.sqrt (Real.pi * M)) * ‖a - b‖ /
          max (min ‖a - w‖ ‖b - w‖) lam
      else 0) := by
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  set Kv := 2 * (1 + 2 * Real.sqrt (Real.pi * M)) with hKv
  set Ks := Real.sqrt (Real.pi * M) with hKs
  set D := min ‖a - w‖ ‖b - w‖ with hD
  set r := ‖a - b‖ with hrdef
  have hKs0 : 0 ≤ Ks := Real.sqrt_nonneg _
  have hKv0 : 0 ≤ Kv := by positivity
  have hτ0 : 0 < τ := hlam.trans_le hτ
  have hη0 : 0 < η := hlam.trans_le hη
  have hX : 0 < max D lam := lt_max_of_lt_right hlam
  have hY : 0 < max τ η := lt_max_of_lt_left hτ0
  have hr0 : 0 ≤ r := norm_nonneg _
  have hV : |smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)| ≤ Kv * r / max D lam :=
    abs_smearedKernel_sub_sub_le hχ hM hlam (d := (a, b)) (x := w) hr
  have hdiff := abs_halfCore_sub_le_of_eq hχ hM (lam := lam) hτ0 hη0 a b w
  by_cases hnear : D ≤ τ + η
  · have hfar : ¬ τ + η < D := not_lt.2 hnear
    rw [ite_eq_left hnear, ite_eq_left hnear, ite_eq_right hfar, add_zero]
    have hdiff' := hdiff.trans (show Ks * r / max τ η ≤ (Kv + 2 * Ks) * r / max τ η by
      gcongr; linarith)
    refine ⟨?_, hdiff'⟩
    -- `max(D, λ) ≤ 2 max(τ, η)`
    have hXY : max D lam ≤ 2 * max τ η := by
      refine max_le ?_ ?_
      · have := le_max_left τ η
        have := le_max_right τ η
        linarith
      · have := le_max_left τ η
        linarith
    have hratio : r / max τ η ≤ 2 * (r / max D lam) := by
      rw [div_le_iff₀ hY, mul_comm 2, mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hX]
      nlinarith
    have htri : |(smearedKernel χ lam (a - w) - twoRadiusKernel χ τ η (a - w)) -
        (smearedKernel χ lam (b - w) - twoRadiusKernel χ τ η (b - w))| ≤
        |smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)| +
          |(smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
            ((smearedKernel χ lam (a - w) - twoRadiusKernel χ τ η (a - w)) -
              (smearedKernel χ lam (b - w) - twoRadiusKernel χ τ η (b - w)))| := by
      have := abs_sub (smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w))
        ((smearedKernel χ lam (a - w) - smearedKernel χ lam (b - w)) -
          ((smearedKernel χ lam (a - w) - twoRadiusKernel χ τ η (a - w)) -
            (smearedKernel χ lam (b - w) - twoRadiusKernel χ τ η (b - w))))
      rwa [sub_sub_cancel] at this
    refine htri.trans ?_
    have e1 : Kv * r / max D lam = Kv * (r / max D lam) := by ring
    have e2 : Ks * r / max τ η = Ks * (r / max τ η) := by ring
    have e3 : (Kv + 2 * Ks) * r / max D lam = (Kv + 2 * Ks) * (r / max D lam) := by ring
    rw [e1] at hV
    rw [e2] at hdiff
    rw [e3]
    nlinarith
  · have hfar : τ + η < D := not_le.1 hnear
    rw [ite_eq_right hnear, ite_eq_right hnear, ite_eq_left hfar, zero_add]
    have hfar' : max τ τ + η < D := by rwa [max_self]
    have hzero := halfCore_eq_zero hχ hlam hτ hτ hη hfar'
    rw [hzero, abs_zero, sub_zero]
    refine ⟨le_rfl, hV.trans ?_⟩
    gcongr
    linarith

end Half

/-! ### Item (3): the interaction `v'_ij` -/

section Full

/-- **The sentence after (3.46)**: if `τ_i^+ = τ_i^-` and
`τ_j^+ = τ_j^-`, then `|v'_ij - v_ij| ≤ 3 π M r_i r_j / max(τ_i, τ_j)²`, for all positions:
`v'_ij - v_ij` is minus the mixed second difference of `K_{τ_i,τ_j}`. -/
theorem abs_ballGrowthInteraction_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {N : ℕ} (lam : ℝ) {τp τm : Fin N → ℝ} (c : Fin N → ℂ × ℂ) {i j : Fin N} (hi : 0 < τp i)
    (hj : 0 < τp j) (hτi : τp i = τm i) (hτj : τp j = τm j) :
    |ballGrowthInteraction χ lam τp τm c i j - dipoleInteraction χ lam (c i) (c j)| ≤
      3 * (Real.pi * M / max (τp i) (τp j) ^ 2) *
        (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) := by
  set K := twoRadiusKernel χ (τp i) (τp j)
  have hmix := abs_twoRadiusKernel_mixed_le hχ hM hi hj ((c i).2 - (c j).2)
    ((c i).1 - (c i).2) ((c j).2 - (c j).1)
  rw [show (c i).2 - (c j).2 + ((c i).1 - (c i).2) + ((c j).2 - (c j).1) = (c i).1 - (c j).1 by
      ring, show (c i).2 - (c j).2 + ((c i).1 - (c i).2) = (c i).1 - (c j).2 by ring,
    show (c i).2 - (c j).2 + ((c j).2 - (c j).1) = (c i).2 - (c j).1 by ring,
    norm_sub_rev (c j).2] at hmix
  have e : ballGrowthInteraction χ lam τp τm c i j - dipoleInteraction χ lam (c i) (c j) =
      -(K ((c i).1 - (c j).1) - K ((c i).1 - (c j).2) - K ((c i).2 - (c j).1) +
        K ((c i).2 - (c j).2)) := by
    rw [dipoleInteraction_eq_sub hχ]
    unfold ballGrowthInteraction
    rw [← hτi, ← hτj]
    ring
  rw [e, abs_neg]
  calc _ ≤ 3 * (Real.pi * M / max (τp i) (τp j) ^ 2) * ‖(c i).1 - (c i).2‖ *
        ‖(c j).1 - (c j).2‖ := hmix
    _ = _ := by ring

/-- Far range of item (3) (the proof of Lemma 3.9): if `d_ij > τ_i + τ_j` (with `τ^+ = τ^-`), all four pairs
of enlarged balls are disjoint and `v'_ij = 0`. -/
theorem ballGrowthInteraction_eq_zero (hχ : IsMollifier χ) (hlam : 0 < lam) {N : ℕ}
    {τp τm : Fin N → ℝ} (c : Fin N → ℂ × ℂ) {i j : Fin N} (hi : lam ≤ τp i) (hj : lam ≤ τp j)
    (hτi : τp i = τm i) (hτj : τp j = τm j) (hfar : τp i + τp j < dipoleDist (c i) (c j)) :
    ballGrowthInteraction χ lam τp τm c i j = 0 := by
  have h1 := dipoleDist_le_fst_fst (c i) (c j)
  have h2 := dipoleDist_le_fst_snd (c i) (c j)
  have h3 := dipoleDist_le_snd_fst (c i) (c j)
  have h4 := dipoleDist_le_snd_snd (c i) (c j)
  unfold ballGrowthInteraction
  rw [← hτi, ← hτj, smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam hi hj (by linarith),
    smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam hi hj (by linarith),
    smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam hi hj (by linarith),
    smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam hi hj (by linarith)]
  ring

/-- `max(d_ij, λ) max(d_ij, r_i, r_j) ≤ 8 max(τ_i, τ_j)²` when `0 ≤ d_ij ≤ τ_i + τ_j`,
`r_i ≤ 4 τ_i`, `r_j ≤ 4 τ_j` and `λ ≤ τ_i` (the display after (3.49)). -/
theorem max_mul_max_le_eight_mul {D lam ri rj τi τj : ℝ} (hD0 : 0 ≤ D) (hτi : lam ≤ τi)
    (hD : D ≤ τi + τj) (hri : ri ≤ 4 * τi) (hrj : rj ≤ 4 * τj) (hτj : 0 ≤ τj) :
    max D lam * max D (max ri rj) ≤ 8 * max τi τj ^ 2 := by
  have hm1 := le_max_left τi τj
  have hm2 := le_max_right τi τj
  have hm0 : 0 ≤ max τi τj := hτj.trans hm2
  have hX : max D lam ≤ 2 * max τi τj := max_le (by linarith) (by linarith)
  have hY : max D (max ri rj) ≤ 4 * max τi τj :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  have hY0 : 0 ≤ max D (max ri rj) := hD0.trans (le_max_left _ _)
  calc max D lam * max D (max ri rj) ≤ (2 * max τi τj) * (4 * max τi τj) :=
        mul_le_mul hX hY hY0 (by linarith)
    _ = 8 * max τi τj ^ 2 := by ring

/-- **Item (3)** with an explicit constant `C = 16(1 + 2√(πM)) + 4(1 + 12πM) + 24πM`
(equations (3.45), (3.46)): if `τ_i^+ = τ_i^-`, `τ_j^+ = τ_j^-`, `r_i ≤ 2(τ_i^+ + τ_i^-)`,
`r_j ≤ 2(τ_j^+ + τ_j^-)` and `d_ij ≥ min(r_i, r_j)`. -/
theorem ballGrowth_item_three (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam)
    {N : ℕ} {τp τm : Fin N → ℝ} (c : Fin N → ℂ × ℂ) {i j : Fin N} (hi : lam ≤ τp i)
    (hj : lam ≤ τp j) (hτi : τp i = τm i) (hτj : τp j = τm j)
    (hri : ‖(c i).1 - (c i).2‖ ≤ 2 * (τp i + τm i)) (hrj : ‖(c j).1 - (c j).2‖ ≤ 2 * (τp j + τm j))
    (hD : min ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖ ≤ dipoleDist (c i) (c j)) :
    |ballGrowthInteraction χ lam τp τm c i j| ≤
      (if dipoleDist (c i) (c j) ≤ τp i + τp j then
        (16 * (1 + 2 * Real.sqrt (Real.pi * M)) + 4 * (1 + 12 * Real.pi * M) +
            24 * Real.pi * M) * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) /
          (max (dipoleDist (c i) (c j)) lam *
            max (dipoleDist (c i) (c j)) (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖))
      else 0) ∧
    |ballGrowthInteraction χ lam τp τm c i j - dipoleInteraction χ lam (c i) (c j)| ≤
      (if dipoleDist (c i) (c j) ≤ τp i + τp j then
        (16 * (1 + 2 * Real.sqrt (Real.pi * M)) + 4 * (1 + 12 * Real.pi * M) +
            24 * Real.pi * M) * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) /
          max (τp i) (τp j) ^ 2
      else 0) +
      (if τp i + τp j < dipoleDist (c i) (c j) then
        (16 * (1 + 2 * Real.sqrt (Real.pi * M)) + 4 * (1 + 12 * Real.pi * M) +
            24 * Real.pi * M) * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) /
          (max (dipoleDist (c i) (c j)) lam *
            max (dipoleDist (c i) (c j)) (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖))
      else 0) := by
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  set K7 := 16 * (1 + 2 * Real.sqrt (Real.pi * M)) + 4 * (1 + 12 * Real.pi * M) with hK7
  set C := K7 + 24 * Real.pi * M with hC
  set D := dipoleDist (c i) (c j) with hDdef
  set ri := ‖(c i).1 - (c i).2‖ with hridef
  set rj := ‖(c j).1 - (c j).2‖ with hrjdef
  set X := max D lam with hXdef
  set Y := max D (max ri rj) with hYdef
  set m := max (τp i) (τp j) with hmdef
  have hK70 : 0 ≤ K7 := by positivity
  have hq0 : 0 ≤ 24 * Real.pi * M := by positivity
  have hri0 : 0 ≤ ri := norm_nonneg _
  have hrj0 : 0 ≤ rj := norm_nonneg _
  have hrr : 0 ≤ ri * rj := mul_nonneg hri0 hrj0
  have hD0 : 0 ≤ D := dipoleDist_nonneg _ _
  have hX : 0 < X := lt_max_of_lt_right hlam
  have hY0 : 0 ≤ Y := hD0.trans (le_max_left _ _)
  have hτi0 : 0 < τp i := hlam.trans_le hi
  have hτj0 : 0 < τp j := hlam.trans_le hj
  have hm : 0 < m := lt_max_of_lt_left hτi0
  have hv : |dipoleInteraction χ lam (c i) (c j)| ≤ K7 * (ri * rj) / (X * Y) :=
    abs_dipoleInteraction_le_of_bound hχ hM hlam hD
  have hdiff : |ballGrowthInteraction χ lam τp τm c i j - dipoleInteraction χ lam (c i) (c j)| ≤
      3 * (Real.pi * M / m ^ 2) * (ri * rj) :=
    abs_ballGrowthInteraction_sub_le hχ hM lam c hτi0 hτj0 hτi hτj
  have hXYnn : 0 ≤ K7 * (ri * rj) / (X * Y) := div_nonneg (mul_nonneg hK70 hrr)
    (mul_nonneg hX.le hY0)
  have hCK : K7 * (ri * rj) / (X * Y) ≤ C * (ri * rj) / (X * Y) := by
    gcongr
    linarith
  by_cases hnear : D ≤ τp i + τp j
  · have hfar : ¬ τp i + τp j < D := not_lt.2 hnear
    rw [ite_eq_left hnear, ite_eq_left hnear, ite_eq_right hfar, add_zero]
    have hdiff' : 3 * (Real.pi * M / m ^ 2) * (ri * rj) = 3 * Real.pi * M * (ri * rj) / m ^ 2 := by
      ring
    have hCm : 3 * Real.pi * M * (ri * rj) / m ^ 2 ≤ C * (ri * rj) / m ^ 2 := by
      gcongr
      linarith
    refine ⟨?_, by rw [hdiff'] at hdiff; exact hdiff.trans hCm⟩
    -- `3 π M r_i r_j / max(τ)² ≤ 24 π M r_i r_j / (X Y)`
    have key : 3 * (Real.pi * M / m ^ 2) * (ri * rj) ≤ 24 * Real.pi * M * (ri * rj) / (X * Y) := by
      rcases hY0.eq_or_lt with hY | hY
      · have hri' : ri = 0 := by
          have : ri ≤ Y := (le_max_left ri rj).trans (le_max_right _ _)
          linarith
        rw [hri', zero_mul, mul_zero, mul_zero, zero_div]
      · rw [le_div_iff₀ (mul_pos hX hY)]
        have hri4 : ri ≤ 4 * τp i := by rw [← hτi] at hri; linarith
        have hrj4 : rj ≤ 4 * τp j := by rw [← hτj] at hrj; linarith
        have h8 : X * Y ≤ 8 * m ^ 2 := max_mul_max_le_eight_mul hD0 hi hnear hri4 hrj4 hτj0.le
        calc 3 * (Real.pi * M / m ^ 2) * (ri * rj) * (X * Y) ≤
              3 * (Real.pi * M / m ^ 2) * (ri * rj) * (8 * m ^ 2) := by gcongr
          _ = 24 * Real.pi * M * (ri * rj) := by field_simp; ring
    have htri : |ballGrowthInteraction χ lam τp τm c i j| ≤
        |dipoleInteraction χ lam (c i) (c j)| +
          |ballGrowthInteraction χ lam τp τm c i j - dipoleInteraction χ lam (c i) (c j)| := by
      have := abs_add_le (dipoleInteraction χ lam (c i) (c j))
        (ballGrowthInteraction χ lam τp τm c i j - dipoleInteraction χ lam (c i) (c j))
      rwa [add_sub_cancel] at this
    calc _ ≤ K7 * (ri * rj) / (X * Y) + 24 * Real.pi * M * (ri * rj) / (X * Y) :=
          htri.trans (add_le_add hv (hdiff.trans key))
      _ = C * (ri * rj) / (X * Y) := by ring
  · have hfar : τp i + τp j < D := not_le.1 hnear
    rw [ite_eq_right hnear, ite_eq_right hnear, ite_eq_left hfar, zero_add]
    rw [ballGrowthInteraction_eq_zero hχ hlam c hi hj hτi hτj hfar, abs_zero, zero_sub, abs_neg]
    exact ⟨le_rfl, hv.trans hCK⟩

end Full

/-! ### Lemma 3.9 -/

section Statement

/-- **Lemma 3.9 (1)** (equations (3.41), (3.42)): there is `C > 0` depending only on `χ` such that, for `λ > 0`, radii
`τ_i^±, τ_j^± ≥ λ` and every configuration, if `d_{i,j}^± ≥ r_i` then
`|v'_{i,j,±}| ≤ C (r_i / max(d_{i,j}^±, λ) + r_i / τ_j^± + max(τ_i^+, τ_i^-)² / (τ_j^±)²)
  𝟙_{d_{i,j}^± ≤ max(τ_i^+, τ_i^-) + τ_j^±}` and
`|v_{i,j,±} - v'_{i,j,±}| ≤ C (r_i / τ_j^± + max(τ_i^+, τ_i^-)² / (τ_j^±)²)
  𝟙_{d_{i,j}^± ≤ max(τ_i^+, τ_i^-) + τ_j^±} + C r_i / max(d_{i,j}^±, λ)
  𝟙_{d_{i,j}^± > max(τ_i^+, τ_i^-) + τ_j^±}`.
The first conjunct is the `+` case, the second the `-` case. The paper's hypothesis
`σ₂[(x_i, x_j), (y_i, y_j)] = Id` is not needed. -/
theorem lemma_3_9_1 (hχ : IsMollifier χ) : ∃ C > 0, ∀ {N : ℕ} (lam : ℝ) (τp τm : Fin N → ℝ)
    (c : Fin N → ℂ × ℂ) (i j : Fin N), 0 < lam → lam ≤ τp i → lam ≤ τm i → lam ≤ τp j →
    lam ≤ τm j →
    (‖(c i).1 - (c i).2‖ ≤ min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖ →
      |halfInteractionPlus χ lam τp τm c i j| ≤
          (if min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖ ≤ max (τp i) (τm i) + τp j then
            C * (‖(c i).1 - (c i).2‖ / max (min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖) lam +
              ‖(c i).1 - (c i).2‖ / τp j + max (τp i) (τm i) ^ 2 / τp j ^ 2)
          else 0) ∧
        |(smearedKernel χ lam ((c i).1 - (c j).1) - smearedKernel χ lam ((c i).2 - (c j).1)) -
            halfInteractionPlus χ lam τp τm c i j| ≤
          (if min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖ ≤ max (τp i) (τm i) + τp j then
            C * (‖(c i).1 - (c i).2‖ / τp j + max (τp i) (τm i) ^ 2 / τp j ^ 2)
          else 0) +
          (if max (τp i) (τm i) + τp j < min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖ then
            C * ‖(c i).1 - (c i).2‖ / max (min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖) lam
          else 0)) ∧
    (‖(c i).1 - (c i).2‖ ≤ min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖ →
      |halfInteractionMinus χ lam τp τm c i j| ≤
          (if min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖ ≤ max (τp i) (τm i) + τm j then
            C * (‖(c i).1 - (c i).2‖ / max (min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖) lam +
              ‖(c i).1 - (c i).2‖ / τm j + max (τp i) (τm i) ^ 2 / τm j ^ 2)
          else 0) ∧
        |(smearedKernel χ lam ((c i).1 - (c j).2) - smearedKernel χ lam ((c i).2 - (c j).2)) -
            halfInteractionMinus χ lam τp τm c i j| ≤
          (if min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖ ≤ max (τp i) (τm i) + τm j then
            C * (‖(c i).1 - (c i).2‖ / τm j + max (τp i) (τm i) ^ 2 / τm j ^ 2)
          else 0) +
          (if max (τp i) (τm i) + τm j < min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖ then
            C * ‖(c i).1 - (c i).2‖ / max (min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖) lam
          else 0)) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  refine ⟨2 * (1 + 2 * Real.sqrt (Real.pi * M)) + Real.sqrt (Real.pi * M) + 6 * Real.pi * M,
    by positivity, fun lam τp τm c i j hlam hpi hmi hpj hmj => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · exact halfCore_item_one hχ hM hlam hpi hmi hpj hr
  · exact halfCore_item_one hχ hM hlam hpi hmi hmj hr

/-- **Lemma 3.9 (2)** (equations (3.43), (3.44)):
there is `C > 0` depending only on `χ` such that, for `λ > 0`, radii `τ_i^+ = τ_i^- = τ_i ≥ λ`,
`τ_j^± ≥ λ` and every configuration, if `d_{i,j}^± ≥ r_i` then
`|v'_{i,j,±}| ≤ C r_i / max(d_{i,j}^±, λ) 𝟙_{d_{i,j}^± ≤ τ_i + τ_j^±}` and
`|v_{i,j,±} - v'_{i,j,±}| ≤ C r_i / max(τ_i, τ_j^±) 𝟙_{d_{i,j}^± ≤ τ_i + τ_j^±}
  + C r_i / max(d_{i,j}^±, λ) 𝟙_{d_{i,j}^± > τ_i + τ_j^±}`.
Here `τ_i = τp i`. The paper's hypothesis `σ₂[(x_i, x_j), (y_i, y_j)] = Id` is not needed. -/
theorem lemma_3_9_2 (hχ : IsMollifier χ) : ∃ C > 0, ∀ {N : ℕ} (lam : ℝ) (τp τm : Fin N → ℝ)
    (c : Fin N → ℂ × ℂ) (i j : Fin N), 0 < lam → lam ≤ τp i → τp i = τm i → lam ≤ τp j →
    lam ≤ τm j →
    (‖(c i).1 - (c i).2‖ ≤ min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖ →
      |halfInteractionPlus χ lam τp τm c i j| ≤
          (if min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖ ≤ τp i + τp j then
            C * ‖(c i).1 - (c i).2‖ / max (min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖) lam
          else 0) ∧
        |(smearedKernel χ lam ((c i).1 - (c j).1) - smearedKernel χ lam ((c i).2 - (c j).1)) -
            halfInteractionPlus χ lam τp τm c i j| ≤
          (if min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖ ≤ τp i + τp j then
            C * ‖(c i).1 - (c i).2‖ / max (τp i) (τp j)
          else 0) +
          (if τp i + τp j < min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖ then
            C * ‖(c i).1 - (c i).2‖ / max (min ‖(c i).1 - (c j).1‖ ‖(c i).2 - (c j).1‖) lam
          else 0)) ∧
    (‖(c i).1 - (c i).2‖ ≤ min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖ →
      |halfInteractionMinus χ lam τp τm c i j| ≤
          (if min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖ ≤ τp i + τm j then
            C * ‖(c i).1 - (c i).2‖ / max (min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖) lam
          else 0) ∧
        |(smearedKernel χ lam ((c i).1 - (c j).2) - smearedKernel χ lam ((c i).2 - (c j).2)) -
            halfInteractionMinus χ lam τp τm c i j| ≤
          (if min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖ ≤ τp i + τm j then
            C * ‖(c i).1 - (c i).2‖ / max (τp i) (τm j)
          else 0) +
          (if τp i + τm j < min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖ then
            C * ‖(c i).1 - (c i).2‖ / max (min ‖(c i).1 - (c j).2‖ ‖(c i).2 - (c j).2‖) lam
          else 0)) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  refine ⟨2 * (1 + 2 * Real.sqrt (Real.pi * M)) + 2 * Real.sqrt (Real.pi * M), by positivity,
    fun lam τp τm c i j hlam hpi hτi hpj hmj => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · have h := halfCore_item_two (χ := χ) hχ hM hlam hpi hpj hr
    unfold halfInteractionPlus
    rw [← hτi]
    exact h
  · have h := halfCore_item_two (χ := χ) hχ hM hlam hpi hmj hr
    unfold halfInteractionMinus
    rw [← hτi]
    exact h

/-- **Lemma 3.9 (3)** (equations (3.45), (3.46)): there is
`C > 0` depending only on `χ` such that, for `λ > 0` and every configuration:

* if `τ_i^+ = τ_i^- = τ_i ≥ λ` and `τ_j^+ = τ_j^- = τ_j ≥ λ`, then
  `|v'_ij - v_ij| ≤ C r_i r_j / max(τ_i, τ_j)²` (the sentence after (3.46), without
  `d_ij ≥ min(r_i, r_j)`).
* if moreover `r_i ≤ 2(τ_i^+ + τ_i^-)`, `r_j ≤ 2(τ_j^+ + τ_j^-)` and `d_ij ≥ min(r_i, r_j)`, then
  `|v'_ij| ≤ C r_i r_j / (max(d_ij, λ) max(r_i, r_j, d_ij)) 𝟙_{d_ij ≤ τ_i + τ_j}` and
  `|v'_ij - v_ij| ≤ C r_i r_j / max(τ_i, τ_j)² 𝟙_{d_ij ≤ τ_i + τ_j}
    + C r_i r_j / (max(d_ij, λ) max(r_i, r_j, d_ij)) 𝟙_{d_ij > τ_i + τ_j}`.

Here `τ_i = τp i`, `τ_j = τp j`. The paper's hypothesis `σ₂[(x_i, x_j), (y_i, y_j)] = Id` is not
needed. -/
theorem lemma_3_9_3 (hχ : IsMollifier χ) : ∃ C > 0, ∀ {N : ℕ} (lam : ℝ) (τp τm : Fin N → ℝ)
    (c : Fin N → ℂ × ℂ) (i j : Fin N), 0 < lam → lam ≤ τp i → τp i = τm i → lam ≤ τp j →
    τp j = τm j →
    |ballGrowthInteraction χ lam τp τm c i j - dipoleInteraction χ lam (c i) (c j)| ≤
        C * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max (τp i) (τp j) ^ 2 ∧
    (‖(c i).1 - (c i).2‖ ≤ 2 * (τp i + τm i) → ‖(c j).1 - (c j).2‖ ≤ 2 * (τp j + τm j) →
      min ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖ ≤ dipoleDist (c i) (c j) →
      |ballGrowthInteraction χ lam τp τm c i j| ≤
          (if dipoleDist (c i) (c j) ≤ τp i + τp j then
            C * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) /
              (max (dipoleDist (c i) (c j)) lam *
                max (dipoleDist (c i) (c j)) (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖))
          else 0) ∧
        |ballGrowthInteraction χ lam τp τm c i j - dipoleInteraction χ lam (c i) (c j)| ≤
          (if dipoleDist (c i) (c j) ≤ τp i + τp j then
            C * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max (τp i) (τp j) ^ 2
          else 0) +
          (if τp i + τp j < dipoleDist (c i) (c j) then
            C * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) /
              (max (dipoleDist (c i) (c j)) lam *
                max (dipoleDist (c i) (c j)) (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖))
          else 0)) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  set C := 16 * (1 + 2 * Real.sqrt (Real.pi * M)) + 4 * (1 + 12 * Real.pi * M) +
    24 * Real.pi * M with hC
  refine ⟨C, by positivity, fun lam τp τm c i j hlam hpi hτi hpj hτj => ⟨?_,
    fun hri hrj hD => ballGrowth_item_three hχ hM hlam c hpi hpj hτi hτj hri hrj hD⟩⟩
  have hτi0 : 0 < τp i := hlam.trans_le hpi
  have hτj0 : 0 < τp j := hlam.trans_le hpj
  refine (abs_ballGrowthInteraction_sub_le hχ hM lam c hτi0 hτj0 hτi hτj).trans ?_
  have hm : 0 < max (τp i) (τp j) := lt_max_of_lt_left hτi0
  have hrr : 0 ≤ ‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖ := by positivity
  rw [show 3 * (Real.pi * M / max (τp i) (τp j) ^ 2) *
      (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) =
      3 * Real.pi * M * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max (τp i) (τp j) ^ 2 by
    ring]
  gcongr
  have : 0 ≤ 16 * (1 + 2 * Real.sqrt (Real.pi * M)) + 4 * (1 + 12 * Real.pi * M) := by positivity
  have hpm : 0 ≤ Real.pi * M := by positivity
  rw [hC]
  linarith

end Statement

end MultipoleBKT

end
