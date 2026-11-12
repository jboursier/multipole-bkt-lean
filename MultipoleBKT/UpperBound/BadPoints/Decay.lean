/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Radii
public import MultipoleBKT.Potential.BondBound
public import MultipoleBKT.Potential.Monotonicity
public import MultipoleBKT.UpperBound.BadPoints.RouteShell.Continuous

/-!
# Half-interaction decay and continuous packing shells

The paper: Lemma 5.11,
Lemma 5.12. Equal radii give the translation estimate.
For unequal radii, insert a common radius at the second centre before estimating
translation and radius change at that centre. `RouteShell.Comparison` assembles
the quadratic version downstream of this module.

The continuous shell count uses two balls at scale `t/2` and the packing
hypothesis (5.15). The scale integral is proved in `RouteShell.Continuous`.
-/

@[expose] public section

open Finset Metric MeasureTheory
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

namespace UpperBound

variable {χ : ℂ → ℝ} {N : ℕ}

/-! ### Kernel estimates -/

section Kernel

variable {lam : ℝ}

/-- `g * δ₀^{(η)}` is `√(π M)/η`-Lipschitz. -/
theorem abs_smearedPotential_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) {η : ℝ}
    (hη : 0 < η) (a b : ℂ) :
    |smearedPotential χ η a - smearedPotential χ η b| ≤ Real.sqrt (Real.pi * M) / η * ‖a - b‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (fun x _ => (differentiable_smearedPotential hχ hη x))
    (fun x _ => norm_fderiv_smearedPotential_le hχ hM hη x) convex_univ (Set.mem_univ b)
    (Set.mem_univ a)
  rwa [Real.norm_eq_abs] at this

/-- `g * δ₀^{(α)} * δ₀^{(η)}` is `√(π M)/η`-Lipschitz. -/
theorem abs_twoRadiusKernel_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) {α η : ℝ}
    (hα : 0 < α) (hη : 0 < η) (a b : ℂ) :
    |twoRadiusKernel χ α η a - twoRadiusKernel χ α η b| ≤
      Real.sqrt (Real.pi * M) / η * ‖a - b‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (fun x _ => (differentiable_twoRadiusKernel hχ hα hη x))
    (fun x _ => norm_fderiv_twoRadiusKernel_le hχ hM hα hη x) convex_univ (Set.mem_univ b)
    (Set.mem_univ a)
  rwa [Real.norm_eq_abs] at this

/-- `|(g * δ₀^{(α)} * δ₀^{(η)})(w) - (g * δ₀^{(η)})(w)| ≤ √(π M) α / η`: the charge `δ₀^{(α)}` is a
probability measure carried by `B(0, α)`. -/
theorem abs_twoRadiusKernel_sub_smearedPotential_le (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (w : ℂ) :
    |twoRadiusKernel χ α η w - smearedPotential χ η w| ≤ Real.sqrt (Real.pi * M) / η * α := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  set L := Real.sqrt (Real.pi * M) / η
  have hL : 0 ≤ L := by positivity
  rw [twoRadiusKernel_eq_integral_smearedPotential hχ]
  have hint := integrable_smearedPotential_comp hχ hη (f := fun a => w - a)
    (continuous_const.sub continuous_id) 0 α
  have heq : ∫ a, smearedPotential χ η (w - a) ∂smearedCharge χ 0 α - smearedPotential χ η w =
      ∫ a, (smearedPotential χ η (w - a) - smearedPotential χ η w) ∂smearedCharge χ 0 α := by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [heq, ← Real.norm_eq_abs]
  have hb : ∀ᵐ a ∂smearedCharge χ 0 α,
      ‖smearedPotential χ η (w - a) - smearedPotential χ η w‖ ≤ L * α := by
    filter_upwards [ae_mem_closedBall_smearedCharge hχ (z := 0) hα] with a ha
    rw [mem_closedBall, dist_zero_right] at ha
    rw [Real.norm_eq_abs]
    calc |smearedPotential χ η (w - a) - smearedPotential χ η w| ≤ L * ‖w - a - w‖ :=
          abs_smearedPotential_sub_le hχ hM hη _ _
      _ = L * ‖a‖ := by rw [sub_sub_cancel_left, norm_neg]
      _ ≤ L * α := mul_le_mul_of_nonneg_left ha hL
  calc ‖∫ a, (smearedPotential χ η (w - a) - smearedPotential χ η w) ∂smearedCharge χ 0 α‖
      ≤ L * α * (smearedCharge χ 0 α).real Set.univ := norm_integral_le_of_norm_le_const hb
    _ = L * α := by rw [probReal_univ, mul_one]

/-- **Eq. (5.37)** (Lemma 3.2): `g_λ - g * δ₀^{(α)} * δ₀^{(η)} ≥ 0` for `α, η ≥ λ > 0`. -/
theorem smearedKernel_sub_twoRadiusKernel_nonneg (hχ : IsMollifier χ) (hlam : 0 < lam)
    {α η : ℝ} (hα : lam ≤ α) (hη : lam ≤ η) (w : ℂ) :
    0 ≤ smearedKernel χ lam w - twoRadiusKernel χ α η w := by
  have := twoRadiusKernel_le_twoRadiusKernel hχ hlam hα hlam hη w
  rw [twoRadiusKernel_self] at this
  linarith

/-- `g_λ(a) - g_λ(b) ≥ -(log 6 + max(c_χ, 0))` when `|a| ≤ 2|b|` (the paper (5.44)). -/
theorem neg_le_smearedKernel_sub (hχ : IsMollifier χ) (hlam : 0 < lam) {a b : ℂ}
    (hab : ‖a‖ ≤ 2 * ‖b‖) :
    -(Real.log 6 + max (∫ y, logKernel y ∂smearedCharge χ 0 1) 0) ≤
      smearedKernel χ lam a - smearedKernel χ lam b := by
  have h1 := neg_log_three_sub_le_smearedKernel hχ hlam a
  have h2 := smearedKernel_le_neg_log_max hχ hlam b
  have hma : 0 < max ‖a‖ lam := lt_max_of_lt_right hlam
  have hmb : 0 < max ‖b‖ lam := lt_max_of_lt_right hlam
  have h3 : max ‖a‖ lam ≤ 2 * max ‖b‖ lam := max_le_two_mul_max hlam.le hab
  have h4 : Real.log (max ‖a‖ lam) ≤ Real.log 2 + Real.log (max ‖b‖ lam) := by
    rw [← Real.log_mul (by norm_num) hmb.ne']
    exact Real.log_le_log hma h3
  have h6 : Real.log 6 = Real.log 3 + Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith

end Kernel

/-! ### The half-interaction `v'_{i,j,+}` -/

section Half

variable {lam : ℝ}

/-- `v'_{i,j,+} - v_{i,j,+}`, with `v_{i,j,+} = g_λ(x_i - x_j) - g_λ(y_i - x_j)`. -/
theorem halfInteractionPlus_eq (τp τm : Fin N → ℝ) (d : Fin N → ℂ × ℂ) (i j : Fin N) :
    halfInteractionPlus χ lam τp τm d i j =
      (smearedKernel χ lam ((d i).1 - (d j).1) - smearedKernel χ lam ((d i).2 - (d j).1)) +
        (twoRadiusKernel χ (τm i) (τp j) ((d i).2 - (d j).1) -
          twoRadiusKernel χ (τp i) (τp j) ((d i).1 - (d j).1)) := by
  unfold halfInteractionPlus
  ring

/-- For `τ_i^+ = τ_i^-`: `|v'_{i,j,+} - v_{i,j,+}| ≤ √(π M) r_i / τ_j^+` (proof of
(3.43), the paper). -/
theorem abs_halfInteractionPlus_sub_le_of_eq (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {τp τm : Fin N → ℝ} (d : Fin N → ℂ × ℂ) {i j : Fin N} (hi : 0 < τp i) (hj : 0 < τp j)
    (heq : τp i = τm i) :
    |halfInteractionPlus χ lam τp τm d i j -
        (smearedKernel χ lam ((d i).1 - (d j).1) - smearedKernel χ lam ((d i).2 - (d j).1))| ≤
      Real.sqrt (Real.pi * M) / τp j * ‖(d i).1 - (d i).2‖ := by
  rw [halfInteractionPlus_eq, add_sub_cancel_left, ← heq]
  have := abs_twoRadiusKernel_sub_le hχ hM hi hj ((d i).2 - (d j).1) ((d i).1 - (d j).1)
  rwa [show (d i).2 - (d j).1 - ((d i).1 - (d j).1) = -((d i).1 - (d i).2) by ring,
    norm_neg] at this

/-- In general: `|v'_{i,j,+} - v_{i,j,+}| ≤ √(π M) (r_i + τ_i^+ + τ_i^-) / τ_j^+` (a first-order
form of (3.42), the paper). -/
theorem abs_halfInteractionPlus_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {τp τm : Fin N → ℝ} (d : Fin N → ℂ × ℂ) {i j : Fin N} (hpi : 0 < τp i) (hmi : 0 < τm i)
    (hj : 0 < τp j) :
    |halfInteractionPlus χ lam τp τm d i j -
        (smearedKernel χ lam ((d i).1 - (d j).1) - smearedKernel χ lam ((d i).2 - (d j).1))| ≤
      Real.sqrt (Real.pi * M) / τp j * (‖(d i).1 - (d i).2‖ + τp i + τm i) := by
  rw [halfInteractionPlus_eq, add_sub_cancel_left]
  set L := Real.sqrt (Real.pi * M) / τp j
  set a := (d i).2 - (d j).1
  set b := (d i).1 - (d j).1
  set f := smearedPotential χ (τp j)
  -- Insert the radius `τm i` at `b` before changing the radius at that same centre.
  have ht := abs_twoRadiusKernel_sub_le hχ hM hmi hj a b
  rw [show a - b = -((d i).1 - (d i).2) by dsimp [a, b]; ring, norm_neg] at ht
  have hr₁ := abs_twoRadiusKernel_sub_smearedPotential_le hχ hM hmi hj b
  have hr₂ := abs_twoRadiusKernel_sub_smearedPotential_le hχ hM hpi hj b
  calc |twoRadiusKernel χ (τm i) (τp j) a - twoRadiusKernel χ (τp i) (τp j) b|
      = |(twoRadiusKernel χ (τm i) (τp j) a - twoRadiusKernel χ (τm i) (τp j) b) +
          ((twoRadiusKernel χ (τm i) (τp j) b - f b) -
            (twoRadiusKernel χ (τp i) (τp j) b - f b))| := by ring_nf
    _ ≤ |twoRadiusKernel χ (τm i) (τp j) a - twoRadiusKernel χ (τm i) (τp j) b| +
        (|twoRadiusKernel χ (τm i) (τp j) b - f b| +
          |twoRadiusKernel χ (τp i) (τp j) b - f b|) :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ L * ‖(d i).1 - (d i).2‖ + (L * τm i + L * τp i) :=
      add_le_add ht (add_le_add hr₁ hr₂)
    _ = L * (‖(d i).1 - (d i).2‖ + τp i + τm i) := by ring

/-- The configuration with `x` and `y` exchanged. -/
def swapConfig (d : Fin N → ℂ × ℂ) : Fin N → ℂ × ℂ :=
  fun k => ((d k).2, (d k).1)

theorem norm_swapConfig (d : Fin N → ℂ × ℂ) (k : Fin N) :
    ‖(swapConfig d k).1 - (swapConfig d k).2‖ = ‖(d k).1 - (d k).2‖ := by
  simp only [swapConfig]
  exact norm_sub_rev _ _

/-- `v'_{i,j,-} = -v'_{i,j,+}` of the exchanged configuration with exchanged radii. -/
theorem halfInteractionMinus_eq_neg_swap (τp τm : Fin N → ℝ) (d : Fin N → ℂ × ℂ)
    (i j : Fin N) :
    halfInteractionMinus χ lam τp τm d i j =
      -halfInteractionPlus χ lam τm τp (swapConfig d) i j := by
  unfold halfInteractionMinus halfInteractionPlus swapConfig
  ring

end Half

/-! ### Continuous packing shells -/

/-- The uniform bound on `𝒩_i(t)` from (5.15), the paper.
Each continuous shell lies in two balls at scale `t/2`. -/
theorem card_continuous_shell_le {lam : ℝ} {d : Fin N → ℂ × ℂ} {τp : Fin N → ℝ} {i : Fin N}
    {T : Finset (Fin N)} {f : Fin N → ℝ} {P : ℕ}
    (hpack : ∀ t : ℝ, 0 ≤ t → ∀ z : ℂ,
      (T.filter fun k => ‖(d k).1 - z‖ ≤ 8 * t ∧ t ≤ τp k ∧ lam < τp k).card ≤ P)
    (hT : ∀ j ∈ T, min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖ ≤ f j ∧ f j ≤ 2 * τp j ∧
      lam < τp j)
    {t : ℝ} (ht : 0 < t) :
    (T.filter fun j => t < f j ∧ f j < 2 * t).card ≤ 2 * P := by
  classical
  set s := t / 2
  have hs : 0 ≤ s := by positivity
  have hsub : (T.filter fun j => t < f j ∧ f j < 2 * t) ⊆
      (T.filter fun j => ‖(d j).1 - (d i).1‖ ≤ 8 * s ∧ s ≤ τp j ∧ lam < τp j) ∪
        (T.filter fun j => ‖(d j).1 - (d i).2‖ ≤ 8 * s ∧ s ≤ τp j ∧ lam < τp j) := by
    intro j hj
    obtain ⟨hjT, hlo, hhi⟩ := Finset.mem_filter.mp hj
    obtain ⟨hmin, hf2, hlt⟩ := hT j hjT
    have htj : s ≤ τp j := by dsimp [s]; linarith
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases min_le_iff.mp (hmin.trans hhi.le) with h | h
    · left
      refine ⟨hjT, ?_, htj, hlt⟩
      rw [norm_sub_rev]
      dsimp [s]
      linarith
    · right
      refine ⟨hjT, ?_, htj, hlt⟩
      rw [norm_sub_rev]
      dsimp [s]
      linarith
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h1 := hpack s hs (d i).1
  have h2 := hpack s hs (d i).2
  omega


end UpperBound

end MultipoleBKT

end
