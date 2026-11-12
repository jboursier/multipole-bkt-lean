/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Packing
public import MultipoleBKT.UpperBound.BadPoints.RouteShell.Comparison
public import MultipoleBKT.Matching.Pair

/-!
# Control of bad–bad interactions (Lemma 5.12)

The paper: Lemma 5.12. Order the pairs by dipole length and split the charge signs.
For each positive half-interaction keep the four classes of (5.34):

* `d⁺ ≥ r_i` and `τ_j = λ`: both Newton corrections vanish (5.36).
* `d⁺ < r_i`: outside the negative-charge support the term is nonnegative.
  Treat `τ_j = λ`, `τ_j ≥ r_i/8` and `τ_j ≤ r_i/8` separately. Only strictly
  negative terms enter the packing count ((5.43), (5.45), (5.46)).
* `d⁺ ≥ max(r_i, λ)` and `τ_j > λ`: Newton support gives (5.47), the
  common-radius comparison gives the quadratic error, and the continuous
  counting integral gives (5.48).
* `r_i ≤ d⁺ < λ` and `τ_j > λ`: both radii of `i` equal `λ`, the quadratic
  comparison is uniformly bounded, and packing at scale `λ` gives (5.49).

The negative half follows by exchanging charges. Label order resolves equal
lengths in the external statements. No distinct-length assumption
is required for those statements.
-/

@[expose] public section

open Finset
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

namespace UpperBound

variable {χ : ℂ → ℝ}

/-! ### The case analysis of Steps 1–2 -/

section Steps

variable {N : ℕ} {lam : ℝ} {d : Fin N → ℂ × ℂ} {τp τm : Fin N → ℝ} {i j : Fin N}

/-- `(g_λ - g * δ₀^{(α)} * δ₀^{(η)})(w) = 0` when `α = η = λ`. -/
theorem smearedKernel_sub_twoRadiusKernel_lam (w : ℂ) :
    smearedKernel χ lam w - twoRadiusKernel χ lam lam w = 0 := by
  rw [twoRadiusKernel_self, sub_self]

/-- A radius `λ < τ ≤ max(r/4, λ)` forces `λ < r/4` and `τ ≤ r/4`. -/
theorem lt_div_of_lt_of_le_max {r τ : ℝ} (hlt : lam < τ) (hle : τ ≤ max (r / 4) lam) :
    lam < r / 4 ∧ τ ≤ r / 4 := by
  rcases le_total (r / 4) lam with h | h
  · rw [max_eq_right h] at hle
    exact absurd hlt (not_lt.mpr hle)
  · rw [max_eq_left h] at hle
    exact ⟨hlt.trans_le hle, hle⟩

/-- **Step 1 support** ((5.36), the paper): if `τ_j^+ = λ`, the radii of `i` are at most
`max(r_i/4, λ)` and `|x_i - x_j| ≥ r_i`, then
`P_j = (g_λ - g * δ^{τ_i^+} * δ^{λ})(x_i - x_j) = 0`. -/
theorem smearedKernel_sub_twoRadiusKernel_eq_zero_of_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    {α r : ℝ} (hα : lam ≤ α) (hαr : α ≤ max (r / 4) lam) {w : ℂ} (hw : r ≤ ‖w‖) :
    smearedKernel χ lam w - twoRadiusKernel χ α lam w = 0 := by
  rcases hα.eq_or_lt with h | h
  · rw [← h]
    exact smearedKernel_sub_twoRadiusKernel_lam w
  · obtain ⟨h1, h2⟩ := lt_div_of_lt_of_le_max h hαr
    exact smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam hα le_rfl (by linarith)

/-- **Eqs. (5.39), (5.40)** : if `|x_j - y_i| ≥ r_i`, `τ_i^- ≤ max(r_i/4, λ)` and
`Q_j ≠ 0`, then `τ_j^+ > λ` and `τ_j^+ > r_i/4`. -/
theorem lt_radius_of_Q_ne_zero (hχ : IsMollifier χ) (hlam : 0 < lam) (hpj : lam ≤ τp j)
    (hmi : lam ≤ τm i) (hmi' : τm i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam)
    (hA : ‖(d i).1 - (d i).2‖ ≤ ‖(d j).1 - (d i).2‖)
    (hQ : smearedKernel χ lam ((d i).2 - (d j).1) - twoRadiusKernel χ (τm i) (τp j)
      ((d i).2 - (d j).1) ≠ 0) :
    lam < τp j ∧ ‖(d i).1 - (d i).2‖ / 4 < τp j := by
  set r := ‖(d i).1 - (d i).2‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hdist : ‖(d i).2 - (d j).1‖ < τm i + τp j := by
    by_contra h
    exact hQ (smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam hmi hpj (not_lt.mp h))
  rw [norm_sub_rev] at hA
  have hlt : lam < τp j := by
    rcases hpj.eq_or_lt with h | h
    · -- `τ_j^+ = λ`: then `τ_i^- > λ`, so `r_i > 4λ`, and `r_i < r_i/4 + λ` is impossible
      exfalso
      rcases hmi.eq_or_lt with h' | h'
      · apply hQ
        rw [← h, ← h']
        exact smearedKernel_sub_twoRadiusKernel_lam _
      · obtain ⟨h1, h2⟩ := lt_div_of_lt_of_le_max h' hmi'
        rw [← h] at hdist
        linarith
    · exact h
  refine ⟨hlt, ?_⟩
  rcases le_total (r / 4) lam with h | h
  · exact h.trans_lt hlt
  · rw [max_eq_left h] at hmi'
    linarith

/-- (5.38): outside the negative-charge Newton support the interaction is nonnegative. -/
theorem halfInteractionPlus_nonneg_of_outside (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hpi : lam ≤ τp i) (hmi : lam ≤ τm i) (hj : lam ≤ τp j)
    (hout : τm i + τp j ≤ ‖(d i).2 - (d j).1‖) :
    0 ≤ halfInteractionPlus χ lam τp τm d i j := by
  have hQ := smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam hmi hj hout
  have hP := smearedKernel_sub_twoRadiusKernel_nonneg hχ hlam hpi hj ((d i).1 - (d j).1)
  unfold halfInteractionPlus
  linarith

/-- The strict-negativity qualification of (5.40) and (5.41),
the paper. A nonzero interaction alone does not imply these bounds. -/
theorem radius_bounds_of_halfInteractionPlus_neg (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hpi : lam ≤ τp i) (hmi : lam ≤ τm i) (hj : lam ≤ τp j)
    (hmi' : τm i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam)
    (hA : ‖(d i).1 - (d i).2‖ ≤ ‖(d j).1 - (d i).2‖)
    (hv : halfInteractionPlus χ lam τp τm d i j < 0) :
    lam < τp j ∧ ‖(d i).1 - (d i).2‖ / 4 < τp j ∧
      (4 * lam ≤ ‖(d i).1 - (d i).2‖ → 3 * ‖(d i).1 - (d i).2‖ / 4 ≤ τp j) ∧
      ‖(d i).1 - (d i).2‖ ≤ 2 * τp j := by
  have hdist : ‖(d i).2 - (d j).1‖ < τm i + τp j := by
    by_contra h
    exact (not_lt_of_ge (halfInteractionPlus_nonneg_of_outside hχ hlam hpi hmi hj (not_lt.mp h))) hv
  have hQ : smearedKernel χ lam ((d i).2 - (d j).1) -
      twoRadiusKernel χ (τm i) (τp j) ((d i).2 - (d j).1) ≠ 0 := by
    intro hzero
    have hpos := smearedKernel_sub_twoRadiusKernel_nonneg hχ hlam hpi hj ((d i).1 - (d j).1)
    unfold halfInteractionPlus at hv
    linarith
  obtain ⟨ht, hr⟩ := lt_radius_of_Q_ne_zero hχ hlam hj hmi hmi' hA hQ
  have hm : τm i ≤ τp j := hmi'.trans (max_le hr.le ht.le)
  rw [norm_sub_rev (d j).1 (d i).2] at hA
  refine ⟨ht, hr, ?_, by linarith⟩
  intro hlarge
  rw [max_eq_left (by linarith : lam ≤ ‖(d i).1 - (d i).2‖ / 4)] at hmi'
  linarith

/-- (5.43): a negative interaction is impossible when the other radius is `λ`.
This uses matching and Newton's theorem, before any packing estimate. -/
theorem halfInteractionPlus_nonneg_of_radius_eq_lam (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hpi : lam ≤ τp i) (hmi : lam ≤ τm i)
    (hmi' : τm i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam)
    (hj : τp j = lam) (hA : ‖(d i).1 - (d i).2‖ ≤ ‖(d j).1 - (d i).2‖) :
    0 ≤ halfInteractionPlus χ lam τp τm d i j := by
  have hQ := smearedKernel_sub_twoRadiusKernel_eq_zero_of_le hχ hlam hmi hmi'
    (w := (d i).2 - (d j).1) (by rw [norm_sub_rev (d i).2 (d j).1]; exact hA)
  have hP := smearedKernel_sub_twoRadiusKernel_nonneg hχ hlam hpi (le_of_eq hj.symm)
    ((d i).1 - (d j).1)
  unfold halfInteractionPlus
  rw [hj] at hP ⊢
  linarith

/-- The small-radius subcase of (5.44).
The negative-charge correction vanishes outside its Newton support. -/
theorem halfInteractionPlus_nonneg_of_radius_le_eighth (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hpi : lam ≤ τp i) (hmi : lam ≤ τm i) (hj : lam ≤ τp j)
    (hmi' : τm i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam)
    (hsmall : τp j ≤ ‖(d i).1 - (d i).2‖ / 8)
    (hA : ‖(d i).1 - (d i).2‖ ≤ ‖(d j).1 - (d i).2‖) :
    0 ≤ halfInteractionPlus χ lam τp τm d i j := by
  have hr : 0 ≤ ‖(d i).1 - (d i).2‖ := norm_nonneg _
  have hl : lam ≤ ‖(d i).1 - (d i).2‖ / 4 := by linarith
  rw [max_eq_left hl] at hmi'
  apply halfInteractionPlus_nonneg_of_outside hχ hlam hpi hmi hj
  rw [norm_sub_rev (d i).2 (d j).1]
  linarith

/-- **Eq. (5.44)**, the case `τ_j^+ ≥ max(r_i/8, λ)` : if `|x_j - y_i| ≥ r_i` and the
radii of `i` are at most `max(r_i/4, λ) ≤ 2τ_j^+`, then
`v'_{i,j,+} ≥ -(log 6 + max(c_χ, 0) + 12 √(π M))`. -/
theorem neg_le_halfInteractionPlus (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) (hpi : lam ≤ τp i) (hmi : lam ≤ τm i)
    (hpi' : τp i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam)
    (hmi' : τm i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam)
    (hpj : max (‖(d i).1 - (d i).2‖ / 8) lam ≤ τp j)
    (hA : ‖(d i).1 - (d i).2‖ ≤ ‖(d j).1 - (d i).2‖) :
    -(Real.log 6 + max (∫ y, logKernel y ∂smearedCharge χ 0 1) 0 +
        12 * Real.sqrt (Real.pi * M)) ≤ halfInteractionPlus χ lam τp τm d i j := by
  set r := ‖(d i).1 - (d i).2‖
  set m := max (r / 4) lam
  set S := Real.sqrt (Real.pi * M)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hτj : 0 < τp j := hlam.trans_le ((le_max_right _ _).trans hpj)
  have hr8 : r ≤ 8 * τp j := by linarith [le_max_left (r / 8) lam]
  have hmτ : m ≤ 2 * τp j := max_le (by linarith) (by linarith [le_max_right (r / 8) lam])
  rw [norm_sub_rev] at hA
  -- the `g_λ` part
  have h1 : -(Real.log 6 + max (∫ y, logKernel y ∂smearedCharge χ 0 1) 0) ≤
      smearedKernel χ lam ((d i).1 - (d j).1) - smearedKernel χ lam ((d i).2 - (d j).1) := by
    refine neg_le_smearedKernel_sub hχ hlam ?_
    calc ‖(d i).1 - (d j).1‖ = ‖((d i).1 - (d i).2) + ((d i).2 - (d j).1)‖ := by ring_nf
      _ ≤ r + ‖(d i).2 - (d j).1‖ := norm_add_le _ _
      _ ≤ 2 * ‖(d i).2 - (d j).1‖ := by linarith
  -- the kernel part
  have h2 := abs_halfInteractionPlus_sub_le (lam := lam) hχ hM d (hlam.trans_le hpi)
    (hlam.trans_le hmi) hτj
  have h3 : S / τp j * (r + τp i + τm i) ≤ 12 * S := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hτj]
    have : r + τp i + τm i ≤ 12 * τp j := by linarith
    nlinarith
  have h4 := neg_abs_le (halfInteractionPlus χ lam τp τm d i j -
    (smearedKernel χ lam ((d i).1 - (d j).1) - smearedKernel χ lam ((d i).2 - (d j).1)))
  linarith

/-- **Step 3 pointwise bound** ((5.47), (5.48), the paper): if `d^+ ≥ r_i`, `τ_j^+ > λ`,
the radii of `i` are at most `max(r_i/4, λ)` and `v'_{i,j,+} ≠ 0`, then
`max(d^+, λ) ≤ 2 τ_j^+` and
`|v'_{i,j,+}| ≤ (C_χ + 6 √(π M) + 12πM) max(r_i, λ) / max(d^+, λ)`, with `C_χ` the constant of
Lemma 3.7 (3). -/
theorem abs_halfInteractionPlus_le_of_far (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {Cχ : ℝ} (h37 : ∀ d e : ℂ × ℂ, ‖d.1 - d.2‖ ≤ min ‖d.1 - e.1‖ ‖d.2 - e.1‖ →
      |smearedKernel χ lam (d.1 - e.1) - smearedKernel χ lam (d.2 - e.1)| ≤
        Cχ * ‖d.1 - d.2‖ / max (min ‖d.1 - e.1‖ ‖d.2 - e.1‖) lam) (hCχ : 0 ≤ Cχ)
    (hlam : 0 < lam) (hp : ∀ k, lam ≤ τp k) (hm : ∀ k, lam ≤ τm k)
    (hpi' : τp i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam)
    (hmi' : τm i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam)
    (hfar : ‖(d i).1 - (d i).2‖ ≤ min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖)
    (hlt : lam < τp j) (hv : halfInteractionPlus χ lam τp τm d i j ≠ 0) :
    max (min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖) lam ≤ 2 * τp j ∧
      |halfInteractionPlus χ lam τp τm d i j| ≤ (Cχ + 6 * Real.sqrt (Real.pi * M) + 12 * Real.pi * M) *
        max ‖(d i).1 - (d i).2‖ lam / max (min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖) lam := by
  set r := ‖(d i).1 - (d i).2‖
  set e := min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖
  set m := max (r / 4) lam
  set B := max r lam
  set f := max e lam
  set S := Real.sqrt (Real.pi * M)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hτj : 0 < τp j := hlam.trans hlt
  have hr0 : 0 ≤ r := norm_nonneg _
  have hf0 : 0 < f := lt_max_of_lt_right hlam
  -- `τ_j^+ ≥ max(r_i/4, λ)` and `d^+ < 2 τ_j^+` (eq. (5.47))
  have hsupp := halfInteractionPlus_ne_zero hχ hlam hp hm hv
  have he : e < m + τp j := by
    rcases hsupp with h | h
    · exact (min_le_left _ _).trans_lt (by linarith)
    · exact (min_le_right _ _).trans_lt (by linarith)
  have hmτ : m ≤ τp j := by
    rcases le_total (r / 4) lam with h | h
    · rw [show m = lam from max_eq_right h]
      exact hlt.le
    · rw [show m = r / 4 from max_eq_left h] at he ⊢
      linarith
  have hf2 : f ≤ 2 * τp j := max_le (by linarith) (by linarith)
  refine ⟨hf2, ?_⟩
  -- the bound
  have h1 := h37 (d i) (d j) hfar
  have h2 := abs_halfInteractionPlus_sub_le_sq (lam := lam) hχ hM d (hlam.trans_le (hp i))
    (hlam.trans_le (hm i)) hτj
  have hmB : m ≤ B := max_le_max (by linarith) le_rfl
  have hrB : r ≤ B := le_max_left _ _
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  have h3 : Cχ * r / f ≤ Cχ * B / f := by gcongr
  have htrans : S * r / τp j ≤ 2 * S * B / f := by
    rw [div_le_div_iff₀ hτj hf0]
    calc S * r * f ≤ S * B * (2 * τp j) := by gcongr
      _ = 2 * S * B * τp j := by ring
  have hm0 : 0 ≤ max (τp i) (τm i) := (hlam.trans_le (hp i)).le.trans (le_max_left _ _)
  have hmle : max (τp i) (τm i) ≤ m := max_le hpi' hmi'
  have hquad : max (τp i) (τm i) ^ 2 / (τp j) ^ 2 ≤ 2 * B / f := by
    have hsq : max (τp i) (τm i) ^ 2 ≤ B * τp j :=
      calc _ ≤ max (τp i) (τm i) * τp j := by nlinarith [hmle.trans hmτ]
           _ ≤ B * τp j := mul_le_mul_of_nonneg_right (hmle.trans hmB) hτj.le
    rw [div_le_div_iff₀ (sq_pos_of_pos hτj) hf0]
    calc max (τp i) (τm i) ^ 2 * f ≤ (B * τp j) * (2 * τp j) := by gcongr
      _ = 2 * B * (τp j) ^ 2 := by ring
  have h4 : 6 * Real.pi * M * max (τp i) (τm i) ^ 2 / (τp j) ^ 2 ≤
      12 * Real.pi * M * B / f := by
    calc _ = (6 * Real.pi * M) * (max (τp i) (τm i) ^ 2 / (τp j) ^ 2) := by ring
      _ ≤ (6 * Real.pi * M) * (2 * B / f) := by gcongr
      _ = _ := by ring
  have h5 := abs_add_le (smearedKernel χ lam ((d i).1 - (d j).1) -
    smearedKernel χ lam ((d i).2 - (d j).1)) (halfInteractionPlus χ lam τp τm d i j -
      (smearedKernel χ lam ((d i).1 - (d j).1) - smearedKernel χ lam ((d i).2 - (d j).1)))
  rw [add_sub_cancel] at h5
  have hB0 : 0 ≤ B := hr0.trans hrB
  calc |halfInteractionPlus χ lam τp τm d i j| ≤
        Cχ * B / f + 2 * S * B / f + 12 * Real.pi * M * B / f := by linarith
    _ ≤ (Cχ + 6 * S + 12 * Real.pi * M) * B / f := by
      have : 0 ≤ S * B / f := by positivity
      linarith [show (Cχ + 6 * S + 12 * Real.pi * M) * B / f =
        Cχ * B / f + 2 * S * B / f + 12 * Real.pi * M * B / f + 4 * (S * B / f) by ring]

end Steps

/-! ### The abstract lower bound for the `+` part -/

/-- **Steps 1–4 of Lemma 5.12** ((5.36)–(5.49), the paper) in abstract form: if the radii are
`≥ λ > 0`, those of `i` are at most `max(r_i/4, λ)`, every `j ∈ J` has `|x_j - y_i| ≥ r_i`, and the
packing bound `P` holds for the charges `x_k`, `k ∈ J`, then
`Σ_{j ∈ J} v'_{i,j,+} ≥ -C P` with `C` depending only on `χ`. -/
theorem sum_halfInteractionPlus_ge (hχ : IsMollifier χ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {N : ℕ} (lam : ℝ) (d : Fin N → ℂ × ℂ) (τp τm : Fin N → ℝ) (J : Finset (Fin N)) (i : Fin N)
      (P : ℕ), 0 < lam → (∀ k, lam ≤ τp k) → (∀ k, lam ≤ τm k) →
      τp i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam → τm i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam →
      (∀ t : ℝ, 0 ≤ t → ∀ z : ℂ,
        (J.filter fun k => ‖(d k).1 - z‖ ≤ 8 * t ∧ t ≤ τp k ∧ lam < τp k).card ≤ P) →
      (∀ j ∈ J, ‖(d i).1 - (d i).2‖ ≤ ‖(d j).1 - (d i).2‖) →
      -(C * P) ≤ ∑ j ∈ J, halfInteractionPlus χ lam τp τm d i j := by
  classical
  obtain ⟨Cχ, hCχ, h37⟩ := lemma_3_7_3 hχ
  obtain ⟨Mχ, hMχ⟩ := hχ.exists_bound
  set S := Real.sqrt (Real.pi * Mχ)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  set Cg := Real.log 6 + max (∫ y, logKernel y ∂smearedCharge χ 0 1) 0
  have hCg : 0 ≤ Cg := by
    have : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have := le_max_right (∫ y, logKernel y ∂smearedCharge χ 0 1) 0
    linarith
  have hM0 : 0 ≤ Mχ := hχ.nonneg_of_le hMχ
  set C₁ := Cg + 12 * S
  set C₂ := Cχ + 6 * S + 12 * Real.pi * Mχ
  have hC₁ : 0 ≤ C₁ := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + 6 * C₂, by positivity, ?_⟩
  intro N lam d τp τm J i P hlam hp hm hpi' hmi' hpack hA
  set r := ‖(d i).1 - (d i).2‖
  have hr0 : 0 ≤ r := norm_nonneg _
  set v := fun j => halfInteractionPlus χ lam τp τm d i j
  set e := fun j => min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖
  set J₁ := J.filter fun j => r ≤ e j ∧ τp j = lam
  set J₂ := J.filter fun j => e j < r
  set J₃ := J.filter fun j => max r lam ≤ e j ∧ lam < τp j
  set J₄ := J.filter fun j => r ≤ e j ∧ e j < lam ∧ lam < τp j
  -- (5.34): retain all four interaction classes.
  have hsplit : ∑ j ∈ J, v j = (∑ j ∈ J₁, v j) + (∑ j ∈ J₂, v j) +
      (∑ j ∈ J₃, v j) + ∑ j ∈ J₄, v j := by
    simp only [J₁, J₂, J₃, J₄, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hτ := hp j
    by_cases hn : e j < r
    · simp [hn, not_le.mpr hn, show ¬ max r lam ≤ e j by intro h; linarith [le_max_left r lam]]
    · have hr : r ≤ e j := not_lt.mp hn
      by_cases he : e j < lam
      · have hmax : ¬ max r lam ≤ e j := by intro h; linarith [le_max_right r lam]
        rcases hτ.eq_or_lt with ht | ht
        · simp [hn, hr, he, hmax, ht.symm]
        · simp [hn, hr, he, hmax, ht, ne_of_gt ht]
      · have hmax : max r lam ≤ e j := max_le hr (not_lt.mp he)
        rcases hτ.eq_or_lt with ht | ht
        · simp [hn, hr, he, hmax, ht.symm]
        · simp [hn, hr, he, hmax, ht, ne_of_gt ht]
  -- Step 1, (5.36): both Newton corrections vanish.
  have h₁ : ∑ j ∈ J₁, v j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨_, hej, htj⟩ := Finset.mem_filter.mp hj
    dsimp [v]
    unfold halfInteractionPlus
    rw [htj, smearedKernel_sub_twoRadiusKernel_eq_zero_of_le hχ hlam (hp i) hpi'
        (hej.trans (min_le_left _ _)),
      smearedKernel_sub_twoRadiusKernel_eq_zero_of_le hχ hlam (hm i) hmi'
        (hej.trans (min_le_right _ _)), sub_zero]
  -- Step 2: distinguish the zero-radius, large-radius and small-radius subcases.
  have h₂ : -(C₁ * P) ≤ ∑ j ∈ J₂, v j := by
    have hlow : ∀ j ∈ J₂, -C₁ ≤ v j := by
      intro j hj
      have hjJ := (Finset.mem_filter.mp hj).1
      rcases (hp j).eq_or_lt with ht | ht
      · exact (neg_nonpos.mpr hC₁).trans
          (halfInteractionPlus_nonneg_of_radius_eq_lam hχ hlam (hp i) (hm i) hmi' ht.symm (hA j hjJ))
      · by_cases hs : τp j ≤ r / 8
        · exact (neg_nonpos.mpr hC₁).trans
            (halfInteractionPlus_nonneg_of_radius_le_eighth hχ hlam (hp i) (hm i) (hp j)
              hmi' hs (hA j hjJ))
        · exact neg_le_halfInteractionPlus hχ hMχ hlam (hp i) (hm i) hpi' hmi'
            (max_le (not_le.mp hs).le ht.le) (hA j hjJ)
    rw [← Finset.sum_filter_add_sum_filter_not J₂ fun j => v j < 0]
    set K := J₂.filter fun j => v j < 0
    have hnonneg : 0 ≤ ∑ j ∈ J₂ with ¬ v j < 0, v j :=
      Finset.sum_nonneg fun j hj => not_lt.mp (Finset.mem_filter.mp hj).2
    -- The radius restriction is asserted only for strictly negative interactions.
    have hmem : ∀ j ∈ K, lam < τp j ∧ r / 4 < τp j ∧ e j < r ∧ j ∈ J := by
      intro j hj
      obtain ⟨hj₂, hv⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjJ, hej⟩ := Finset.mem_filter.mp hj₂
      obtain ⟨h₁, h₂, _, _⟩ := radius_bounds_of_halfInteractionPlus_neg hχ hlam
        (hp i) (hm i) (hp j) hmi' (hA j hjJ) hv
      exact ⟨h₁, h₂, hej, hjJ⟩
    have hcard : K.card ≤ P := by
      refine (Finset.card_le_card fun j hj => ?_).trans (hpack (r / 4) (by positivity) (d i).1)
      obtain ⟨h₁, h₂, hej, hjJ⟩ := hmem j hj
      refine Finset.mem_filter.mpr ⟨hjJ, ?_, h₂.le, h₁⟩
      rcases min_lt_iff.mp hej with h | h
      · rw [norm_sub_rev]; linarith
      · calc ‖(d j).1 - (d i).1‖ = ‖((d j).1 - (d i).2) + ((d i).2 - (d i).1)‖ := by ring_nf
          _ ≤ ‖(d j).1 - (d i).2‖ + ‖(d i).2 - (d i).1‖ := norm_add_le _ _
          _ ≤ 8 * (r / 4) := by
            rw [norm_sub_rev (d j).1 (d i).2, norm_sub_rev (d i).2 (d i).1]
            linarith
    have hsum := Finset.sum_le_sum (s := K) (fun j hj => hlow j (Finset.mem_filter.mp hj).1)
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have : (K.card : ℝ) ≤ P := by exact_mod_cast hcard
    nlinarith
  set B := max r lam
  have hB : 0 < B := lt_max_of_lt_right hlam
  -- Step 3, (5.47), quadratic comparison, continuous packing integral, (5.48).
  have h₃ : ∑ j ∈ J₃, |v j| ≤ 4 * C₂ * P := by
    set K := J₃.filter fun j => v j ≠ 0
    have hsum : ∑ j ∈ J₃, |v j| = ∑ j ∈ K, |v j| := by
      simpa only [abs_ne_zero] using (Finset.sum_filter_ne_zero (f := fun j => |v j|) J₃).symm
    have hmem : ∀ j ∈ K, j ∈ J ∧ B ≤ e j ∧ lam < τp j ∧ v j ≠ 0 := by
      intro j hj
      obtain ⟨hj₃, hv⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjJ, he, ht⟩ := Finset.mem_filter.mp hj₃
      exact ⟨hjJ, he, ht, hv⟩
    have hbound : ∀ j ∈ K, e j ≤ 2 * τp j ∧ |v j| ≤ C₂ * B / e j := by
      intro j hj
      obtain ⟨_, he, ht, hv⟩ := hmem j hj
      have hfar := (le_max_left r lam).trans he
      have h := abs_halfInteractionPlus_le_of_far hχ hMχ (fun d e => (h37 lam hlam d e).1)
        hCχ.le hlam hp hm hpi' hmi' hfar ht hv
      rwa [max_eq_left ((le_max_right r lam).trans he)] at h
    have hcount := sum_div_le_of_continuous_count K e hB (fun j hj => (hmem j hj).2.1) (2 * P)
      fun t ht => card_continuous_shell_le (T := K) (τp := τp) (f := e)
        (fun s hs z => (Finset.card_le_card (Finset.filter_subset_filter _
          ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))).trans (hpack s hs z))
        (fun j hj => ⟨le_rfl, (hbound j hj).1, (hmem j hj).2.2.1⟩) ht
    rw [hsum]
    calc ∑ j ∈ K, |v j| ≤ ∑ j ∈ K, C₂ * (B / e j) :=
          Finset.sum_le_sum fun j hj => by simpa only [mul_div_assoc] using (hbound j hj).2
      _ = C₂ * ∑ j ∈ K, B / e j := by rw [Finset.mul_sum]
      _ ≤ C₂ * (2 * ((2 * P : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hcount hC₂
      _ = 4 * C₂ * P := by push_cast; ring
  -- Step 4, (5.49): here both radii of `i` equal `λ`. One packing scale suffices.
  have h₄ : ∑ j ∈ J₄, |v j| ≤ 2 * C₂ * P := by
    have hrLam : ∀ j ∈ J₄, r < lam := fun j hj => by
      obtain ⟨_, hr, he, _⟩ := Finset.mem_filter.mp hj
      exact hr.trans_lt he
    have hbound : ∀ j ∈ J₄, |v j| ≤ C₂ := by
      intro j hj
      obtain ⟨_, hr, he, ht⟩ := Finset.mem_filter.mp hj
      have hri := hrLam j hj
      have hpiLam : τp i = lam := le_antisymm (hpi'.trans (max_le (by linarith) le_rfl)) (hp i)
      have hmiLam : τm i = lam := le_antisymm (hmi'.trans (max_le (by linarith) le_rfl)) (hm i)
      have h₁ := (h37 lam hlam (d i) (d j)).1 hr
      have h₂ := abs_halfInteractionPlus_sub_le_sq (lam := lam) hχ hMχ d
        (hlam.trans_le (hp i)) (hlam.trans_le (hm i)) (hlam.trans ht)
      rw [hpiLam, hmiLam, max_self] at h₂
      have htrans : S * r / τp j ≤ S := (div_le_iff₀ (hlam.trans ht)).mpr (by nlinarith)
      have hquad : 6 * Real.pi * Mχ * lam ^ 2 / (τp j) ^ 2 ≤ 6 * Real.pi * Mχ := by
        rw [div_le_iff₀ (sq_pos_of_pos (hlam.trans ht))]
        gcongr
      rw [max_eq_right he.le] at h₁
      have hbase : Cχ * r / lam ≤ Cχ := (div_le_iff₀ hlam).mpr (by nlinarith)
      have hadd := abs_add_le (smearedKernel χ lam ((d i).1 - (d j).1) -
        smearedKernel χ lam ((d i).2 - (d j).1)) (v j -
          (smearedKernel χ lam ((d i).1 - (d j).1) - smearedKernel χ lam ((d i).2 - (d j).1)))
      rw [add_sub_cancel] at hadd
      dsimp [C₂, S] at *
      nlinarith [Real.pi_pos]
    have hcard : J₄.card ≤ 2 * P := by
      have hsub : J₄ ⊆ (J.filter fun j => ‖(d j).1 - (d i).1‖ ≤ 8 * lam ∧ lam ≤ τp j ∧ lam < τp j) ∪
          (J.filter fun j => ‖(d j).1 - (d i).2‖ ≤ 8 * lam ∧ lam ≤ τp j ∧ lam < τp j) := by
        intro j hj
        obtain ⟨hjJ, _, he, ht⟩ := Finset.mem_filter.mp hj
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rcases min_lt_iff.mp he with hx | hy
        · exact Or.inl ⟨hjJ, by rw [norm_sub_rev]; linarith, ht.le, ht⟩
        · exact Or.inr ⟨hjJ, by rw [norm_sub_rev]; linarith, ht.le, ht⟩
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (by simpa only [two_mul] using
          Nat.add_le_add (hpack lam hlam.le (d i).1) (hpack lam hlam.le (d i).2)))
    have hsum := Finset.sum_le_sum hbound
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have : (J₄.card : ℝ) ≤ 2 * P := by exact_mod_cast hcard
    nlinarith
  have h₃low : -(∑ j ∈ J₃, |v j|) ≤ ∑ j ∈ J₃, v j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => neg_abs_le _
  have h₄low : -(∑ j ∈ J₄, |v j|) ≤ ∑ j ∈ J₄, v j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => neg_abs_le _
  rw [hsplit, h₁]
  linarith

/-! ### Reordering the pairs -/

/-- For a symmetric `f` and a relation `R` that orders every pair of distinct labels exactly one
way and is irreflexive, `Σ_{i ∈ S} Σ_{j ∈ S, R i j} f_ij` is half of `Σ_{i ≠ j ∈ S} f_ij`. -/
theorem two_mul_sum_filter_rel {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ι → ℝ)
    (hf : ∀ i j, f i j = f j i) (R : ι → ι → Prop) [DecidableRel R]
    (hR : ∀ i j, i ≠ j ↔ (R i j ∨ R j i)) (hR' : ∀ i j, ¬ (R i j ∧ R j i)) :
    2 * ∑ i ∈ S, ∑ j ∈ S with R i j, f i j = ∑ i ∈ S, ∑ j ∈ S with i ≠ j, f i j := by
  have hsplit : ∀ i, ∑ j ∈ S with i ≠ j, f i j =
      ∑ j ∈ S with R i j, f i j + ∑ j ∈ S with R j i, f i j := by
    intro i
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j
      simp only [Finset.mem_filter, Finset.mem_union, hR i j]
      tauto
    · rw [Finset.disjoint_filter]
      exact fun j _ h1 h2 => hR' i j ⟨h1, h2⟩
  have hswap : ∑ i ∈ S, ∑ j ∈ S with R j i, f i j = ∑ i ∈ S, ∑ j ∈ S with R i j, f i j := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hf]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, hswap]
  ring

/-- For a symmetric `f`, the sum over `i < j` equals the sum over `R i j` for any relation `R`
ordering every pair of distinct labels exactly one way. -/
theorem sum_filter_lt_eq_sum_filter_rel {ι : Type*} [LinearOrder ι] (S : Finset ι)
    (f : ι → ι → ℝ) (hf : ∀ i j, f i j = f j i) (R : ι → ι → Prop) [DecidableRel R]
    (hR : ∀ i j, i ≠ j ↔ (R i j ∨ R j i)) (hR' : ∀ i j, ¬ (R i j ∧ R j i)) :
    ∑ i ∈ S, ∑ j ∈ S with i < j, f i j = ∑ i ∈ S, ∑ j ∈ S with R i j, f i j := by
  have h1 := two_mul_sum_filter_rel S f hf R hR hR'
  have h2 := two_mul_sum_filter_rel S f hf (· < ·) (fun i j => by
    constructor
    · exact fun h => h.lt_or_gt
    · rintro (h | h)
      · exact h.ne
      · exact h.ne') (fun i j h => lt_asymm h.1 h.2)
  linarith

/-! ### Lemma 5.12 -/

section Lemma

variable {N : ℕ}

/-- **Compatibility of the matching** (Lemma 4.5, the paper (5.39)): on `𝒜_ij` (in the order of the
labels), if `r_i ≤ r_j`, then `|x_j - y_i| ≥ r_i` and `|x_i - y_j| ≥ r_i`. -/
theorem le_norm_of_isStableDipolePair {c : Fin N → ℂ × ℂ} {i j : Fin N}
    (hst : (i < j → IsStableDipolePair (c i) (c j)) ∧ (j < i → IsStableDipolePair (c j) (c i)))
    (hij : i ≠ j) (hr : ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖) :
    ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ‖(c i).1 - (c j).2‖ := by
  rcases hij.lt_or_gt with h | h
  · rcases (isStableDipolePair_iff' _ _).mp (hst.1 h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h2, h1⟩
    · exact ⟨hr.trans h2.le, hr.trans h1.le⟩
  · rcases (isStableDipolePair_iff' _ _).mp (hst.2 h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hr.trans h1, hr.trans h2⟩
    · exact ⟨h1.le, h2.le⟩

/-- `v'_ij` depends only on the radii of `i` and `j`. -/
theorem ballGrowthInteraction_congr {lam : ℝ} {τp τm τp' τm' : Fin N → ℝ} (c : Fin N → ℂ × ℂ)
    {i j : Fin N} (hpi : τp i = τp' i) (hpj : τp j = τp' j) (hmi : τm i = τm' i)
    (hmj : τm j = τm' j) :
    ballGrowthInteraction χ lam τp τm c i j = ballGrowthInteraction χ lam τp' τm' c i j := by
  unfold ballGrowthInteraction
  rw [hpi, hpj, hmi, hmj]

/-- **Lemma 5.12 for the radii of any clustering** (the general form of eq. (5.32)):
there is `C > 0` depending only on `χ` and `q` such that for every configuration `c`, cutoff
`h`, `λ > 0` and set `S` of labels with `𝒜_ij` for all `i < j` in `S`,
`Σ_{i<j ∈ S} v'_ij ≥ -C |S|`, where `v'_ij` is computed with the radii
`τ_k^± = max(λ, removal value)` of the `q`-clusterings of the positive and negative charges of
`c` with cutoff `h`. With `S = I_bad` this is Lemma 5.12 (`lemma_5_12`). With `S` all the labels
of a frozen bad configuration it is the form used at (5.112). -/
theorem sum_lt_ballGrowthInteraction_ge (hχ : IsMollifier χ) (q : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} (h lam : ℝ) (c : Fin N → ℂ × ℂ) (S : Finset (Fin N)), 0 < lam →
      (∀ i ∈ S, ∀ j ∈ S, i < j → IsStableDipolePair (c i) (c j)) →
      -(C * S.card) ≤ ∑ i ∈ S, ∑ j ∈ S with i < j, ballGrowthInteraction χ lam
        (clusterRadius q h lam (fun k => (c k).1) fun k => ‖(c k).1 - (c k).2‖)
        (clusterRadius q h lam (fun k => (c k).2) fun k => ‖(c k).1 - (c k).2‖) c i j := by
  classical
  obtain ⟨C₀, hC₀, hplus⟩ := sum_halfInteractionPlus_ge hχ
  set P := packingConstant q 8
  refine ⟨2 * C₀ * P + 1, by positivity, ?_⟩
  intro N h lam c S hlam hS
  set τp := clusterRadius q h lam (fun k => (c k).1) fun k => ‖(c k).1 - (c k).2‖
  set τm := clusterRadius q h lam (fun k => (c k).2) fun k => ‖(c k).1 - (c k).2‖
  set key : Fin N → ℝ ×ₗ Fin N := fun k => toLex (‖(c k).1 - (c k).2‖, k)
  have hkey : Function.Injective key := fun a b h => by
    simpa [key] using congrArg (fun p => (ofLex p).2) h
  set R : Fin N → Fin N → Prop := fun a b => key a < key b
  rw [sum_filter_lt_eq_sum_filter_rel S _ (ballGrowthInteraction_comm hχ τp τm c) R
    (fun a b => ⟨fun h => (lt_or_gt_of_ne (hkey.ne h)), fun h hab => by
      rcases h with h | h <;> simp [R, hab] at h⟩)
    (fun a b h => lt_asymm h.1 h.2)]
  -- the bound for each `i ∈ S`
  have hi : ∀ i ∈ S, -(2 * C₀ * P) ≤
      ∑ j ∈ S with R i j, ballGrowthInteraction χ lam τp τm c i j := by
    intro i hiS
    set J := S.filter fun j => R i j
    have hJ : ∀ j ∈ J, j ≠ i ∧ ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖ := fun j hj => by
      have hR := (Finset.mem_filter.mp hj).2
      refine ⟨fun h => by simp [R, h] at hR, ?_⟩
      simp only [R, key, Prod.Lex.toLex_lt_toLex] at hR
      rcases hR with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    have hA : ∀ j ∈ J, ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c i).2‖ ∧
        ‖(c i).1 - (c i).2‖ ≤ ‖(c i).1 - (c j).2‖ := fun j hj => by
      have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
      exact le_norm_of_isStableDipolePair ⟨hS i hiS j hjS, hS j hjS i hiS⟩ (hJ j hj).1.symm
        (hJ j hj).2
    have hJS : J ⊆ S := Finset.filter_subset _ _
    have hmax : ∀ (z : Fin N → ℂ) (k : Fin N), clusterRadius q h lam z
        (fun k => ‖(c k).1 - (c k).2‖) k ≤ max (‖(c k).1 - (c k).2‖ / 4) lam :=
      fun z k => clusterRadius_le_max_div lam k
    -- the `+` part
    have h1 : -(C₀ * P) ≤ ∑ j ∈ J, halfInteractionPlus χ lam τp τm c i j :=
      hplus lam c τp τm J i P hlam (le_clusterRadius lam) (le_clusterRadius lam) (hmax _ i)
        (hmax _ i)
        (fun t ht z => (Finset.card_le_card (Finset.filter_subset_filter _ hJS)).trans
          (card_filter_clusterRadius_le hlam ht 8 z S))
        fun j hj => (hA j hj).1
    -- the `-` part, through the exchanged configuration
    have h2 : -(C₀ * P) ≤ ∑ j ∈ J, -halfInteractionMinus χ lam τp τm c i j := by
      have hswap : ∀ j, -halfInteractionMinus χ lam τp τm c i j =
          halfInteractionPlus χ lam τm τp (swapConfig c) i j := fun j => by
        rw [halfInteractionMinus_eq_neg_swap, neg_neg]
      simp only [hswap]
      refine hplus lam (swapConfig c) τm τp J i P hlam (le_clusterRadius lam)
        (le_clusterRadius lam) (by rw [norm_swapConfig]; exact hmax _ i)
        (by rw [norm_swapConfig]; exact hmax _ i)
        (fun t ht z => (Finset.card_le_card (Finset.filter_subset_filter _ hJS)).trans
          (card_filter_clusterRadius_le hlam ht 8 z S))
        fun j hj => ?_
      rw [norm_swapConfig]
      simp only [swapConfig]
      rw [norm_sub_rev (c j).2 (c i).1]
      exact (hA j hj).2
    have : ∑ j ∈ J, ballGrowthInteraction χ lam τp τm c i j =
        ∑ j ∈ J, halfInteractionPlus χ lam τp τm c i j +
          ∑ j ∈ J, -halfInteractionMinus χ lam τp τm c i j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [← halfInteractionPlus_sub_halfInteractionMinus, sub_eq_add_neg]
    rw [this]
    linarith
  have hsum := Finset.sum_le_sum hi
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hB : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  nlinarith

/-- **Lemma 5.12** (Lemma 5.12, the paper, (5.32)): there is `C > 0`
depending only on `χ` and `q(β)` such that for every configuration `c` with `σ_N = Id` and every
`λ > 0`, `Σ_{i<j, i,j ∈ I_bad} v^Z_ij ≥ -C |I_bad|`. -/
theorem lemma_5_12 (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} (lam M ε₀ : ℝ) (c : Fin N → ℂ × ℂ), 0 < lam → stableMatching c = Equiv.refl _ →
      -(C * (badPoints p₀ β lam M ε₀ c).card) ≤
        ∑ i ∈ badPoints p₀ β lam M ε₀ c, ∑ j ∈ badPoints p₀ β lam M ε₀ c with i < j,
          interactionZ χ p₀ β lam M ε₀ c i j := by
  obtain ⟨C, hC, hgen⟩ := sum_lt_ballGrowthInteraction_ge hχ (clusterThreshold p₀ β)
  refine ⟨C, hC, fun lam M ε₀ c hlam hσ => ?_⟩
  have hst := (stableMatching_eq_refl_iff c).mp hσ
  have h := hgen (clusterCutoff p₀ β lam ε₀) lam c (badPoints p₀ β lam M ε₀ c) hlam
    fun i _ j _ hij => hst i j hij
  refine h.trans_eq (Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_)
  have hj' : j ∈ badPoints p₀ β lam M ε₀ c := (Finset.mem_filter.mp hj).1
  rw [interactionZ_eq_ballGrowthInteraction]
  refine ballGrowthInteraction_congr c ?_ ?_ ?_ ?_
  · rw [radiusPlusZ_of_bad hi, clusterRadius, max_comm]
  · rw [radiusPlusZ_of_bad hj', clusterRadius, max_comm]
  · rw [radiusMinusZ_of_bad hi, clusterRadius, max_comm]
  · rw [radiusMinusZ_of_bad hj', clusterRadius, max_comm]

end Lemma

end UpperBound

end MultipoleBKT

end
