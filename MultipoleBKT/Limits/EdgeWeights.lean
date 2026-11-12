/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Kernels

/-!
# The inter-block bonds and their bounds

See the proof of Lemma A.5:
the bond `e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1` of `𝖪^mult` is split by the reversals into an even part
`a^v_ij` and an odd part `b^v_ij`, with `|odd| ≤ C â_ij` and `|even| ≤ C (â_ij² + 𝟙_{𝓑_ij})`,
`â_ij = r_i r_j / (d_ij max(d_ij, r_i, r_j))` (Lemma 3.7).

* `unlinkedBond_flip`: after reversing the dipoles `d`, `e` according to `a`, `b`, the bond is
  `α + σ γ` with `σ = ±1` (`-1` iff exactly one is reversed), `α = -1, γ = 0` on `𝓑_ij` and
  `α = cosh(β v) - 1`, `γ = -sinh(β v)` on `𝓑_ij^c`;
* `exists_bond_bounds`: on `𝓑_ij^c` (`M ≥ 1`), `|γ| ≤ C â`, `|α| ≤ C â²`, `â ≤ 1` and
  `d_ij > λ`;
* the normalized near and odd weights `nearW`, `oddW` (functions of the dipole distance,
  nonincreasing) whose integrals in the relative position are bounded by constants
  (`lintegral_nearW_le`, `lintegral_oddW_le`).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset
open scoped ENNReal

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Elementary bounds for `exp`, `sinh`, `cosh` -/

theorem abs_exp_sub_one_le_mul_exp (y : ℝ) : |Real.exp y - 1| ≤ |y| * Real.exp |y| := by
  rcases le_total 0 y with hy | hy
  · have h1 : 0 ≤ Real.exp y - 1 := by linarith [Real.add_one_le_exp y]
    rw [abs_of_nonneg h1, abs_of_nonneg hy]
    have h2 := Real.add_one_le_exp (-y)
    have h3 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos y]
  · have h1 : Real.exp y - 1 ≤ 0 := by
      have := Real.exp_le_exp.2 hy
      rw [Real.exp_zero] at this
      linarith
    rw [abs_of_nonpos h1, abs_of_nonpos hy]
    have h2 := Real.add_one_le_exp y
    have h3 : 1 ≤ Real.exp (-y) := Real.one_le_exp (by linarith)
    nlinarith

theorem abs_sinh_le (y : ℝ) : |Real.sinh y| ≤ |y| * Real.exp |y| := by
  rw [Real.sinh_eq]
  have h1 := abs_exp_sub_one_le_mul_exp y
  have h2 := abs_exp_sub_one_le_mul_exp (-y)
  rw [abs_neg] at h2
  have : (Real.exp y - Real.exp (-y)) / 2 = ((Real.exp y - 1) - (Real.exp (-y) - 1)) / 2 := by ring
  rw [this, abs_div, abs_two]
  have := abs_sub (Real.exp y - 1) (Real.exp (-y) - 1)
  linarith

theorem cosh_sub_one_le (y : ℝ) : Real.cosh y - 1 ≤ y ^ 2 * Real.exp |y| := by
  have h := Real.cosh_two_mul (y / 2)
  rw [show 2 * (y / 2) = y by ring, Real.cosh_sq] at h
  have hs := abs_sinh_le (y / 2)
  have hy2 : |y / 2| ≤ |y| := by rw [abs_div, abs_two]; linarith [abs_nonneg y]
  have he : Real.exp |y / 2| ≤ Real.exp |y| := Real.exp_le_exp.2 hy2
  have hs2 : Real.sinh (y / 2) ^ 2 ≤ (|y / 2| * Real.exp |y / 2|) ^ 2 := by
    rw [← sq_abs (Real.sinh _)]
    exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  have h3 : (|y / 2| * Real.exp |y / 2|) ^ 2 ≤ y ^ 2 / 4 * Real.exp |y| := by
    rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * |y / 2| = |y| := by rw [abs_div, abs_two]; push_cast; ring
    rw [this]
    ring_nf
    rfl
  have h4 : 0 ≤ y ^ 2 * Real.exp |y| := by positivity
  nlinarith

/-! ### The bond after reversals -/

/-- The radius `ρ = max(|x - y|, λ)` of a dipole. -/
noncomputable def rhoD (lam : ℝ) (d : ℂ × ℂ) : ℝ := max ‖d.1 - d.2‖ lam

theorem rhoD_swap (lam : ℝ) (d : ℂ × ℂ) : rhoD lam d.swap = rhoD lam d := by
  unfold rhoD
  rw [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]

/-- `â = r_i r_j / (d_ij max(d_ij, r_i, r_j))`. -/
noncomputable def ahat (d e : ℂ × ℂ) : ℝ :=
  ‖d.1 - d.2‖ * ‖e.1 - e.2‖ /
    (dipoleDist d e * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖))

open scoped Classical in
/-- The even part of the reversed bond: `-1` on `𝓑_ij`, `cosh(β v_ij) - 1` on `𝓑_ij^c`. -/
noncomputable def edgeAlpha (χ : ℂ → ℝ) (β lam M : ℝ) (d e : ℂ × ℂ) : ℝ :=
  if MultipoleLinked M lam d e then -1 else Real.cosh (β * dipoleInteraction χ lam d e) - 1

open scoped Classical in
/-- The odd part of the reversed bond: `0` on `𝓑_ij`, `-sinh(β v_ij)` on `𝓑_ij^c`. -/
noncomputable def edgeGamma (χ : ℂ → ℝ) (β lam M : ℝ) (d e : ℂ × ℂ) : ℝ :=
  if MultipoleLinked M lam d e then 0 else -Real.sinh (β * dipoleInteraction χ lam d e)

/-- **The reversed bond.** Reversing `d` if `a` and `e` if `b`, the bond
`e^{-β v} 𝟙_{𝓑^c} - 1` becomes `α + σ γ` with `σ = 1` if `a ↔ b` and `σ = -1` otherwise. -/
theorem unlinkedBond_flip (hχ : IsMollifier χ) (d e : ℂ × ℂ) (a b : Prop) [Decidable a]
    [Decidable b] :
    unlinkedPairWeight χ β lam M (if a then d.swap else d) (if b then e.swap else e) - 1 =
      edgeAlpha χ β lam M d e + (if (a ↔ b) then 1 else -1) * edgeGamma χ β lam M d e := by
  have hML : MultipoleLinked M lam (if a then d.swap else d) (if b then e.swap else e) ↔
      MultipoleLinked M lam d e := by
    split_ifs
    · rw [multipoleLinked_swap_left, multipoleLinked_swap_right]
    · rw [multipoleLinked_swap_left]
    · rw [multipoleLinked_swap_right]
    · rfl
  have hv : dipoleInteraction χ lam (if a then d.swap else d) (if b then e.swap else e) =
      (if (a ↔ b) then 1 else -1) * dipoleInteraction χ lam d e := by
    by_cases ha : a <;> by_cases hb : b <;>
      simp [ha, hb, dipoleInteraction_swap_swap _ _ hχ, dipoleInteraction_swap_left _ _ hχ,
        dipoleInteraction_swap_right _ _ hχ]
  unfold unlinkedPairWeight edgeAlpha edgeGamma
  by_cases hl : MultipoleLinked M lam d e
  · rw [ite_eq_left (hML.2 hl), ite_eq_left hl, ite_eq_left hl]
    ring
  · rw [ite_eq_right (mt hML.1 hl), ite_eq_right hl, ite_eq_right hl, hv]
    by_cases hab : (a ↔ b)
    · rw [ite_eq_left hab, one_mul, neg_mul, ← Real.cosh_sub_sinh]
      ring
    · rw [ite_eq_right hab, show -β * (-1 * dipoleInteraction χ lam d e) =
        β * dipoleInteraction χ lam d e by ring, ← Real.cosh_add_sinh]
      ring

/-! ### Bounds on `𝓑_ij^c` -/

theorem ahat_nonneg (d e : ℂ × ℂ) : 0 ≤ ahat d e := by
  unfold ahat
  have h1 : 0 ≤ dipoleDist d e := le_min (le_min (norm_nonneg _) (norm_nonneg _))
    (le_min (norm_nonneg _) (norm_nonneg _))
  positivity

/-- Monotonicity of `r_i r_j / (D max(D, r_i, r_j))` in the radii. -/
theorem div_mul_max_le {r₁ r₂ s₁ s₂ D : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (hr₁ : r₁ ≤ s₁)
    (hr₂ : r₂ ≤ s₂) (hD : 0 < D) :
    r₁ * r₂ / (D * max D (max r₁ r₂)) ≤ s₁ * s₂ / (D * max D (max s₁ s₂)) := by
  have hs₁ : 0 ≤ s₁ := h₁.trans hr₁
  have hs₂ : 0 ≤ s₂ := h₂.trans hr₂
  have hm : 0 < max D (max r₁ r₂) := lt_max_of_lt_left hD
  have hm' : 0 < max D (max s₁ s₂) := lt_max_of_lt_left hD
  rw [div_le_div_iff₀ (mul_pos hD hm) (mul_pos hD hm')]
  have key : r₁ * r₂ * max D (max s₁ s₂) ≤ s₁ * s₂ * max D (max r₁ r₂) := by
    rw [mul_max_of_nonneg _ _ (mul_nonneg h₁ h₂), mul_max_of_nonneg _ _ (mul_nonneg h₁ h₂)]
    refine max_le ?_ (max_le ?_ ?_)
    · calc r₁ * r₂ * D ≤ s₁ * s₂ * D := by gcongr
        _ ≤ s₁ * s₂ * max D (max r₁ r₂) := by gcongr; exact le_max_left _ _
    · calc r₁ * r₂ * s₁ = s₁ * (r₂ * r₁) := by ring
        _ ≤ s₁ * (s₂ * r₁) := by gcongr
        _ ≤ s₁ * s₂ * max D (max r₁ r₂) := by
            rw [← mul_assoc]; gcongr
            exact (le_max_left _ _).trans (le_max_right _ _)
    · calc r₁ * r₂ * s₂ = s₂ * (r₁ * r₂) := by ring
        _ ≤ s₂ * (s₁ * r₂) := by gcongr
        _ ≤ s₁ * s₂ * max D (max r₁ r₂) := by
            rw [show s₂ * (s₁ * r₂) = s₁ * s₂ * r₂ by ring]; gcongr
            exact (le_max_right _ _).trans (le_max_right _ _)
  nlinarith

/-- **The bond bounds** (Lemma 3.7 (2) and the expansion of `cosh`, `sinh`): there is `C ≥ 0`
depending on `χ` and `β` such that, for `λ > 0`, `M ≥ 1` and dipoles with `¬ (i ↔ j)`,
`λ < d_ij`, `â ≤ 1`, `|γ| ≤ C â` and `|α| ≤ C â²`. -/
theorem exists_bond_bounds (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ C, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ M : ℝ, 1 ≤ M → ∀ d e : ℂ × ℂ,
      ¬ MultipoleLinked M lam d e → lam < dipoleDist d e ∧ ahat d e ≤ 1 ∧
        |edgeGamma χ β lam M d e| ≤ C * ahat d e ∧ |edgeAlpha χ β lam M d e| ≤ C * ahat d e ^ 2 := by
  obtain ⟨Cv, hCv0, hCv⟩ := abs_dipoleInteraction_le hχ
  set K := β * Cv
  have hK : 0 ≤ K := mul_nonneg hβ hCv0.le
  refine ⟨max (K * Real.exp K) (K ^ 2 * Real.exp K), by positivity,
    fun lam hlam M hM d e hnl => ?_⟩
  set dd := dipoleDist d e
  set r₁ := ‖d.1 - d.2‖
  set r₂ := ‖e.1 - e.2‖
  have hnl' : M * min (max r₁ lam) (max r₂ lam) < dd := by
    rw [MultipoleLinked, not_le] at hnl
    exact hnl
  have hmin : min (max r₁ lam) (max r₂ lam) ≤ M * min (max r₁ lam) (max r₂ lam) :=
    le_mul_of_one_le_left (le_min (le_max_of_le_right hlam.le) (le_max_of_le_right hlam.le)) hM
  have hlamd : lam < dd :=
    lt_of_le_of_lt ((le_min (le_max_right _ _) (le_max_right _ _)).trans hmin) hnl'
  have hdd : 0 < dd := hlam.trans hlamd
  have hrmin : min r₁ r₂ ≤ dd :=
    ((min_le_min (le_max_left _ _) (le_max_left _ _)).trans hmin).trans hnl'.le
  -- `â ≤ min r / d < 1`
  have hahat1 : ahat d e ≤ 1 := by
    unfold ahat
    rw [div_le_one (mul_pos hdd (lt_max_of_lt_left hdd))]
    rcases le_total r₁ r₂ with h | h
    · calc r₁ * r₂ ≤ dd * r₂ := by
            gcongr
            exact (min_eq_left h ▸ hrmin)
        _ ≤ dd * max dd (max r₁ r₂) := by
            gcongr; exact (le_max_right _ _).trans (le_max_right _ _)
    · calc r₁ * r₂ ≤ r₁ * dd := by
            gcongr
            exact (min_eq_right h ▸ hrmin)
        _ = dd * r₁ := by ring
        _ ≤ dd * max dd (max r₁ r₂) := by
            gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
  have ha0 := ahat_nonneg d e
  -- `|v| ≤ C_v â`
  have hv : |dipoleInteraction χ lam d e| ≤ Cv * ahat d e := by
    have := hCv lam hlam d e hrmin
    rw [max_eq_left hlamd.le] at this
    unfold ahat
    rwa [mul_div_assoc] at this
  have hy : |β * dipoleInteraction χ lam d e| ≤ K * ahat d e := by
    rw [abs_mul, abs_of_nonneg hβ, mul_assoc]
    exact mul_le_mul_of_nonneg_left hv hβ
  have hyK : |β * dipoleInteraction χ lam d e| ≤ K :=
    hy.trans (by nlinarith)
  have hexp : Real.exp |β * dipoleInteraction χ lam d e| ≤ Real.exp K := Real.exp_le_exp.2 hyK
  refine ⟨hlamd, hahat1, ?_, ?_⟩
  · unfold edgeGamma
    rw [ite_eq_right hnl, abs_neg]
    calc |Real.sinh (β * dipoleInteraction χ lam d e)|
        ≤ |β * dipoleInteraction χ lam d e| * Real.exp |β * dipoleInteraction χ lam d e| :=
          abs_sinh_le _
      _ ≤ (K * ahat d e) * Real.exp K := by gcongr
      _ = K * Real.exp K * ahat d e := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · unfold edgeAlpha
    rw [ite_eq_right hnl]
    have hc : 0 ≤ Real.cosh (β * dipoleInteraction χ lam d e) - 1 := by
      have h1 := Real.cosh_pos (β * dipoleInteraction χ lam d e)
      have h2 := Real.cosh_sq (β * dipoleInteraction χ lam d e)
      nlinarith [sq_nonneg (Real.sinh (β * dipoleInteraction χ lam d e))]
    rw [abs_of_nonneg hc]
    calc Real.cosh (β * dipoleInteraction χ lam d e) - 1
        ≤ (β * dipoleInteraction χ lam d e) ^ 2 * Real.exp |β * dipoleInteraction χ lam d e| :=
          cosh_sub_one_le _
      _ ≤ (K * ahat d e) ^ 2 * Real.exp K := by
          have hsq : (β * dipoleInteraction χ lam d e) ^ 2 ≤ (K * ahat d e) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hy 2
          exact mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg _)
      _ = K ^ 2 * Real.exp K * ahat d e ^ 2 := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- On `𝓑_ij` with radii `s ≥ ρ`: `1 ≤ M⁴ min(1, s_v s_w / (D max(D, s_v, s_w)))²` for
`D = max(d_ij, λ)`. -/
theorem one_le_of_multipoleLinked {lam : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M) {d e : ℂ × ℂ}
    (h : MultipoleLinked M lam d e) {sv sw : ℝ} (hsv : rhoD lam d ≤ sv)
    (hsw : rhoD lam e ≤ sw) :
    1 ≤ M ^ 4 * min 1 (sv * sw / (max (dipoleDist d e) lam *
      max (max (dipoleDist d e) lam) (max sv sw))) ^ 2 := by
  have hρv : lam ≤ rhoD lam d := le_max_right _ _
  have hρw : lam ≤ rhoD lam e := le_max_right _ _
  have hsv0 : 0 < sv := hlam.trans_le (hρv.trans hsv)
  have hsw0 : 0 < sw := hlam.trans_le (hρw.trans hsw)
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  set m := min sv sw
  set Mx := max sv sw
  have hm0 : 0 < m := lt_min hsv0 hsw0
  have hmMx : m ≤ Mx := min_le_max
  have hprod : sv * sw = m * Mx := (min_mul_max sv sw).symm
  set D := max (dipoleDist d e) lam
  have hdd : dipoleDist d e ≤ M * m := by
    have := h
    unfold MultipoleLinked at this
    refine this.trans ?_
    gcongr
    exact min_le_min hsv hsw
  have hD : D ≤ M * m := max_le hdd
    ((le_min (hρv.trans hsv) (hρw.trans hsw)).trans (le_mul_of_one_le_left hm0.le hM))
  have hD0 : 0 < D := lt_max_of_lt_right hlam
  have hmax : max D Mx ≤ M * Mx := max_le (hD.trans (by gcongr)) (le_mul_of_one_le_left (by
    linarith) hM)
  have hA : 1 / M ^ 2 ≤ sv * sw / (D * max D Mx) := by
    rw [hprod, div_le_div_iff₀ (by positivity) (mul_pos hD0 (lt_max_of_lt_left hD0))]
    calc 1 * (D * max D Mx) ≤ (M * m) * (M * Mx) := by
          rw [one_mul]
          exact mul_le_mul hD hmax (le_max_of_le_left hD0.le) (by positivity)
      _ = m * Mx * M ^ 2 := by ring
  have hmin : 1 / M ^ 2 ≤ min 1 (sv * sw / (D * max D Mx)) :=
    le_min (by rw [div_le_one (by positivity)]; nlinarith) hA
  have h2 : (1 / M ^ 2) ^ 2 ≤ min 1 (sv * sw / (D * max D Mx)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hmin 2
  calc (1 : ℝ) = M ^ 4 * (1 / M ^ 2) ^ 2 := by field_simp
    _ ≤ _ := by gcongr

/-! ### Normalized edge weights -/

/-- The near weight `𝟙_{i ↔ j} / min(ρᵢ, ρⱼ)²`. -/
noncomputable def nearW (M lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  (if dipoleDist d e ≤ M * min (rhoD lam d) (rhoD lam e) then 1 else 0) /
    min (rhoD lam d) (rhoD lam e) ^ 2

/-- The odd weight `R^{-δ} max(d, λ)^{δ-2} min(1, R / max(d, λ))^{2θ}`. -/
noncomputable def oddW (lam δ θ R : ℝ) (d e : ℂ × ℂ) : ℝ :=
  R ^ (-δ) * max (dipoleDist d e) lam ^ (δ - 2) * min 1 (R / max (dipoleDist d e) lam) ^ (2 * θ)

theorem nearW_nonneg (M lam : ℝ) (d e : ℂ × ℂ) : 0 ≤ nearW M lam d e := by
  unfold nearW; split_ifs <;> positivity

theorem oddW_nonneg {lam : ℝ} (hlam : 0 < lam) (δ θ : ℝ) {R : ℝ} (hR : 0 ≤ R) (d e : ℂ × ℂ) :
    0 ≤ oddW lam δ θ R d e := by
  unfold oddW
  have : (0 : ℝ) < max (dipoleDist d e) lam := lt_max_of_lt_right hlam
  have : 0 ≤ min 1 (R / max (dipoleDist d e) lam) := le_min zero_le_one (by positivity)
  positivity

theorem rhoD_mk (lam : ℝ) (t u : ℂ) : rhoD lam (t, t + u) = rho lam u := by
  unfold rhoD rho
  simp

/-- **The near weight integrates to at most `4π M²`.** -/
theorem lintegral_nearW_le (hlam : 0 < lam) (hM : 0 ≤ M) (u v y : ℂ) :
    ∫⁻ t : ℂ, ENNReal.ofReal (nearW M lam (t, t + u) (y, y + v)) ≤
      ENNReal.ofReal (4 * Real.pi * M ^ 2) := by
  set s := min (rho lam u) (rho lam v)
  have hs : 0 < s := lt_min (rho_pos hlam u) (rho_pos hlam v)
  have hpt : ∀ t : ℂ, ENNReal.ofReal (nearW M lam (t, t + u) (y, y + v)) =
      ENNReal.ofReal (s ^ 2)⁻¹ * (Iic (M * s)).indicator 1 (dipoleDist (t, t + u) (y, y + v)) := by
    intro t
    unfold nearW
    rw [rhoD_mk, rhoD_mk]
    by_cases h : dipoleDist (t, t + u) (y, y + v) ≤ M * s
    · rw [ite_eq_left h, indicator_of_mem (show _ ∈ Iic (M * s) from h), Pi.one_apply, mul_one,
        one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
    · rw [ite_eq_right h, indicator_of_notMem (show _ ∉ Iic (M * s) from h), mul_zero, zero_div,
        ENNReal.ofReal_zero]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hanti : Antitone ((Iic (M * s)).indicator (1 : ℝ → ℝ≥0∞)) := by
    intro a b hab
    by_cases hb : b ≤ M * s
    · rw [indicator_of_mem (show b ∈ Iic (M * s) from hb),
        indicator_of_mem (show a ∈ Iic (M * s) from hab.trans hb)]
      exact le_rfl
    · rw [indicator_of_notMem (show b ∉ Iic (M * s) from hb)]
      exact bot_le
  have hint := lintegral_antitone_dipoleDist_le hanti
    (measurable_one.indicator measurableSet_Iic) u (y, y + v)
  rw [lintegral_indicator_norm_le] at hint
  calc ENNReal.ofReal (s ^ 2)⁻¹ * ∫⁻ t, (Iic (M * s)).indicator 1 (dipoleDist (t, t + u) (y, y + v))
      ≤ ENNReal.ofReal (s ^ 2)⁻¹ * (4 * (ENNReal.ofReal (M * s) ^ 2 * NNReal.pi)) := by gcongr
    _ = ENNReal.ofReal (4 * Real.pi * M ^ 2) := by
        rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_pow
          (mul_nonneg hM hs.le), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- **The odd weight integrates to at most `8π (1/δ + 1/(2θ - δ))`.** -/
theorem lintegral_oddW_le {δ θ R : ℝ} (hδ : 0 < δ) (hδθ : δ < 2 * θ)
    (hδ2 : δ < 2) (hR : 0 < R) (u v y : ℂ) :
    ∫⁻ t : ℂ, ENNReal.ofReal (oddW lam δ θ R (t, t + u) (y, y + v)) ≤
      ENNReal.ofReal (8 * Real.pi * (1 / δ + 1 / (2 * θ - δ))) := by
  have hθ : 0 ≤ 2 * θ := by linarith
  have hpt : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal (R ^ (-δ) * max t lam ^ (δ - 2) *
      min 1 (R / max t lam) ^ (2 * θ)) ≤ ENNReal.ofReal (R ^ (-δ)) * kern δ (2 * θ) R t := by
    intro t ht
    rcases ht.eq_or_lt with rfl | ht
    · have hk : kern δ (2 * θ) R 0 = ⊤ := by
        unfold kern
        rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
          ENNReal.div_zero (ENNReal.ofReal_pos.2 hR).ne', min_eq_left le_top, ENNReal.one_rpow,
          mul_one]
      rw [hk, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hR _)).ne']
      exact le_top
    rw [kern_of_pos ht hR.le hθ, ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hR.le _)
    have hmt : t ≤ max t lam := le_max_left _ _
    refine mul_le_mul (Real.rpow_le_rpow_of_nonpos ht hmt (by linarith)) ?_
      (Real.rpow_nonneg (le_min zero_le_one (div_nonneg hR.le (ht.trans_le hmt).le)) _)
      (Real.rpow_nonneg ht.le _)
    exact Real.rpow_le_rpow (le_min zero_le_one (div_nonneg hR.le (ht.trans_le hmt).le))
      (min_le_min le_rfl (div_le_div_of_nonneg_left hR.le ht hmt)) hθ
  have hanti : Antitone (fun t => ENNReal.ofReal (R ^ (-δ)) * kern δ (2 * θ) R t) :=
    fun a b hab => by
      simp only
      gcongr
      exact kern_antitone hδ2.le hθ hab
  calc ∫⁻ t : ℂ, ENNReal.ofReal (oddW lam δ θ R (t, t + u) (y, y + v))
      ≤ ∫⁻ t : ℂ, ENNReal.ofReal (R ^ (-δ)) * kern δ (2 * θ) R (dipoleDist (t, t + u) (y, y + v)) :=
        lintegral_mono fun t => hpt _ (le_min (le_min (norm_nonneg _) (norm_nonneg _))
          (le_min (norm_nonneg _) (norm_nonneg _)))
    _ ≤ 4 * ∫⁻ z : ℂ, ENNReal.ofReal (R ^ (-δ)) * kern δ (2 * θ) R ‖z‖ :=
        lintegral_antitone_dipoleDist_le hanti
          ((measurable_kern δ (2 * θ) R).const_mul _) u (y, y + v)
    _ = 4 * (ENNReal.ofReal (R ^ (-δ)) * ∫⁻ z : ℂ, kern δ (2 * θ) R ‖z‖) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ 4 * (ENNReal.ofReal (R ^ (-δ)) *
          ENNReal.ofReal (2 * Real.pi * (R ^ δ * (1 / δ + 1 / (2 * θ - δ))))) := by
        gcongr
        exact lintegral_kern_le hδ hδθ hR
    _ = ENNReal.ofReal (8 * Real.pi * (1 / δ + 1 / (2 * θ - δ))) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _), ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        have : R ^ (-δ) * R ^ δ = 1 := by
          rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
        have h2 : 0 ≤ 1 / δ + 1 / (2 * θ - δ) := by
          have : 0 < 2 * θ - δ := by linarith
          positivity
        calc 4 * (R ^ (-δ) * (2 * Real.pi * (R ^ δ * (1 / δ + 1 / (2 * θ - δ)))))
            = 8 * Real.pi * (1 / δ + 1 / (2 * θ - δ)) * (R ^ (-δ) * R ^ δ) := by ring
          _ = _ := by rw [this, mul_one]

/-- The odd-edge factor of `odd_bound` at `D = max(d, λ)`: `ω(D) ≤ (R/λ)^δ W_odd`. -/
theorem oddWeight_le_oddW {lam : ℝ} (hlam : 0 < lam) {δ θ R : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (d e : ℂ × ℂ) :
    oddWeight R θ (max (dipoleDist d e) lam) ≤ (R / lam) ^ δ * oddW lam δ θ R d e := by
  set t := max (dipoleDist d e) lam
  have ht : lam ≤ t := le_max_right _ _
  have ht0 : 0 < t := hlam.trans_le ht
  unfold oddWeight oddW
  rw [← Real.rpow_two, ← Real.rpow_neg ht0.le, Real.div_rpow hR.le hlam.le]
  have hm : 0 ≤ min 1 (R / t) ^ (2 * θ) :=
    Real.rpow_nonneg (le_min zero_le_one (div_nonneg hR.le ht0.le)) _
  have key : t ^ (-(2 : ℝ)) ≤ lam ^ (-δ) * t ^ (δ - 2) := by
    rw [show t ^ (-(2 : ℝ)) = t ^ (-δ) * t ^ (δ - 2) by
      rw [← Real.rpow_add ht0]; ring_nf]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hlam ht (by linarith))
      (Real.rpow_nonneg ht0.le _)
  calc t ^ (-(2 : ℝ)) * min 1 (R / t) ^ (2 * θ)
      ≤ lam ^ (-δ) * t ^ (δ - 2) * min 1 (R / t) ^ (2 * θ) := by gcongr
    _ = R ^ δ / lam ^ δ * (R ^ (-δ) * t ^ (δ - 2) * min 1 (R / t) ^ (2 * θ)) := by
        rw [Real.rpow_neg hlam.le, Real.rpow_neg hR.le]
        field_simp

end Limits

end MultipoleBKT

end
