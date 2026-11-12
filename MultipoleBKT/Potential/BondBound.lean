/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.DipoleInteraction
public import MultipoleBKT.Matching.Pair

/-!
# The bond bound `v_ij ≥ -C` on `𝒜_ij`

The bound `e^{-β v_ij} 𝟙_{𝒜_ij} ≤ C_β` is used without proof in the proofs of
Proposition 4.23 and Lemma A.5 ("The matching gives `v_ij ≥ -C` on `𝒜_ij`"). Here `χ` is an admissible mollifier, `g_λ = smearedKernel χ λ`,
`λ > 0`, `d = (x_i, y_i)`, `e = (x_j, y_j)`, `v_ij = dipoleInteraction χ λ d e`, and
`c_χ = ∫ g dδ₀^{(1)}`.

**Proof.** Write `m(w) = max(|w|, λ)`.

1. `g_λ(w) = -log m(w) + O(1)`: `g_λ(w) ≥ -log(|w| + 2λ) ≥ -log 3 - log m(w)`, since the two
   smeared charges are supported in discs of radius `λ` (`neg_log_add_le_smearedKernel`); and
   `g_λ(w) ≤ min(g(w), g(λ) + c_χ) ≤ -log m(w) + max(c_χ, 0)` (`smearedKernel_le_neg_log_max`).
2. On `𝒜_ij` (in either label order), both cross distances `A = |x_i - y_j|`, `B = |x_j - y_i|`
   are at least `min(r_i, r_j)` (`isStableDipolePair_iff'`). If they are at least `r_i`, the
   triangle inequality gives `|x_i - x_j| ≤ r_i + B ≤ 2B` and `|y_i - y_j| ≤ r_i + A ≤ 2A`; if
   they are at least `r_j`, then `|x_i - x_j| ≤ A + r_j ≤ 2A` and `|y_i - y_j| ≤ B + r_j ≤ 2B`.
   Either way `m(x_i - x_j) m(y_i - y_j) ≤ 4 m(x_i - y_j) m(x_j - y_i)`
   (`max_mul_max_le_of_min_le`).
3. Hence `v_ij ≥ log(m(x_i - y_j) m(x_j - y_i) / (m(x_i - x_j) m(y_i - y_j))) - 2 log 3 -
   2 max(c_χ, 0) ≥ -(log 36 + 2 max(c_χ, 0))`, uniformly in `λ > 0` and the positions.

Main results:

* `neg_le_dipoleInteraction` (`𝒜_ij`, lower label first) and `neg_le_dipoleInteraction_swap`
  (the other label order): `v_ij ≥ -C` with `C = C(χ) ≥ 0`.
* `dipoleBond_le` : `e^{-β v_ij} 𝟙_{𝒜_ij} ≤ e^{β C}` for `β ≥ 0`, in the form of the Mayer bonds of
  `dipoleActivity`; `abs_dipoleBond_sub_one_le` : `|f_ij^v| ≤ e^{β C}`.
* `multipoleBond_le` : the same for the bonds `e^{-β v_ij} 𝟙_{𝓑_ij^c}` of `multipoleActivity`
  (`𝓑_ij^c ⊆ 𝒜_ij`, Remark 4.6).
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam : ℝ}

/-! ### `g_λ(w) = -log max(|w|, λ) + O(1)` -/

/-- Lower bound `g_λ(w) ≥ -log(|w| + 2λ)`: the two smeared charges are supported in discs of
radius `λ`. -/
theorem neg_log_add_le_smearedKernel (hχ : IsMollifier χ) (hlam : 0 < lam) (w : ℂ) :
    -Real.log (‖w‖ + 2 * lam) ≤ smearedKernel χ lam w := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hlam
  have := isProbabilityMeasure_smearedCharge hχ w hlam
  have hae : ∀ᵐ p ∂(smearedCharge χ 0 lam).prod (smearedCharge χ w lam),
      -Real.log (‖w‖ + 2 * lam) ≤ logKernel (p.1 - p.2) := by
    have h1 : ∀ᵐ p ∂(smearedCharge χ 0 lam).prod (smearedCharge χ w lam),
        p.1 ∈ closedBall (0 : ℂ) lam :=
      Measure.quasiMeasurePreserving_fst.ae (ae_mem_closedBall_smearedCharge hχ hlam)
    have h2 : ∀ᵐ p ∂(smearedCharge χ 0 lam).prod (smearedCharge χ w lam),
        p.2 ∈ closedBall w lam :=
      Measure.quasiMeasurePreserving_snd.ae (ae_mem_closedBall_smearedCharge hχ hlam)
    filter_upwards [h1, h2, ae_prod_smearedCharge_ne χ 0 w lam lam] with p hp1 hp2 hne
    rw [mem_closedBall_zero_iff] at hp1
    rw [mem_closedBall, dist_eq_norm] at hp2
    have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have hle : ‖p.1 - p.2‖ ≤ ‖w‖ + 2 * lam := by
      calc ‖p.1 - p.2‖ = ‖p.1 - (p.2 - w) - w‖ := by congr 1; ring
        _ ≤ ‖p.1‖ + ‖p.2 - w‖ + ‖w‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
        _ ≤ ‖w‖ + 2 * lam := by linarith
    rw [TwoComponentCoulomb.logKernel]
    exact neg_le_neg (Real.log_le_log hpos hle)
  calc -Real.log (‖w‖ + 2 * lam)
      = ∫ _p : ℂ × ℂ, -Real.log (‖w‖ + 2 * lam)
          ∂(smearedCharge χ 0 lam).prod (smearedCharge χ w lam) := by
        rw [integral_const, probReal_univ, one_smul]
    _ ≤ smearedKernel χ lam w :=
        integral_mono_ae (integrable_const _)
          (integrable_logKernel_prod_smearedCharge hχ 0 w lam lam) hae

/-- Lower bound `g_λ(w) ≥ -log 3 - log max(|w|, λ)`. -/
theorem neg_log_three_sub_le_smearedKernel (hχ : IsMollifier χ) (hlam : 0 < lam) (w : ℂ) :
    -Real.log 3 - Real.log (max ‖w‖ lam) ≤ smearedKernel χ lam w := by
  have hm : 0 < max ‖w‖ lam := lt_max_of_lt_right hlam
  have h1 : ‖w‖ + 2 * lam ≤ 3 * max ‖w‖ lam := by
    linarith [le_max_left ‖w‖ lam, le_max_right ‖w‖ lam]
  have h2 : Real.log (‖w‖ + 2 * lam) ≤ Real.log 3 + Real.log (max ‖w‖ lam) := by
    rw [← Real.log_mul (by norm_num) hm.ne']
    exact Real.log_le_log (by positivity) h1
  linarith [neg_log_add_le_smearedKernel hχ hlam w]

/-- Upper bound `g_λ(w) ≤ -log max(|w|, λ) + max(c_χ, 0)`, with `c_χ = ∫ g dδ₀^{(1)}`. -/
theorem smearedKernel_le_neg_log_max (hχ : IsMollifier χ) (hlam : 0 < lam) (w : ℂ) :
    smearedKernel χ lam w ≤
      -Real.log (max ‖w‖ lam) + max (∫ y, logKernel y ∂smearedCharge χ 0 1) 0 := by
  rcases le_total lam ‖w‖ with h | h
  · rw [max_eq_left h]
    have hw : w ≠ 0 := norm_pos_iff.1 (hlam.trans_le h)
    have h1 := smearedKernel_le_logKernel hχ hlam hw
    rw [TwoComponentCoulomb.logKernel] at h1
    linarith [le_max_right (∫ y, logKernel y ∂smearedCharge χ 0 1) 0]
  · rw [max_eq_right h]
    have h1 := smearedKernel_le hχ hlam w
    rw [logKernel_ofReal hlam] at h1
    linarith [le_max_left (∫ y, logKernel y ∂smearedCharge χ 0 1) 0]

/-! ### The geometry of `𝒜_ij` -/

/-- `max(a, λ) ≤ 2 max(b, λ)` when `a ≤ 2 b` and `λ ≥ 0`. -/
theorem max_le_two_mul_max {a b lam : ℝ} (hlam : 0 ≤ lam) (h : a ≤ 2 * b) :
    max a lam ≤ 2 * max b lam :=
  max_le (by linarith [le_max_left b lam]) (by linarith [le_max_right b lam])

/-- If both cross distances `A = |x_i - y_j|`, `B = |x_j - y_i|` are at least `min(r_i, r_j)`,
then `max(|x_i - x_j|, λ) max(|y_i - y_j|, λ) ≤ 4 max(A, λ) max(B, λ)`. -/
theorem max_mul_max_le_of_min_le {d e : ℂ × ℂ} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ min ‖d.1 - e.2‖ ‖e.1 - d.2‖) :
    max ‖d.1 - e.1‖ lam * max ‖d.2 - e.2‖ lam ≤
      4 * (max ‖d.1 - e.2‖ lam * max ‖e.1 - d.2‖ lam) := by
  have hP1 : ‖d.1 - e.1‖ ≤ ‖d.1 - d.2‖ + ‖e.1 - d.2‖ := by
    rw [norm_sub_rev e.1]
    simpa using norm_add_le (d.1 - d.2) (d.2 - e.1)
  have hQ1 : ‖d.2 - e.2‖ ≤ ‖d.1 - d.2‖ + ‖d.1 - e.2‖ := by
    rw [norm_sub_rev d.1 d.2]
    simpa using norm_add_le (d.2 - d.1) (d.1 - e.2)
  have hP2 : ‖d.1 - e.1‖ ≤ ‖d.1 - e.2‖ + ‖e.1 - e.2‖ := by
    rw [norm_sub_rev e.1 e.2]
    simpa using norm_add_le (d.1 - e.2) (e.2 - e.1)
  have hQ2 : ‖d.2 - e.2‖ ≤ ‖e.1 - d.2‖ + ‖e.1 - e.2‖ := by
    rw [norm_sub_rev e.1 d.2]
    simpa using norm_add_le (d.2 - e.1) (e.1 - e.2)
  have hA := le_max_right ‖d.1 - e.2‖ lam
  have hB := le_max_right ‖e.1 - d.2‖ lam
  have hA0 : 0 ≤ max ‖d.1 - e.2‖ lam := hlam.trans hA
  have hB0 : 0 ≤ max ‖e.1 - d.2‖ lam := hlam.trans hB
  rw [min_le_iff, le_min_iff, le_min_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · calc max ‖d.1 - e.1‖ lam * max ‖d.2 - e.2‖ lam
        ≤ (2 * max ‖e.1 - d.2‖ lam) * (2 * max ‖d.1 - e.2‖ lam) :=
          mul_le_mul (max_le_two_mul_max hlam (by linarith))
            (max_le_two_mul_max hlam (by linarith)) (hlam.trans (le_max_right _ _))
            (by positivity)
      _ = 4 * (max ‖d.1 - e.2‖ lam * max ‖e.1 - d.2‖ lam) := by ring
  · calc max ‖d.1 - e.1‖ lam * max ‖d.2 - e.2‖ lam
        ≤ (2 * max ‖d.1 - e.2‖ lam) * (2 * max ‖e.1 - d.2‖ lam) :=
          mul_le_mul (max_le_two_mul_max hlam (by linarith))
            (max_le_two_mul_max hlam (by linarith)) (hlam.trans (le_max_right _ _))
            (by positivity)
      _ = 4 * (max ‖d.1 - e.2‖ lam * max ‖e.1 - d.2‖ lam) := by ring

/-- On `𝒜_ij` (lower label first), both cross distances are at least `min(r_i, r_j)`. -/
theorem min_le_min_of_isStableDipolePair {d e : ℂ × ℂ} (h : IsStableDipolePair d e) :
    min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ min ‖d.1 - e.2‖ ‖e.1 - d.2‖ := by
  rw [isStableDipolePair_iff'] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (min_le_left _ _).trans (le_min h1 h2)
  · exact (min_le_right _ _).trans (le_min h1.le h2.le)

/-- On `𝒜_ji` (the other label order), both cross distances are at least `min(r_i, r_j)`. -/
theorem min_le_min_of_isStableDipolePair_swap {d e : ℂ × ℂ} (h : IsStableDipolePair e d) :
    min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ min ‖d.1 - e.2‖ ‖e.1 - d.2‖ := by
  rw [isStableDipolePair_iff'] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (min_le_right _ _).trans (le_min h2 h1)
  · exact (min_le_left _ _).trans (le_min h2.le h1.le)

/-! ### The bond bound -/

/-- `log 36 = 2 log 3 + log 4`. -/
theorem log_thirtySix : Real.log 36 = 2 * Real.log 3 + Real.log 4 := by
  rw [show (36 : ℝ) = 3 * 3 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- **The bond bound**, explicit form: if both cross distances are at least `min(r_i, r_j)`
(which holds on `𝒜_ij` in either label order), then
`v_ij ≥ -(log 36 + 2 max(c_χ, 0))`, with `c_χ = ∫ g dδ₀^{(1)}`. -/
theorem neg_le_dipoleInteraction_of_min_le (hχ : IsMollifier χ) (hlam : 0 < lam) {d e : ℂ × ℂ}
    (h : min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ min ‖d.1 - e.2‖ ‖e.1 - d.2‖) :
    -(Real.log 36 + 2 * max (∫ y, logKernel y ∂smearedCharge χ 0 1) 0) ≤
      dipoleInteraction χ lam d e := by
  set c := max (∫ y, logKernel y ∂smearedCharge χ 0 1) 0 with hc
  set mP := max ‖d.1 - e.1‖ lam
  set mQ := max ‖d.2 - e.2‖ lam
  set mA := max ‖d.1 - e.2‖ lam
  set mB := max ‖e.1 - d.2‖ lam
  have hmA : 0 < mA := lt_max_of_lt_right hlam
  have hmB : 0 < mB := lt_max_of_lt_right hlam
  have hmP : 0 < mP := lt_max_of_lt_right hlam
  have hmQ : 0 < mQ := lt_max_of_lt_right hlam
  have hgeo := max_mul_max_le_of_min_le hlam.le h
  have hlog : Real.log mP + Real.log mQ ≤ Real.log 4 + (Real.log mA + Real.log mB) := by
    rw [← Real.log_mul hmP.ne' hmQ.ne', ← Real.log_mul hmA.ne' hmB.ne',
      ← Real.log_mul (by norm_num) (mul_pos hmA hmB).ne']
    exact Real.log_le_log (mul_pos hmP hmQ) hgeo
  have hP := neg_log_three_sub_le_smearedKernel hχ hlam (d.1 - e.1)
  have hQ := neg_log_three_sub_le_smearedKernel hχ hlam (d.2 - e.2)
  have hA := smearedKernel_le_neg_log_max hχ hlam (d.1 - e.2)
  have hB := smearedKernel_le_neg_log_max hχ hlam (e.1 - d.2)
  rw [dipoleInteraction, log_thirtySix]
  linarith

/-- **The bond bound** (used without proof in Proposition 4.23 and Lemma A.5): there is `C ≥ 0`
depending only on `χ` such that `v_ij ≥ -C` on `𝒜_ij` (lower label first), for every `λ > 0` and
all positions. -/
theorem neg_le_dipoleInteraction (hχ : IsMollifier χ) : ∃ C, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam →
    ∀ d e : ℂ × ℂ, IsStableDipolePair d e → -C ≤ dipoleInteraction χ lam d e :=
  ⟨_, add_nonneg (Real.log_nonneg (by norm_num)) (mul_nonneg (by norm_num) (le_max_right _ _)),
    fun _ hlam _ _ h =>
      neg_le_dipoleInteraction_of_min_le hχ hlam (min_le_min_of_isStableDipolePair h)⟩

/-- **The bond bound** in the other label order: `v_ij ≥ -C` when
`IsStableDipolePair (x_j, y_j) (x_i, y_i)`, with the same constant. -/
theorem neg_le_dipoleInteraction_swap (hχ : IsMollifier χ) : ∃ C, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam →
    ∀ d e : ℂ × ℂ, IsStableDipolePair e d → -C ≤ dipoleInteraction χ lam d e :=
  ⟨_, add_nonneg (Real.log_nonneg (by norm_num)) (mul_nonneg (by norm_num) (le_max_right _ _)),
    fun _ hlam _ _ h =>
      neg_le_dipoleInteraction_of_min_le hχ hlam (min_le_min_of_isStableDipolePair_swap h)⟩

open scoped Classical in
/-- **`e^{-β v_ij} 𝟙_{𝒜_ij} ≤ e^{β C}`** (the proof of Proposition 4.23), in the form of the bonds of
`dipoleActivity`: there is `C ≥ 0` depending only on `χ` such that for every `β ≥ 0`, `λ > 0`
and all dipoles, `(if 𝒜_ij then e^{-β v_ij} else 0) ≤ e^{β C}`. -/
theorem dipoleBond_le (hχ : IsMollifier χ) : ∃ C, 0 ≤ C ∧ ∀ β : ℝ, 0 ≤ β → ∀ lam : ℝ, 0 < lam →
    ∀ d e : ℂ × ℂ,
      (if IsStableDipolePair d e then Real.exp (-β * dipoleInteraction χ lam d e) else 0) ≤
        Real.exp (β * C) := by
  obtain ⟨C, hC0, hC⟩ := neg_le_dipoleInteraction hχ
  refine ⟨C, hC0, fun β hβ lam hlam d e => ?_⟩
  split_ifs with h
  · refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (hC lam hlam d e h) hβ
    linarith
  · exact (Real.exp_pos _).le

open scoped Classical in
/-- The Mayer bond `f_ij^v = e^{-β v_ij} 𝟙_{𝒜_ij} - 1` of `dipoleActivity` satisfies
`|f_ij^v| ≤ e^{β C}`, with `C ≥ 0` depending only on `χ`, for every `β ≥ 0` and `λ > 0`. -/
theorem abs_dipoleBond_sub_one_le (hχ : IsMollifier χ) : ∃ C, 0 ≤ C ∧ ∀ β : ℝ, 0 ≤ β →
    ∀ lam : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      |(if IsStableDipolePair d e then Real.exp (-β * dipoleInteraction χ lam d e) else 0) - 1| ≤
        Real.exp (β * C) := by
  obtain ⟨C, hC0, hC⟩ := dipoleBond_le hχ
  refine ⟨C, hC0, fun β hβ lam hlam d e => ?_⟩
  have h1 := hC β hβ lam hlam d e
  have h0 : 0 ≤ if IsStableDipolePair d e then Real.exp (-β * dipoleInteraction χ lam d e)
      else 0 := by
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have h2 : 1 ≤ Real.exp (β * C) := Real.one_le_exp (mul_nonneg hβ hC0)
  rw [abs_le]
  constructor <;> linarith

open scoped Classical in
/-- The bonds `e^{-β v_ij} 𝟙_{𝓑_ij^c}` of `multipoleActivity` (with `M ≥ 1`) are at most
`e^{β C}`, since `𝓑_ij^c ⊆ 𝒜_ij` (Remark 4.6). -/
theorem multipoleBond_le (hχ : IsMollifier χ) : ∃ C, 0 ≤ C ∧ ∀ β : ℝ, 0 ≤ β → ∀ M : ℝ, 1 ≤ M →
    ∀ lam : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      (if MultipoleLinked M lam d e then 0 else Real.exp (-β * dipoleInteraction χ lam d e)) ≤
        Real.exp (β * C) := by
  obtain ⟨C, hC0, hC⟩ := dipoleBond_le hχ
  refine ⟨C, hC0, fun β hβ M hM lam hlam d e => ?_⟩
  split_ifs with h
  · exact (Real.exp_pos _).le
  · have := hC β hβ lam hlam d e
    simpa only [remark_4_6 hM h, ite_true] using this

end MultipoleBKT

end
