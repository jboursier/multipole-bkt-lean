/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.Radial
public import MultipoleBKT.Appendix.GeneralExpansion.TreeRoot
import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.TailMoments
import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Polar
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Configurations with a dipole beyond the cutoff

See Step 3 of
the proof of Lemma A.6, (A.46) and (A.47).
Split by a largest radius, integrate the tree positions and the inner radii,
and retain the literal nested radial integral. `ordered_tail_lt_four`,
`ordered_tail_four` and `ordered_tail_gt_four` give the three displayed
bounds. The exponents `tailSigma` and `tailExp` occur only after these
integrations, when comparing with the consumed normalization.
-/

@[expose] public section

namespace MultipoleBKT

namespace GeneralExpansion

open MeasureTheory Set Finset Function
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral

variable {M lam : ℝ}

section Tail

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight `4π M² max(|w|, λ)²` of a near edge (the area of `linkSet`). -/
noncomputable def edgeWeight (M lam : ℝ) (w : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2)

theorem measurable_edgeWeight (M lam : ℝ) : Measurable (edgeWeight M lam) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

/-- The indicator `𝟙_{|s| ≤ |t|}`. -/
noncomputable def normLe (s t : ℂ) : ℝ≥0∞ :=
  {p : ℂ × ℂ | ‖p.1‖ ≤ ‖p.2‖}.indicator 1 (s, t)

theorem measurable_normLe : Measurable (uncurry normLe) := by
  have : MeasurableSet {p : ℂ × ℂ | ‖p.1‖ ≤ ‖p.2‖} := measurableSet_le (by fun_prop) (by fun_prop)
  exact measurable_const.indicator this

theorem normLe_of_le {s t : ℂ} (h : ‖s‖ ≤ ‖t‖) : normLe s t = 1 := by
  unfold normLe
  rw [indicator_of_mem (show (s, t) ∈ {p : ℂ × ℂ | ‖p.1‖ ≤ ‖p.2‖} from h)]
  rfl


/-- **The tree/star reduction of Step 3**: for measurable radial weights `H`,
`∫_{(Λ²)^ι} 𝟙_{𝓑} ∏_i H(r_i) 𝟙_{|r_{i₀}| > h} ≤ k · k^k N ∫ 𝟙_{|t| > h} H(t)
(∫ H(s) 4πM² max(|s|, λ)² 𝟙_{|s| ≤ |t|} ds)^{k-1} dt`. -/
theorem lintegral_tail_le (hM : 0 ≤ M) (hlam : 0 ≤ lam) (N : ℕ) (i₀ : ι) (H : ℂ → ℝ≥0∞)
    (hH : Measurable H) (h : ℝ) :
    ∫⁻ c : ι → ℂ × ℂ, (Set.univ.pi fun _ : ι => box N ×ˢ box N).indicator
        (fun c => connInd M lam c * ∏ i, H ((c i).1 - (c i).2)) c *
        {u : ℂ | h < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2) ≤
      (Fintype.card ι : ℝ≥0∞) * (((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞) * N) *
        ∫⁻ t, {u : ℂ | h < ‖u‖}.indicator 1 t * H t *
          (∫⁻ s, H s * edgeWeight M lam s * normLe s t) ^ (Fintype.card ι - 1) := by
  classical
  set K : ℝ≥0∞ := ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞)
  set P : Set (ι → ℂ × ℂ) := Set.univ.pi fun _ : ι => box N ×ˢ box N
  set T : Set ℂ := {u : ℂ | h < ‖u‖}
  have hT : MeasurableSet T := measurableSet_lt measurable_const measurable_norm
  have hHr : ∀ i, Measurable fun c : ι → ℂ × ℂ => H ((c i).1 - (c i).2) := fun i =>
    hH.comp ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd)
  -- the term of the root `j₀`
  set F : ι → (ι → ℂ × ℂ) → ℝ≥0∞ := fun j₀ c =>
    (box N).indicator 1 (c j₀).2 * connInd M lam c * (∏ i, H ((c i).1 - (c i).2)) *
      (T.indicator 1 ((c j₀).1 - (c j₀).2) *
        ∏ c' ∈ univ.erase j₀, normLe ((c c').1 - (c c').2) ((c j₀).1 - (c j₀).2))
  have hFm : ∀ j₀, Measurable (F j₀) := by
    intro j₀
    refine ((((measurable_const.indicator (TwoComponentCoulomb.measurableSet_box N)).comp
      (measurable_pi_apply j₀).snd).mul (measurable_connInd M lam)).mul
      (Finset.measurable_prod _ fun i _ => hHr i)).mul
      (((measurable_const.indicator hT).comp
        ((measurable_pi_apply j₀).fst.sub (measurable_pi_apply j₀).snd)).mul
      (Finset.measurable_prod _ fun c' _ => ?_))
    exact measurable_normLe.comp
      (((measurable_pi_apply c').fst.sub (measurable_pi_apply c').snd).prodMk
        ((measurable_pi_apply j₀).fst.sub (measurable_pi_apply j₀).snd))
  -- pointwise: split according to the dipole of largest radius
  have hpt : ∀ c : ι → ℂ × ℂ, P.indicator (fun c => connInd M lam c *
      ∏ i, H ((c i).1 - (c i).2)) c * T.indicator 1 ((c i₀).1 - (c i₀).2) ≤ ∑ j₀, F j₀ c := by
    intro c
    have : Nonempty ι := ⟨i₀⟩
    obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun i => ‖(c i).1 - (c i).2‖
    refine le_trans ?_ (single_le_sum (fun j _ => zero_le) (mem_univ j₀))
    by_cases hcP : c ∈ P
    · rw [indicator_of_mem hcP]
      by_cases hi₀ : (c i₀).1 - (c i₀).2 ∈ T
      · have hj₀T : (c j₀).1 - (c j₀).2 ∈ T := lt_of_lt_of_le hi₀ (hj₀ i₀)
        have hbox : (c j₀).2 ∈ box N := (Set.mem_univ_pi.1 hcP j₀).2
        simp only [F, indicator_of_mem hi₀, indicator_of_mem hj₀T, indicator_of_mem hbox,
          Pi.one_apply, one_mul, mul_one]
        rw [prod_eq_one fun c' _ => normLe_of_le (hj₀ c'), mul_one]
      · rw [indicator_of_notMem hi₀, mul_zero]
        exact zero_le
    · rw [indicator_of_notMem hcP, zero_mul]
      exact zero_le
  -- each root term
  have hterm : ∀ j₀, ∫⁻ c, F j₀ c ≤ K * N *
      ∫⁻ t, T.indicator 1 t * H t * (∫⁻ s, H s * edgeWeight M lam s * normLe s t) ^
        (Fintype.card ι - 1) := by
    intro j₀
    rw [lintegral_dipole_coords (hFm j₀)]
    have hinner : ∀ r : ι → ℂ, ∫⁻ y : ι → ℂ, F j₀ (fun i => (y i + r i, y i)) ≤
        K * N * ((T.indicator 1 (r j₀) * H (r j₀)) *
          ∏ c' ∈ univ.erase j₀, (H (r c') * edgeWeight M lam (r c') * normLe (r c') (r j₀))) := by
      intro r
      have hsplit : ∀ y : ι → ℂ, F j₀ (fun i => (y i + r i, y i)) =
          ((∏ i, H (r i)) * (T.indicator 1 (r j₀) *
            ∏ c' ∈ univ.erase j₀, normLe (r c') (r j₀))) *
          ((box N).indicator (1 : ℂ → ℝ≥0∞) (y j₀) * connectedIndicator M lam y r) := by
        intro y
        simp only [F, add_sub_cancel_left]
        rw [connInd_dipole]
        ring
      simp_rw [hsplit]
      have hmy : Measurable fun y : ι → ℂ =>
          (box N).indicator (1 : ℂ → ℝ≥0∞) (y j₀) * connectedIndicator M lam y r := by
        refine ((measurable_const.indicator (TwoComponentCoulomb.measurableSet_box N)).comp
          (measurable_pi_apply j₀)).mul ?_
        have hm : Measurable fun y : ι → ℂ => connInd M lam (fun i => (y i + r i, y i)) :=
          (measurable_connInd (ι := ι) M lam).comp
            (f := fun y : ι → ℂ => fun i => (y i + r i, y i))
            (measurable_pi_iff.2 fun i =>
              ((measurable_pi_apply i).add measurable_const).prodMk (measurable_pi_apply i))
        have heq : (fun y : ι → ℂ => connInd M lam (fun i => (y i + r i, y i))) =
            fun y => connectedIndicator M lam y r := funext fun y => connInd_dipole y r
        rw [heq] at hm
        exact hm
      rw [lintegral_const_mul _ hmy]
      calc ((∏ i, H (r i)) * (T.indicator 1 (r j₀) *
            ∏ c' ∈ univ.erase j₀, normLe (r c') (r j₀))) *
            ∫⁻ y : ι → ℂ, (box N).indicator (1 : ℂ → ℝ≥0∞) (y j₀) * connectedIndicator M lam y r
          ≤ ((∏ i, H (r i)) * (T.indicator 1 (r j₀) *
            ∏ c' ∈ univ.erase j₀, normLe (r c') (r j₀))) *
            (K * N * ∏ c' ∈ univ.erase j₀, edgeWeight M lam (r c')) := by
            gcongr
            exact lintegral_positions_le hM hlam N r j₀
        _ = K * N * ((T.indicator 1 (r j₀) * H (r j₀)) *
            ∏ c' ∈ univ.erase j₀, (H (r c') * edgeWeight M lam (r c') *
              normLe (r c') (r j₀))) := by
            rw [← mul_prod_erase univ (fun i => H (r i)) (mem_univ j₀), prod_mul_distrib,
              prod_mul_distrib]
            ring
    have hf : Measurable fun t : ℂ => T.indicator (1 : ℂ → ℝ≥0∞) t * H t :=
      (measurable_const.indicator hT).mul hH
    have hg : Measurable (uncurry fun s t : ℂ => H s * edgeWeight M lam s * normLe s t) := by
      have h1 : Measurable fun p : ℂ × ℂ => H p.1 * edgeWeight M lam p.1 :=
        (hH.comp measurable_fst).mul ((measurable_edgeWeight M lam).comp measurable_fst)
      exact h1.mul measurable_normLe
    calc ∫⁻ r : ι → ℂ, ∫⁻ y : ι → ℂ, F j₀ (fun i => (y i + r i, y i))
        ≤ ∫⁻ r : ι → ℂ, K * N * ((T.indicator 1 (r j₀) * H (r j₀)) *
            ∏ c' ∈ univ.erase j₀, (H (r c') * edgeWeight M lam (r c') *
              normLe (r c') (r j₀))) := lintegral_mono hinner
      _ = K * N * ∫⁻ r : ι → ℂ, (T.indicator 1 (r j₀) * H (r j₀)) *
            ∏ c' ∈ univ.erase j₀, (H (r c') * edgeWeight M lam (r c') *
              normLe (r c') (r j₀)) := by
          refine lintegral_const_mul _ ?_
          refine (hf.comp (measurable_pi_apply j₀)).mul (Finset.measurable_prod _ fun c' _ => ?_)
          have := hg.comp (f := fun r : ι → ℂ => (r c', r j₀))
            ((measurable_pi_apply c').prodMk (measurable_pi_apply j₀))
          exact this
      _ = K * N * ∫⁻ t, T.indicator 1 t * H t * (∫⁻ s, H s * edgeWeight M lam s * normLe s t) ^
            (Fintype.card ι - 1) := by
          rw [lintegral_star j₀ (fun t => T.indicator 1 t * H t) hf
            (fun s t => H s * edgeWeight M lam s * normLe s t) hg]
  calc ∫⁻ c : ι → ℂ × ℂ, P.indicator (fun c => connInd M lam c * ∏ i, H ((c i).1 - (c i).2)) c *
        T.indicator 1 ((c i₀).1 - (c i₀).2)
      ≤ ∫⁻ c, ∑ j₀, F j₀ c := lintegral_mono hpt
    _ = ∑ j₀, ∫⁻ c, F j₀ c := lintegral_finsetSum _ fun j₀ _ => hFm j₀
    _ ≤ ∑ _j₀ : ι, K * N * ∫⁻ t, T.indicator 1 t * H t *
          (∫⁻ s, H s * edgeWeight M lam s * normLe s t) ^ (Fintype.card ι - 1) :=
        sum_le_sum fun j₀ _ => hterm j₀
    _ = (Fintype.card ι : ℝ≥0∞) * (K * N) * ∫⁻ t, T.indicator 1 t * H t *
          (∫⁻ s, H s * edgeWeight M lam s * normLe s t) ^ (Fintype.card ι - 1) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring

end Tail

/-! ### The exponents -/

/-- The exponent `σ` of the inner radial integral: `4 - β` for `β < 4`, `1/(k(2p₀ + 1))` for
`β ≥ 4`, used after the logarithmic tail has been evaluated. -/
noncomputable def tailSigma (p₀ : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  if β < 4 then 4 - β else 1 / (k * (2 * p₀ + 1))

theorem zero_lt_tailSigma {p₀ : ℕ} {β : ℝ} {k : ℕ} (hk : 1 ≤ k) : 0 < tailSigma p₀ β k := by
  unfold tailSigma
  by_cases hβ : β < 4
  · rw [ite_eq_left hβ]
    linarith
  · rw [ite_eq_right hβ]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity

theorem four_sub_le_tailSigma {p₀ : ℕ} {β : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    4 - β ≤ tailSigma p₀ β k := by
  by_cases hβ : β < 4
  · unfold tailSigma; rw [ite_eq_left hβ]
  · have := zero_lt_tailSigma (p₀ := p₀) (β := β) hk
    linarith [not_lt.1 hβ]

/-- **The final algebra of Step 3**: with `σ = tailSigma`, `x = σ(k-1) - β + 2` and
`h = ε₀ R̄`, `λ^{(4-β-σ)(k-1)} h^x ≤ ε₀^x λ^{(2-β)k} R̄^{-2}` for `0 < λ ≤ 1`. -/
theorem tail_power_le {p₀ : ℕ} {β lam ε₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hε₀ : 0 < ε₀) :
    lam ^ ((4 - β - tailSigma p₀ β k) * ((k : ℝ) - 1)) *
        (ε₀ * truncationScale p₀ β lam) ^ (tailSigma p₀ β k * ((k : ℝ) - 1) - β + 2) ≤
      ε₀ ^ (tailSigma p₀ β k * ((k : ℝ) - 1) - β + 2) *
        (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set x := tailSigma p₀ β k * ((k : ℝ) - 1) - β + 2
  rw [Real.mul_rpow hε₀.le hR.le]
  have key : lam ^ ((4 - β - tailSigma p₀ β k) * ((k : ℝ) - 1)) * truncationScale p₀ β lam ^ x ≤
      lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ) := by
    by_cases hβ4 : β < 4
    · have hσ : tailSigma p₀ β k = 4 - β := by unfold tailSigma; rw [ite_eq_left hβ4]
      have hx : x = (4 - β) * k + (-2) := by simp only [x, hσ]; ring
      rw [hσ, hx, Real.rpow_add hR, Appendix.rpow_truncationScale_mul_of_lt hlam hβ4]
      rw [show (4 - β - (4 - β)) * ((k : ℝ) - 1) = 0 by ring, Real.rpow_zero, one_mul]
    · push Not at hβ4
      have hRe : ∀ y : ℝ, truncationScale p₀ β lam ^ y = lam ^ (-(2 * (p₀ : ℝ)) * y) := by
        intro y
        rw [Appendix.truncationScale_of_ge hβ4, ← Real.rpow_intCast, ← Real.rpow_mul hlam.le]
        congr 1
        push_cast
        ring
      rw [hRe, hRe, ← Real.rpow_add hlam, ← Real.rpow_add hlam]
      refine Real.rpow_le_rpow_of_exponent_ge hlam hlam1 ?_
      have hσ : tailSigma p₀ β k = 1 / (k * (2 * p₀ + 1)) := by
        unfold tailSigma; rw [ite_eq_right (not_lt.2 hβ4)]
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hp : (0 : ℝ) ≤ p₀ := Nat.cast_nonneg p₀
      have hkey : tailSigma p₀ β k * ((k : ℝ) - 1) * (2 * p₀ + 1) ≤ 1 := by
        rw [hσ]
        have hpos : (0 : ℝ) < k * (2 * p₀ + 1) := by positivity
        rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_one hpos]
        nlinarith
      simp only [x]
      nlinarith
  calc lam ^ ((4 - β - tailSigma p₀ β k) * ((k : ℝ) - 1)) *
        (ε₀ ^ x * truncationScale p₀ β lam ^ x)
      = ε₀ ^ x * (lam ^ ((4 - β - tailSigma p₀ β k) * ((k : ℝ) - 1)) *
          truncationScale p₀ β lam ^ x) := by ring
    _ ≤ ε₀ ^ x * (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left key (Real.rpow_nonneg hε₀.le _)

/-! ### The bound (A.46) -/

/-- The exponent `x = σ(k-1) - β + 2 < 0` of `ε₀` in the bound (A.46). -/
noncomputable def tailExp (p₀ : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  tailSigma p₀ β k * ((k : ℝ) - 1) - β + 2

/-- **Eq. (A.46)**: for `β > 2`, `1 ≤ k` with `(4 - β)k - 2 < 0` (i.e.
`k ≤ p*(β)`), `M ≥ 0` and `p₀`, there is `C > 0` (depending on `χ, β, M, k, p₀`) such that for
`ε₀ > 0`, `0 < λ ≤ 1` with `λ ≤ h = ε₀ R̄`, every `N`, every `S` with `|S| = k` and `i₀ ∈ S`,
`∫_{(Λ²)^S} 𝟙_{𝓑_S} ∏_i e^{β g_λ(r_i)} 𝟙_{|r_{i₀}| > h} ≤ C ε₀^x N λ^{(2-β)k} R̄^{-2}`, with
`x = tailExp p₀ β k`. -/
theorem lintegral_cutoff_tail_le {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β : ℝ} (hβ : 2 < β)
    {k : ℕ} (hk : 1 ≤ k) (hkp : (4 - β) * k - 2 < 0) (hM : 0 ≤ M) (p₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε₀ lam : ℝ), 0 < ε₀ → 0 < lam → lam ≤ 1 →
      lam ≤ ε₀ * truncationScale p₀ β lam → ∀ (N : ℕ) (S : Finset ℕ), S.card = k → ∀ i₀ : S,
        ∫⁻ c : S → ℂ × ℂ, (Set.univ.pi fun _ : S => box N ×ˢ box N).indicator
            (fun c => connInd M lam c *
              ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
            {u : ℂ | ε₀ * truncationScale p₀ β lam < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2) ≤
          ENNReal.ofReal (C * ε₀ ^ tailExp p₀ β k * N *
            (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ))) := by
  classical
  have hβ0 : 0 ≤ β := by linarith
  let σ := tailSigma p₀ β k
  have hσ : 0 < σ := zero_lt_tailSigma hk
  have hσβ : 4 - β ≤ σ := four_sub_le_tailSigma hk
  obtain ⟨Ctail, hCtail, htail⟩ := ordered_tail_compat hβ hσ hσβ hk hkp
  let K₀ := Real.exp (β * MultipoleIntegral.kernelConst χ)
  let D₀ := 4 * Real.pi * M ^ 2 * K₀ * (2 * Real.pi)
  let C₀ := (k : ℝ) * (k ^ k : ℕ) * K₀ * D₀ ^ (k - 1) * (2 * Real.pi) * Ctail
  have hK₀ : 0 < K₀ := Real.exp_pos _
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀ + 1, by positivity, fun eps lam heps hlam hlam1 hlh N S hS i₀ => ?_⟩
  let h := eps * truncationScale p₀ β lam
  have hh : 0 < h := hlam.trans_le hlh
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  let H (w : ℂ) := ENNReal.ofReal (Real.exp (β * smearedKernel χ lam w))
  have hH : Measurable H := ENNReal.measurable_ofReal.comp (measurable_exp_smearedKernel hχ hlam β)
  have hHle : ∀ w, H w ≤ ENNReal.ofReal (K₀ * max ‖w‖ lam ^ (-β)) := fun w =>
    ENNReal.ofReal_le_ofReal (exp_smearedKernel_le hχ hβ0 hlam w)
  have hinner : ∀ t : ℂ, ∫⁻ s, H s * edgeWeight M lam s * normLe s t ≤
      ENNReal.ofReal D₀ * orderedInner β lam ‖t‖ := by
    intro t
    have hset : MeasurableSet {u : ℂ | ‖u‖ ∈ Iic ‖t‖} := measurable_norm measurableSet_Iic
    have hpt : ∀ s, H s * edgeWeight M lam s * normLe s t ≤ {u : ℂ | ‖u‖ ∈ Iic ‖t‖}.indicator
        (fun s => ENNReal.ofReal (4 * Real.pi * M ^ 2 * K₀) *
          ENNReal.ofReal (max ‖s‖ lam ^ (2 - β))) s := by
      intro s
      by_cases hs : ‖s‖ ≤ ‖t‖
      · rw [indicator_of_mem (show s ∈ {u : ℂ | ‖u‖ ∈ Iic ‖t‖} from hs), normLe_of_le hs, mul_one]
        have hm : 0 < max ‖s‖ lam := lt_max_of_lt_right hlam
        calc H s * edgeWeight M lam s ≤ ENNReal.ofReal (K₀ * max ‖s‖ lam ^ (-β)) *
              edgeWeight M lam s := by gcongr; exact hHle s
          _ = ENNReal.ofReal (4 * Real.pi * M ^ 2 * K₀) *
                ENNReal.ofReal (max ‖s‖ lam ^ (2 - β)) := by
              unfold edgeWeight
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              have : max ‖s‖ lam ^ (2 - β) = max ‖s‖ lam ^ (-β) * max ‖s‖ lam ^ 2 := by
                rw [← Real.rpow_natCast, ← Real.rpow_add hm]
                ring_nf
              rw [this]
              ring
      · have hn : normLe s t = 0 := by
          unfold normLe
          exact indicator_of_notMem (show (s, t) ∉ {p : ℂ × ℂ | ‖p.1‖ ≤ ‖p.2‖} from hs) _
        rw [hn, mul_zero]
        exact zero_le
    calc ∫⁻ s, H s * edgeWeight M lam s * normLe s t
        ≤ ∫⁻ s, {u : ℂ | ‖u‖ ∈ Iic ‖t‖}.indicator
            (fun s => ENNReal.ofReal (4 * Real.pi * M ^ 2 * K₀) *
              ENNReal.ofReal (max ‖s‖ lam ^ (2 - β))) s := lintegral_mono hpt
      _ = ENNReal.ofReal (4 * Real.pi * M ^ 2 * K₀) *
            ∫⁻ s in {u : ℂ | ‖u‖ ∈ Iic ‖t‖}, ENNReal.ofReal (max ‖s‖ lam ^ (2 - β)) := by
          rw [lintegral_indicator hset, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal D₀ * orderedInner β lam ‖t‖ := by
          have he : {u : ℂ | ‖u‖ ∈ Iic ‖t‖} = Metric.closedBall (0 : ℂ) ‖t‖ := by
            ext u
            simp only [Set.mem_ofPred_eq, Set.mem_Iic, mem_closedBall_zero_iff]
          rw [he, ← lintegral_indicator measurableSet_closedBall,
            lintegral_radial_disc hlam (2 - β) ‖t‖, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1

  let c₁ := K₀ * D₀ ^ (k - 1)
  have hc₁ : 0 ≤ c₁ := by dsimp only [c₁]; positivity
  let F (t : ℂ) := {u : ℂ | h < ‖u‖}.indicator
    (fun t => ENNReal.ofReal (max ‖t‖ lam ^ (-β)) * orderedInner β lam ‖t‖ ^ (k - 1)) t
  have houter : ∀ t : ℂ, {u : ℂ | h < ‖u‖}.indicator 1 t * H t *
      (∫⁻ s, H s * edgeWeight M lam s * normLe s t) ^ (k - 1) ≤ ENNReal.ofReal c₁ * F t := by
    intro t
    by_cases ht : h < ‖t‖
    · simp only [F, indicator_of_mem (show t ∈ {u : ℂ | h < ‖u‖} from ht),
        Pi.one_apply, one_mul]
      calc
        _ ≤ ENNReal.ofReal (K₀ * max ‖t‖ lam ^ (-β)) *
            (ENNReal.ofReal D₀ * orderedInner β lam ‖t‖) ^ (k - 1) :=
          mul_le_mul' (hHle t) (pow_le_pow_left' (hinner t) _)
        _ = _ := by
          rw [ENNReal.ofReal_mul hK₀.le, mul_pow, ENNReal.ofReal_mul hK₀.le,
            ENNReal.ofReal_pow hD₀]
          ring
    · simp [F, ht]
  have hstepB : (∫⁻ t, {u : ℂ | h < ‖u‖}.indicator 1 t * H t *
      (∫⁻ s, H s * edgeWeight M lam s * normLe s t) ^ (k - 1)) ≤
      ENNReal.ofReal (c₁ * (2 * Real.pi) * Ctail *
        (lam ^ ((4 - β - σ) * ((k : ℝ) - 1)) * h ^ tailExp p₀ β k)) := by
    refine (lintegral_mono houter).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    dsimp only [F]
    rw [lintegral_ordered_tail_profile hlam hh]
    refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl (htail lam h hlam hlh))).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc₁]
    congr 1
    dsimp only [tailExp, σ]
    ring
  have hmain := lintegral_tail_le (ι := S) hM hlam.le N i₀ H hH h
  rw [hcard] at hmain
  refine hmain.trans ((mul_le_mul' le_rfl hstepB).trans ?_)
  have hpow := tail_power_le (p₀ := p₀) (β := β) hk hlam hlam1 heps
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hraw : ((k : ℝ≥0∞) * (((k ^ k : ℕ) : ℝ≥0∞) * N)) *
      ENNReal.ofReal (c₁ * (2 * Real.pi) * Ctail *
        (lam ^ ((4 - β - σ) * ((k : ℝ) - 1)) * h ^ tailExp p₀ β k)) =
      ENNReal.ofReal (C₀ * N *
        (lam ^ ((4 - β - σ) * ((k : ℝ) - 1)) * h ^ tailExp p₀ β k)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp only [C₀, c₁]
    ring
  rw [hraw]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C₀ * N * (eps ^ tailExp p₀ β k *
        (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₀ hN)
      exact hpow
    _ ≤ (C₀ + 1) * eps ^ tailExp p₀ β k * N *
        (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
      have hT : 0 ≤ eps ^ tailExp p₀ β k * N *
          (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
        have := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
        positivity
      nlinarith

end GeneralExpansion

end MultipoleBKT

end
