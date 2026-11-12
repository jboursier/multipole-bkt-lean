/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.MultipoleDiff

/-!
# Comparison of the block integrals (proof of (4.44) and (4.45))

The proof of Proposition 4.24. Each block retains its own power `λ^{2(|S|-1)}` from
its lower bound. Telescoping uses the largest block size `X.sup Finset.card`,
so the relative error retains `R̄^{-2} λ^{-2(max |S|-1)}`.

`minus_blocks` and `zero_blocks` give the size-dependent block comparisons.
`prod_blockComparison` telescopes any common positive scale.
`blockComparison_max` supplies the maximum-block scale to that telescoping.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionErrors

open MeasureTheory Set Finset Metric Filter
open scoped ENNReal
open TwoComponentCoulomb (box)
open Hierarchical MultipoleIntegral

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

/-! ### The cutoff of the true model -/

open scoped Classical in
/-- **(A.47)** (eqs. (A.37), (A.46), (A.47) of the proof of Lemma A.6): for `1 ≤ k ≤ p*(β)`, `M ≥ 0`, `p₀` and `ε₀ > 0` there is `C > 0` such that for
`0 < λ ≤ 1` with `λ ≤ ε₀ R̄`, every `N` and `|S| = k`,
`|I^0_{mult,ε₀}(S) - I^0_{mult,∞}(S)| ≤ C N λ^{(2-β)k} R̄^{-2}`. -/
theorem multipoleIntegralCut_sub_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (p₀ : ℕ) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      lam ≤ ε₀ * truncationScale p₀ β lam → ∀ (N : ℕ) (S : Finset ℕ), S.card = k →
        |multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S -
            multipoleIntegral χ N β lam M S| ≤
          C * N * (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hkp' : (4 - β) * k - 2 < 0 :=
    (Appendix.transitionBeta_lt_iff hk β).1 ((Appendix.le_pStar_iff hk).1 hkp)
  obtain ⟨Cb, hCb0, hCb⟩ := dipoleBond_le hχ
  obtain ⟨CT, hCT0, htail⟩ :=
    GeneralExpansion.lintegral_cutoff_tail_le (M := M) hχ hβ hk hkp' hM p₀
  intro ε₀ hε₀
  set W : ℝ := Real.exp (β * Cb)
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg hβ0 hCb0)
  set K : ℝ := W ^ (k * k)
  have hK : 0 ≤ K := by positivity
  set D : ℝ := CT * ε₀ ^ GeneralExpansion.tailExp p₀ β k
  have hD : 0 ≤ D := by positivity
  refine ⟨K * k * D + 1, by positivity, fun lam hlam hlam1 hlh N S hS => ?_⟩
  set R := truncationScale p₀ β lam
  set h := ε₀ * R
  set T : ℝ := lam ^ ((2 - β) * k) * R ^ (-2 : ℝ)
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hT : 0 ≤ T := by positivity
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  set P : Set (S → ℂ × ℂ) := Set.univ.pi fun _ : S => box N ×ˢ box N
  set E : (S → ℂ × ℂ) → ℝ := fun c =>
    ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))
  set F₂ : S → (S → ℂ × ℂ) → ℝ≥0∞ := fun i₀ c => P.indicator (fun c =>
      GeneralExpansion.connInd M lam c *
        ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
    {u : ℂ | h < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2)
  have hF₂m : ∀ i₀, Measurable (F₂ i₀) := by
    intro i₀
    refine (Measurable.indicator ((GeneralExpansion.measurable_connInd M lam).mul
      (Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
        ((measurable_exp_smearedKernel hχ hlam β).comp
          ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd))))
      (measurableSet_pi_box_prod N)).mul ?_
    exact (measurable_one.indicator (measurableSet_lt measurable_const measurable_norm)).comp
      ((measurable_pi_apply i₀).fst.sub (measurable_pi_apply i₀).snd)
  -- the pointwise bound
  have hstab : ∀ d e : ℂ × ℂ, stablePairWeight χ β lam d e ≤ W := fun d e =>
    hCb β hβ0 lam hlam d e
  have hpt : ∀ c ∈ P, ENNReal.ofReal |multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
          (closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) -
        multipolePartitionFunctionIntegrand χ β lam M c * E c| ≤
      ENNReal.ofReal K * ∑ i₀, F₂ i₀ c := by
    intro c hc
    by_cases hall : ∀ i : S, ‖(c i).1 - (c i).2‖ ≤ h
    · have hprod : ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
          (closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) = E c := by
        refine prod_congr rfl fun i _ => ?_
        rw [indicator_of_mem (by rw [mem_closedBall_zero_iff]; exact hall i), Pi.one_apply,
          mul_one]
      rw [hprod, sub_self, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hprod : ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
          (closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) = 0 := by
        refine prod_eq_zero (mem_univ i₀) ?_
        rw [indicator_of_notMem (by rw [mem_closedBall_zero_iff]; exact not_le.2 hi₀), mul_zero]
      have hE0 : 0 ≤ E c := prod_nonneg fun i _ => (Real.exp_pos _).le
      have hg0 : 0 ≤ multipolePartitionFunctionIntegrand χ β lam M c * E c :=
        mul_nonneg (multipolePartitionFunctionIntegrand_nonneg χ β lam M c) hE0
      rw [hprod, mul_zero, zero_sub, abs_neg, abs_of_nonneg hg0]
      have hb := multipolePartitionFunctionIntegrand_le (M := M) hW hstab c
      rw [hS] at hb
      have hb2 : multipolePartitionFunctionIntegrand χ β lam M c ≤
          K * (GeneralExpansion.connInd M lam c).toReal := by
        refine hb.trans (le_of_eq ?_)
        congr 1
        unfold GeneralExpansion.connInd
        split_ifs <;> simp_all
      have hci : GeneralExpansion.connInd M lam c ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (GeneralExpansion.connInd_le_one c)
      have hterm : F₂ i₀ c = GeneralExpansion.connInd M lam c *
          ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) := by
        simp only [F₂]
        rw [indicator_of_mem hc,
          indicator_of_mem (show (c i₀).1 - (c i₀).2 ∈ {u : ℂ | h < ‖u‖} from hi₀),
          Pi.one_apply, mul_one]
      calc ENNReal.ofReal (multipolePartitionFunctionIntegrand χ β lam M c * E c)
          ≤ ENNReal.ofReal (K * (GeneralExpansion.connInd M lam c).toReal * E c) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hb2 hE0)
        _ = ENNReal.ofReal K * F₂ i₀ c := by
            rw [hterm, mul_assoc, ENNReal.ofReal_mul hK]
            congr 1
            rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hci,
              ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
        _ ≤ ENNReal.ofReal K * ∑ i₀, F₂ i₀ c :=
            mul_le_mul' le_rfl (Finset.single_le_sum (f := fun i => F₂ i c)
              (fun i _ => zero_le) (mem_univ i₀))
  -- the bound on the integral of the difference
  have hlint : ∫⁻ c in P, ENNReal.ofReal |multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) *
          (closedBall (0 : ℂ) h).indicator 1 ((c i).1 - (c i).2)) -
        multipolePartitionFunctionIntegrand χ β lam M c * E c| ≤
      ENNReal.ofReal (K * k * D * N * T) := by
    calc _ ≤ ∫⁻ c in P, ENNReal.ofReal K * ∑ i₀, F₂ i₀ c :=
          setLIntegral_mono' (measurableSet_pi_box_prod N) hpt
      _ ≤ ∫⁻ c, ENNReal.ofReal K * ∑ i₀, F₂ i₀ c := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal K * ∑ i₀, ∫⁻ c, F₂ i₀ c := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_finsetSum _ fun i₀ _ => hF₂m i₀]
      _ ≤ ENNReal.ofReal K * ∑ _i₀ : S, ENNReal.ofReal (D * N * T) := by
          refine mul_le_mul' le_rfl (sum_le_sum fun i₀ _ => ?_)
          exact htail ε₀ lam hε₀ hlam hlam1 hlh N S hS i₀
      _ = ENNReal.ofReal (K * k * D * N * T) := by
          rw [sum_const, card_univ, hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hK]
          congr 1
          ring
  have hmain := GeneralExpansion.abs_setIntegral_sub_le (μ := volume) (P := P)
    (measurable_cutIntegrand hχ hlam β M h) (GeneralExpansion.integrableOn_multipoleIntegrand hχ
      hlam N S) (by positivity) hlint
  unfold multipoleIntegralCut multipoleIntegral
  refine hmain.2.trans ?_
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : 0 ≤ N * T := by positivity
  calc K * k * D * N * T = (K * k * D) * (N * T) := by ring
    _ ≤ (K * k * D + 1) * (N * T) := by nlinarith
    _ = (K * k * D + 1) * N * T := by ring

/-! ### Singletons -/

/-- **The singleton of the model `0`**. See the proof of Proposition 4.24: `I^0_{mult,ε₀}({i}) = N C_{β,λ,ε₀}`. -/
theorem multipoleIntegralCut_singleton (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) {S : Finset ℕ} (hS : S.card = 1) :
    multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S =
      N * cutoffDipoleNormalization χ N p₀ β lam ε₀ := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hS
  have := isProbabilityMeasure_cutoffDipoleMeasure (p₀ := p₀) hχ hlam β hε₀ hN
  have h := zeroPartitionFunction_singleton_eq (β := β) (M := M) (p₀ := p₀) hχ hlam hε₀ hN {i}
  rw [zeroPartitionFunction, Finset.prod_singleton, modelPartitionFunction_singleton_one,
    Finset.card_singleton, pow_one] at h
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  rw [eq_comm, inv_mul_eq_one₀ hC.ne'] at h
  exact h.symm

/-- **The singleton lower bound for every real `L`**. See the proof of Proposition 4.24.
The singleton has no pair interaction. On the cutoff, its damping is at least
`exp (-|L|)`, which is the written `exp (-L)` when `L ≥ 0`. -/
theorem multipoleIntegralMinus_singleton_lower_abs (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) {S : Finset ℕ} (hS : S.card = 1) :
    Real.exp (-|L|) * (N * cutoffDipoleNormalization χ N p₀ β lam ε₀) ≤
      multipoleIntegralMinus χ N β lam M L ε₀ (truncationScale p₀ β lam) S := by
  classical
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hS
  let S : Finset ℕ := {i}
  have : Subsingleton S := Finset.card_le_one_iff_subsingleton_coe.1 (by simp [S])
  let a : S := ⟨i, mem_singleton_self i⟩
  have huniv : (univ : Finset S) = {a} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_singleton, Subsingleton.elim u a, iff_self]
  let R := truncationScale p₀ β lam
  let F : (S → ℂ × ℂ) → ℝ := fun c =>
    multipolePartitionFunctionIntegrand χ β lam M c *
      ∏ u : S, (Real.exp (β * smearedKernel χ lam ((c u).1 - (c u).2)) *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((c u).1 - (c u).2))
  -- Both pair products are empty, so only the Gaussian damping differs.
  have heq (c : S → ℂ × ℂ) : minusIntegrand χ β lam M L ε₀ R c =
      Real.exp (-L * ‖(c a).1 - (c a).2‖ ^ 2 / (ε₀ * R) ^ 2) * F c := by
    unfold minusIntegrand F multipolePartitionFunctionIntegrand
    simp only [huniv, Finset.prod_singleton, lt_self_iff_false, ↓reduceIte, mul_one]
    ring
  have hF0 (c : S → ℂ × ℂ) : 0 ≤ F c := cutIntegrand_nonneg lam (ε₀ * R) c
  have hpoint (c : S → ℂ × ℂ) :
      Real.exp (-|L|) * F c ≤ minusIntegrand χ β lam M L ε₀ R c ∧
        minusIntegrand χ β lam M L ε₀ R c ≤ Real.exp |L| * F c := by
    rw [heq]
    by_cases hc : (c a).1 - (c a).2 ∈ closedBall (0 : ℂ) (ε₀ * R)
    · have hd := abs_damping_le (L := L) (norm_nonneg ((c a).1 - (c a).2))
        (mem_closedBall_zero_iff.1 hc)
      exact ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (abs_le.1 hd).1) (hF0 c),
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (abs_le.1 hd).2) (hF0 c)⟩
    · have hz : F c = 0 := by
        simp only [F, huniv, Finset.prod_singleton, indicator_of_notMem hc, mul_zero]
      simp only [hz, mul_zero, le_refl, and_self]
  -- Domination justifies monotonicity of the real integrals.
  have hFi : IntegrableOn F (univ.pi fun _ : S => box N ×ˢ box N) := by
    refine (GeneralExpansion.integrableOn_multipoleIntegrand (β := β) (M := M) hχ hlam N S).mono'
      (measurable_cutIntegrand hχ hlam β M (ε₀ * R)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun c => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 c)]
    exact cutIntegrand_le lam (ε₀ * R) c
  have hmi : IntegrableOn (minusIntegrand χ β lam M L ε₀ R)
      (univ.pi fun _ : S => box N ×ˢ box N) := by
    refine (hFi.const_mul (Real.exp |L|)).mono'
      (measurable_minusIntegrand hχ hlam β M L ε₀ R).aestronglyMeasurable
      (Filter.Eventually.of_forall fun c => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (minusIntegrand_nonneg β lam M L ε₀ R c)]
    exact (hpoint c).2
  have h := integral_mono (hFi.const_mul (Real.exp (-|L|))) hmi fun c => (hpoint c).1
  rw [integral_const_mul] at h
  change Real.exp (-|L|) * multipoleIntegralCut χ N β lam M (ε₀ * R) S ≤
    multipoleIntegralMinus χ N β lam M L ε₀ R S at h
  rwa [multipoleIntegralCut_singleton hχ hlam hε₀ hN (by simp [S])] at h

/-- **The written singleton lower bound**. See the proof of Proposition 4.24: `I^-({i}) ≥ exp (-L) N C_{β,λ,ε₀}` for `L ≥ 0`. -/
theorem multipoleIntegralMinus_singleton_lower (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hL : 0 ≤ L) {S : Finset ℕ} (hS : S.card = 1) :
    Real.exp (-L) * (N * cutoffDipoleNormalization χ N p₀ β lam ε₀) ≤
      multipoleIntegralMinus χ N β lam M L ε₀ (truncationScale p₀ β lam) S := by
  simpa only [abs_of_nonneg hL] using
    (multipoleIntegralMinus_singleton_lower_abs (L := L) hχ hlam hε₀ hN hS)

/-! ### The comparison of two block integrals -/

/-- The comparison of the block integrals `I₁` (model `-` or `0`) and `I₀` (model `∞`):
`I₁ > 0`, `0 ≤ I₀ ≤ C I₁` and `|I₀ - I₁| ℓ ≤ C I₁ η`, with `η ≥ 0`. -/
def BlockComparison (C ℓ η I₁ I₀ : ℝ) : Prop :=
  0 ≤ η ∧ 0 < I₁ ∧ 0 ≤ I₀ ∧ I₀ ≤ C * I₁ ∧ |I₀ - I₁| * ℓ ≤ C * I₁ * η

theorem BlockComparison.mono {C C' ℓ η I₁ I₀ : ℝ} (hCC' : C ≤ C')
    (h : BlockComparison C ℓ η I₁ I₀) : BlockComparison C' ℓ η I₁ I₀ := by
  obtain ⟨hη, h1, h0, hle, hd⟩ := h
  refine ⟨hη, h1, h0, hle.trans (mul_le_mul_of_nonneg_right hCC' h1.le), hd.trans ?_⟩
  have := mul_le_mul_of_nonneg_right hCC' h1.le
  exact mul_le_mul_of_nonneg_right this hη

/-- **The comparison from size bounds**: with `u = v λ^{2(s-1)} > 0`, `ℓ v ≤ u`,
`c u ≤ I₁`, `0 ≤ I₀ ≤ C_u u` and `|I₀ - I₁| ≤ C_A v η`, the comparison holds with the constant
`max 1 (max (C_u/c) (C_A/c))`. -/
theorem blockComparison_of_bounds {c Cu CA u v ℓ η I₁ I₀ : ℝ} (hc : 0 < c) (hCA : 0 ≤ CA)
    (hu : 0 < u) (hℓ : 0 ≤ ℓ) (hη : 0 ≤ η) (hℓv : ℓ * v ≤ u) (h₁ : c * u ≤ I₁)
    (h₀ : 0 ≤ I₀) (h₀' : I₀ ≤ Cu * u) (hd : |I₀ - I₁| ≤ CA * v * η) :
    BlockComparison (max 1 (max (Cu / c) (CA / c))) ℓ η I₁ I₀ := by
  have hI₁ : 0 < I₁ := lt_of_lt_of_le (by positivity) h₁
  have hu' : u ≤ I₁ / c := by rw [le_div_iff₀ hc]; linarith
  have hCu : 0 ≤ Cu := by
    by_contra hneg
    push Not at hneg
    nlinarith
  refine ⟨hη, hI₁, h₀, ?_, ?_⟩
  · calc I₀ ≤ Cu * u := h₀'
      _ ≤ Cu * (I₁ / c) := mul_le_mul_of_nonneg_left hu' hCu
      _ = Cu / c * I₁ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hI₁.le
  · calc |I₀ - I₁| * ℓ ≤ CA * v * η * ℓ := mul_le_mul_of_nonneg_right hd hℓ
      _ = CA * (ℓ * v) * η := by ring
      _ ≤ CA * u * η := by gcongr
      _ ≤ CA * (I₁ / c) * η := by gcongr
      _ = CA / c * I₁ * η := by ring
      _ ≤ _ := by
          gcongr
          exact (le_max_right _ _).trans (le_max_right _ _)

/-- **The telescoping over the blocks**: if every block of `X` satisfies `BlockComparison C ℓ η`
with `C ≥ 1` and `ℓ > 0`, then `∏ I₁ > 0`, `∏ I₀ ≤ C^{|X|} ∏ I₁` and
`|∏ I₀ - ∏ I₁| ℓ ≤ C^{|X|} |X| C η ∏ I₁`. -/
theorem prod_blockComparison {X : Finset (Finset ℕ)} {I₁ I₀ : Finset ℕ → ℝ} {C ℓ η : ℝ}
    (hC : 1 ≤ C) (hℓ : 0 < ℓ) (h : ∀ S ∈ X, BlockComparison C ℓ η (I₁ S) (I₀ S)) :
    0 < ∏ S ∈ X, I₁ S ∧ ∏ S ∈ X, I₀ S ≤ C ^ X.card * ∏ S ∈ X, I₁ S ∧
      |∏ S ∈ X, I₀ S - ∏ S ∈ X, I₁ S| * ℓ ≤ C ^ X.card * (X.card * C) * η * ∏ S ∈ X, I₁ S := by
  classical
  have hpos : ∀ S ∈ X, 0 < I₁ S := fun S hS => (h S hS).2.1
  have hP : 0 < ∏ S ∈ X, I₁ S := prod_pos hpos
  set r : Finset ℕ → ℝ := fun S => I₀ S / I₁ S
  have hr0 : ∀ S ∈ X, 0 ≤ r S := fun S hS => div_nonneg (h S hS).2.2.1 (hpos S hS).le
  have hrC : ∀ S ∈ X, r S ≤ C := fun S hS => by
    rw [div_le_iff₀ (hpos S hS)]; exact (h S hS).2.2.2.1
  have hr1 : ∀ S ∈ X, |r S - 1| ≤ C * η / ℓ := fun S hS => by
    have hS1 := hpos S hS
    rw [le_div_iff₀ hℓ]
    have : r S - 1 = (I₀ S - I₁ S) / I₁ S := by simp only [r]; field_simp
    rw [this, abs_div, abs_of_pos hS1, div_mul_eq_mul_div, div_le_iff₀ hS1]
    have := (h S hS).2.2.2.2
    linarith
  have hprodr : ∏ S ∈ X, I₀ S = (∏ S ∈ X, r S) * ∏ S ∈ X, I₁ S := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun S hS => ?_
    simp only [r]
    field_simp [(hpos S hS).ne']
  refine ⟨hP, ?_, ?_⟩
  · rw [hprodr]
    exact mul_le_mul_of_nonneg_right (prod_le_pow_card_of_nonneg X hr0 hrC) hP.le
  · have htel := abs_prod_sub_one_le X hC hr0 hrC hr1
    have hsub : ∏ S ∈ X, I₀ S - ∏ S ∈ X, I₁ S = (∏ S ∈ X, r S - 1) * ∏ S ∈ X, I₁ S := by
      rw [hprodr]; ring
    rw [hsub, abs_mul, abs_of_pos hP]
    calc |∏ S ∈ X, r S - 1| * (∏ S ∈ X, I₁ S) * ℓ
        ≤ C ^ X.card * (X.card * (C * η / ℓ)) * (∏ S ∈ X, I₁ S) * ℓ := by gcongr
      _ = C ^ X.card * (X.card * C) * η * ∏ S ∈ X, I₁ S := by
          field_simp

/-- The common scale in the telescoping is the maximum block size.
proof of Proposition 4.24. -/
theorem blockComparison_max {X : Finset (Finset ℕ)} {S : Finset ℕ} (hS : S ∈ X)
    {C η I₁ I₀ lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (h : BlockComparison C (lam ^ (2 * (S.card - 1))) η I₁ I₀) :
    BlockComparison C (lam ^ (2 * (X.sup Finset.card - 1))) η I₁ I₀ := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  apply le_trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hlam.le hlam1 (by
      have := Finset.le_sup (f := Finset.card) hS
      omega)) (abs_nonneg _)) h.2.2.2.2

/-- The total-size numerator power is at most the maximum-block power.
proof of Proposition 4.24.
This comparison is used only after multiplying by the reciprocal error. -/
theorem total_power_le_max_block_power {X : Finset (Finset ℕ)} {k : ℕ}
    (hXk : (X.biUnion id).card = k) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    lam ^ (2 * (k - 1)) ≤ lam ^ (2 * (X.sup Finset.card - 1)) := by
  have hm : X.sup Finset.card ≤ k := Finset.sup_le fun S hS => by
    rw [← hXk]
    exact Finset.card_le_card (Finset.subset_biUnion_of_mem id hS)
  exact pow_le_pow_of_le_one hlam.le hlam1 (by omega)

/-! ### The comparisons for all blocks of size at most `k` -/

/-- **The comparisons from lower bounds and differences**: if a block integral `I₁` satisfies,
for every block size `1 ≤ s ≤ k`, `I₁(S) ≥ c N λ^{(2-β)s} λ^{2(s-1)}` and
`|I^0_{mult,∞}(S) - I₁(S)| ≤ A N λ^{(2-β)s} R̄^{-2}` (each for `λ` small and `N` large), then
`BlockComparison C λ^{2(|S|-1)} R̄^{-2} (I₁(S)) (I^0_{mult,∞}(S))` holds for `1 ≤ |S| ≤ k`, with one
`C ≥ 1`, for `λ` small and `N` large. -/
theorem blocks_of_bounds (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hkp : (k : ℕ∞) ≤ pStar β)
    (hM : 0 ≤ M) (p₀ : ℕ) (I₁ : ℕ → ℝ → Finset ℕ → ℝ)
    (hlow : ∀ s, 1 ≤ s → s ≤ k → ∃ c : ℝ, 0 < c ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, S.card = s →
          c * (N * lam ^ ((2 - β) * s) * lam ^ (2 * (s - 1))) ≤ I₁ N lam S)
    (hdiff : ∀ s, 1 ≤ s → s ≤ k → ∃ A : ℝ, 0 ≤ A ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, S.card = s →
          |multipoleIntegral χ N β lam M S - I₁ N lam S| ≤
            A * (N * lam ^ ((2 - β) * s)) * truncationScale p₀ β lam ^ (-2 : ℝ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ k →
          BlockComparison C (lam ^ (2 * (S.card - 1))) (truncationScale p₀ β lam ^ (-2 : ℝ))
            (I₁ N lam S) (multipoleIntegral χ N β lam M S) := by
  set P : ℕ → ℝ → ℝ → ℕ → Prop := fun s C lam N => ∀ S : Finset ℕ, S.card = s →
    BlockComparison C (lam ^ (2 * (s - 1))) (truncationScale p₀ β lam ^ (-2 : ℝ))
      (I₁ N lam S) (multipoleIntegral χ N β lam M S)
  have hmono : ∀ s C C' lam N, C ≤ C' → P s C lam N → P s C' lam N :=
    fun s C C' lam N hCC' h S hS => (h S hS).mono hCC'
  have hblock : ∀ s, 1 ≤ s → s ≤ k → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P s C lam N := by
    intro s hs1 hsk
    have hsp : (s : ℕ∞) ≤ pStar β := le_trans (by exact_mod_cast hsk) hkp
    obtain ⟨c, hc, l₁, hl₁, hl⟩ := hlow s hs1 hsk
    obtain ⟨A, hA, l₂, hl₂, hd⟩ := hdiff s hs1 hsk
    obtain ⟨Cu, hCu, hup⟩ := multipoleIntegral_le hχ hβ hs1 hsp hM
    refine ⟨max 1 (max (Cu / c) (A / c)), lt_max_of_lt_left one_pos, min (min l₁ l₂) 1,
      lt_min (lt_min hl₁ hl₂) one_pos, fun lam hlam hlt => ?_⟩
    obtain ⟨N₁, hN₁⟩ := hl lam hlam (hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    obtain ⟨N₂, hN₂⟩ := hd lam hlam (hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
    refine ⟨max (max N₁ N₂) 1, fun N hN S hS => ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
    have hu : 0 < (N : ℝ) * lam ^ ((2 - β) * s) * lam ^ (2 * (s - 1)) := by positivity
    have hℓv : lam ^ (2 * (s - 1)) * ((N : ℝ) * lam ^ ((2 - β) * s)) ≤
        (N : ℝ) * lam ^ ((2 - β) * s) * lam ^ (2 * (s - 1)) := by
      rw [mul_comm]
    have hI0 : 0 ≤ multipoleIntegral χ N β lam M S := by
      rw [multipoleIntegral_eq_toReal_lintegral hχ hlam N β M S]
      exact ENNReal.toReal_nonneg
    have hup' : multipoleIntegral χ N β lam M S ≤
        Cu * ((N : ℝ) * lam ^ ((2 - β) * s) * lam ^ (2 * (s - 1))) := by
      have := hup lam hlam N S hS
      linarith
    have hd' := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) S hS
    exact blockComparison_of_bounds hc hA hu (by positivity) (Real.rpow_nonneg hR.le _) hℓv
      (hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) S hS) hI0 hup' hd'
  obtain ⟨C, hC, lam₀, hlam₀, h⟩ := exists_uniform P hmono k hblock
  refine ⟨max C 1, le_max_right _ _, min lam₀ 1, lt_min hlam₀ one_pos, min_le_right _ _,
    fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h lam hlam (hlt.trans_le (min_le_left _ _))
  exact ⟨N₀, fun N hN S hS1 hSk => (hN₀ N hN S.card hS1 hSk S rfl).mono (le_max_left _ _)⟩

/-- **The blocks of the model `-`** (proof of Proposition 4.24): for `k ≤ p*(β)`, `M > 20`, `L`, `p₀` and
`ε₀ ∈ (0, 1)`, `BlockComparison C λ^{2(|S|-1)} R̄^{-2} (I^-_{mult,ε₀}(S)) (I^0_{mult,∞}(S))` for
`1 ≤ |S| ≤ k`, `λ` small and `N` large. The inputs are Lemma A.3 for `(ṽ, τ̃)` (`|S| ≥ 2`), the
singleton bound (`|S| = 1`), Lemma A.6 and Lemma 4.12. -/
theorem minus_blocks (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hkp : (k : ℕ∞) ≤ pStar β)
    (hM : 20 < M) (L : ℝ) (p₀ : ℕ) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 1 ≤ C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ k →
          BlockComparison C (lam ^ (2 * (S.card - 1))) (truncationScale p₀ β lam ^ (-2 : ℝ))
            (multipoleIntegralMinus χ N β lam M L ε₀ (truncationScale p₀ β lam) S)
            (multipoleIntegral χ N β lam M S) := by
  intro ε₀ hε₀ hε₁
  obtain ⟨Cn, hCn, ln, hln, hln1, hnorm⟩ := normalization_bounds hχ hβ p₀ ε₀ hε₀ hε₁
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  refine blocks_of_bounds hχ hβ hkp (by linarith) p₀
    (fun N lam S => multipoleIntegralMinus χ N β lam M L ε₀ (truncationScale p₀ β lam) S)
    (fun s hs1 hsk => ?_) (fun s hs1 hsk => ?_)
  · -- the lower bounds
    have hsp : (s : ℕ∞) ≤ pStar β := le_trans (by exact_mod_cast hsk) hkp
    rcases Nat.lt_or_ge 1 s with hs2 | hs2
    · obtain ⟨Cm, hCm, hm⟩ := multipoleIntegralMinus_two_sided hχ hβ hs2 hsp hM L
      refine ⟨Cm⁻¹, inv_pos.2 hCm, ln, hln, fun lam hlam hlt => ?_⟩
      obtain ⟨N₁, hN₁⟩ := hm lam hlam
      obtain ⟨N₂, hN₂⟩ := hnorm lam hlam hlt
      refine ⟨max N₁ N₂, fun N hN S hS => ?_⟩
      obtain ⟨-, h2, -⟩ := hN₂ N (le_trans (le_max_right _ _) hN)
      have := (hN₁ N (le_trans (le_max_left _ _) hN) ε₀ (truncationScale p₀ β lam) h2 S hS).1
      linarith
    · have hs : s = 1 := by omega
      subst hs
      refine ⟨Real.exp (-|L|) * (Z / 2), by positivity, ln, hln,
        fun lam hlam hlt => ?_⟩
      obtain ⟨N₂, hN₂⟩ := hnorm lam hlam hlt
      refine ⟨N₂, fun N hN S hS => ?_⟩
      obtain ⟨hN1, -, hCe, -⟩ := hN₂ N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      have h := multipoleIntegralMinus_singleton_lower_abs (p₀ := p₀) (β := β) (M := M) (L := L)
        hχ hlam hε₀ hN1 hS
      rw [Nat.cast_one, mul_one, Nat.sub_self, mul_zero, pow_zero, mul_one]
      have he : 0 < Real.exp (-|L|) := Real.exp_pos _
      calc Real.exp (-|L|) * (Z / 2) * ((N : ℝ) * lam ^ (2 - β))
          = Real.exp (-|L|) * (N * (1 / 2 * Z * lam ^ (2 - β))) := by ring
        _ ≤ Real.exp (-|L|) *
              (N * cutoffDipoleNormalization χ N p₀ β lam ε₀) := by gcongr
        _ ≤ _ := h
  · -- Lemma A.6
    have hsp : (s : ℕ∞) ≤ pStar β := le_trans (by exact_mod_cast hsk) hkp
    obtain ⟨CA, hCA, hA7⟩ := GeneralExpansion.multipoleIntegralMinus_sub_le hχ hβ hs1 hsp
      (M := M) (by linarith) L p₀ ε₀ hε₀
    refine ⟨CA, hCA.le, ln, hln, fun lam hlam hlt => ?_⟩
    obtain ⟨N₂, hN₂⟩ := hnorm lam hlam hlt
    refine ⟨N₂, fun N hN S hS => ?_⟩
    obtain ⟨-, h2, -⟩ := hN₂ N hN
    have hlam1 : lam ≤ 1 := (hlt.trans_le hln1).le
    have := hA7 lam hlam hlam1 (by linarith) N S hS
    rw [abs_sub_comm]
    linarith

/-- **The blocks of the model `0`** (proof of Proposition 4.24, "in the same way"): for `k ≤ p*(β)`, `M > 20`, `p₀`
and `ε₀ ∈ (0, 1)`, `BlockComparison C λ^{2(|S|-1)} R̄^{-2} (I^0_{mult,ε₀}(S)) (I^0_{mult,∞}(S))` for
`1 ≤ |S| ≤ k`, `λ` small and `N` large. The inputs are Lemma A.3 for `(v, ∞)` with a cutoff
(`|S| ≥ 2`), the singleton identity (`|S| = 1`), (A.47) and Lemma 4.12. -/
theorem zero_blocks (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hkp : (k : ℕ∞) ≤ pStar β)
    (hM : 20 < M) (p₀ : ℕ) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 1 ≤ C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ k →
          BlockComparison C (lam ^ (2 * (S.card - 1))) (truncationScale p₀ β lam ^ (-2 : ℝ))
            (multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S)
            (multipoleIntegral χ N β lam M S) := by
  intro ε₀ hε₀ hε₁
  obtain ⟨Cn, hCn, ln, hln, hln1, hnorm⟩ := normalization_bounds hχ hβ p₀ ε₀ hε₀ hε₁
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  refine blocks_of_bounds hχ hβ hkp (by linarith) p₀
    (fun N lam S => multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S)
    (fun s hs1 hsk => ?_) (fun s hs1 hsk => ?_)
  · -- the lower bounds
    have hsp : (s : ℕ∞) ≤ pStar β := le_trans (by exact_mod_cast hsk) hkp
    rcases Nat.lt_or_ge 1 s with hs2 | hs2
    · obtain ⟨Cm, hCm, hm⟩ := multipoleIntegralCut_two_sided hχ hβ hs2 hsp hM
      refine ⟨Cm⁻¹, inv_pos.2 hCm, ln, hln, fun lam hlam hlt => ?_⟩
      obtain ⟨N₁, hN₁⟩ := hm lam hlam
      obtain ⟨N₂, hN₂⟩ := hnorm lam hlam hlt
      refine ⟨max N₁ N₂, fun N hN S hS => ?_⟩
      obtain ⟨-, h2, -⟩ := hN₂ N (le_trans (le_max_right _ _) hN)
      have := (hN₁ N (le_trans (le_max_left _ _) hN) _ h2 S hS).1
      linarith
    · have hs : s = 1 := by omega
      subst hs
      refine ⟨Z / 2, by positivity, ln, hln, fun lam hlam hlt => ?_⟩
      obtain ⟨N₂, hN₂⟩ := hnorm lam hlam hlt
      refine ⟨N₂, fun N hN S hS => ?_⟩
      obtain ⟨hN1, h2, hCe, -⟩ := hN₂ N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      rw [multipoleIntegralCut_singleton hχ hlam hε₀ hN1 hS, Nat.sub_self, mul_zero, pow_zero,
        mul_one, Nat.cast_one, mul_one]
      calc Z / 2 * ((N : ℝ) * lam ^ (2 - β)) = N * (1 / 2 * Z * lam ^ (2 - β)) := by ring
        _ ≤ N * cutoffDipoleNormalization χ N p₀ β lam ε₀ := by gcongr
  · -- (A.47)
    have hsp : (s : ℕ∞) ≤ pStar β := le_trans (by exact_mod_cast hsk) hkp
    obtain ⟨CT, hCT, htail⟩ := multipoleIntegralCut_sub_le hχ hβ hs1 hsp (M := M) (by linarith)
      p₀ ε₀ hε₀
    refine ⟨CT, hCT.le, ln, hln, fun lam hlam hlt => ?_⟩
    obtain ⟨N₂, hN₂⟩ := hnorm lam hlam hlt
    refine ⟨N₂, fun N hN S hS => ?_⟩
    obtain ⟨-, h2, -⟩ := hN₂ N hN
    have hlam1 : lam ≤ 1 := (hlt.trans_le hln1).le
    have := htail lam hlam hlam1 (by linarith) N S hS
    rw [abs_sub_comm]
    linarith

end ExpansionErrors

end MultipoleBKT

end
