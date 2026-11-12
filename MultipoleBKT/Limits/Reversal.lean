/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Ear
public import MultipoleBKT.Limits.MultipoleLimit

/-!
# Reversal of dipoles and the parity expansion

See the operator `Sym_Y` ("the average over the
`2^{|Y|}` independent simultaneous reversals `x_i ↔ y_i` for all `i` in each part of `Y`") and the
paragraph of the proof of Lemma 4.26: "the finite-box numerators are
unchanged by these averages, since endpoint reversals preserve `(Λ²)^k`"; and the parity
argument of Lemma A.5 (equation (A.29)).

* `flipCfg B c` reverses the dipoles with labels in `B`; it is a measure-preserving involution of
  `(ℂ²)^ι` that preserves `(Λ²)^ι` (`integral_boxConfig_flipCfg`);
* `v_ij` changes sign when one of the two dipoles is reversed (`dipoleInteraction_swap_left`),
  `i ↔ j` and the weights `e^{β g_λ(x - y)}` do not change, and `𝒜_ij` does not change when both
  dipoles are reversed (`isStableDipolePair_swap_swap`);
* `abs_avg_prod_le` (the parity expansion): averaging `∏_{e ∈ E} (α_e + σ_e(A) γ_e)` over the
  sets of reversed blocks `A`, where `σ_e(A) = -1` if `A` separates the endpoints of `e`, gives
  at most `∑_{F ⊆ E cut-even} ∏_{E \ F} |α_e| ∏_F |γ_e|`.
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

/-! ### Reversing dipoles -/

section Swap

variable (d e : ℂ × ℂ)

theorem smearedKernel_sub_comm (hχ : IsMollifier χ) (lam : ℝ) (x y : ℂ) :
    smearedKernel χ lam (x - y) = smearedKernel χ lam (y - x) := by
  rw [← smearedKernel_neg hχ lam (y - x), neg_sub]

theorem dipoleInteraction_swap_left (hχ : IsMollifier χ) (lam : ℝ) :
    dipoleInteraction χ lam d.swap e = -dipoleInteraction χ lam d e := by
  unfold dipoleInteraction
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [smearedKernel_sub_comm hχ lam d.2 e.1, smearedKernel_sub_comm hχ lam e.1 d.1]
  ring

theorem dipoleInteraction_swap_right (hχ : IsMollifier χ) (lam : ℝ) :
    dipoleInteraction χ lam d e.swap = -dipoleInteraction χ lam d e := by
  unfold dipoleInteraction
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [smearedKernel_sub_comm hχ lam d.2 e.1, smearedKernel_sub_comm hχ lam e.2 d.2]
  ring

theorem dipoleInteraction_swap_swap (hχ : IsMollifier χ) (lam : ℝ) :
    dipoleInteraction χ lam d.swap e.swap = dipoleInteraction χ lam d e := by
  rw [dipoleInteraction_swap_left _ _ hχ, dipoleInteraction_swap_right _ _ hχ, neg_neg]

theorem multipoleLinked_swap_left (M lam : ℝ) :
    MultipoleLinked M lam d.swap e ↔ MultipoleLinked M lam d e := by
  unfold MultipoleLinked
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [min_comm (min ‖d.2 - e.1‖ ‖d.2 - e.2‖), norm_sub_rev d.2 d.1]

theorem multipoleLinked_swap_right (M lam : ℝ) :
    MultipoleLinked M lam d e.swap ↔ MultipoleLinked M lam d e := by
  unfold MultipoleLinked
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [min_comm ‖d.1 - e.2‖, min_comm ‖d.2 - e.2‖, norm_sub_rev e.2 e.1]

theorem isStableDipolePair_swap_swap :
    IsStableDipolePair d.swap e.swap ↔ IsStableDipolePair d e := by
  rw [isStableDipolePair_iff, isStableDipolePair_iff]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev d.2 d.1, norm_sub_rev e.2 e.1, norm_sub_rev d.2 e.1, norm_sub_rev e.2 d.1]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h2, h1, h3⟩
    · exact Or.inr ⟨h1, h3, h2⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h2, h1, h3⟩
    · exact Or.inr ⟨h1, h3, h2⟩

theorem stablePairWeight_swap_swap (hχ : IsMollifier χ) (β lam : ℝ) :
    stablePairWeight χ β lam d.swap e.swap = stablePairWeight χ β lam d e := by
  unfold stablePairWeight
  rw [dipoleInteraction_swap_swap _ _ hχ]
  congr 1
  exact propext (isStableDipolePair_swap_swap d e)

theorem pairDensity_swap (hχ : IsMollifier χ) (β lam : ℝ) :
    pairDensity χ β lam d.swap = pairDensity χ β lam d := by
  unfold pairDensity
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [smearedKernel_sub_comm hχ]

end Swap

/-! ### Reversing the dipoles of a set of labels -/

section Flip

variable {ι : Type*} [DecidableEq ι]

/-- Reverse the dipoles with labels in `B`: `(x_i, y_i) ↦ (y_i, x_i)` for `i ∈ B`. -/
def flipCfg (B : Finset ι) (c : ι → ℂ × ℂ) : ι → ℂ × ℂ :=
  fun i => if i ∈ B then (c i).swap else c i

theorem flipCfg_apply (B : Finset ι) (c : ι → ℂ × ℂ) (i : ι) :
    flipCfg B c i = if i ∈ B then (c i).swap else c i := rfl

theorem flipCfg_flipCfg (B : Finset ι) (c : ι → ℂ × ℂ) : flipCfg B (flipCfg B c) = c := by
  funext i
  unfold flipCfg
  split_ifs <;> simp

theorem measurable_flipCfg (B : Finset ι) : Measurable (flipCfg B) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold flipCfg
  split_ifs
  · exact measurable_swap.comp (measurable_pi_apply i)
  · exact measurable_pi_apply i

/-- `flipCfg B` as a measurable involution. -/
noncomputable def flipEquiv (B : Finset ι) : (ι → ℂ × ℂ) ≃ᵐ (ι → ℂ × ℂ) where
  toFun := flipCfg B
  invFun := flipCfg B
  left_inv := flipCfg_flipCfg B
  right_inv := flipCfg_flipCfg B
  measurable_toFun := measurable_flipCfg B
  measurable_invFun := measurable_flipCfg B

theorem measurePreserving_flipCfg [Fintype ι] (B : Finset ι) :
    MeasurePreserving (flipCfg B) volume volume := by
  have h : ∀ i, MeasurePreserving (fun p : ℂ × ℂ => if i ∈ B then p.swap else p)
      (volume : Measure (ℂ × ℂ)) volume := by
    intro i
    by_cases hi : i ∈ B
    · simp only [hi, ite_true]
      exact Measure.measurePreserving_swap
    · simp only [hi, ite_false]
      exact MeasurePreserving.id _
  exact measurePreserving_pi (fun _ : ι => (volume : Measure (ℂ × ℂ)))
    (fun _ : ι => (volume : Measure (ℂ × ℂ))) h

theorem flipCfg_mem_boxConfig (B : Finset ι) (c : ι → ℂ × ℂ) :
    flipCfg B c ∈ boxConfig ι N ↔ c ∈ boxConfig ι N := by
  simp only [boxConfig, Set.mem_pi, Set.mem_univ, true_implies, flipCfg]
  refine forall_congr' fun i => ?_
  split_ifs
  · simp only [Set.mem_prod, Prod.fst_swap, Prod.snd_swap]
    exact and_comm
  · rfl

/-- **Reversals preserve box integrals** (the proof of Lemma 4.26: "the finite-box numerators are
unchanged by these averages, since endpoint reversals preserve `(Λ²)^k`"). -/
theorem integral_boxConfig_flipCfg [Fintype ι] (B : Finset ι) (F : (ι → ℂ × ℂ) → ℝ) :
    ∫ c in boxConfig ι N, F (flipCfg B c) = ∫ c in boxConfig ι N, F c := by
  rw [← integral_indicator (measurableSet_boxConfig N),
    ← integral_indicator (measurableSet_boxConfig N)]
  have h := (measurePreserving_flipCfg (ι := ι) B).integral_comp'
    (f := flipEquiv B) ((boxConfig ι N).indicator F)
  refine Eq.trans ?_ h
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only [flipEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  by_cases h : c ∈ boxConfig ι N
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((flipCfg_mem_boxConfig B c).2 h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (mt (flipCfg_mem_boxConfig B c).1 h)]

end Flip

/-! ### The parity expansion -/

section Parity

variable {β ε : Type*} [Fintype β] [DecidableEq β] [DecidableEq ε]

open scoped Classical in
/-- `σ_e(A) = -1` if the reversal set `A` separates the endpoints of `e`, `1` otherwise. -/
noncomputable def signCross (ends : ε → Sym2 β) (A : Finset β) (e : ε) : ℝ :=
  if Crosses A (ends e) then -1 else 1

omit [Fintype β] in
theorem crosses_symmDiff (A A₀ : Finset β) (z : Sym2 β) :
    Crosses (symmDiff A A₀) z ↔ ¬ (Crosses A z ↔ Crosses A₀ z) := by
  induction z using Sym2.ind with
  | h v w =>
    simp only [crosses_mk, Finset.mem_symmDiff]
    by_cases hv : v ∈ A <;> by_cases hw : w ∈ A <;> by_cases hv' : v ∈ A₀ <;>
      by_cases hw' : w ∈ A₀ <;> simp [hv, hw, hv', hw']

omit [DecidableEq ε] in
omit [Fintype β] in
theorem signCross_symmDiff (ends : ε → Sym2 β) (A A₀ : Finset β) (e : ε) :
    signCross ends (symmDiff A A₀) e = signCross ends A e * signCross ends A₀ e := by
  unfold signCross
  have := crosses_symmDiff A A₀ (ends e)
  by_cases h1 : Crosses A (ends e) <;> by_cases h2 : Crosses A₀ (ends e) <;>
    simp_all

open scoped Classical in
omit [Fintype β] [DecidableEq β] [DecidableEq ε] in
theorem prod_signCross (ends : ε → Sym2 β) (A : Finset β) (F : Finset ε) :
    ∏ e ∈ F, signCross ends A e = (-1) ^ (F.filter fun e => Crosses A (ends e)).card := by
  unfold signCross
  rw [prod_ite, prod_const, prod_const_one, mul_one]

omit [Fintype β] [DecidableEq β] [DecidableEq ε] in
theorem abs_prod_signCross (ends : ε → Sym2 β) (A : Finset β) (F : Finset ε) :
    |∏ e ∈ F, signCross ends A e| = 1 := by
  rw [prod_signCross, abs_pow, abs_neg, abs_one, one_pow]

omit [DecidableEq ε] in
/-- Averaging the signs over the reversal sets kills the sets that are not cut-even. -/
theorem sum_prod_signCross_eq_zero (ends : ε → Sym2 β) {F : Finset ε}
    (hF : ¬ CutEven ends F) : ∑ A : Finset β, ∏ e ∈ F, signCross ends A e = 0 := by
  classical
  unfold CutEven at hF
  push Not at hF
  obtain ⟨A₀, hA₀⟩ := hF
  have hodd : ∏ e ∈ F, signCross ends A₀ e = -1 := by
    rw [prod_signCross]
    convert (Nat.not_even_iff_odd.1 hA₀).neg_one_pow
  set S := ∑ A : Finset β, ∏ e ∈ F, signCross ends A e
  have hinv : Function.Involutive fun A : Finset β => symmDiff A A₀ := fun A =>
    symmDiff_symmDiff_cancel_right A₀ A
  have hS : S = -S := by
    calc S = ∑ A : Finset β, ∏ e ∈ F, signCross ends (symmDiff A A₀) e :=
          Fintype.sum_equiv (hinv.toPerm _) _ _ fun A => by
            simp only [Function.Involutive.coe_toPerm]
            rw [symmDiff_symmDiff_cancel_right]
      _ = ∑ A : Finset β, (∏ e ∈ F, signCross ends A e) * ∏ e ∈ F, signCross ends A₀ e := by
          refine sum_congr rfl fun A _ => ?_
          rw [← prod_mul_distrib]
          exact prod_congr rfl fun e _ => signCross_symmDiff ends A A₀ e
      _ = -S := by rw [hodd, ← sum_neg_distrib]; simp
  linarith

open scoped Classical in
/-- **The parity expansion.** -/
theorem abs_avg_prod_le (ends : ε → Sym2 β) (E : Finset ε) (α γ : ε → ℝ) :
    |(∑ A : Finset β, ∏ e ∈ E, (α e + signCross ends A e * γ e)) / 2 ^ Fintype.card β| ≤
      ∑ F ∈ E.powerset.filter (CutEven ends), (∏ e ∈ E \ F, |α e|) * ∏ e ∈ F, |γ e| := by
  classical
  have hpos : (0 : ℝ) < 2 ^ Fintype.card β := by positivity
  have hcard : (Fintype.card (Finset β) : ℝ) = 2 ^ Fintype.card β := by
    rw [Fintype.card_finset]; push_cast; rfl
  have hexp : ∀ A : Finset β, ∏ e ∈ E, (α e + signCross ends A e * γ e) =
      ∑ F ∈ E.powerset, (∏ e ∈ F, signCross ends A e) * ((∏ e ∈ F, γ e) * ∏ e ∈ E \ F, α e) := by
    intro A
    rw [show (fun e => α e + signCross ends A e * γ e) =
      fun e => signCross ends A e * γ e + α e from funext fun e => add_comm _ _, prod_add]
    refine sum_congr rfl fun F _ => ?_
    rw [prod_mul_distrib]
    ring
  simp_rw [hexp]
  rw [sum_comm]
  simp_rw [← sum_mul]
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← sum_filter_add_sum_filter_not E.powerset (CutEven ends)]
  have hzero : ∑ F ∈ E.powerset.filter (fun F => ¬ CutEven ends F),
      |(∑ A : Finset β, ∏ e ∈ F, signCross ends A e) * ((∏ e ∈ F, γ e) * ∏ e ∈ E \ F, α e)| = 0 :=
    sum_eq_zero fun F hF => by
      rw [sum_prod_signCross_eq_zero ends (mem_filter.1 hF).2, zero_mul, abs_zero]
  rw [hzero, add_zero]
  refine sum_le_sum fun F _ => ?_
  rw [abs_mul, abs_mul, abs_prod, abs_prod]
  have h1 : |∑ A : Finset β, ∏ e ∈ F, signCross ends A e| ≤ 2 ^ Fintype.card β := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp_rw [abs_prod_signCross]
    rw [sum_const, card_univ, nsmul_eq_mul, mul_one, hcard]
  have h2 : 0 ≤ (∏ e ∈ F, |γ e|) * ∏ e ∈ E \ F, |α e| :=
    mul_nonneg (prod_nonneg fun _ _ => abs_nonneg _) (prod_nonneg fun _ _ => abs_nonneg _)
  calc |∑ A : Finset β, ∏ e ∈ F, signCross ends A e| *
        ((∏ e ∈ F, |γ e|) * ∏ e ∈ E \ F, |α e|)
      ≤ 2 ^ Fintype.card β * ((∏ e ∈ F, |γ e|) * ∏ e ∈ E \ F, |α e|) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

end Parity

end Limits

end MultipoleBKT

end
