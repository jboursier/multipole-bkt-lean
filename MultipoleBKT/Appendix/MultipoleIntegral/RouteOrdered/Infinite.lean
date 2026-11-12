/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Reduction
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Scaling

/-!
# Infinite cutoff and singleton compatibility

See (A.13) and (A.14). Exhaust the vector space by finite radial cutoffs. The
singleton interface reduces to the one-radius integral with no inner factor.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set Finset
open scoped ENNReal Classical

variable {ι : Type*} [Fintype ι]

/-- Increasing finite radial cutoffs exhaust a finite configuration. -/
theorem lintegral_le_of_radial_cutoffs {F : (ι → ℂ) → ℝ≥0∞}
    (hF : Measurable F) {K : ℝ≥0∞}
    (hbound : ∀ h : ℝ, ∫⁻ x : ι → ℂ,
      {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h}.indicator F x ≤ K) :
    ∫⁻ x, F x ≤ K := by
  let D (n : ℕ) := {x : ι → ℂ | ∀ i, ‖x i‖ ≤ n}
  have hD : ∀ n, MeasurableSet (D n) := by
    intro n
    simp only [D, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (measurable_pi_apply i).norm measurable_const
  have hcover : ∀ x : ι → ℂ, ∃ n : ℕ, x ∈ D n := by
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (∑ i, ‖x i‖)
    exact ⟨n, fun i => (single_le_sum (fun j _ => norm_nonneg (x j)) (mem_univ i)).trans hn.le⟩
  have heq : F = fun x => ⨆ n : ℕ, (D n).indicator F x := by
    funext x
    obtain ⟨n, hn⟩ := hcover x
    apply le_antisymm
    · exact le_iSup_of_le n (by rw [indicator_of_mem hn])
    · exact iSup_le fun n => indicator_le_self _ _ x
  conv_lhs => rw [heq]
  rw [lintegral_iSup (fun n => hF.indicator (hD n))]
  · exact iSup_le fun n => hbound n
  · intro n m hnm x
    dsimp only
    by_cases hx : x ∈ D n
    · have hy : x ∈ D m := fun i => (hx i).trans (Nat.cast_le.mpr hnm)
      rw [indicator_of_mem hx, indicator_of_mem hy]
    · rw [indicator_of_notMem hx]
      exact zero_le

/-- Measurability of the exact tree-minimum radial weight. -/
theorem measurable_tree_radial_weight (T : SimpleGraph ι) (β : ℝ)
    {lam : ℝ} (hlam : 0 < lam) :
    Measurable fun x : ι → ℂ => ENNReal.ofReal
      (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
        ∏ i, ENNReal.ofReal (max ‖x i‖ lam ^ (-β)) := by
  refine (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun e _ => ?_)).mul ?_
  · induction e using Sym2.inductionOn with
    | _ i j =>
      exact (((measurable_pi_apply i : Measurable (fun x : ι → ℂ => x i)).norm.min
        (measurable_pi_apply j).norm).max measurable_const).pow_const 2
  · exact Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      (((continuous_apply i).norm.max continuous_const).rpow_const
        (fun x => Or.inl (lt_max_of_lt_right hlam).ne')).measurable

variable [DecidableEq ι]

/-- The polar tree bound with infinite cutoff. It also holds for one
vertex, where the inner moment has exponent zero. -/
theorem lintegral_tree_radial_infinite_le [Nonempty ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {lam : ℝ} (hlam : 0 < lam) (β : ℝ) :
    ∫⁻ x : ι → ℂ, ENNReal.ofReal
      (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
        ∏ i, ENNReal.ofReal (max ‖x i‖ lam ^ (-β)) ≤
      (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
        orderedRadial β lam (Ioi 0) (Fintype.card ι - 1) := by
  apply lintegral_le_of_radial_cutoffs (measurable_tree_radial_weight T β hlam)
  intro h
  refine (lintegral_tree_radial_le hT hlam β h).trans ?_
  apply mul_le_mul' le_rfl
  exact lintegral_mono_set Ioc_subset_Ioi_self

/-- The infinite-cutoff tree bound with the smoothed kernel weights. -/
theorem lintegral_tree_smoothed_infinite_le [Nonempty ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {χ : ℂ → ℝ} (hχ : IsMollifier χ) {lam β : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β) :
    ∫⁻ x : ι → ℂ, ENNReal.ofReal
      (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
        ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (x i))) ≤
      ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ Fintype.card ι *
        ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
          orderedRadial β lam (Ioi 0) (Fintype.card ι - 1)) := by
  have hm : Measurable fun x : ι → ℂ => ENNReal.ofReal
      (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
        ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (x i))) := by
    refine (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun e _ => ?_)).mul ?_
    · induction e using Sym2.inductionOn with
      | _ i j => exact (((measurable_pi_apply i : Measurable (fun x : ι → ℂ => x i)).norm.min
          (measurable_pi_apply j).norm).max measurable_const).pow_const 2
    · exact Finset.measurable_prod _ fun i _ =>
        (ENNReal.measurable_ofReal.comp (measurable_exp_smearedKernel hχ hlam β)).comp
          (measurable_pi_apply i)
  apply lintegral_le_of_radial_cutoffs hm
  intro h
  refine (lintegral_tree_smoothed_le hT hχ hlam hβ h).trans ?_
  apply mul_le_mul' le_rfl
  apply mul_le_mul' le_rfl
  exact lintegral_mono_set Ioc_subset_Ioi_self

/-- The singleton radial coefficient is finite for every `β > 2`. -/
theorem orderedRadial_singleton_ne_top {β lam : ℝ} (hβ : 2 < β) (hlam : 0 < lam) :
    orderedRadial β lam (Ioi 0) 0 ≠ ⊤ := by
  have hi := (integrable_fun_norm_complex_iff (fun r : ℝ => max r lam ^ (-β))).mp
    (integrable_max_norm_rpow hlam (by linarith : -β < -2))
  have hi' : IntegrableOn (fun r : ℝ => r * max r lam ^ (-β)) (Ioi 0) := by
    simpa only [mul_comm] using hi
  unfold orderedRadial
  simp only [pow_zero, mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal hi']
  · exact ENNReal.ofReal_ne_top
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun r hr =>
        mul_nonneg hr.le (Real.rpow_nonneg (le_max_of_le_right hlam.le) _))

/-- Exact infinite-cutoff scaling with a finite real coefficient. Its
finiteness uses the separate temperature regimes, including the singleton. -/
theorem orderedRadial_eq_unit_coefficient {β lam : ℝ} (hβ : 2 < β)
    {k : ℕ} (hk : 1 ≤ k) (hE : (4 - β) * k - 2 < 0) (hlam : 0 < lam) :
    orderedRadial β lam (Ioi 0) (k - 1) =
      ENNReal.ofReal (lam ^ ((4 - β) * k - 2)) *
        ENNReal.ofReal (orderedRadial β 1 (Ioi 0) (k - 1)).toReal := by
  have hfin : orderedRadial β 1 (Ioi 0) (k - 1) ≠ ⊤ := by
    by_cases hk2 : 2 ≤ k
    · exact orderedRadial_infinite_ne_top hβ hk2 hE (by norm_num)
    · have hk1 : k = 1 := by omega
      subst k
      exact orderedRadial_singleton_ne_top hβ (by norm_num)
  rw [ENNReal.ofReal_toReal hfin, orderedRadial_scale_infinite hlam]
  congr 2
  rw [Nat.cast_sub hk]
  push_cast
  ring_nf

end MultipoleBKT.MultipoleIntegral

end
