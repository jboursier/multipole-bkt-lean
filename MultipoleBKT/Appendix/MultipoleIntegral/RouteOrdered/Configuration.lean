/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Weight
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.TreeAssembly
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Infinite
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Gamma
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Connected configurations in endpoint tree coordinates

See (A.6) through
(A.14). The connected weight is reduced to actual-tree
integrals by the measurable endpoint cover and the tree-coordinate map.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {ι : Type*} [Fintype ι]
variable {χ : ℂ → ℝ} {lam β M : ℝ}

open scoped Classical

/-- The exact minimum-radius tree weight after integrating positions. -/
noncomputable def treeDipoleWeight (T : SimpleGraph ι) (χ : ℂ → ℝ) (β lam : ℝ)
    (r : ι → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ e ∈ T.edgeFinset,
    edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e) *
      ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (r i)))

theorem measurable_treeDipoleWeight (T : SimpleGraph ι) (hχ : IsMollifier χ)
    (hlam : 0 < lam) (β : ℝ) : Measurable (treeDipoleWeight T χ β lam) := by
  refine (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun e _ => ?_)).mul ?_
  · induction e using Sym2.inductionOn with
    | _ i j => exact (((measurable_pi_apply i : Measurable (fun x : ι → ℂ => x i)).norm.min
        (measurable_pi_apply j).norm).max measurable_const).pow_const 2
  · exact Finset.measurable_prod _ fun i _ =>
      (ENNReal.measurable_ofReal.comp (measurable_exp_smearedKernel hχ hlam β)).comp
        (measurable_pi_apply i)

/-- The position fiber of the connected configuration integral, with
the exact tree minimum retained. This is (A.6)–(A.11) before polar integration. -/
theorem lintegral_connectedWeight_fiber_le (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (N : ℕ) (r : ι → ℂ) (root : ι) :
    ∫⁻ y : ι → ℂ, connectedWeight χ N β lam M (fun i => (y i + r i, y i)) ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
          treeDipoleWeight T χ β lam r := by
  let w := ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (r i)))
  let G (y : ι → ℂ) := SimpleGraph.fromRel fun i j =>
    MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)
  have hpt (y : ι → ℂ) : connectedWeight χ N β lam M (fun i => (y i + r i, y i)) ≤
      w * ((box N).indicator (1 : ℂ → ℝ≥0∞) (y root) *
        (if (G y).Connected then (1 : ℝ≥0∞) else 0)) := by
    unfold connectedWeight
    by_cases hc : (fun i => (y i + r i, y i)) ∈ Set.univ.pi fun _ : ι => box N ×ˢ box N
    · rw [indicator_of_mem hc]
      have hy : y root ∈ box N := (Set.mem_univ_pi.mp hc root).2
      rw [indicator_of_mem hy]
      simp only [add_sub_cancel_left, Pi.one_apply, one_mul]
      dsimp only [w, G]
      split_ifs <;> simp only [one_mul, mul_one, zero_mul, mul_zero, le_refl]
    · rw [indicator_of_notMem hc]
      exact zero_le
  calc
    _ ≤ ∫⁻ y : ι → ℂ, w * ((box N).indicator (1 : ℂ → ℝ≥0∞) (y root) *
        (if (G y).Connected then (1 : ℝ≥0∞) else 0)) := lintegral_mono hpt
    _ = w * ∫⁻ y : ι → ℂ, (box N).indicator (1 : ℂ → ℝ≥0∞) (y root) *
        (if (G y).Connected then (1 : ℝ≥0∞) else 0) :=
      lintegral_const_mul' _ _ (ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top)
    _ ≤ w * (volume (box N) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
          ENNReal.ofReal (∏ e ∈ T.edgeFinset,
            edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e)) := by
      apply mul_le_mul' le_rfl
      have ht := lintegral_connected_positions_tree_le hM hlam r root
        (TwoComponentCoulomb.measurableSet_box N)
      convert ht using 1
    _ = _ := by
      rw [TwoComponentCoulomb.volume_box]
      simp only [treeDipoleWeight, ← sum_mul]
      dsimp only [w]
      ring

/-- The connected configuration integral is bounded by the sum of
actual-tree radial integrals. `H` retains any measurable radial cutoff. -/
theorem lintegral_connectedWeight_radial_reduction [Nonempty ι]
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 0 ≤ M) (N : ℕ)
    (H : (ι → ℂ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ c : ι → ℂ × ℂ, H (fun i => (c i).1 - (c i).2) * connectedWeight χ N β lam M c ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
          ∫⁻ r : ι → ℂ, H r * treeDipoleWeight T χ β lam r := by
  have hmeas : Measurable fun c : ι → ℂ × ℂ =>
      H (fun i => (c i).1 - (c i).2) * connectedWeight χ N β lam M c :=
    (hH.comp (by fun_prop)).mul (measurable_connectedWeight hχ hlam N β M)
  rw [lintegral_dipole_coords hmeas]
  simp only [add_sub_cancel_left]
  have hinner (r : ι → ℂ) : (∫⁻ y : ι → ℂ,
      H r * connectedWeight χ N β lam M (fun i => (y i + r i, y i))) =
      H r * ∫⁻ y : ι → ℂ, connectedWeight χ N β lam M (fun i => (y i + r i, y i)) := by
    apply lintegral_const_mul
    exact (measurable_connectedWeight hχ hlam N β M).comp
      (f := fun y : ι → ℂ => fun i => (y i + r i, y i)) (by fun_prop)
  simp_rw [hinner]
  let A := (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1)
  calc
    _ ≤ ∫⁻ r : ι → ℂ, H r * (A *
        ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
          treeDipoleWeight T χ β lam r) := by
      apply lintegral_mono
      intro r
      exact mul_le_mul' le_rfl (lintegral_connectedWeight_fiber_le hM hlam.le N r
        (Classical.choice ‹Nonempty ι›))
    _ = A * ∫⁻ r : ι → ℂ,
        ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
          H r * treeDipoleWeight T χ β lam r := by
      simp_rw [← mul_sum, mul_left_comm (H _) A]
      apply lintegral_const_mul
      exact hH.mul (Finset.measurable_sum _ fun T _ => measurable_treeDipoleWeight T hχ hlam β)
    _ = _ := by
      congr 1
      exact lintegral_finsetSum _ (fun T _ =>
        (hH.mul (measurable_treeDipoleWeight T hχ hlam β) :
          Measurable (fun r => H r * treeDipoleWeight T χ β lam r)))

/-- The full connected integral through tree counting and the ordered
infinite-cutoff polar integral. -/
theorem lintegral_connectedWeight_ordered_infinite_le [Nonempty ι]
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hM : 0 ≤ M) (N : ℕ) :
    ∫⁻ c : ι → ℂ × ℂ, connectedWeight χ N β lam M c ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ((Fintype.card ι ^ (Fintype.card ι - 2) : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ Fintype.card ι *
            ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
              orderedRadial β lam (Ioi 0) (Fintype.card ι - 1))) := by
  have hred := lintegral_connectedWeight_radial_reduction (ι := ι) (β := β) hχ hlam hM N (fun _ => 1) measurable_const
  simp only [one_mul] at hred
  refine hred.trans ?_
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∑ _T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
        ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ Fintype.card ι *
          ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
            orderedRadial β lam (Ioi 0) (Fintype.card ι - 1)) := by
      apply sum_le_sum
      intro T hT
      exact lintegral_tree_smoothed_infinite_le (mem_filter.mp hT).2 hχ hlam hβ
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_trees_eq_pow]

/-- The finite-cutoff counterpart of the connected ordered bound. -/
theorem lintegral_connectedWeight_ordered_cut_le [Nonempty ι]
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hM : 0 ≤ M) (N : ℕ) (h : ℝ) :
    ∫⁻ c : ι → ℂ × ℂ, {c : ι → ℂ × ℂ | ∀ i, ‖(c i).1 - (c i).2‖ ≤ h}.indicator
      (connectedWeight χ N β lam M) c ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ((Fintype.card ι ^ (Fintype.card ι - 2) : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ Fintype.card ι *
            ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
              orderedRadial β lam (Ioc 0 h) (Fintype.card ι - 1))) := by
  let D := {r : ι → ℂ | ∀ i, ‖r i‖ ≤ h}
  have hD : MeasurableSet D := by
    simp only [D, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).norm measurable_const
  have hred := lintegral_connectedWeight_radial_reduction (ι := ι) (β := β) hχ hlam hM N
    (D.indicator (1 : (ι → ℂ) → ℝ≥0∞)) (measurable_const.indicator hD)
  have hleft (c : ι → ℂ × ℂ) : D.indicator (1 : (ι → ℂ) → ℝ≥0∞)
      (fun i => (c i).1 - (c i).2) * connectedWeight χ N β lam M c =
      {c : ι → ℂ × ℂ | ∀ i, ‖(c i).1 - (c i).2‖ ≤ h}.indicator
        (connectedWeight χ N β lam M) c := by
    by_cases hc : ∀ i, ‖(c i).1 - (c i).2‖ ≤ h <;> simp [D, Set.indicator, hc]
  have hright (T : SimpleGraph ι) (r : ι → ℂ) :
      D.indicator (1 : (ι → ℂ) → ℝ≥0∞) r * treeDipoleWeight T χ β lam r =
        D.indicator (treeDipoleWeight T χ β lam) r := by
    by_cases hr : r ∈ D <;> simp [Set.indicator, hr]
  simp_rw [hleft, hright] at hred
  refine hred.trans ?_
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∑ _T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
        ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ Fintype.card ι *
          ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
            orderedRadial β lam (Ioc 0 h) (Fintype.card ι - 1)) := by
      apply sum_le_sum
      intro T hT
      exact lintegral_tree_smoothed_le (mem_filter.mp hT).2 hχ hlam hβ h
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_trees_eq_pow]

/-- The literal single-tree bound (A.14), with the gamma normalization
from (A.2). The cutoff may be finite even beyond the infinite-cutoff
size range. -/
theorem lintegral_tree_gamma [Nonempty ι] {T : SimpleGraph ι} (hT : T.IsTree)
    (hχ : IsMollifier χ) (hβ : 2 < β) (hk : 2 ≤ Fintype.card ι) (p₀ : ℕ)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ < 1 ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
        (∫⁻ r : ι → ℂ,
          {r : ι → ℂ | ∀ i, ‖r i‖ ≤ eps * truncationScale p₀ β lam}.indicator
            (treeDipoleWeight T χ β lam) r) ≤
          ENNReal.ofReal (C * (lam ^ ((2 - β) * Fintype.card ι) *
            Appendix.gammaBeta p₀ β lam (Fintype.card ι))) := by
  obtain ⟨C, hC, lam₀, hl0, hl1, hb⟩ := orderedRadial_gamma p₀ hβ hk heps heps1
  let A : ℝ := Real.exp (β * kernelConst χ) ^ Fintype.card ι *
    ((Fintype.card ι : ℝ) * (2 * Real.pi) ^ Fintype.card ι)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A * C, mul_pos hA hC, lam₀, hl0, hl1, fun lam hlam hle => ?_⟩
  have hbound := lintegral_tree_smoothed_le hT hχ hlam (by linarith : 0 ≤ β)
    (eps * truncationScale p₀ β lam)
  have heq : ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ Fintype.card ι *
      ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
        orderedRadial β lam (Ioc 0 (eps * truncationScale p₀ β lam)) (Fintype.card ι - 1)) =
      ENNReal.ofReal A *
        orderedRadial β lam (Ioc 0 (eps * truncationScale p₀ β lam)) (Fintype.card ι - 1) := by
    dsimp only [A]
    simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_natCast]
    ring
  rw [heq] at hbound
  refine hbound.trans ((mul_le_mul' le_rfl (hb lam hlam hle)).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul hA.le]
  congr 1
  ring

/-- The finite-cutoff configuration bound (A.14) after the tree and
endpoint sums, with the normalization supplied by (A.2). -/
theorem lintegral_connectedWeight_gamma [Nonempty ι] (hχ : IsMollifier χ)
    (hβ : 2 < β) (hM : 0 ≤ M) (hk : 2 ≤ Fintype.card ι) (p₀ : ℕ)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ < 1 ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ → ∀ N : ℕ,
        (∫⁻ c : ι → ℂ × ℂ,
          {c : ι → ℂ × ℂ | ∀ i, ‖(c i).1 - (c i).2‖ ≤ eps * truncationScale p₀ β lam}.indicator
            (connectedWeight χ N β lam M) c) ≤
          ENNReal.ofReal (C * N * (lam ^ ((2 - β) * Fintype.card ι) *
            Appendix.gammaBeta p₀ β lam (Fintype.card ι))) := by
  obtain ⟨C, hC, lam₀, hl0, hl1, hb⟩ := orderedRadial_gamma p₀ hβ hk heps heps1
  let A : ℝ := (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
    (Fintype.card ι ^ (Fintype.card ι - 2) : ℕ) *
      (Real.exp (β * kernelConst χ) ^ Fintype.card ι *
        ((Fintype.card ι : ℝ) * (2 * Real.pi) ^ Fintype.card ι))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨(A + 1) * C, mul_pos (by linarith) hC, lam₀, hl0, hl1,
    fun lam hlam hle N => ?_⟩
  have hbound := lintegral_connectedWeight_ordered_cut_le (ι := ι) hχ hlam
    (by linarith : 0 ≤ β) hM N (eps * truncationScale p₀ β lam)
  have hnum : (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
      ((Fintype.card ι ^ (Fintype.card ι - 2) : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ Fintype.card ι *
          ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
            orderedRadial β lam (Ioc 0 (eps * truncationScale p₀ β lam)) (Fintype.card ι - 1))) =
      ENNReal.ofReal (N * A) *
        orderedRadial β lam (Ioc 0 (eps * truncationScale p₀ β lam)) (Fintype.card ι - 1) := by
    dsimp only [A]
    simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_natCast]
    ring
  rw [hnum] at hbound
  refine hbound.trans ((mul_le_mul' le_rfl (hb lam hlam hle)).trans ?_)
  rw [← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hA)]
  apply ENNReal.ofReal_le_ofReal
  have htarget : 0 ≤ lam ^ ((2 - β) * Fintype.card ι) *
      Appendix.gammaBeta p₀ β lam (Fintype.card ι) := by
    rw [Appendix.gammaBeta]
    split_ifs <;> positivity
  calc
    _ = A * (N * C * (lam ^ ((2 - β) * Fintype.card ι) *
        Appendix.gammaBeta p₀ β lam (Fintype.card ι))) := by ring
    _ ≤ (A + 1) * (N * C * (lam ^ ((2 - β) * Fintype.card ι) *
        Appendix.gammaBeta p₀ β lam (Fintype.card ι))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end MultipoleBKT.MultipoleIntegral

end
