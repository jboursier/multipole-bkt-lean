/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Volume
import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.SpatialAssembly

/-!
# Weighted integration on the full lower event

See (A.16). Root the prescribed path at any chosen dipole. Use the
four endpoint sectors and the corresponding Jacobian-one tree coordinates.
The radii are bounded by `2λ`, so each remaining integral has scale `λ²`.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral.RouteChain

open MeasureTheory Set Finset
open scoped ENNReal Classical

variable {ι : Type*} [Fintype ι] {k : ℕ}

/-- The Boltzmann weight of the individual dipoles. -/
noncomputable def radialWeight (χ : ℂ → ℝ) (β lam : ℝ) (c : ι → ℂ × ℂ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))

/-- The paper's weighted lower event, before stable and box restrictions. -/
noncomputable def eventWeight (χ : ℂ → ℝ) (β lam : ℝ) (σ : ι ≃ Fin k)
    (c : ι → ℂ × ℂ) : ℝ≥0∞ :=
  {c | Event lam σ c}.indicator (radialWeight χ β lam) c

/-- Measurability of a finite conjunction written as a predicate. -/
theorem measurable_forall {α : Type*} [MeasurableSpace α] {p : ι → α → Prop}
    (hp : ∀ i, MeasurableSet {x | p i x}) : MeasurableSet {x | ∀ i, p i x} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter hp

theorem measurableSet_event (lam : ℝ) (σ : ι ≃ Fin k) : MeasurableSet {c | Event lam σ c} := by
  change MeasurableSet {c : ι → ℂ × ℂ |
    (∀ i, lam < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ < 2 * lam) ∧
      ∀ i j, (σ j : ℕ) = σ i + 1 → 2 * lam < dipoleDist (c i) (c j) ∧ dipoleDist (c i) (c j) < 4 * lam}
  apply MeasurableSet.inter
  · exact measurable_forall fun i =>
      (measurableSet_lt (f := fun _ : ι → ℂ × ℂ => lam) measurable_const
        (by fun_prop : Measurable (fun c : ι → ℂ × ℂ => ‖(c i).1 - (c i).2‖))).inter
        (measurableSet_lt (by fun_prop : Measurable (fun c : ι → ℂ × ℂ => ‖(c i).1 - (c i).2‖)) measurable_const)
  · apply measurable_forall
    intro i
    apply measurable_forall
    intro j
    by_cases h : (σ j : ℕ) = σ i + 1
    · simp only [h, true_implies]
      exact (measurableSet_lt measurable_const (by unfold dipoleDist; fun_prop : Measurable (fun c : ι → ℂ × ℂ => dipoleDist (c i) (c j)))).inter
        (measurableSet_lt (by unfold dipoleDist; fun_prop : Measurable (fun c : ι → ℂ × ℂ => dipoleDist (c i) (c j))) measurable_const)
    · simp only [h, false_implies, ofPred_true]
      exact MeasurableSet.univ

theorem measurable_radialWeight {χ : ℂ → ℝ} (hχ : IsMollifier χ) {lam : ℝ} (hlam : 0 < lam)
    (β : ℝ) : Measurable (radialWeight (ι := ι) χ β lam) := by
  exact Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
    (((continuous_exp_smearedKernel_sub hχ hlam β).comp (continuous_apply i)).measurable)

theorem measurable_eventWeight {χ : ℂ → ℝ} (hχ : IsMollifier χ) {lam : ℝ} (hlam : 0 < lam)
    (β : ℝ) (σ : ι ≃ Fin k) : Measurable (eventWeight χ β lam σ) :=
  (measurable_radialWeight hχ hlam β).indicator (measurableSet_event lam σ)

omit [Fintype ι] in
/-- Orient the prescribed path towards an arbitrary root. -/
theorem exists_path_parent (σ : ι ≃ Fin k) (root : ι) :
    ∃ par : ι → ι, IsParentMap root par ∧ ∀ i, i ≠ root →
      (σ (par i) : ℕ) = σ i + 1 ∨ (σ i : ℕ) = σ (par i) + 1 := by
  let G := SimpleGraph.fromRel fun i j : ι => (σ j : ℕ) = σ i + 1
  have hconn : G.Connected := by
    apply connected_of_chain σ (Nat.zero_lt_of_lt (σ root).2)
    intro i j hij
    exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨fun h => by rw [h] at hij; omega, Or.inl hij⟩
  obtain ⟨par, hp, ha⟩ := exists_parent_of_connected hconn root
  exact ⟨par, hp, fun i hi => ((SimpleGraph.fromRel_adj _ _ _).mp (ha i hi)).2⟩

omit [Fintype ι] in
/-- The full event forces the links on any orientation of its path. -/
theorem Event.parent_linked {lam : ℝ} (_hlam : 0 < lam) {σ : ι ≃ Fin k}
    {c : ι → ℂ × ℂ} (hc : Event lam σ c) {i j : ι}
    (hij : (σ j : ℕ) = σ i + 1 ∨ (σ i : ℕ) = σ j + 1) :
    MultipoleLinked 4 lam (c i) (c j) := by
  have hd : dipoleDist (c i) (c j) < 4 * lam := by
    rcases hij with h | h
    · exact (hc.2 i j h).2
    · rw [dipoleDist_comm]
      exact (hc.2 j i h).2
  change dipoleDist (c i) (c j) ≤ _
  have hm : lam ≤ min (max ‖(c i).1 - (c i).2‖ lam) (max ‖(c j).1 - (c j).2‖ lam) :=
    le_min (le_max_right _ _) (le_max_right _ _)
  linarith

/-- The endpoint ball area used below. -/
theorem volume_closedBall_eq (z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (Metric.closedBall z ρ) = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
  rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hρ, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- Weighted `𝒞` with a constrained negative root. The right side is
`|B| C_{β,k} λ^{(4-β)k-2}`, displayed as its separate radial and spatial factors. -/
theorem lintegral_event_root_le {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) (σ : ι ≃ Fin k) (root : ι)
    {B : Set ℂ} (hB : MeasurableSet B) :
    ∫⁻ c, B.indicator (1 : ℂ → ℝ≥0∞) (c root).2 * eventWeight χ β lam σ c ≤
      volume B * ENNReal.ofReal (256 * Real.pi * lam ^ 2) ^ (Fintype.card ι - 1) *
        (ENNReal.ofReal (Real.exp (β * kernelConst χ) * lam ^ (-β)) *
          ENNReal.ofReal (4 * Real.pi * lam ^ 2)) ^ Fintype.card ι := by
  obtain ⟨par, hpar, ha⟩ := exists_path_parent σ root
  let U := ENNReal.ofReal (Real.exp (β * kernelConst χ) * lam ^ (-β))
  let R (r : ι → ℂ) := ∏ i, (Metric.closedBall (0 : ℂ) (2 * lam)).indicator
    (fun _ : ℂ => U) (r i)
  have hRm : Measurable R := Finset.measurable_prod _ fun i _ =>
    (measurable_const.indicator measurableSet_closedBall).comp (measurable_pi_apply i)
  let H (r y : ι → ℂ) := B.indicator (1 : ℂ → ℝ≥0∞) (y root) *
    ∏ i ∈ univ.erase root, (if MultipoleLinked 4 lam (y i + r i, y i)
      (y (par i) + r (par i), y (par i)) then (1 : ℝ≥0∞) else 0)
  have hHm (r : ι → ℂ) : Measurable (H r) := by
    refine ((measurable_const.indicator hB).comp (measurable_pi_apply root)).mul ?_
    apply Finset.measurable_prod
    intro i _
    exact (Measurable.ite (measurableSet_multipoleLinked 4 lam) measurable_const measurable_const).comp
      (f := fun y : ι → ℂ => ((y i + r i, y i), (y (par i) + r (par i), y (par i)))) (by fun_prop)
  have hpt (r y : ι → ℂ) :
      B.indicator (1 : ℂ → ℝ≥0∞) (y root) * eventWeight χ β lam σ (fun i => (y i + r i, y i)) ≤ R r * H r y := by
    by_cases hy : y root ∈ B
    · rw [indicator_of_mem hy, Pi.one_apply, one_mul]
      by_cases hc : Event lam σ (fun i => (y i + r i, y i))
      · rw [eventWeight, indicator_of_mem (show (fun i => (y i + r i, y i)) ∈ {c | Event lam σ c} from hc)]
        have he : H r y = 1 := by
          dsimp [H]
          rw [indicator_of_mem hy]
          simp only [Pi.one_apply, one_mul]
          apply prod_eq_one
          intro i hi
          rw [ite_eq_left (hc.parent_linked hlam (ha i (mem_erase.mp hi).1))]
        rw [he, mul_one]
        unfold radialWeight R
        apply prod_le_prod
        intro i _
        have hr := (hc.1 i).2
        simp only [add_sub_cancel_left] at hr ⊢
        rw [indicator_of_mem (show r i ∈ Metric.closedBall (0 : ℂ) (2 * lam) by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hr.le)]
        apply ENNReal.ofReal_le_ofReal
        exact (exp_smearedKernel_le hχ hβ hlam _).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hlam (le_max_right _ _) (by linarith)) (Real.exp_pos _).le)
      · rw [eventWeight, indicator_of_notMem (show (fun i => (y i + r i, y i)) ∉ {c | Event lam σ c} from hc)]
        exact zero_le
    · rw [indicator_of_notMem hy, zero_mul]
      exact zero_le
  have hsp (r : ι → ℂ) (hr : ∀ i, ‖r i‖ ≤ 2 * lam) :
      ∫⁻ y, H r y ≤ volume B * ENNReal.ofReal (256 * Real.pi * lam ^ 2) ^ (Fintype.card ι - 1) := by
    refine (lintegral_links_parent_le hpar 4 lam r hB).trans ?_
    have hb (i : ι) : volume (Metric.closedBall (0 : ℂ)
        (4 * min (max ‖r i‖ lam) (max ‖r (par i)‖ lam))) ≤
        ENNReal.ofReal (64 * Real.pi * lam ^ 2) := by
      rw [volume_closedBall_eq _ (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hm : min (max ‖r i‖ lam) (max ‖r (par i)‖ lam) ≤ 2 * lam :=
        (min_le_left _ _).trans (max_le (hr i) (by linarith))
      have hm0 : 0 ≤ min (max ‖r i‖ lam) (max ‖r (par i)‖ lam) := by positivity
      calc _ ≤ Real.pi * (4 * (2 * lam)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left hm (by norm_num)) 2) Real.pi_pos.le
        _ = _ := by ring

    calc _ ≤ (4 : ℝ≥0∞) ^ (Fintype.card ι - 1) *
          (volume B * ∏ _i ∈ univ.erase root, ENNReal.ofReal (64 * Real.pi * lam ^ 2)) := by
          gcongr with i _
          exact hb i
      _ = _ := by
        rw [prod_const, card_erase_of_mem (mem_univ root), card_univ]
        have he : ENNReal.ofReal (256 * Real.pi * lam ^ 2) = 4 * ENNReal.ofReal (64 * Real.pi * lam ^ 2) := by
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
        rw [he, mul_pow]
        ring
  have hinner (r : ι → ℂ) : ∫⁻ y, R r * H r y ≤
      R r * (volume B * ENNReal.ofReal (256 * Real.pi * lam ^ 2) ^ (Fintype.card ι - 1)) := by
    rw [lintegral_const_mul _ (hHm r)]
    by_cases hr : ∀ i, ‖r i‖ ≤ 2 * lam
    · exact mul_le_mul' le_rfl (hsp r hr)
    · push Not at hr
      obtain ⟨i, hi⟩ := hr
      have hz : R r = 0 := prod_eq_zero (mem_univ i) (indicator_of_notMem (by
        rw [Metric.mem_closedBall, dist_zero_right]; exact not_le.mpr hi) _)
      rw [hz, zero_mul, zero_mul]
  have hrint : ∫⁻ r, R r = (U * ENNReal.ofReal (4 * Real.pi * lam ^ 2)) ^ Fintype.card ι := by
    rw [lintegral_pi_prod_eq _ (fun _ => measurable_const.indicator measurableSet_closedBall)]
    have hv : ∀ i : ι, (∫⁻ t : ℂ, (Metric.closedBall (0 : ℂ) (2 * lam)).indicator (fun _ : ℂ => U) t) =
        U * ENNReal.ofReal (4 * Real.pi * lam ^ 2) := by
      intro i
      rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const, volume_closedBall_eq _ (by positivity)]
      congr 2
      ring
    have he : (∫⁻ t : ℂ, (Metric.closedBall (0 : ℂ) (2 * lam)).indicator (fun _ : ℂ => U) t) =
        U * ENNReal.ofReal (4 * Real.pi * lam ^ 2) := hv root
    rw [he, prod_const, card_univ]
  have hF : Measurable (fun c : ι → ℂ × ℂ =>
      B.indicator (1 : ℂ → ℝ≥0∞) (c root).2 * eventWeight χ β lam σ c) :=
    ((measurable_const.indicator hB).comp (by fun_prop)).mul (measurable_eventWeight hχ hlam β σ)
  rw [lintegral_dipole_coords hF]
  calc _ ≤ ∫⁻ r : ι → ℂ, ∫⁻ y : ι → ℂ, R r * H r y := lintegral_mono fun r => lintegral_mono (hpt r)
    _ ≤ ∫⁻ r : ι → ℂ, R r * (volume B * ENNReal.ofReal (256 * Real.pi * lam ^ 2) ^ (Fintype.card ι - 1)) :=
      lintegral_mono hinner
    _ = _ := by rw [lintegral_mul_const _ hRm, hrint]; ring

end MultipoleBKT.MultipoleIntegral.RouteChain

end
