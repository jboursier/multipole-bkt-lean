/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Weighted

/-!
# The weighted lower event with its stable-pair constraints

See (A.15) and
(A.16). The box and stable constraints are retained in
this weight. A cutoff at least `2λ` is automatic on the event.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral.RouteChain

open MeasureTheory Set Finset
open scoped ENNReal Classical
open TwoComponentCoulomb (box)

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- All the stable-pair constraints, in the original label order. -/
def Stable (c : ι → ℂ × ℂ) : Prop := ∀ i j, i < j → IsStableDipolePair (c i) (c j)

theorem measurableSet_stable : MeasurableSet {c : ι → ℂ × ℂ | Stable c} := by
  unfold Stable
  apply measurable_forall (p := fun i (c : ι → ℂ × ℂ) => ∀ j, i < j → IsStableDipolePair (c i) (c j))
  intro i
  apply measurable_forall (p := fun j (c : ι → ℂ × ℂ) => i < j → IsStableDipolePair (c i) (c j))
  intro j
  by_cases h : i < j
  · simp only [h, true_implies]
    exact measurableSet_setOf_isStableDipolePair i j
  · simp only [h, false_implies, ofPred_true]
    exact MeasurableSet.univ

/-- The exact weight on the right of (A.15), including the box. -/
noncomputable def supportWeight (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) (σ : ι ≃ Fin k)
    (c : ι → ℂ × ℂ) : ℝ≥0∞ :=
  {c | c ∈ univ.pi (fun _ : ι => box N ×ˢ box N) ∧ Event lam σ c ∧ Stable c}.indicator
    (radialWeight χ β lam) c

theorem measurable_supportWeight {χ : ℂ → ℝ} (hχ : IsMollifier χ) {lam : ℝ} (hlam : 0 < lam)
    (N : ℕ) (β : ℝ) (σ : ι ≃ Fin k) : Measurable (supportWeight χ N β lam σ) :=
  (measurable_radialWeight hχ hlam β).indicator
    ((measurableSet_pi_box_prod N).inter ((measurableSet_event lam σ).inter measurableSet_stable))

omit [Fintype ι] [LinearOrder ι] in
/-- The path links on `𝒞` imply the connected-cluster constraint. -/
theorem Event.connected {lam M : ℝ} (hlam : 0 < lam) (hM : 4 ≤ M)
    {σ : ι ≃ Fin k} {c : ι → ℂ × ℂ} (hc : Event lam σ c) (root : ι) :
    (SimpleGraph.fromRel fun i j : ι => MultipoleLinked M lam (c i) (c j)).Connected := by
  apply connected_of_chain σ (Nat.zero_lt_of_lt (σ root).2)
  intro i j hij
  refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨fun h => by rw [h] at hij; omega, Or.inl ?_⟩
  have hd := hc.parent_linked hlam (Or.inl hij)
  unfold MultipoleLinked at hd ⊢
  exact hd.trans (mul_le_mul_of_nonneg_right hM (by positivity))

omit [Fintype ι] [LinearOrder ι] in
/-- The one-dipole lower weight on `𝒞`. -/
theorem Event.density_lower {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) {σ : ι ≃ Fin k} {c : ι → ℂ × ℂ}
    (hc : Event lam σ c) (i : ι) :
    (4 * lam) ^ (-β) ≤ Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) := by
  have h1 := neg_log_add_le_smearedKernel hχ hlam ((c i).1 - (c i).2)
  have h3 : Real.log (‖(c i).1 - (c i).2‖ + 2 * lam) ≤ Real.log (4 * lam) :=
    Real.log_le_log (by positivity) (by linarith [(hc.1 i).2])
  rw [Real.rpow_def_of_pos (by positivity : 0 < 4 * lam)]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The prescribed chain gives the weighted comparison needed for (A.15). -/
theorem chainWeight_le_support {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) (σ : ι ≃ Fin k) (root : ι) (hroot : (σ root : ℕ) = 0)
    (N : ℕ) (c : ι → ℂ × ℂ) :
    ENNReal.ofReal (((4 * lam) ^ (-β)) ^ Fintype.card ι) *
        chainWeight lam σ root (innerBox N (5 * k * lam)) c ≤ supportWeight χ N β lam σ c := by
  by_cases hz : chainWeight lam σ root (innerBox N (5 * k * lam)) c = 0
  · rw [hz, mul_zero]; exact zero_le
  have hc := chain_of_weight_ne_zero hz
  have he := hc.event hlam hroot
  rw [supportWeight, indicator_of_mem (show c ∈ {c | c ∈ univ.pi (fun _ : ι => box N ×ˢ box N) ∧
    Event lam σ c ∧ Stable c} from ⟨Set.mem_univ_pi.mpr (hc.mem_box hlam hroot), he,
      fun i j hij => hc.stable hlam hroot hij.ne⟩)]
  calc _ ≤ ENNReal.ofReal (((4 * lam) ^ (-β)) ^ Fintype.card ι) * 1 :=
      mul_le_mul' le_rfl (chainWeight_le_one lam σ root _ c)
    _ = ∏ _i : ι, ENNReal.ofReal ((4 * lam) ^ (-β)) := by
      rw [prod_const, card_univ, ENNReal.ofReal_pow (by positivity), mul_one]
    _ ≤ _ := prod_le_prod fun i _ => ENNReal.ofReal_le_ofReal (he.density_lower hχ hβ hlam i)

/-- The weighted chain mass (A.15), with its independent endpoint-ball factors. -/
theorem support_mass_lower {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) (σ : ι ≃ Fin k) (root : ι) (hroot : (σ root : ℕ) = 0)
    (N : ℕ) (hN : 4 * (5 * k * lam) ≤ Real.sqrt N) :
    ENNReal.ofReal (((4 * lam) ^ (-β)) ^ Fintype.card ι) *
      (ENNReal.ofReal (N / 4) * ENNReal.ofReal (Real.pi * (lam / 16) ^ 2) ^ (2 * k - 1)) ≤
        ∫⁻ c, supportWeight χ N β lam σ c := by
  calc _ ≤ ENNReal.ofReal (((4 * lam) ^ (-β)) ^ Fintype.card ι) *
        ∫⁻ c, chainWeight lam σ root (innerBox N (5 * k * lam)) c :=
      mul_le_mul' le_rfl (chain_volume_lower hlam σ root N hN)
    _ = ∫⁻ c, ENNReal.ofReal (((4 * lam) ^ (-β)) ^ Fintype.card ι) *
        chainWeight lam σ root (innerBox N (5 * k * lam)) c :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ _ := lintegral_mono (chainWeight_le_support hχ hβ hlam σ root hroot N)

/-- Forgetting box and stable constraints only increases the weight. -/
theorem supportWeight_le_event (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) (σ : ι ≃ Fin k)
    (c : ι → ℂ × ℂ) : supportWeight χ N β lam σ c ≤ eventWeight χ β lam σ c := by
  unfold supportWeight eventWeight
  by_cases hc : c ∈ univ.pi (fun _ : ι => box N ×ˢ box N) ∧ Event lam σ c ∧ Stable c
  · rw [indicator_of_mem (show c ∈ {c | c ∈ univ.pi (fun _ : ι => box N ×ˢ box N) ∧ Event lam σ c ∧ Stable c} from hc), indicator_of_mem (show c ∈ {c | Event lam σ c} from hc.2.1)]
  · rw [indicator_of_notMem (show c ∉ {c | c ∈ univ.pi (fun _ : ι => box N ×ˢ box N) ∧ Event lam σ c ∧ Stable c} from hc)]; exact zero_le

end MultipoleBKT.MultipoleIntegral.RouteChain

end
