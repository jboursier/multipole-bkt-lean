/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Support
public import MultipoleBKT.Appendix.MultipoleIntegralZ.LowerBound
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Basic

/-!
# The weighted bad-neighbourhood loss

See (A.16). A failing dipole is close to a bad endpoint. Root the path
there, integrate that root over the bad neighbourhood, and integrate all
other tree coordinates with the dipole Boltzmann weights still present.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral.RouteChain

open MeasureTheory Set Finset Metric UpperBound MultipoleIntegralZ TheoremTwo
open scoped ENNReal Classical

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {k N p₀ : ℕ} {β lam M ε₀ : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

omit [Fintype ι] [LinearOrder ι] in
/-- A failing root on `𝒞` lies in one of the `2|V_bad|` balls with radius `(2M+2)λ`. -/
theorem bad_root_mem {σ : ι ≃ Fin k} {c : ι → ℂ × ℂ} (hc : Event lam σ c)
    (hlam : 0 < lam) (hM : 0 ≤ M) {i : ι} (hi : ¬ IsGoodZ p₀ β lam M ε₀ V Z (c i)) :
    (c i).2 ∈ badNbhd V Z ((2 * M + 2) * lam) := by
  obtain ⟨j, hj, hd⟩ := exists_near_of_not_isGoodZ hM hi
  have hr := (hc.1 i).2
  have hm : max ‖(c i).1 - (c i).2‖ lam ≤ 2 * lam := max_le hr.le (by linarith)
  have hd' : dipoleDist (c i) (Z j) ≤ 2 * M * lam := by
    have := mul_le_mul_of_nonneg_left hm hM
    linarith
  have key (a : ℂ) (ha : ‖(c i).1 - a‖ ≤ 2 * M * lam) :
      ‖(c i).2 - a‖ ≤ (2 * M + 2) * lam := by
    have := norm_sub_le_norm_sub_add_norm_sub (c i).2 (c i).1 a
    rw [norm_sub_rev (c i).2 (c i).1] at this
    nlinarith
  simp only [badNbhd, Set.mem_iUnion, Set.mem_union, mem_closedBall, dist_eq_norm]
  refine ⟨j, hj, ?_⟩
  unfold dipoleDist at hd'
  rcases min_le_iff.mp hd' with hd | hd <;> rcases min_le_iff.mp hd with hd | hd
  · exact Or.inl (key _ hd)
  · exact Or.inr (key _ hd)
  · exact Or.inl (by nlinarith)
  · exact Or.inr (by nlinarith)

/-- The weighted configurations removed by the good-point requirement. -/
noncomputable def badWeight (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (σ : ι ≃ Fin k)
    (c : ι → ℂ × ℂ) : ℝ≥0∞ :=
  {c | ¬ ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)}.indicator (supportWeight χ N β lam σ) c

/-- The first displayed union bound of the weighted subtraction proof. -/
theorem badWeight_le_sum (χ : ℂ → ℝ) (hlam : 0 < lam) (hM : 0 ≤ M)
    (σ : ι ≃ Fin k) (c : ι → ℂ × ℂ) :
    badWeight χ N p₀ β lam M ε₀ V Z σ c ≤
      ∑ i : ι, (badNbhd V Z ((2 * M + 2) * lam)).indicator (1 : ℂ → ℝ≥0∞) (c i).2 *
        eventWeight χ β lam σ c := by
  by_cases hg : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)
  · simp only [badWeight, indicator_of_notMem (show c ∉ {c | ¬ ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)} from not_not_intro hg)]
    exact zero_le
  rw [badWeight, indicator_of_mem (show c ∈ {c | ¬ ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)} from hg)]
  by_cases hc : c ∈ univ.pi (fun _ : ι => TwoComponentCoulomb.box N ×ˢ TwoComponentCoulomb.box N) ∧
      Event lam σ c ∧ Stable c
  · push Not at hg
    obtain ⟨i, hi⟩ := hg
    have hm := bad_root_mem hc.2.1 hlam hM hi
    have hs : supportWeight χ N β lam σ c ≤
        (badNbhd V Z ((2 * M + 2) * lam)).indicator (1 : ℂ → ℝ≥0∞) (c i).2 * eventWeight χ β lam σ c := by
      rw [indicator_of_mem hm, Pi.one_apply, one_mul]
      exact supportWeight_le_event χ N β lam σ c
    exact hs.trans (single_le_sum (f := fun i : ι => (badNbhd V Z ((2 * M + 2) * lam)).indicator (1 : ℂ → ℝ≥0∞) (c i).2 * eventWeight χ β lam σ c) (fun _ _ => zero_le) (mem_univ i))
  · rw [supportWeight, indicator_of_notMem (show c ∉ {c | c ∈ univ.pi (fun _ : ι => TwoComponentCoulomb.box N ×ˢ TwoComponentCoulomb.box N) ∧ Event lam σ c ∧ Stable c} from hc)]
    exact zero_le

/-- (A.16) with its spatial and radial factors kept visible. The power is
`|V_bad| λ² × λ^{(4-β)k-2}`. No root is excluded from the lower event beforehand. -/
theorem weighted_bad_neighborhood_le {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    (hβ : 0 ≤ β) (hlam : 0 < lam) (hM : 0 ≤ M) (σ : ι ≃ Fin k) :
    ∫⁻ c, badWeight χ N p₀ β lam M ε₀ V Z σ c ≤
      Fintype.card ι * ENNReal.ofReal (2 * V.card * Real.pi * ((2 * M + 2) * lam) ^ 2) *
        ENNReal.ofReal (256 * Real.pi * lam ^ 2) ^ (Fintype.card ι - 1) *
        (ENNReal.ofReal (Real.exp (β * kernelConst χ) * lam ^ (-β)) *
          ENNReal.ofReal (4 * Real.pi * lam ^ 2)) ^ Fintype.card ι := by
  let B := badNbhd V Z ((2 * M + 2) * lam)
  have hB := measurableSet_badNbhd V Z ((2 * M + 2) * lam)
  have hm (i : ι) : Measurable (fun c : ι → ℂ × ℂ =>
      B.indicator (1 : ℂ → ℝ≥0∞) (c i).2 * eventWeight χ β lam σ c) :=
    ((measurable_const.indicator hB).comp (by fun_prop)).mul (measurable_eventWeight hχ hlam β σ)
  calc _ ≤ ∫⁻ c : ι → ℂ × ℂ, ∑ i : ι,
        B.indicator (1 : ℂ → ℝ≥0∞) (c i).2 * eventWeight χ β lam σ c :=
      lintegral_mono (badWeight_le_sum χ hlam hM σ)
    _ = ∑ i : ι, ∫⁻ c : ι → ℂ × ℂ,
        B.indicator (1 : ℂ → ℝ≥0∞) (c i).2 * eventWeight χ β lam σ c :=
      lintegral_finsetSum _ (fun i _ => hm i)
    _ ≤ ∑ _i : ι, ENNReal.ofReal (2 * V.card * Real.pi * ((2 * M + 2) * lam) ^ 2) *
        ENNReal.ofReal (256 * Real.pi * lam ^ 2) ^ (Fintype.card ι - 1) *
        (ENNReal.ofReal (Real.exp (β * kernelConst χ) * lam ^ (-β)) *
          ENNReal.ofReal (4 * Real.pi * lam ^ 2)) ^ Fintype.card ι := by
      apply sum_le_sum
      intro i _
      exact (lintegral_event_root_le hχ hβ hlam σ i hB).trans
        (mul_le_mul' (mul_le_mul' (volume_badNbhd_le V Z (by positivity)) le_rfl) le_rfl)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

/-- Exact weighted subtraction, before applying the lower mass and upper loss estimates. -/
theorem weighted_subtraction (χ : ℂ → ℝ) (hχ : IsMollifier χ) (hlam : 0 < lam)
    (σ : ι ≃ Fin k) :
    (∫⁻ c, {c | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)}.indicator
      (supportWeight χ N β lam σ) c) +
        ∫⁻ c, badWeight χ N p₀ β lam M ε₀ V Z σ c =
          ∫⁻ c, supportWeight χ N β lam σ c := by
  have hs : MeasurableSet {c : ι → ℂ × ℂ | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)} :=
    measurable_forall fun i => (measurableSet_isGoodZ (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) (V := V) (Z := Z)).preimage (by fun_prop)
  rw [← lintegral_add_left ((measurable_supportWeight hχ hlam N β σ).indicator hs)]
  apply lintegral_congr
  intro c
  by_cases hc : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)
  · rw [indicator_of_mem (show c ∈ {c | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)} from hc),
      badWeight, indicator_of_notMem (show c ∉ {c | ¬ ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)} from not_not_intro hc), add_zero]
  · rw [indicator_of_notMem (show c ∉ {c | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)} from hc),
      badWeight, indicator_of_mem (show c ∈ {c | ¬ ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)} from hc), zero_add]

end MultipoleBKT.MultipoleIntegral.RouteChain

end
