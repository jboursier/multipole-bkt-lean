/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoReduce
public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneEstimates
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoIntegral.OrderedConstant

/-!
# Sharp high-beta leaf and ordered-core estimates

The paper: Lemma 5.41,
(5.140). Delete leaves until `p₀ + 1` vertices remain,
then integrate that terminal tree through its largest-radius sectors.
The normalized leaf gain `sourceEta` has a logarithm only at beta four.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open MeasureTheory Finset MultipoleIntegral
open scoped ENNReal

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

/-- The constant `κ` of the leaves: `1` for `β = 4`, `1 + 1/(β-4)` for `β > 4`. -/
noncomputable def leafConst (β : ℝ) : ℝ := if β = 4 then 1 else 1 + 1 / (β - 4)

theorem one_le_leafConst (hβ4 : 4 ≤ β) : 1 ≤ leafConst β := by
  unfold leafConst
  split_ifs with h
  · exact le_rfl
  · have : 0 < β - 4 := lt_of_le_of_ne (by linarith) (fun h' => h (by linarith))
    have : 0 < 1 / (β - 4) := by positivity
    linarith

/-- The leaf factor with a logarithm only at beta four. -/
noncomputable def leafSharp (χ : ℂ → ℝ) (β lam h : ℝ) : ℝ :=
  Real.exp (β * kernelConst χ) * (2 * Real.pi * leafConst β) * lam ^ (4 - β) *
    (if β = 4 then 1 + Real.log (h / lam) else 1)

/-- One leaf: `∫ max(|w|, λ)² 𝟙_{|w| ≤ h} e^{β g_λ(w)} dw ≤ B_h`. -/
theorem lintegral_leaf_le_sharp (hχ : IsMollifier χ) (hβ4 : 4 ≤ β) (hlam : 0 < lam) {h : ℝ}
    (hlh : lam ≤ h) :
    ∫⁻ w : ℂ, ENNReal.ofReal (max ‖w‖ lam ^ (2 : ℝ)) * cutFactor χ β lam h w ≤
      ENNReal.ofReal (leafSharp χ β lam h) := by
  have hβ : 0 ≤ β := by linarith
  have hpt : ∀ w : ℂ, ENNReal.ofReal (max ‖w‖ lam ^ (2 : ℝ)) * cutFactor χ β lam h w ≤
      ENNReal.ofReal (Real.exp (β * kernelConst χ)) *
        (Metric.closedBall (0 : ℂ) h).indicator
          (fun w => ENNReal.ofReal (max ‖w‖ lam ^ (2 - β))) w := by
    intro w
    unfold cutFactor
    by_cases hw : w ∈ Metric.closedBall (0 : ℂ) h
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hm : 0 < max ‖w‖ lam := lt_max_of_lt_right hlam
      calc max ‖w‖ lam ^ (2 : ℝ) * Real.exp (β * smearedKernel χ lam w)
          ≤ max ‖w‖ lam ^ (2 : ℝ) * (Real.exp (β * kernelConst χ) * max ‖w‖ lam ^ (-β)) :=
            mul_le_mul_of_nonneg_left (exp_smearedKernel_le hχ hβ hlam w)
              (Real.rpow_nonneg hm.le _)
        _ = Real.exp (β * kernelConst χ) * max ‖w‖ lam ^ (2 - β) := by
            rw [sub_eq_add_neg, Real.rpow_add hm]
            ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero, mul_zero]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hrad : ∫⁻ w : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun w => ENNReal.ofReal (max ‖w‖ lam ^ (2 - β))) w ≤
        ENNReal.ofReal (2 * Real.pi * leafConst β * lam ^ (4 - β) * (if β = 4 then 1 + Real.log (h / lam) else 1)) := by
    by_cases h4 : β = 4
    · subst h4
      have : (2 : ℝ) - 4 = -2 := by norm_num
      rw [this]
      refine (lintegral_closedBall_max_rpow_le_of_eq hlam hlh).trans (le_of_eq ?_)
      unfold leafConst
      rw [ite_eq_left rfl, ite_eq_left rfl]
      norm_num
    · have hβ4' : 4 < β := lt_of_le_of_ne hβ4 (Ne.symm h4)
      refine (lintegral_closedBall_max_rpow_le_of_neg hlam hlh (by linarith)).trans (le_of_eq ?_)
      unfold leafConst
      rw [ite_eq_right h4, ite_eq_right h4,
        show (2 : ℝ) - β + 2 = 4 - β by ring, show -(4 - β) = β - 4 by ring]
      congr 1
      ring
  calc ENNReal.ofReal (Real.exp (β * kernelConst χ)) * ∫⁻ w : ℂ,
        (Metric.closedBall (0 : ℂ) h).indicator
          (fun w => ENNReal.ofReal (max ‖w‖ lam ^ (2 - β))) w
      ≤ ENNReal.ofReal (Real.exp (β * kernelConst χ)) *
          ENNReal.ofReal (2 * Real.pi * leafConst β * lam ^ (4 - β) *
            (if β = 4 then 1 + Real.log (h / lam) else 1)) := by gcongr
    _ = ENNReal.ofReal (leafSharp χ β lam h) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        unfold leafSharp
        ring_nf

/-- The sharper intermediate estimate (5.140). Only a leaf at beta
four carries a logarithm. The core is the terminal tree of leaf deletion. -/
private theorem lintegral_blockWeight_cut_le_high_ordered (hχ : IsMollifier χ) (hβ4 : 4 ≤ β)
    (hM : 0 ≤ M) (hlam : 0 < lam) {h : ℝ} (hlh : lam ≤ h) (N : ℕ)
    {ι : Type*} [Fintype ι] [Nonempty ι] (hp : p₀ + 1 ≤ Fintype.card ι) :
    ∫⁻ c : ι → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam h N) c ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ((Fintype.card ι ^ (Fintype.card ι - 2) : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (leafSharp χ β lam h) ^ (Fintype.card ι - (p₀ + 1)) *
            orderedCoreBound χ β lam (p₀ + 1)) := by
  refine (lintegral_blockWeight_cut_le_ordered hχ hlam (by linarith) hM h N
    (Nat.succ_le_succ (Nat.zero_le p₀)) hp).trans ?_
  gcongr
  simpa only [Real.rpow_two] using lintegral_leaf_le_sharp hχ hβ4 hlam hlh

/-- The scalar form of (5.140). After the dipole normalization power,
the core contributes `λ^(2p₀)` and each deleted leaf contributes `λ²`.
Only beta four has a logarithmic leaf factor. -/
theorem lintegral_blockWeight_cut_le_high_sharp (hχ : IsMollifier χ) (hβ4 : 4 ≤ β)
    (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ h : ℝ, lam ≤ h → ∀ N : ℕ,
      ∀ (ι : Type*) [Fintype ι] [Nonempty ι], p₀ + 1 ≤ Fintype.card ι →
      ∫⁻ c : ι → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam h N) c ≤
        (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
          ((Fintype.card ι ^ (Fintype.card ι - 2) : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal ((Real.exp (β * kernelConst χ) * (2 * Real.pi * leafConst β)) ^
              (Fintype.card ι - (p₀ + 1)) * C * lam ^ ((2 - β) * Fintype.card ι) *
                lam ^ (2 * p₀) *
                  (lam ^ 2 * (if β = 4 then 1 + Real.log (h / lam) else 1)) ^
                    (Fintype.card ι - (p₀ + 1))) := by
  obtain ⟨C, hC, hcore⟩ := orderedCoreBound_le_power (χ := χ) hβ4
    (show 1 ≤ p₀ + 1 by omega)
  refine ⟨C, hC, fun lam hlam h hlh N ι _ _ hp => ?_⟩
  let m := Fintype.card ι
  let j := m - (p₀ + 1)
  have hm : p₀ + 1 + j = m := by dsimp [j]; omega
  have hκ := one_le_leafConst hβ4
  have hlog : 0 ≤ Real.log (h / lam) := Real.log_nonneg (by rw [le_div_iff₀ hlam]; linarith)
  have hL : 0 ≤ (if β = 4 then 1 + Real.log (h / lam) else 1) := by split_ifs <;> linarith
  have hleaf0 : 0 ≤ leafSharp χ β lam h := by unfold leafSharp; positivity
  have he : (lam ^ (4 - β)) ^ j * lam ^ ((4 - β) * (p₀ + 1 : ℕ) - 2) =
      lam ^ ((2 - β) * m) * lam ^ (2 * p₀) * (lam ^ 2) ^ j := by
    simp only [← Real.rpow_natCast, ← Real.rpow_mul hlam.le, ← Real.rpow_add hlam]
    congr 1
    rw [← hm]
    push_cast
    ring
  refine (lintegral_blockWeight_cut_le_high_ordered hχ hβ4 hM hlam hlh N hp).trans ?_
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ENNReal.ofReal (leafSharp χ β lam h) ^ j *
        ENNReal.ofReal (C * lam ^ ((4 - β) * (p₀ + 1 : ℕ) - 2)) :=
      mul_le_mul' le_rfl (hcore lam hlam)
    _ = ENNReal.ofReal ((Real.exp (β * kernelConst χ) * (2 * Real.pi * leafConst β)) ^ j *
        C * lam ^ ((2 - β) * m) * lam ^ (2 * p₀) *
          (lam ^ 2 * (if β = 4 then 1 + Real.log (h / lam) else 1)) ^ j) := by
      rw [← ENNReal.ofReal_pow hleaf0, ← ENNReal.ofReal_mul (pow_nonneg hleaf0 j)]
      congr 1
      unfold leafSharp
      rw [mul_pow, mul_pow, mul_pow]
      calc
        _ = (Real.exp (β * kernelConst χ) * (2 * Real.pi * leafConst β)) ^ j * C *
            ((lam ^ (4 - β)) ^ j * lam ^ ((4 - β) * (p₀ + 1 : ℕ) - 2)) *
              (if β = 4 then 1 + Real.log (h / lam) else 1) ^ j := by ring
        _ = _ := by rw [he, mul_pow]; ring

/-- The paper's high-beta leaf gain. -/
noncomputable def sourceEta (β lam : ℝ) : ℝ :=
  lam ^ 2 * (1 + if β = 4 then |Real.log lam| else 0)

/-- At the paper cutoff, the critical logarithm is bounded by a
constant depending on `p₀` times `1 + |log λ|`. -/
theorem cutoff_eta_le_source (hβ4 : 4 ≤ β) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) :
    lam ^ 2 * (if β = 4 then 1 + Real.log (cutoff p₀ β lam ε₀ / lam) else 1) ≤
      (2 * p₀ + 2) * sourceEta β lam := by
  unfold sourceEta
  by_cases h4 : β = 4
  · rw [ite_eq_left h4, ite_eq_left h4]
    have hR : truncationScale p₀ β lam = lam ^ (-(2 * (p₀ : ℝ))) := truncationScale_of_ge_rpow hβ4
    have hh : 0 < cutoff p₀ β lam ε₀ / lam := by
      unfold cutoff
      rw [hR]
      positivity
    have hratio : cutoff p₀ β lam ε₀ / lam ≤ lam ^ (-(2 * (p₀ : ℝ) + 1)) := by
      unfold cutoff
      rw [hR, div_le_iff₀ hlam]
      calc
        ε₀ * lam ^ (-(2 * (p₀ : ℝ))) ≤ 1 * lam ^ (-(2 * (p₀ : ℝ))) := by gcongr
        _ = _ := by rw [one_mul, ← Real.rpow_add_one hlam.ne']; congr 1; ring
    have hl : Real.log (cutoff p₀ β lam ε₀ / lam) ≤ (2 * p₀ + 1) * |Real.log lam| := by
      calc
        _ ≤ Real.log (lam ^ (-(2 * (p₀ : ℝ) + 1))) := Real.log_le_log hh hratio
        _ = (2 * p₀ + 1) * (-Real.log lam) := by rw [Real.log_rpow hlam]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)
    have hL : 1 + Real.log (cutoff p₀ β lam ε₀ / lam) ≤
        (2 * p₀ + 2) * (1 + |Real.log lam|) := by
      have : 0 ≤ (2 * (p₀ : ℝ) + 1) + |Real.log lam| := by positivity
      nlinarith
    calc
      _ ≤ lam ^ 2 * ((2 * p₀ + 2) * (1 + |Real.log lam|)) :=
        mul_le_mul_of_nonneg_left hL (sq_nonneg lam)
      _ = _ := by ring
  · rw [ite_eq_right h4, ite_eq_right h4]
    have hD : (1 : ℝ) ≤ 2 * p₀ + 2 := by linarith [show (0 : ℝ) ≤ p₀ from Nat.cast_nonneg p₀]
    nlinarith [sq_nonneg lam]

/-- (5.140) with the paper's literal `η_{β,λ}`. Cayley's count
stays explicit. The endpoint coefficient is absorbed into `C^m`. -/
theorem lintegral_blockWeight_cut_le_high_source (hχ : IsMollifier χ) (hβ4 : 4 ≤ β)
    (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 →
      lam ≤ cutoff p₀ β lam ε₀ → ∀ N : ℕ, ∀ (ι : Type*) [Fintype ι] [Nonempty ι],
      p₀ + 1 ≤ Fintype.card ι →
      ∫⁻ c : ι → ℂ × ℂ,
        blockWeight M lam (cutDipoleWeight χ β lam (cutoff p₀ β lam ε₀) N) c ≤
        (N : ℝ≥0∞) * ((Fintype.card ι ^ (Fintype.card ι - 2) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (C ^ Fintype.card ι * lam ^ ((2 - β) * Fintype.card ι) *
            lam ^ (2 * p₀) * sourceEta β lam ^ (Fintype.card ι - (p₀ + 1))) := by
  obtain ⟨C, hC, hb⟩ := lintegral_blockWeight_cut_le_high_sharp (p₀ := p₀) hχ hβ4 hM
  let S := 4 * Real.pi * M ^ 2
  let K := Real.exp (β * kernelConst χ) * (2 * Real.pi * leafConst β)
  let D : ℝ := 2 * p₀ + 2
  let Q := max 1 S * max 1 K * max 1 C * D
  have hD : 1 ≤ D := by dsimp [D]; linarith [show (0 : ℝ) ≤ p₀ from Nat.cast_nonneg p₀]
  have hκ := one_le_leafConst hβ4
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨Q, by dsimp [Q]; positivity, fun lam hlam ε₀ hε₀ hε₀1 hlh N ι _ _ hp => ?_⟩
  let m := Fintype.card ι
  let j := m - (p₀ + 1)
  have hm : 1 ≤ m := by omega
  have hj : j ≤ m := Nat.sub_le _ _
  have hη := cutoff_eta_le_source (p₀ := p₀) hβ4 hlam hε₀ hε₀1
  have hη0 : 0 ≤ sourceEta β lam := by unfold sourceEta; split_ifs <;> positivity
  have hlog : 0 ≤ Real.log (cutoff p₀ β lam ε₀ / lam) :=
    Real.log_nonneg (by rw [le_div_iff₀ hlam, one_mul]; exact hlh)
  have hcut0 : 0 ≤ lam ^ 2 *
      (if β = 4 then 1 + Real.log (cutoff p₀ β lam ε₀ / lam) else 1) := by
    split_ifs <;> positivity
  have hcoef : S ^ (m - 1) * K ^ j * C * D ^ j ≤ Q ^ m := by
    have hs : S ^ (m - 1) ≤ (max 1 S) ^ m :=
      (pow_le_pow_left₀ hS (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le _ _))
    have hk : K ^ j ≤ (max 1 K) ^ m :=
      (pow_le_pow_left₀ hK (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hj)
    have hc : C ≤ (max 1 C) ^ m :=
      (le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))
    have hd : D ^ j ≤ D ^ m := pow_le_pow_right₀ hD hj
    calc
      _ ≤ (max 1 S) ^ m * (max 1 K) ^ m * (max 1 C) ^ m * D ^ m := by gcongr
      _ = Q ^ m := by dsimp [Q]; simp only [mul_pow]
  refine (hb lam hlam _ hlh N ι hp).trans ?_
  have hrad : K ^ j * C * lam ^ ((2 - β) * m) * lam ^ (2 * p₀) *
      (lam ^ 2 * (if β = 4 then 1 + Real.log (cutoff p₀ β lam ε₀ / lam) else 1)) ^ j ≤
        K ^ j * C * lam ^ ((2 - β) * m) * lam ^ (2 * p₀) * (D * sourceEta β lam) ^ j := by
    gcongr
  calc
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal S ^ (m - 1) * ((m ^ (m - 2) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (K ^ j * C * lam ^ ((2 - β) * m) * lam ^ (2 * p₀) *
          (D * sourceEta β lam) ^ j) := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hrad)
    _ = (N : ℝ≥0∞) * ((m ^ (m - 2) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((S ^ (m - 1) * K ^ j * C * D ^ j) * lam ^ ((2 - β) * m) *
          lam ^ (2 * p₀) * sourceEta β lam ^ j) := by
      rw [← ENNReal.ofReal_pow hS,
        mul_right_comm (N : ℝ≥0∞) (ENNReal.ofReal (S ^ (m - 1))) _, mul_assoc,
        ← ENNReal.ofReal_mul (pow_nonneg hS _)]
      congr 1
      congr 1
      rw [mul_pow]
      ring_nf
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      apply ENNReal.ofReal_le_ofReal
      gcongr

end MultipoleBKT.BadPointTypes

end
