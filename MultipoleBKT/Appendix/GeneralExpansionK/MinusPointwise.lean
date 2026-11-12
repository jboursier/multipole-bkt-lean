/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.WeightBounds
public import MultipoleBKT.LowerBound.BoundedLowerEps.Bonds

/-!
# Pointwise bounds for the models `(ṽ, e^{-L r²/h²})` and `(v, 1)`

See the proof of Lemma A.7 for
`(w, τ) = (ṽ, τ̃)`: on configurations with all `r_i ≤ h = ε₀ R̄` and `λ ≤ h`,

* `minus_far_facts`: `|ṽ_ij|, |v_ij| ≤ C â_ij` and `â_ij ≤ 1` on `𝓑^c`, and (Lemma 3.10)
  `|ṽ_ij - v_ij| ≤ C ρ_i ρ_j / h²`;
* `minus_stable_facts`, `gaussian_facts`: the pair weights `e^{-β w} 𝟙_𝒜` of both models are in
  `[0, W]` and differ by `K (ρ_i² + ρ_j²)/h²`; the damping `e^{-L r²/h²}` is in `[0, e^{|L|}]` and
  differs from `1` by `e^{|L|} |L| r²/h²`;
* `farBondW_upper_eq_zero`: `ṽ_ij = 0` if `d_ij > 17 h`, so that the far bond of the model `ṽ`
  vanishes (the restriction to `𝒟`).
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph
open Hierarchical Multipole Parity Limits SmallIntegral

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Constants -/

/-- The lower bound `v_ij ≥ -C_b` on stable pairs (`MultipoleBKT.neg_le_dipoleInteraction`). -/
noncomputable def cbK (hχ : IsMollifier χ) : ℝ := Classical.choose (neg_le_dipoleInteraction hχ)

theorem cbK_nonneg (hχ : IsMollifier χ) : 0 ≤ cbK hχ :=
  (Classical.choose_spec (neg_le_dipoleInteraction hχ)).1

theorem neg_cbK_le (hχ : IsMollifier χ) (hlam : 0 < lam) {d e : ℂ × ℂ}
    (h : IsStableDipolePair d e) : -cbK hχ ≤ dipoleInteraction χ lam d e :=
  (Classical.choose_spec (neg_le_dipoleInteraction hχ)).2 lam hlam d e h

/-- The constant of Lemma 3.10 (`MultipoleBKT.lemma_3_10`). -/
noncomputable def c310 (hχ : IsMollifier χ) : ℝ := Classical.choose (lemma_3_10 hχ)

theorem c310_pos (hχ : IsMollifier χ) : 0 < c310 hχ :=
  (Classical.choose_spec (lemma_3_10 hχ)).1

/-- The constant `C` of `|v_ij| + |ṽ_ij| ≤ C â_ij` on `𝓑^c`. -/
noncomputable def cA (hχ : IsMollifier χ) : ℝ :=
  Classical.choose (BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ) +
    Classical.choose (BoundedLowerEps.abs_upperBoundInteraction_le_ahat hχ)

theorem cA_nonneg (hχ : IsMollifier χ) : 0 ≤ cA hχ :=
  add_nonneg (Classical.choose_spec (BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ)).1
    (Classical.choose_spec (BoundedLowerEps.abs_upperBoundInteraction_le_ahat hχ)).1

/-! ### The far bonds -/

section Far

variable {ι : Type*}

/-- The bounds of the interactions on `𝓑^c`, and Lemma 3.10. -/
theorem minus_far_facts (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M) {ε₀ R : ℝ}
    (hlh : lam ≤ ε₀ * R) (c : ι → ℂ × ℂ) (hcut : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) :
    (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
      |upperBoundInteraction χ lam ε₀ R (c i) (c j)| ≤ cA hχ * ahat (c i) (c j)) ∧
    (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
      |dipoleInteraction χ lam (c i) (c j)| ≤ cA hχ * ahat (c i) (c j)) ∧
    (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) → ahat (c i) (c j) ≤ 1) ∧
    (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
      |upperBoundInteraction χ lam ε₀ R (c i) (c j) - dipoleInteraction χ lam (c i) (c j)| ≤
        c310 hχ / 64 * (rhoD lam (c i) * rhoD lam (c j) / (ε₀ * R) ^ 2)) := by
  obtain ⟨hCv0, hCv⟩ := Classical.choose_spec (BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ)
  obtain ⟨hCt0, hCt⟩ :=
    Classical.choose_spec (BoundedLowerEps.abs_upperBoundInteraction_le_ahat hχ)
  set Cv := Classical.choose (BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ)
  set Ct := Classical.choose (BoundedLowerEps.abs_upperBoundInteraction_le_ahat hχ)
  have hcA : cA hχ = Cv + Ct := rfl
  have hh0 : 0 < ε₀ * R := hlam.trans_le hlh
  refine ⟨fun i j hl => ?_, fun i j hl => ?_, fun i j hl => ?_, fun i j hl => ?_⟩
  · refine (hCt lam ε₀ R hlam hlh M hM (c i) (c j) (hcut i) (hcut j) hl).trans ?_
    rw [hcA]
    exact mul_le_mul_of_nonneg_right (by linarith) (ahat_nonneg _ _)
  · refine (hCv lam hlam M hM (c i) (c j) hl).trans ?_
    rw [hcA]
    exact mul_le_mul_of_nonneg_right (by linarith) (ahat_nonneg _ _)
  · exact BoundedLowerEps.ahat_le_one_of_not_linked hχ hlam hM hl
  · obtain ⟨hC0, h310⟩ := Classical.choose_spec (lemma_3_10 hχ)
    have h8 : ∀ l, 8 * max ‖(c l).2 - (c l).1‖ lam ≤ 8 * ε₀ * R := fun l => by
      rw [norm_sub_rev, mul_assoc]
      exact mul_le_mul_of_nonneg_left (max_le (hcut l) hlh) (by norm_num)
    have := (h310 lam (8 * ε₀ * R) hlam (c i) (c j) (h8 i) (h8 j)).1
    unfold upperBoundInteraction
    refine this.trans ?_
    have hri : ‖(c i).1 - (c i).2‖ ≤ rhoD lam (c i) := le_max_left _ _
    have hrj : ‖(c j).1 - (c j).2‖ ≤ rhoD lam (c j) := le_max_left _ _
    have hprod : ‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖ ≤ rhoD lam (c i) * rhoD lam (c j) :=
      mul_le_mul hri hrj (norm_nonneg _) ((norm_nonneg _).trans hri)
    rw [show (8 * ε₀ * R) ^ 2 = 64 * (ε₀ * R) ^ 2 by ring]
    have hC := c310_pos hχ
    have hh2 : 0 < (ε₀ * R) ^ 2 := pow_pos hh0 2
    rw [show c310 hχ / 64 * (rhoD lam (c i) * rhoD lam (c j) / (ε₀ * R) ^ 2) =
      c310 hχ * (rhoD lam (c i) * rhoD lam (c j)) / (64 * (ε₀ * R) ^ 2) by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hC.le) (by positivity)

/-- **The screened interaction vanishes beyond `17 h`**, so does the far bond of the model `ṽ`. -/
theorem farBondW_upper_eq_zero [LinearOrder ι] (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hM : 1 ≤ M) {ε₀ R : ℝ} (hlh : lam ≤ ε₀ * R) (c : ι → ℂ × ℂ)
    (hcut : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) {i j : ι}
    (hd : 17 * (ε₀ * R) < dipoleDist (c i) (c j)) :
    farBondW β (upperBoundInteraction χ lam ε₀ R) M lam c s(i, j) = 0 := by
  classical
  obtain ⟨hC0, h310⟩ := Classical.choose_spec (lemma_3_10 hχ)
  have h8 : ∀ l, 8 * max ‖(c l).2 - (c l).1‖ lam ≤ 8 * ε₀ * R := fun l => by
    rw [norm_sub_rev, mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le (hcut l) hlh) (by norm_num)
  have hzero : ∀ a b : ι, dipoleDist (c a) (c b) = dipoleDist (c i) (c j) →
      upperBoundInteraction χ lam ε₀ R (c a) (c b) = 0 := by
    intro a b hab
    have hmin : min ‖(c a).1 - (c a).2‖ ‖(c b).1 - (c b).2‖ ≤ dipoleDist (c a) (c b) := by
      rw [hab]
      have hh0 : 0 < ε₀ * R := hlam.trans_le hlh
      exact (min_le_left _ _).trans ((hcut a).trans (by linarith))
    have h2 := ((h310 lam (8 * ε₀ * R) hlam (c a) (c b) (h8 a) (h8 b)).2 hmin).1
    have hgt : ¬ dipoleDist (c a) (c b) ≤ 17 / 8 * (8 * ε₀ * R) := by
      rw [hab]; push Not; linarith
    rw [ite_eq_right hgt] at h2
    unfold upperBoundInteraction
    exact abs_nonpos_iff.1 h2
  simp only [farBondW, symmLift_mk, farBondWij]
  split_ifs with hl
  · rfl
  · rw [sOrd_of_not_linked hM _ c hl]
    unfold wOrd
    split_ifs
    · rw [hzero i j rfl, mul_zero, Real.exp_zero, sub_self]
    · rw [hzero j i (dipoleDist_comm _ _), mul_zero, Real.exp_zero, sub_self]

end Far

/-! ### The pair weights and the damping -/

section Stable

variable {ι : Type*}

/-- The pair weights of both models are in `[0, W]`, `W = e^{β(C_b + C/64)}`, and differ by
`K₁ (ρ_i + ρ_j)`, `ρ_i = r_i²/h²`, `K₁ = W β C/128`. -/
theorem minus_stable_facts (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam) {ε₀ R : ℝ}
    (hlh : lam ≤ ε₀ * R) (c : ι → ℂ × ℂ) (hcut : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) :
    (∀ i j, 0 ≤ stableWeight β (upperBoundInteraction χ lam ε₀ R) (c i) (c j) ∧
      stableWeight β (upperBoundInteraction χ lam ε₀ R) (c i) (c j) ≤
        Real.exp (β * (cbK hχ + c310 hχ / 64))) ∧
    (∀ i j, 0 ≤ stableWeight β (dipoleInteraction χ lam) (c i) (c j) ∧
      stableWeight β (dipoleInteraction χ lam) (c i) (c j) ≤
        Real.exp (β * (cbK hχ + c310 hχ / 64))) ∧
    (∀ i j, |stableWeight β (upperBoundInteraction χ lam ε₀ R) (c i) (c j) -
        stableWeight β (dipoleInteraction χ lam) (c i) (c j)| ≤
      Real.exp (β * (cbK hχ + c310 hχ / 64)) * β * c310 hχ / 128 *
        (‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2 + ‖(c j).1 - (c j).2‖ ^ 2 / (ε₀ * R) ^ 2)) := by
  classical
  obtain ⟨hC0, h310⟩ := Classical.choose_spec (lemma_3_10 hχ)
  set C₁ := c310 hχ
  set Cb := cbK hχ
  have hC₁ : 0 < C₁ := c310_pos hχ
  have hCb : 0 ≤ Cb := cbK_nonneg hχ
  set h := ε₀ * R
  have hh0 : 0 < h := hlam.trans_le hlh
  set W := Real.exp (β * (Cb + C₁ / 64))
  have h8 : ∀ l, 8 * max ‖(c l).2 - (c l).1‖ lam ≤ 8 * ε₀ * R := fun l => by
    rw [norm_sub_rev, mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le (hcut l) hlh) (by norm_num)
  have hv : ∀ i j, |upperBoundInteraction χ lam ε₀ R (c i) (c j) - dipoleInteraction χ lam (c i) (c j)| ≤
      C₁ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / (64 * h ^ 2) := fun i j => by
    have := (h310 lam (8 * ε₀ * R) hlam (c i) (c j) (h8 i) (h8 j)).1
    rw [show (8 * ε₀ * R) ^ 2 = 64 * h ^ 2 by simp only [h]; ring] at this
    exact this
  have hvC : ∀ i j, |upperBoundInteraction χ lam ε₀ R (c i) (c j) -
      dipoleInteraction χ lam (c i) (c j)| ≤ C₁ / 64 := fun i j => by
    refine (hv i j).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul (hcut i) (hcut j) (norm_nonneg _) hh0.le
    nlinarith
  refine ⟨fun i j => ⟨?_, ?_⟩, fun i j => ⟨?_, ?_⟩, fun i j => ?_⟩
  · unfold stableWeight; split_ifs <;> positivity
  · unfold stableWeight
    split_ifs with hst
    · refine Real.exp_le_exp.2 ?_
      have h2 := hvC i j
      have h3 := neg_cbK_le hχ hlam hst (lam := lam)
      rw [abs_le] at h2
      nlinarith
    · positivity
  · unfold stableWeight; split_ifs <;> positivity
  · unfold stableWeight
    split_ifs with hst
    · refine Real.exp_le_exp.2 ?_
      have h3 := neg_cbK_le hχ hlam hst (lam := lam)
      nlinarith
    · positivity
  · unfold stableWeight
    split_ifs with hst
    · refine (GeneralExpansion.abs_exp_sub_exp_le _ _).trans ?_
      have h1 := hv i j
      have h2 := hvC i j
      have h3 := neg_cbK_le hχ hlam hst (lam := lam)
      rw [abs_le] at h2
      have hmax : max (-β * upperBoundInteraction χ lam ε₀ R (c i) (c j))
          (-β * dipoleInteraction χ lam (c i) (c j)) ≤ β * (Cb + C₁ / 64) :=
        max_le (by nlinarith) (by nlinarith)
      have hexp : Real.exp (max (-β * upperBoundInteraction χ lam ε₀ R (c i) (c j))
          (-β * dipoleInteraction χ lam (c i) (c j))) ≤ W := Real.exp_le_exp.2 hmax
      have hdiff : |-β * upperBoundInteraction χ lam ε₀ R (c i) (c j) -
          -β * dipoleInteraction χ lam (c i) (c j)| ≤
          β * (C₁ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / (64 * h ^ 2)) := by
        rw [show -β * upperBoundInteraction χ lam ε₀ R (c i) (c j) -
          -β * dipoleInteraction χ lam (c i) (c j) =
          -(β * (upperBoundInteraction χ lam ε₀ R (c i) (c j) -
            dipoleInteraction χ lam (c i) (c j))) by ring, abs_neg, abs_mul, abs_of_nonneg hβ]
        exact mul_le_mul_of_nonneg_left h1 hβ
      have hρij : C₁ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / (64 * h ^ 2) ≤
          C₁ * (‖(c i).1 - (c i).2‖ ^ 2 / h ^ 2 + ‖(c j).1 - (c j).2‖ ^ 2 / h ^ 2) / 128 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have hsq := two_mul_le_add_sq ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖
        have hh2 : 0 < h ^ 2 := by positivity
        field_simp
        nlinarith
      calc Real.exp (max (-β * upperBoundInteraction χ lam ε₀ R (c i) (c j))
            (-β * dipoleInteraction χ lam (c i) (c j))) *
            |-β * upperBoundInteraction χ lam ε₀ R (c i) (c j) -
              -β * dipoleInteraction χ lam (c i) (c j)|
          ≤ W * (β * (C₁ * (‖(c i).1 - (c i).2‖ ^ 2 / h ^ 2 +
              ‖(c j).1 - (c j).2‖ ^ 2 / h ^ 2) / 128)) :=
            mul_le_mul hexp (hdiff.trans (mul_le_mul_of_nonneg_left hρij hβ))
              (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · simp only [sub_self, abs_zero]
      positivity

/-- The damping `e^{-L r²/h²}`: in `[0, e^{|L|}]`, at distance `e^{|L|} |L| r²/h²` from `1`. -/
theorem gaussian_facts (p₀ : ℕ) (β lam ε₀ L : ℝ) (hh0 : 0 < ε₀ * truncationScale p₀ β lam)
    (d : ℂ × ℂ) (hd : ‖d.1 - d.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    0 ≤ gaussianWeight p₀ β lam ε₀ L d ∧ gaussianWeight p₀ β lam ε₀ L d ≤ Real.exp |L| ∧
      |gaussianWeight p₀ β lam ε₀ L d - 1| ≤
        Real.exp |L| * |L| * (‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2) := by
  set h := ε₀ * truncationScale p₀ β lam
  set ρ := ‖d.1 - d.2‖ ^ 2 / h ^ 2
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  have harg : |-L * ρ| = |L| * ρ := by rw [abs_mul, abs_neg, abs_of_nonneg hρ0]
  unfold gaussianWeight
  refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 ((le_abs_self _).trans ?_), ?_⟩
  · rw [harg]; exact mul_le_of_le_one_right (abs_nonneg L) hρ1
  · have := GeneralExpansion.abs_exp_sub_exp_le (-L * ρ) 0
    rw [Real.exp_zero, sub_zero, harg] at this
    refine this.trans ?_
    have hmax : max (-L * ρ) 0 ≤ |L| := by
      refine max_le ((le_abs_self _).trans ?_) (abs_nonneg L)
      rw [harg]; exact mul_le_of_le_one_right (abs_nonneg L) hρ1
    calc Real.exp (max (-L * ρ) 0) * (|L| * ρ) ≤ Real.exp |L| * (|L| * ρ) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hmax) (mul_nonneg (abs_nonneg L) hρ0)
      _ = _ := by ring

end Stable

end ExpansionK

end MultipoleBKT

end
