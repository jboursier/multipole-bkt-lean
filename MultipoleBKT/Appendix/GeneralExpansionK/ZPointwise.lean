/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.MinusAssembly
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.RootDefinition
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.MinusInfrastructure
public import MultipoleBKT.UpperBound.BoundedUpper.WeightBounds

/-!
# Pointwise bounds for the model with frozen bad points

See Lemma A.7,
(A.35) and (A.54). On good dipoles the frozen
and baseline interactions obey the absolute bond bounds. The one-body
weight and stable pair weights have uniform bounds on the radial support.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset Metric SimpleGraph
open scoped ENNReal
open TwoComponentCoulomb (box)
open Hierarchical Multipole Parity Limits SmallIntegral UpperBound BoundedUpper MultipoleIntegralZ

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Constants -/

/-- The constant of eq. (5.73) (`MultipoleBKT.UpperBound.BoundedUpper.abs_interactionGoodZ_le_absOdd`)
plus that of `|v| ≤ C â`. -/
noncomputable def cZ (hχ : IsMollifier χ) : ℝ :=
  Classical.choose (abs_interactionGoodZ_le_absOdd hχ) +
    Classical.choose (BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ)

/-- The constant of eq. (A.35) (`MultipoleBKT.MultipoleIntegralZ.abs_interactionGoodZ_sub_le`). -/
noncomputable def c3Z (hχ : IsMollifier χ) : ℝ :=
  Classical.choose (MultipoleIntegralZ.abs_interactionGoodZ_sub_le hχ)

theorem c3Z_pos (hχ : IsMollifier χ) : 0 < c3Z hχ :=
  (Classical.choose_spec (MultipoleIntegralZ.abs_interactionGoodZ_sub_le hχ)).1

/-- The bound `e^{β(C_b + 16 C)}` of the pair weights of both models. -/
noncomputable def WZ (hχ : IsMollifier χ) (β : ℝ) : ℝ := Real.exp (β * (cbK hχ + 16 * c3Z hχ))

theorem one_le_WZ (hχ : IsMollifier χ) (hβ : 0 ≤ β) : 1 ≤ WZ hχ β :=
  Real.one_le_exp (mul_nonneg hβ (add_nonneg (cbK_nonneg hχ) (by have := c3Z_pos hχ; positivity)))

/-! ### The pointwise facts -/

section Facts

variable {ι : Type*} {N p₀ : ℕ} {ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

theorem absOddWeight_le_ahat (M lam ε₀ R : ℝ) (d e : ℂ × ℂ) :
    Parity.absOddWeight M lam ε₀ R d e ≤ ahat d e := by
  classical
  unfold Parity.absOddWeight
  have h0 : 0 ≤ ‖d.1 - d.2‖ * ‖e.1 - e.2‖ /
      (dipoleDist d e * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖)) := by
    have := dipoleDist_nonneg d e
    positivity
  split_ifs <;> simp [ahat, h0]

/-- **The interactions of the frozen model on good dipoles.** -/
theorem plus_far_facts (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hlh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM3 : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hV : badPointsOn p₀ β lam M ε₀ V Z = V) (c : ι → ℂ × ℂ)
    (hbox : ∀ i, c i ∈ box N ×ˢ box N) (hcut : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * truncationScale p₀ β lam)
    (hgood : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)) {hc : ℝ} (hhc0 : 0 < hc)
    (hhc : ∀ i, hc ≤ goodRadiusZ p₀ β lam ε₀ V Z (c i)) :
    (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
      |interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)| ≤ cZ hχ * ahat (c i) (c j)) ∧
    (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
      |dipoleInteraction χ lam (c i) (c j)| ≤ cZ hχ * ahat (c i) (c j)) ∧
    (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) → ahat (c i) (c j) ≤ 1) ∧
    (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
      |interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) - dipoleInteraction χ lam (c i) (c j)| ≤
        c3Z hχ * (rhoD lam (c i) * rhoD lam (c j) / hc ^ 2)) ∧
    (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
      17 * (ε₀ * truncationScale p₀ β lam) < dipoleDist (c i) (c j) →
      interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) = 0) := by
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM3
  have hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z := hV.symm ▸ subset_rfl
  obtain ⟨hC00, hC0⟩ := Classical.choose_spec (abs_interactionGoodZ_le_absOdd hχ)
  obtain ⟨hCv0, hCv⟩ := Classical.choose_spec (BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ)
  have hsup : ∀ i, OnSupportZ p₀ β lam M ε₀ V Z (c i) := fun i => ⟨⟨hbox i, hcut i⟩, hgood i⟩
  have hcZ : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ (x + y) := fun x y _ hy => by linarith
  refine ⟨fun i j hl => ?_, fun i j hl => ?_, fun i j hl => ?_, fun i j _ => ?_, fun i j hl hd => ?_⟩
  · obtain ⟨h1, -⟩ := hC0 p₀ β lam M ε₀ V Z hlam hlh hM3 hVZ (c i) (c j) (hsup i) (hsup j) hl
    refine h1.trans ?_
    unfold cZ
    exact mul_le_mul (by linarith) (absOddWeight_le_ahat _ _ _ _ _ _) (by
      unfold Parity.absOddWeight
      have := dipoleDist_nonneg (c i) (c j)
      split_ifs <;> positivity) (by linarith)
  · refine (hCv lam hlam M hM1 (c i) (c j) hl).trans ?_
    unfold cZ
    exact mul_le_mul_of_nonneg_right (by linarith) (ahat_nonneg _ _)
  · exact BoundedLowerEps.ahat_le_one_of_not_linked hχ hlam hM1 hl
  · obtain ⟨-, h3⟩ := Classical.choose_spec (MultipoleIntegralZ.abs_interactionGoodZ_sub_le hχ)
    refine (h3 p₀ β lam ε₀ V Z hlam (c i) (c j)).trans ?_
    have hri : ‖(c i).1 - (c i).2‖ ≤ rhoD lam (c i) := le_max_left _ _
    have hrj : ‖(c j).1 - (c j).2‖ ≤ rhoD lam (c j) := le_max_left _ _
    have hprod : ‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖ ≤ rhoD lam (c i) * rhoD lam (c j) :=
      mul_le_mul hri hrj (norm_nonneg _) ((norm_nonneg _).trans hri)
    have hmax : hc ^ 2 ≤ max (goodRadiusZ p₀ β lam ε₀ V Z (c i))
        (goodRadiusZ p₀ β lam ε₀ V Z (c j)) ^ 2 :=
      pow_le_pow_left₀ hhc0.le ((hhc i).trans (le_max_left _ _)) 2
    have hC3 := c3Z_pos hχ
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC3.le
    exact div_le_div₀ (mul_nonneg ((norm_nonneg _).trans hri) ((norm_nonneg _).trans hrj)) hprod
      (by positivity) hmax
  · obtain ⟨h1, -⟩ := hC0 p₀ β lam M ε₀ V Z hlam hlh hM3 hVZ (c i) (c j) (hsup i) (hsup j) hl
    have hz : Parity.absOddWeight M lam ε₀ (truncationScale p₀ β lam) (c i) (c j) = 0 := by
      classical
      unfold Parity.absOddWeight
      have hnot : ¬ dipoleDist (c i) (c j) ≤ 17 * ε₀ * truncationScale p₀ β lam :=
        not_le.2 (by rw [mul_assoc]; exact hd)
      rw [ite_eq_right hl, ite_eq_right hnot, mul_zero]
    rw [hz, mul_zero] at h1
    exact abs_nonpos_iff.1 h1

/-- **The pair weights and the one-body weights of the frozen model on good dipoles.** -/
theorem plus_stable_facts (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam)
    (hlh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM3 : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hV : badPointsOn p₀ β lam M ε₀ V Z = V) (c : ι → ℂ × ℂ)
    (hcut : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * truncationScale p₀ β lam)
    (hgood : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)) :
    (∀ i, ‖(c i).1 - (c i).2‖ ≤ 4 * goodRadiusZ p₀ β lam ε₀ V Z (c i)) ∧
    (∀ i j, 0 ≤ stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c i) (c j) ∧
      stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c i) (c j) ≤ WZ hχ β) ∧
    (∀ i j, 0 ≤ stableWeight β (dipoleInteraction χ lam) (c i) (c j) ∧
      stableWeight β (dipoleInteraction χ lam) (c i) (c j) ≤ WZ hχ β) ∧
    (∀ i j, |stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c i) (c j) -
        stableWeight β (dipoleInteraction χ lam) (c i) (c j)| ≤
      WZ hχ β * β * c3Z hχ / 2 *
        ((‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (c i)) ^ 2 +
          (‖(c j).1 - (c j).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (c j)) ^ 2)) ∧
    (∀ i, 0 ≤ dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) ∧
      dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) ≤ Real.exp (16 * |L|)) ∧
    (∀ i, |dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) - 1| ≤
      Real.exp (16 * |L|) * |L| *
        (‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (c i)) ^ 2) := by
  classical
  have hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z := hV.symm ▸ subset_rfl
  set τ : ι → ℝ := fun i => goodRadiusZ p₀ β lam ε₀ V Z (c i)
  have hτpos : ∀ i, 0 < τ i := fun i => hlam.trans_le (lam_le_goodRadiusZ _)
  have hr4 : ∀ i, ‖(c i).1 - (c i).2‖ ≤ 4 * τ i := fun i => by
    have := div_four_le_goodRadiusZ hlam hlh hM3 hVZ (hgood i) (hcut i)
    simp only [τ]; linarith
  set ρh : ι → ℝ := fun i => (‖(c i).1 - (c i).2‖ / τ i) ^ 2
  have hρh16 : ∀ i, ρh i ≤ 16 := fun i => by
    simp only [ρh]
    rw [div_pow, div_le_iff₀ (pow_pos (hτpos i) 2)]
    have := pow_le_pow_left₀ (norm_nonneg _) (hr4 i) 2
    nlinarith
  have hρh0 : ∀ i, 0 ≤ ρh i := fun i => sq_nonneg _
  obtain ⟨-, h3⟩ := Classical.choose_spec (MultipoleIntegralZ.abs_interactionGoodZ_sub_le hχ)
  set C₃ := c3Z hχ
  have hC₃ : 0 < C₃ := c3Z_pos hχ
  set Cb := cbK hχ
  have hCb : 0 ≤ Cb := cbK_nonneg hχ
  set W := WZ hχ β
  -- the key ratio
  have hratio : ∀ i j, ‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖ / max (τ i) (τ j) ^ 2 ≤
      (ρh i + ρh j) / 2 := by
    intro i j
    have hmi : τ i ≤ max (τ i) (τ j) := le_max_left _ _
    have hmj : τ j ≤ max (τ i) (τ j) := le_max_right _ _
    have hm0 : 0 < max (τ i) (τ j) := (hτpos i).trans_le hmi
    have h1 : ‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖ / max (τ i) (τ j) ^ 2 ≤
        (‖(c i).1 - (c i).2‖ / τ i) * (‖(c j).1 - (c j).2‖ / τ j) := by
      rw [div_mul_div_comm]
      refine div_le_div_of_nonneg_left (by positivity) (mul_pos (hτpos i) (hτpos j)) ?_
      rw [sq]
      exact mul_le_mul hmi hmj (hτpos j).le hm0.le
    refine h1.trans ?_
    have := two_mul_le_add_sq (‖(c i).1 - (c i).2‖ / τ i) (‖(c j).1 - (c j).2‖ / τ j)
    simp only [ρh]
    linarith
  have hv : ∀ i j, |interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
      dipoleInteraction χ lam (c i) (c j)| ≤ C₃ * ((ρh i + ρh j) / 2) := fun i j => by
    refine (h3 p₀ β lam ε₀ V Z hlam (c i) (c j)).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hratio i j) hC₃.le
  have hvC : ∀ i j, |interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
      dipoleInteraction χ lam (c i) (c j)| ≤ 16 * C₃ := fun i j => by
    refine (hv i j).trans ?_
    have := hρh16 i
    have := hρh16 j
    nlinarith
  refine ⟨hr4, fun i j => ⟨?_, ?_⟩, fun i j => ⟨?_, ?_⟩, fun i j => ?_, fun i => ⟨?_, ?_⟩,
    fun i => ?_⟩
  · unfold stableWeight; split_ifs <;> positivity
  · unfold stableWeight
    split_ifs with hst
    · refine Real.exp_le_exp.2 ?_
      have h2 := hvC i j
      have h3' := neg_cbK_le hχ hlam hst (lam := lam)
      rw [abs_le] at h2
      nlinarith
    · exact (Real.exp_pos _).le
  · unfold stableWeight; split_ifs <;> positivity
  · unfold stableWeight
    split_ifs with hst
    · refine Real.exp_le_exp.2 ?_
      have h3' := neg_cbK_le hχ hlam hst (lam := lam)
      nlinarith
    · exact (Real.exp_pos _).le
  · unfold stableWeight
    split_ifs with hst
    · refine (GeneralExpansion.abs_exp_sub_exp_le _ _).trans ?_
      have h2 := hvC i j
      have h3' := neg_cbK_le hχ hlam hst (lam := lam)
      rw [abs_le] at h2
      have hmax : max (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j))
          (-β * dipoleInteraction χ lam (c i) (c j)) ≤ β * (Cb + 16 * C₃) :=
        max_le (by nlinarith) (by nlinarith)
      have hexp : Real.exp (max (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j))
          (-β * dipoleInteraction χ lam (c i) (c j))) ≤ W := Real.exp_le_exp.2 hmax
      have hdiff : |-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
          -β * dipoleInteraction χ lam (c i) (c j)| ≤ β * (C₃ * ((ρh i + ρh j) / 2)) := by
        rw [show -β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
          -β * dipoleInteraction χ lam (c i) (c j) =
          -(β * (interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
            dipoleInteraction χ lam (c i) (c j))) by ring, abs_neg, abs_mul, abs_of_nonneg hβ]
        exact mul_le_mul_of_nonneg_left (hv i j) hβ
      calc Real.exp (max (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j))
            (-β * dipoleInteraction χ lam (c i) (c j))) *
            |-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
              -β * dipoleInteraction χ lam (c i) (c j)|
          ≤ W * (β * (C₃ * ((ρh i + ρh j) / 2))) :=
            mul_le_mul hexp hdiff (abs_nonneg _) (zero_le_one.trans (one_le_WZ hχ hβ))
        _ = _ := by simp only [ρh, τ, W]; ring
    · simp only [sub_self, abs_zero]
      have := hρh0 i
      have := hρh0 j
      have := zero_le_one.trans (one_le_WZ hχ hβ)
      positivity
  · exact dipoleWeightZ_nonneg _
  · unfold dipoleWeightZ
    rw [ite_eq_left (hgood i), mul_one]
    refine Real.exp_le_exp.2 ?_
    have := hρh16 i
    have := hρh0 i
    have hL := neg_abs_le L
    have : L * ρh i ≤ |L| * 16 := by nlinarith [le_abs_self L, abs_nonneg L]
    simp only [ρh, τ] at this
    linarith
  · unfold dipoleWeightZ
    rw [ite_eq_left (hgood i), mul_one]
    have := GeneralExpansion.abs_exp_sub_exp_le (L * (‖(c i).1 - (c i).2‖ /
      goodRadiusZ p₀ β lam ε₀ V Z (c i)) ^ 2) 0
    rw [Real.exp_zero, sub_zero] at this
    refine this.trans ?_
    have h16 := hρh16 i
    have h0 := hρh0 i
    simp only [ρh, τ] at h16 h0
    have hmax : max (L * (‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (c i)) ^ 2) 0 ≤
        16 * |L| := max_le (by nlinarith [le_abs_self L, abs_nonneg L]) (by positivity)
    rw [abs_mul, abs_of_nonneg h0]
    calc Real.exp (max (L * (‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (c i)) ^ 2) 0) *
          (|L| * (‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (c i)) ^ 2)
        ≤ Real.exp (16 * |L|) * (|L| * (‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V Z (c i)) ^ 2) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hmax) (by positivity)
      _ = _ := by ring

end Facts

end ExpansionK

end MultipoleBKT

end
