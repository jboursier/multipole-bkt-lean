/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.FrozenExtension
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.BondError

/-!
# Estimates valid throughout the extended frozen expansion

See (A.35),
(A.54) and (A.61).
The equal-radius interaction estimate is applied after extending the radius.
No good-point indicator is required on individual correction terms.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Multipole Hierarchical MultipoleIntegralZ UpperBound BoundedUpper

/-- Equal-radius interactions have the two estimates used in the expansion,
provided the radius is at least one quarter of the dipole length. The
coefficient precedes both screening radii and the mollification scale. -/
theorem equal_radius_interaction_bounds {χ : ℂ → ℝ} (hχ : IsMollifier χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {lam M a b : ℝ}, 0 < lam → 1 ≤ M →
      ∀ d e : ℂ × ℂ, lam ≤ a → lam ≤ b →
      ‖d.1 - d.2‖ ≤ 4 * a → ‖e.1 - e.2‖ ≤ 4 * b →
      (|pairInteraction χ lam d e (a, a) (b, b) - dipoleInteraction χ lam d e| ≤
        C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / max a b ^ 2) ∧
      (¬ MultipoleLinked M lam d e →
        |pairInteraction χ lam d e (a, a) (b, b)| ≤ C * ahat d e) := by
  classical
  obtain ⟨C, hC, h⟩ := lemma_3_9_3 hχ
  refine ⟨C, hC, ?_⟩
  intro lam M a b hlam hM d e ha hb hda heb
  have hpoint := h lam ![a, b] ![a, b] ![d, e] 0 1 hlam ha rfl hb rfl
  rw [← MultipoleIntegralZ.pairInteraction_eq_ballGrowthInteraction] at hpoint
  simp +instances only [Matrix.cons_val_zero, Matrix.cons_val_one] at hpoint
  refine ⟨hpoint.1, fun hfar => ?_⟩
  obtain ⟨hD, -, -⟩ := far_facts hlam hM hfar
  have hmin := (UpperBound.Quadratic.lt_dipoleDist_of_not_linked hlam hM hfar).2
  have hw := (hpoint.2 (by linarith) (by linarith) hmin).1
  change |pairInteraction χ lam d e (a, a) (b, b)| ≤
    (if dipoleDist d e ≤ a + b then C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
      (max (dipoleDist d e) lam * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖)) else 0) at hw
  rw [max_eq_left hD.le] at hw
  by_cases hnear : dipoleDist d e ≤ a + b
  · rw [ite_eq_left hnear, mul_div_assoc] at hw
    exact hw
  · rw [ite_eq_right hnear] at hw
    exact hw.trans (mul_nonneg hC.le (ahat_nonneg d e))

/-- The estimates apply to the extended frozen model on its whole carrier.
In particular a term containing a bad-label correction needs no all-good
hypothesis. -/
theorem routeFrozen_interaction_bounds {χ : ℂ → ℝ} (hχ : IsMollifier χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N p₀ : ℕ} {β lam M ε₀ : ℝ}
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → 1 ≤ M →
      ∀ d e : ℂ × ℂ,
        |routeFrozenInteraction χ p₀ β lam ε₀ V Z d e - dipoleInteraction χ lam d e| ≤
          C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
            max (routeFrozenRadius p₀ β lam ε₀ V Z d) (routeFrozenRadius p₀ β lam ε₀ V Z e) ^ 2 ∧
        (¬ MultipoleLinked M lam d e →
          |routeFrozenInteraction χ p₀ β lam ε₀ V Z d e| ≤ C * ahat d e) := by
  obtain ⟨C, hC, hb⟩ := equal_radius_interaction_bounds hχ
  refine ⟨C, hC, ?_⟩
  intro N p₀ β lam M ε₀ V Z hlam hM d e
  have hd := routeFrozenRadius_lower p₀ β lam ε₀ V Z d
  have he := routeFrozenRadius_lower p₀ β lam ε₀ V Z e
  exact hb hlam hM d e hd.1 he.1 (by linarith [hd.2]) (by linarith [he.2])

/-- The quadratic correction is bounded and has its selected screening gain.
The ratio bound follows from the extended radius, on every dipole. -/
theorem quadratic_correction_bounds {r τ L : ℝ} (hr : 0 ≤ r) (hτ : 0 < τ)
    (hrτ : r ≤ 4 * τ) :
    |Real.exp (L * (r / τ) ^ 2) - 1| ≤ Real.exp (16 * |L|) * |L| * (r / τ) ^ 2 ∧
      |Real.exp (L * (r / τ) ^ 2) - 1| ≤ Real.exp (16 * |L|) * (16 * |L|) := by
  have hratio : (r / τ) ^ 2 ≤ 16 := by
    rw [div_pow, div_le_iff₀ (pow_pos hτ 2)]
    nlinarith [pow_le_pow_left₀ hr hrτ 2]
  have habs : |L * (r / τ) ^ 2| = |L| * (r / τ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (r / τ))]
  have harg : max (L * (r / τ) ^ 2) 0 ≤ 16 * |L| :=
    max_le ((le_abs_self _).trans (by rw [habs]; nlinarith [abs_nonneg L])) (by positivity)
  have hpoint := GeneralExpansion.abs_exp_sub_exp_le (L * (r / τ) ^ 2) 0
  rw [Real.exp_zero, sub_zero, habs] at hpoint
  have hb : |Real.exp (L * (r / τ) ^ 2) - 1| ≤
      Real.exp (16 * |L|) * |L| * (r / τ) ^ 2 := by
    calc _ ≤ Real.exp (16 * |L|) * (|L| * (r / τ) ^ 2) :=
           hpoint.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 harg) (by positivity))
         _ = _ := by ring
  refine ⟨hb, hb.trans ?_⟩
  calc _ ≤ Real.exp (16 * |L|) * |L| * 16 :=
         mul_le_mul_of_nonneg_left hratio (by positivity)
       _ = _ := by ring

/-- The uniform and selected-gain bounds for the actual extended vertex
correction. These bounds hold also at bad dipoles. -/
theorem routeFrozen_quadratic_bounds {N p₀ : ℕ} {β lam ε₀ L : ℝ}
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (hlam : 0 < lam) (d : ℂ × ℂ) :
    |routeFrozenQuadratic p₀ β lam ε₀ L V Z d| ≤
        Real.exp (16 * |L|) * |L| * (‖d.1 - d.2‖ / routeFrozenRadius p₀ β lam ε₀ V Z d) ^ 2 ∧
      |routeFrozenQuadratic p₀ β lam ε₀ L V Z d| ≤ Real.exp (16 * |L|) * (16 * |L|) := by
  have hd := routeFrozenRadius_lower p₀ β lam ε₀ V Z d
  exact quadratic_correction_bounds (norm_nonneg _) (hlam.trans_le hd.1) (by linarith [hd.2])

/-- The interaction error is uniformly bounded on every dipole after the
extension. This is the bound used for all unselected intra-block corrections. -/
theorem routeFrozen_difference_bounded {χ : ℂ → ℝ} (hχ : IsMollifier χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N p₀ : ℕ} {β lam ε₀ : ℝ}
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → ∀ d e : ℂ × ℂ,
        |routeFrozenInteraction χ p₀ β lam ε₀ V Z d e - dipoleInteraction χ lam d e| ≤ C := by
  obtain ⟨C, hC, hb⟩ := routeFrozen_interaction_bounds hχ
  refine ⟨16 * C, by positivity, ?_⟩
  intro N p₀ β lam ε₀ V Z hlam d e
  have hbound := (hb (p₀ := p₀) (β := β) (ε₀ := ε₀) V Z hlam (M := 1) le_rfl d e).1
  let a := routeFrozenRadius p₀ β lam ε₀ V Z d
  let b := routeFrozenRadius p₀ β lam ε₀ V Z e
  have ha := routeFrozenRadius_lower p₀ β lam ε₀ V Z d
  have hb' := routeFrozenRadius_lower p₀ β lam ε₀ V Z e
  have hm : 0 < max a b := (hlam.trans_le ha.1).trans_le (le_max_left _ _)
  have hda : ‖d.1 - d.2‖ ≤ 4 * max a b := by
    have : a ≤ max a b := le_max_left _ _
    dsimp only [a] at this
    linarith [ha.2]
  have heb : ‖e.1 - e.2‖ ≤ 4 * max a b := by
    have : b ≤ max a b := le_max_right _ _
    dsimp only [b] at this
    linarith [hb'.2]
  refine hbound.trans ((div_le_iff₀ (pow_pos hm 2)).2 ?_)
  have hprod := mul_le_mul hda heb (norm_nonneg _) (by positivity)
  nlinarith

/-- A scalar exponential correction with a bounded argument. -/
theorem exp_correction_le {a B : ℝ} (hB : 0 ≤ B) (ha : |a| ≤ B) :
    |Real.exp a - 1| ≤ Real.exp B * B := by
  have hp := GeneralExpansion.abs_exp_sub_exp_le a 0
  rw [Real.exp_zero, sub_zero] at hp
  exact hp.trans (mul_le_mul (Real.exp_le_exp.2 (max_le ((le_abs_self a).trans ha) hB))
    ha (abs_nonneg a) (Real.exp_pos B).le)

end MultipoleBKT.ExpansionK.RouteCases

end
