/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.ProfileProduct
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.CutoffGain
public import Mathlib.Data.Sym.Card

/-!
# A finite envelope for the selected spatial trees

See Step 3 of
the proof of Lemma A.7. The fixed finite sum includes every
near-tree choice, every separate odd tree, the coarse even tree and the root.
It is taken before integration. Its multiplicity depends only on label count.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral
open SmallIntegral.RouteJ SmallIntegral.RouteJext
open scoped Classical ENNReal

/-- All normalized profile choices on a fixed label carrier. Only trees enter. -/
abbrev SpatialChoice (W : Type*) :=
  {T : SimpleGraph W // T.IsTree} × Finset (Sym2 W) × Finset (Sym2 W) × Option (Sym2 W) × W

/-- The finite spatial envelope with its literal root factor. -/
noncomputable def spatialEnvelope {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (χ : ℂ → ℝ) (β M lam h : ℝ) (F : (W → ℂ × ℂ) → W → ℝ≥0∞)
    (c : W → ℂ × ℂ) : ℝ≥0∞ :=
  ∑ s : SpatialChoice W, F c s.2.2.2.2 *
    activityTree M lam h s.1.val s.2.1 s.2.2.1 s.2.2.2.1 c * activityDensity χ β lam h c

/-- One selected original tree is included before its configuration integral. -/
theorem le_spatialEnvelope {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (χ : ℂ → ℝ) (β M lam h : ℝ) (F : (W → ℂ × ℂ) → W → ℝ≥0∞)
    (c : W → ℂ × ℂ) (T : SimpleGraph W) (hT : T.IsTree)
    (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (root : W) :
    F c root * activityTree M lam h T A E mark c * activityDensity χ β lam h c ≤
      spatialEnvelope χ β M lam h F c := by
  unfold spatialEnvelope
  exact single_le_sum (f := fun s : SpatialChoice W => F c s.2.2.2.2 *
    activityTree M lam h s.1.val s.2.1 s.2.2.1 s.2.2.2.1 c * activityDensity χ β lam h c) (fun _ _ => bot_le) (mem_univ (show SpatialChoice W from (⟨T,hT⟩,A,E,mark,root)))
/-- A uniform finite multiplicity for all label trees and profile choices. -/
def spatialMultiplicity (k : ℕ) : ℕ :=
  2 ^ ((k + 1).choose 2) * (2 ^ ((k + 1).choose 2) *
    (2 ^ ((k + 1).choose 2) * (((k + 1).choose 2 + 1) * k)))

/-- The envelope multiplicity is independent of labels, lambda and frozen data. -/
theorem card_spatialChoice_le {W : Type*} [Fintype W] [DecidableEq W] :
    Fintype.card (SpatialChoice W) ≤ spatialMultiplicity (Fintype.card W) := by
  have hG : Fintype.card {T : SimpleGraph W // T.IsTree} ≤ 2 ^ Fintype.card (Sym2 W) := by
    calc
      _ ≤ Fintype.card (SimpleGraph W) := Fintype.card_subtype_le _
      _ ≤ Fintype.card (Finset (Sym2 W)) := Fintype.card_le_of_injective
        (fun T : SimpleGraph W => T.edgeFinset) (fun _ _ he => edgeFinset_inj.1 he)
      _ = _ := Fintype.card_finset
  simp only [SpatialChoice,Fintype.card_prod,Fintype.card_finset,Fintype.card_option]
  unfold spatialMultiplicity
  rw [← Sym2.card]
  exact Nat.mul_le_mul_right _ hG

/-- Tonelli for the fixed finite envelope. Every root weight is measurable. -/
theorem lintegral_spatialEnvelope {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {χ : ℂ → ℝ} (hχ : IsMollifier χ) (β M h : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (F : (W → ℂ × ℂ) → W → ℝ≥0∞) (hF : ∀ i, Measurable (fun c => F c i)) :
    (∫⁻ c : W → ℂ × ℂ, spatialEnvelope χ β M lam h F c) =
      ∑ s : SpatialChoice W, ∫⁻ c : W → ℂ × ℂ, F c s.2.2.2.2 *
        activityTree M lam h s.1.val s.2.1 s.2.2.1 s.2.2.2.1 c * activityDensity χ β lam h c := by
  exact lintegral_finsetSum _ fun s _ => ((hF _).mul (measurable_activityTree _ _ _ _ _ _ _)).mul
    (measurable_activityDensity hχ hlam _ _)

/-- Integrating the frozen-root finite envelope gives (A.63). The coefficient
is chosen before epsilon, lambda, label carrier and frozen data. -/
theorem frozen_spatialEnvelope_bound {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k →
      ∀ {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      UpperBound.badPointsOn p₀ β lam M eps V Z = V →
      (∫⁻ c : W → ℂ × ℂ, spatialEnvelope χ β M lam (eps * truncationScale p₀ β lam)
        (fun c i => ENNReal.ofReal ((rhoD lam (c i) ^ 2)⁻¹) *
          rootM p₀ β lam M eps V Z ((c i).1-(c i).2) (c i).2) c) ≤
        ENNReal.ofReal (lam ^ ((2-β)*k) *
          (C * eps ^ (-2 : ℝ) * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * eps ^ (alphaExponent β * k) * V.card)) := by
  obtain ⟨A,hA,hb⟩ := frozen_activityTree_bound (M := M) hχ hβ p₀ hk
  let D : ℝ := spatialMultiplicity k + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*A,mul_pos hD hA,?_⟩
  intro eps lam hlam hle heps hM W _ _ _ hW N V Z hV
  have heps0 : 0 < eps := hlam.trans_le hle
  have hscale := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  let F (c : W → ℂ × ℂ) (i : W) := ENNReal.ofReal ((rhoD lam (c i) ^ 2)⁻¹) *
    rootM p₀ β lam M eps V Z ((c i).1-(c i).2) (c i).2
  have hF (i : W) : Measurable (fun c => F c i) :=
    ((((measurable_rhoD lam).comp (measurable_pi_apply i)).pow_const 2).inv.ennreal_ofReal).mul
      ((measurable_rootM p₀ β lam M eps V Z).comp
        (show Measurable (fun c : W → ℂ × ℂ => ((c i).1-(c i).2,(c i).2)) by fun_prop))
  change (∫⁻ c : W → ℂ × ℂ, spatialEnvelope χ β M lam _ F c) ≤ _
  rw [lintegral_spatialEnvelope hχ β M _ hlam F hF]
  let B := lam ^ ((2-β)*k) * (A * eps ^ (-2 : ℝ) * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
    A * eps ^ (alphaExponent β * k) * V.card)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (Real.rpow_nonneg hlam.le _) (add_nonneg (by positivity) (by positivity))
  calc
    _ ≤ ∑ _s : SpatialChoice W, ENNReal.ofReal B := sum_le_sum fun s _ =>
      hb eps lam hlam hle heps hM W hW V Z hV s.1.val s.1.property s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2
    _ = ENNReal.ofReal ((Fintype.card (SpatialChoice W) : ℝ) * B) := by
      rw [sum_const,card_univ,nsmul_eq_mul,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (D*B) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by
      have hc := card_spatialChoice_le (W := W)
      rw [hW] at hc
      dsimp [D]
      exact (Nat.cast_le.2 hc).trans (le_add_of_nonneg_right (by norm_num))) hB)
    _ = _ := by congr 1; dsimp [B]; ring

/-- The screened-root envelope gives the area part of (A.63) with no bad data. -/
theorem screened_spatialEnvelope_bound {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k →
      ∀ N : ℕ, (∫⁻ c : W → ℂ × ℂ,
        spatialEnvelope χ β M lam (eps * truncationScale p₀ β lam)
          (fun c i => (TwoComponentCoulomb.box N).indicator 1 (c i).2 *
            ENNReal.ofReal (((eps * truncationScale p₀ β lam) ^ 2)⁻¹)) c) ≤
          ENNReal.ofReal (C * eps ^ (-2 : ℝ) * N *
            lam ^ ((2-β)*k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  obtain ⟨A,hA,hb⟩ := screened_activityTree_bound hχ hβ hM p₀ hk
  let D : ℝ := spatialMultiplicity k + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*A,mul_pos hD hA,?_⟩
  intro eps lam hlam hle heps W _ _ _ hW N
  have heps0 : 0 < eps := hlam.trans_le hle
  have hscale := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  let F (c : W → ℂ × ℂ) (i : W) := (TwoComponentCoulomb.box N).indicator (1 : ℂ → ℝ≥0∞) (c i).2 *
    ENNReal.ofReal (((eps * truncationScale p₀ β lam) ^ 2)⁻¹)
  have hF (i : W) : Measurable (fun c => F c i) :=
    ((measurable_const.indicator (TwoComponentCoulomb.measurableSet_box N)).comp
      (measurable_snd.comp (measurable_pi_apply i))).mul measurable_const
  change (∫⁻ c : W → ℂ × ℂ, spatialEnvelope χ β M lam _ F c) ≤ _
  rw [lintegral_spatialEnvelope hχ β M _ hlam F hF]
  let B := A * eps ^ (-2 : ℝ) * N * lam ^ ((2-β)*k) * truncationScale p₀ β lam ^ (-2 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ _s : SpatialChoice W, ENNReal.ofReal B := sum_le_sum fun s _ =>
      hb eps lam hlam hle heps W hW N s.1.val s.1.property s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2
    _ = ENNReal.ofReal ((Fintype.card (SpatialChoice W) : ℝ) * B) := by
      rw [sum_const,card_univ,nsmul_eq_mul,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (D*B) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by
      have hc := card_spatialChoice_le (W := W)
      rw [hW] at hc
      dsimp [D]
      exact (Nat.cast_le.2 hc).trans (le_add_of_nonneg_right (by norm_num))) hB)
    _ = _ := by congr 1; dsimp [B]; ring

end MultipoleBKT.ExpansionK.RouteSpatial

end
