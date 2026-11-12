/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.Measurable
public import MultipoleBKT.LowerBound.RouteBounded.Density

/-!
# Normalizing the retained grouped integrals

The proof of Proposition 4.23. Count the original groups after parity, then divide by
the dipole and block normalizers.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical Multipole Parity SetPartition Limits
open scoped Classical

/-- Internal density and counting adapter for actual grouped numerator
integrals. The finite and infinite J estimates discharge its input. -/
theorem prod_mul_abs_activity_of_grouped_integrals
    {ρ : Measure (ℂ × ℂ)} {β M lam : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)} (h : ModelHyp ρ β w ψ K)
    (hρ : MeasurePreserving Prod.swap ρ ρ) (hw₁ : ∀ d e, w d.swap e = -w d e)
    (hw₂ : ∀ d e, w d e.swap = -w d e) (hψ : ∀ d, ψ d.swap = ψ d)
    (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C)
    (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (h2 : 2 ≤ X.card) {k N : ℕ} (hk : (X.biUnion id).card = k)
    (D : ℂ × ℂ → ℝ) (hDm : Measurable D) (hD0 : ∀ d, 0 ≤ D d)
    {Q : ℝ} (hQ : 0 < Q)
    (hπ : ∀ f : (X.biUnion id → ℂ × ℂ) → ℝ,
      ∫ y, f y ∂Measure.pi (fun _ : X.biUnion id => ρ) =
        Q⁻¹ ^ k * ∫ y in boxConfig (X.biUnion id) N, f y * ∏ i, D (y i))
    {Ct : ℝ} (hCt : 0 ≤ Ct)
    (hterms : ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      ∀ Es : Fin n → Finset (ℕ × ℕ), (∀ l, Es l ∈ relEdgeSets (Xs l)) →
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
      ∀ A : Finset (ℕ × ℕ), A ⊆ univ.biUnion Es → A ∈ relEulerianPairs X →
      (∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
        ((∏ S ∈ X, blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y)) *
          |eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F (extendConfig (X.biUnion id) y)| *
          ∏ i, D (y i))) ≤ ENNReal.ofReal Ct) :
    (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) * |modelActivity ρ β w ψ M lam X| ≤
      parityCount k * (Q⁻¹ ^ k * Ct) := by
  let P := ∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S
  have hP0 : 0 ≤ P := prod_nonneg fun S _ => h.modelPartitionFunction_nonneg M lam S
  let B : ℝ := Q⁻¹ ^ k * Ct
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcount : 0 ≤ parityCount k := by unfold parityCount; positivity
  by_cases hPz : P = 0
  · change P * _ ≤ _
    rw [hPz, zero_mul]
    exact mul_nonneg hcount hB
  have hP : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hPz)
  have hterm : ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ l m, l ≠ m → Disjoint (Xs l) (Xs m)) →
      ∀ Es : Fin n → Finset (ℕ × ℕ), (∀ l, Es l ∈ relEdgeSets (Xs l)) →
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
      ∀ A ∈ (univ.biUnion Es).powerset.filter (· ∈ relEulerianPairs X),
      |∫ y, eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F
        (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X| ≤ B / P := by
    intro n Xs hXs hdisj Es hEs F hF A hA
    have hAs : A ⊆ univ.biUnion Es := mem_powerset.1 (mem_filter.1 hA).1
    have hAe : A ∈ relEulerianPairs X := (mem_filter.1 hA).2
    let t := eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F
    let bw := fun y : X.biUnion id → ℂ × ℂ =>
      ∏ S ∈ X, blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y)
    have hbw0 (y) : 0 ≤ bw y := prod_nonneg fun S _ => blockWeightOf_nonneg M lam h.nonneg_ψ S _
    have htm : Measurable fun y : X.biUnion id → ℂ × ℂ => t (extendConfig (X.biUnion id) y) :=
      (measurable_eulerTerm h M lam Xs A (univ.biUnion Es \ A) F).comp (measurable_extendConfig _)
    have hbwm : Measurable bw := (Finset.measurable_prod _ fun S _ => h.measurable_blockWeightOf M lam S).comp
      (measurable_extendConfig _)
    have hm : Measurable fun y : X.biUnion id → ℂ × ℂ =>
        bw y * |t (extendConfig (X.biUnion id) y)| * ∏ i, D (y i) :=
      (hbwm.mul (continuous_abs.measurable.comp htm)).mul
        (Finset.measurable_prod _ fun i _ => hDm.comp (measurable_pi_apply i))
    have hn (y : X.biUnion id → ℂ × ℂ) :
        0 ≤ bw y * |t (extendConfig (X.biUnion id) y)| * ∏ i, D (y i) :=
      mul_nonneg (mul_nonneg (hbw0 y) (abs_nonneg _)) (prod_nonneg fun i _ => hD0 _)
    have hint := hterms Xs hXs Es hEs F hF A hAs hAe
    have hreal : (∫ y in boxConfig (X.biUnion id) N,
        bw y * |t (extendConfig (X.biUnion id) y)| * ∏ i, D (y i)) ≤
          Ct := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hm.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hint
    have heq : (∫ y, |t (extendConfig (X.biUnion id) y)| ∂modelHierarchical ρ β w ψ M lam X) =
        P⁻¹ * (Q⁻¹ ^ k * ∫ y in boxConfig (X.biUnion id) N,
          bw y * |t (extendConfig (X.biUnion id) y)| * ∏ i, D (y i)) := by
      rw [integral_model_eq_finite h X, hπ]
    apply (abs_integral_le_integral_abs).trans
    rw [heq]
    calc P⁻¹ * (Q⁻¹ ^ k * ∫ y in boxConfig (X.biUnion id) N,
          bw y * |t (extendConfig (X.biUnion id) y)| * ∏ i, D (y i))
        ≤ P⁻¹ * (Q⁻¹ ^ k * Ct) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hreal (by positivity)) (by positivity)
      _ = B / P := by dsimp [B]; ring
  have hmain := activity_le_of_grouped_integrals (lam := lam) h hρ hw₁ hw₂ hψ hwb hM hX h2 hk.le
    (div_nonneg hB hP.le) hterm
  have hmul := mul_le_mul_of_nonneg_left hmain hP.le
  change P * _ ≤ _
  apply hmul.trans_eq
  change P * (parityCount k * (B / P)) = parityCount k * B
  field_simp

end MultipoleBKT.LowerBound.RouteBounded

end
