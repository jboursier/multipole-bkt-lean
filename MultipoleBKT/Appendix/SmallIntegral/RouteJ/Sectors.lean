/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.TreeCoordinates
public import MultipoleBKT.Appendix.SmallIntegral.JCore

/-!
# The four endpoint sectors and their simultaneous coordinate change

See Lemma A.4, (A.23) and (A.24).
An endpoint sector is selected for every oriented tree edge. The integrand
in the independent edge coordinates can depend jointly on all edge lengths.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Function Limits
open scoped Classical ENNReal

/-- The endpoint indexed by a Boolean, with `false` denoting the first endpoint. -/
def endpoint (a : ℂ × ℂ) (b : Bool) : ℂ := if b then a.2 else a.1

/-- One of the four endpoint distances attains the dipole distance.
See the proof of Lemma A.4. -/
theorem exists_endpoint_sector (a b : ℂ × ℂ) :
    ∃ q : Bool × Bool, ‖endpoint a q.1 - endpoint b q.2‖ = dipoleDist a b := by
  unfold dipoleDist
  rcases le_total ‖a.1 - b.1‖ ‖a.1 - b.2‖ with h₁ | h₁ <;>
    rcases le_total ‖a.2 - b.1‖ ‖a.2 - b.2‖ with h₂ | h₂
  · rw [min_eq_left h₁, min_eq_left h₂]
    rcases le_total ‖a.1 - b.1‖ ‖a.2 - b.1‖ with h | h
    · exact ⟨(false, false), (min_eq_left h).symm⟩
    · exact ⟨(true, false), (min_eq_right h).symm⟩
  · rw [min_eq_left h₁, min_eq_right h₂]
    rcases le_total ‖a.1 - b.1‖ ‖a.2 - b.2‖ with h | h
    · exact ⟨(false, false), (min_eq_left h).symm⟩
    · exact ⟨(true, true), (min_eq_right h).symm⟩
  · rw [min_eq_right h₁, min_eq_left h₂]
    rcases le_total ‖a.1 - b.2‖ ‖a.2 - b.1‖ with h | h
    · exact ⟨(false, true), (min_eq_left h).symm⟩
    · exact ⟨(true, false), (min_eq_right h).symm⟩
  · rw [min_eq_right h₁, min_eq_right h₂]
    rcases le_total ‖a.1 - b.2‖ ‖a.2 - b.2‖ with h | h
    · exact ⟨(false, true), (min_eq_left h).symm⟩
    · exact ⟨(true, true), (min_eq_right h).symm⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The endpoint shift for every oriented edge. Its root entry is zero because
the root coordinate is the common translation. -/
def sectorShift (root : V) (par : V → V) (u : V → ℂ)
    (σ : {i // i ≠ root} → Bool × Bool) (i : V) : ℂ :=
  if hi : i = root then 0 else
    (if (σ ⟨i, hi⟩).1 then u i else 0) -
      (if (σ ⟨i, hi⟩).2 then u (par i) else 0)

omit [Fintype V] in
theorem sectorShift_difference (root : V) (par : V → V) (u x : V → ℂ)
    (σ : {i // i ≠ root} → Bool × Bool) (i : {i // i ≠ root}) :
    treeCoordinates root par (sectorShift root par u σ) x i =
      endpoint (ofPosVec x u i) (σ i).1 - endpoint (ofPosVec x u (par i)) (σ i).2 := by
  simp only [treeCoordinates, sectorShift, dite_eq_right i.property, ite_eq_right i.property,
    endpoint, ofPosVec_apply]
  split_ifs <;> ring

/-- Simultaneous expansion over the four endpoint sectors. Ties may appear in
several sectors, which is harmless for this upper inequality.
See (A.23). -/
theorem endpoint_sector_sum (root : V) (par : V → V) (u x : V → ℂ)
    (Φ : ({i // i ≠ root} → ℝ) → ℝ≥0∞) :
    Φ (fun i => dipoleDist (ofPosVec x u i) (ofPosVec x u (par i))) ≤
      ∑ σ : {i // i ≠ root} → Bool × Bool,
        Φ (fun i => ‖treeCoordinates root par (sectorShift root par u σ) x i‖) := by
  have hex (i : {i // i ≠ root}) :=
    exists_endpoint_sector (ofPosVec x u i) (ofPosVec x u (par i))
  choose σ hσ using hex
  have heq : (fun i : {i // i ≠ root} =>
      ‖treeCoordinates root par (sectorShift root par u σ) x i‖) =
      (fun i : {i // i ≠ root} => dipoleDist (ofPosVec x u i) (ofPosVec x u (par i))) := by
    funext i
    rw [sectorShift_difference]
    exact hσ i
  rw [← heq]
  exact single_le_sum (f := fun τ : {i // i ≠ root} → Bool × Bool =>
    Φ (fun i => ‖treeCoordinates root par (sectorShift root par u τ) x i‖))
      (fun _ _ => bot_le) (mem_univ σ)

/-- All endpoint-sector integrals become the same integral after the tree
coordinate change. This includes the single maximum tail on the odd family.
See the proof of Lemma A.4. -/
theorem lintegral_endpoint_sectors (root : V) (par : V → V) (depth : V → ℕ)
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) (u : V → ℂ)
    (h : ℂ → ℝ≥0∞) (hh : Measurable h)
    (Φ : ({i // i ≠ root} → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ x : V → ℂ, h (x root) *
      Φ (fun i => dipoleDist (ofPosVec x u i) (ofPosVec x u (par i)))) ≤
        (4 : ℝ≥0∞) ^ Fintype.card {i // i ≠ root} *
          ∫⁻ z : V → ℂ, h (z root) * Φ (fun i => ‖z i‖) := by
  let F : (V → ℂ) → ℝ≥0∞ := fun z => h (z root) * Φ (fun i => ‖z i‖)
  have hF : Measurable F := by fun_prop
  have hm (σ : {i // i ≠ root} → Bool × Bool) :
      Measurable fun x : V → ℂ =>
        h (x root) * Φ (fun i => ‖treeCoordinates root par (sectorShift root par u σ) x i‖) := by
    have heq : (fun x : V → ℂ =>
        h (x root) * Φ (fun i => ‖treeCoordinates root par (sectorShift root par u σ) x i‖)) =
        F ∘ treeCoordinates root par (sectorShift root par u σ) := by
      funext x
      simp only [F, comp_apply, treeCoordinates, ite_true]
    rw [heq]
    apply hF.comp
    unfold treeCoordinates
    exact measurable_pi_iff.mpr fun i => by split_ifs <;> fun_prop
  calc
    _ ≤ ∫⁻ x : V → ℂ, ∑ σ : {i // i ≠ root} → Bool × Bool,
        h (x root) * Φ (fun i =>
          ‖treeCoordinates root par (sectorShift root par u σ) x i‖) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← mul_sum]
      exact mul_le_mul_right (endpoint_sector_sum root par u x Φ) _
    _ = ∑ σ : {i // i ≠ root} → Bool × Bool, ∫⁻ x : V → ℂ,
        h (x root) * Φ (fun i =>
          ‖treeCoordinates root par (sectorShift root par u σ) x i‖) :=
      lintegral_finsetSum _ fun σ _ => hm σ
    _ = ∑ _σ : {i // i ≠ root} → Bool × Bool, ∫⁻ z : V → ℂ, F z := by
      apply sum_congr rfl
      intro σ _
      convert lintegral_treeCoordinates root par depth hdepth
        (sectorShift root par u σ) F hF using 1
      simp only [F, treeCoordinates, ite_true]
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fun, Fintype.card_prod]
      norm_num [Fintype.card_bool, F]

end MultipoleBKT.SmallIntegral.RouteJ

end
