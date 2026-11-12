/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.SourceRadius
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.TreeFamilies
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.OddMajorant

/-!
# Normalizing the retained near and even edges

See Lemma A.4. The radius allocation supplies
every squared label radius except the largest. Dividing each near or even
edge by its own squared minimum leaves the common radial factor.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits Hierarchical Peeling BoundedLowerEps
open scoped Classical ENNReal

/-- The squared regularized minimum assigned to one near or even edge. -/
noncomputable def minSq {V : Type*} (lam : ℝ) (c : V → ℂ × ℂ) : Sym2 V → ℝ :=
  edgeMin (fun x => max x lam ^ 2) (fun i => dipoleLength (c i))

theorem minSq_mk {V : Type*} (lam : ℝ) (c : V → ℂ × ℂ) (i j : V) :
    minSq lam c s(i, j) = min (rhoD lam (c i)) (rhoD lam (c j)) ^ 2 := by
  simp only [minSq, edgeMin_mk, max_min_distrib_right]
  rfl

theorem minSq_pos {V : Type*} {lam : ℝ} (hlam : 0 < lam) (c : V → ℂ × ℂ) (e : Sym2 V) :
    0 < minSq lam c e := by
  induction e using Sym2.ind with
  | h i j => rw [minSq_mk]; exact pow_pos (lt_min (rhoD_pos hlam _) (rhoD_pos hlam _)) _

/-- The common radial factor obtained in (A.25). -/
noncomputable def radialFactor {V : Type*} [Fintype V] (lam : ℝ) (c : V → ℂ × ℂ) : ℝ :=
  (∏ i, rhoD lam (c i) ^ 2) * maxRad lam c ^ (-2 : ℝ)

theorem radialFactor_eq_erase {V : Type*} [Fintype V] [DecidableEq V] {lam : ℝ}
    (hlam : 0 < lam) (c : V → ℂ × ℂ) (i₀ : V)
    (hmax : ∀ i, dipoleLength (c i) ≤ dipoleLength (c i₀)) :
    radialFactor lam c = ∏ i ∈ univ.erase i₀, rhoD lam (c i) ^ 2 := by
  have hR : maxRad lam c = rhoD lam (c i₀) := by
    apply le_antisymm
    · exact (fold_max_le _).mpr ⟨le_max_right _ _, fun i _ => max_le_max (hmax i) le_rfl⟩
    · exact rhoD_le_maxRad lam c i₀
  unfold radialFactor
  rw [hR, Real.rpow_neg (rhoD_pos hlam _).le, Real.rpow_two,
    ← mul_prod_erase univ (fun i => rhoD lam (c i) ^ 2) (mem_univ i₀)]
  field_simp [(rhoD_pos hlam (c i₀)).ne']

theorem minSq_mul_nearE {V : Type*} {lam : ℝ} (hlam : 0 < lam) (M : ℝ)
    (c : V → ℂ × ℂ) (e : Sym2 V) :
    minSq lam c e * nearE M lam c e = linkE M lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    rw [minSq_mk]
    change min (rhoD lam (c i)) (rhoD lam (c j)) ^ 2 * nearW M lam (c i) (c j) =
      (if MultipoleLinked M lam (c i) (c j) then 1 else 0)
    unfold nearW
    change min (rhoD lam (c i)) (rhoD lam (c j)) ^ 2 *
      ((if MultipoleLinked M lam (c i) (c j) then (1 : ℝ) else 0) /
        min (rhoD lam (c i)) (rhoD lam (c j)) ^ 2) = _
    split_ifs
    · field_simp [(lt_min (rhoD_pos hlam (c i)) (rhoD_pos hlam (c j))).ne']
    · simp

/-- Normalize the actual hatted even weight by its allocated squared minimum. -/
noncomputable def normalizedEven {V : Type*} (M lam : ℝ) (c : V → ℂ × ℂ) (e : Sym2 V) : ℝ :=
  (aSqE M lam c e + linkE M lam c e) / minSq lam c e

/-- The actual near and hatted even products after the radius allocation.
The input trees and the block maxima are exactly those of `J`.
See (A.25). -/
theorem source_normalized_product {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    [Nonempty (X.biUnion id)] {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (hXs : ∀ l, Xs l ⊆ X) (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (Ta : Fin n → Finset (ℕ × ℕ)) (hTa : ∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf)
    (Tb : Finset (ℕ × ℕ))
    (hTb : Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf)
    (c : X.biUnion id → ℂ × ℂ) (hat : Fin n → X)
    (hhat : ∀ l, hat l ∈ (Xs l).subtype (· ∈ X) ∧
      ∀ S ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i => dipoleLength (c i)) S ≤
          blockRadius hX (fun i => dipoleLength (c i)) (hat l))
    (R : NearTreeFamily (Limits.blockOf X)) {lam : ℝ} (hlam : 0 < lam) (M : ℝ) :
    (∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hat l),
      blockRadius hX (fun i => dipoleLength (c i)) S ^ 2) *
      (∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset, (aSqE M lam c e + linkE M lam c e)) *
      (∏ e ∈ nearForest (Limits.blockOf X) (fun S => (R S).val), linkE M lam c e) ≤
        radialFactor lam c *
          ((∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset, normalizedEven M lam c e) *
            ∏ e ∈ nearForest (Limits.blockOf X) (fun S => (R S).val), nearE M lam c e) := by
  obtain ⟨i₀, hmax, halloc⟩ := source_radius_allocation hX Xs hXs hdisj Ta hTa Tb hTb
    (fun i => dipoleLength (c i)) (fun _ => norm_nonneg _) hat hhat
    (fun S => (R S).val) (fun S => (R S).property) lam hlam
  change _ ≤ ∏ i ∈ univ.erase i₀, rhoD lam (c i) ^ 2 at halloc
  rw [← radialFactor_eq_erase hlam c i₀ hmax] at halloc
  let E := (graphOf (X.biUnion id) Tb).edgeFinset
  let F := nearForest (Limits.blockOf X) (fun S => (R S).val)
  have hEven : (∏ e ∈ E, minSq lam c e) * ∏ e ∈ E, normalizedEven M lam c e =
      ∏ e ∈ E, (aSqE M lam c e + linkE M lam c e) := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro e _
    unfold normalizedEven
    exact mul_div_cancel₀ _ (minSq_pos hlam c e).ne'
  have hNear : (∏ e ∈ F, minSq lam c e) * ∏ e ∈ F, nearE M lam c e =
      ∏ e ∈ F, linkE M lam c e := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun e _ => minSq_mul_nearE hlam M c e
  have hnorm : 0 ≤ (∏ e ∈ E, normalizedEven M lam c e) * ∏ e ∈ F, nearE M lam c e := by
    apply mul_nonneg
    · exact prod_nonneg fun e _ => div_nonneg (add_nonneg (aSqE_nonneg c e) (linkE_nonneg c e))
        (minSq_pos hlam c e).le
    · exact prod_nonneg fun e _ => nearE_nonneg M lam c e
  have h := mul_le_mul_of_nonneg_right halloc hnorm
  dsimp only [minSq] at hEven hNear
  calc
    _ = ((∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hat l),
        blockRadius hX (fun i => dipoleLength (c i)) S ^ 2) *
        (∏ e ∈ E, minSq lam c e) * ∏ e ∈ F, minSq lam c e) *
          ((∏ e ∈ E, normalizedEven M lam c e) * ∏ e ∈ F, nearE M lam c e) := by
      rw [← hEven, ← hNear]
      dsimp only [minSq]
      ring
    _ ≤ _ := h

end MultipoleBKT.SmallIntegral.RouteJ

end
