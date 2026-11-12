/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.LogTrees
public import MultipoleBKT.LowerBound.AbsoluteLower.RoutePosition.FixedGroups
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The literal edge logarithms and their endpoint weights

The proof of Lemma 4.58. The logarithms are pushed
forward from the finite label set, so their block sums are literal finite sums.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open MeasureTheory Finset SimpleGraph Set Limits SmallIntegral Multipole SetPartition
open RoutePosition
open scoped Classical ENNReal

/-- The finite pushforward of the logarithmic weights along the label inclusion. -/
noncomputable def labelLog {U : Finset ℕ} (h : ℝ) (u : U → ℂ) (i : ℕ) : ℝ :=
  ∑ j : U, if (j : ℕ) = i then Real.log (17 * h / ‖u j‖) else 0

theorem labelLog_coe {U : Finset ℕ} (h : ℝ) (u : U → ℂ) (i : U) :
    labelLog h u i = Real.log (17 * h / ‖u i‖) := by
  unfold labelLog
  rw [sum_eq_single i]
  · simp
  · intro j _ hji
    rw [ite_eq_right (fun h => hji (Subtype.ext h))]
  · simp

/-- Every endpoint logarithm on the cutoff is at least one. -/
theorem source_log_one_le {h r : ℝ} (hr : 0 < r) (hrh : r ≤ h) :
    1 ≤ Real.log (17 * h / r) := by
  have hh : 0 < h := hr.trans_le hrh
  apply (Real.le_log_iff_exp_le (by positivity : 0 < 17 * h / r)).mpr
  have : (17 : ℝ) ≤ 17 * h / r := (le_div_iff₀ hr).mpr (by linarith)
  exact Real.exp_one_lt_three.le.trans ((by norm_num : (3 : ℝ) ≤ 17).trans this)

theorem labelLog_nonneg {U : Finset ℕ} {h : ℝ} (u : U → ℂ)
    (hu : ∀ i, 0 < ‖u i‖ ∧ ‖u i‖ ≤ h) (i : ℕ) : 0 ≤ labelLog h u i := by
  apply sum_nonneg
  intro j _
  split_ifs
  · exact zero_le_one.trans (source_log_one_le (hu j).1 (hu j).2)
  · exact le_rfl

/-- The support failure makes the radial product vanish, including zero radii. -/
theorem prod_sourceWeight_eq_zero {U : Finset ℕ} {χ : ℂ → ℝ} {β lam h a : ℝ}
    (ha : 0 < a) (u : U → ℂ) (hu : ¬ ∀ i, 0 < ‖u i‖ ∧ ‖u i‖ ≤ h) :
    (∏ i, sourceWeight χ β lam h a (u i)) = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hu
  apply prod_eq_zero (mem_univ i)
  unfold sourceWeight
  by_cases hib : ‖u i‖ ≤ h
  · have hi0 : ‖u i‖ = 0 := le_antisymm (not_lt.mp (fun hp => hi ⟨hp, hib⟩)) (norm_nonneg _)
    rw [indicator_of_mem (show u i ∈ Metric.closedBall (0 : ℂ) h by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hib), hi0,
      div_zero, Real.zero_rpow ha.ne', mul_zero]
  · rw [indicator_of_notMem (show u i ∉ Metric.closedBall (0 : ℂ) h by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hib), mul_zero]

/-- The edge logarithm is bounded by the product of its endpoint logarithms. -/
theorem source_edge_le {U : Finset ℕ} {h : ℝ} (u : U → ℂ)
    (hu : ∀ i, 0 < ‖u i‖ ∧ ‖u i‖ ≤ h) (e : Sym2 U) :
    Real.log (17 * h / edgeMin id (fun i => ‖u i‖) e) ≤
      symmLift (fun i j : U => labelLog h u i * labelLog h u j)
        (fun _ _ => mul_comm _ _) e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [edgeMin_mk, id_eq, symmLift_mk, labelLog_coe]
    have hi := source_log_one_le (hu i).1 (hu i).2
    have hj := source_log_one_le (hu j).1 (hu j).2
    rcases min_choice ‖u i‖ ‖u j‖ with hm | hm <;> rw [hm]
    · exact le_mul_of_one_le_right (zero_le_one.trans hi) hj
    · exact le_mul_of_one_le_left (zero_le_one.trans hj) hi

/-- Comparison before either tree sum. The original radial exponent stays fixed. -/
theorem sourceSpatialWeight_le_endpoints {U : Finset ℕ} {χ : ℂ → ℝ} {β lam h a : ℝ}
    (hlam : 0 < lam) (hh : 0 ≤ h) (ha : 0 < a) {n : ℕ}
    (Ta : Fin n → Finset (ℕ × ℕ)) (hTa : ∀ l, Ta l ⊆ pairsOn U)
    (Tb : Finset (ℕ × ℕ)) (hTb : Tb ⊆ pairsOn U) (u : U → ℂ) :
    sourceSpatialWeight χ β lam h a
      (univ.biUnion (fun l => (graphOf U (Ta l)).edgeFinset) ∪ (graphOf U Tb).edgeFinset) u ≤
      (radiusFactor lam u * ∏ i, sourceWeight χ β lam h a (u i)) *
        ((∏ l, ∏ p ∈ Ta l, labelLog h u p.1 * labelLog h u p.2) *
          ∏ p ∈ Tb, labelLog h u p.1 * labelLog h u p.2) := by
  by_cases hu : ∀ i, 0 < ‖u i‖ ∧ ‖u i‖ ≤ h
  · let g : Sym2 U → ℝ := symmLift
      (fun i j : U => labelLog h u i * labelLog h u j) (fun _ _ => mul_comm _ _)
    have hg : ∀ e, 1 ≤ g e := by
      intro e
      induction e using Sym2.ind with
      | h i j =>
        simpa only [g, symmLift_mk, labelLog_coe] using
          one_le_mul_of_one_le_of_one_le (source_log_one_le (hu i).1 (hu i).2)
            (source_log_one_le (hu j).1 (hu j).2)
    have hp (E : Finset (ℕ × ℕ)) (hE : E ⊆ pairsOn U) :
        (∏ e ∈ (graphOf U E).edgeFinset, g e) = ∏ p ∈ E, labelLog h u p.1 * labelLog h u p.2 :=
      prod_edgeFinset_graphOf hE g _ (fun _ _ _ _ => by simp only [g, symmLift_mk])
    unfold sourceSpatialWeight
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (radiusFactor_nonneg hlam u)
      (prod_nonneg fun _ _ => sourceWeight_nonneg χ β lam hh a _))
    calc
      _ ≤ ∏ e ∈ univ.biUnion (fun l => (graphOf U (Ta l)).edgeFinset) ∪
          (graphOf U Tb).edgeFinset, g e := by
        apply prod_le_prod₀
        · intro e _
          induction e using Sym2.ind with
          | h i j => exact zero_le_one.trans (source_log_one_le (lt_min (hu i).1 (hu j).1)
              ((min_le_left _ _).trans (hu i).2))
        · exact fun e _ => source_edge_le u hu e
      _ ≤ (∏ l, ∏ e ∈ (graphOf U (Ta l)).edgeFinset, g e) *
          ∏ e ∈ (graphOf U Tb).edgeFinset, g e :=
        (prod_union_le_mul_of_one_le _ _ hg).trans
          (mul_le_mul_of_nonneg_right (prod_biUnion_le_prod_of_one_le _ _ hg)
            (prod_nonneg fun e _ => zero_le_one.trans (hg e)))
      _ = _ := by simp_rw [hp Tb hTb, hp _ (hTa _)]
  · rw [sourceSpatialWeight, prod_sourceWeight_eq_zero ha u hu]
    simp

/-- Nonnegativity of the spatial weight includes its radial support. -/
theorem sourceSpatialWeight_nonneg {U : Finset ℕ} {χ : ℂ → ℝ} {β lam h a : ℝ}
    (hlam : 0 < lam) (hh : 0 ≤ h) (ha : 0 < a) (E : Finset (Sym2 U)) (u : U → ℂ) :
    0 ≤ sourceSpatialWeight χ β lam h a E u := by
  by_cases hu : ∀ i, 0 < ‖u i‖ ∧ ‖u i‖ ≤ h
  · apply mul_nonneg (mul_nonneg (radiusFactor_nonneg hlam u)
      (prod_nonneg fun i _ => sourceWeight_nonneg χ β lam hh a _))
    apply prod_nonneg
    intro e _
    induction e using Sym2.ind with
    | h i j => exact zero_le_one.trans (source_log_one_le (lt_min (hu i).1 (hu j).1)
        ((min_le_left _ _).trans (hu i).2))
  · simp only [sourceSpatialWeight, prod_sourceWeight_eq_zero ha u hu, mul_zero, zero_mul, le_refl]

/-- The radial bound with the numerical dilation 17 also bounds the paper weight. -/
theorem sourceWeight_le_dipoleWeight {χ : ℂ → ℝ} {β lam h a : ℝ}
    (hh : 0 ≤ h) (ha : 0 ≤ a) (u : ℂ) :
    sourceWeight χ β lam h a u ≤ dipoleWeight χ β lam h a u := by
  rw [dipoleWeight_eq_sourceWeight χ β lam hh a]
  exact le_mul_of_one_le_left (sourceWeight_nonneg χ β lam hh a u)
    (Real.one_le_rpow (by norm_num) ha)

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
