/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Large
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteMerge.Inner
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteMerge.Integral
public import MultipoleBKT.UpperBound.SimplifiedUpper.Normalize

/-!
# The lower series before and after merging

The proof of Lemma 4.57. The outer groups have at least
two blocks. The common merger records their former boundaries by marks
on the merged even tree, before any spatial integration or tree summation.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower

open MeasureTheory Finset SimpleGraph Multipole SetPartition Limits SmallIntegral Parity
open scoped Classical ENNReal

variable (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ C₀ : ℝ) (X : Finset (Finset ℕ))

/-- One outer integrand in (4.114). -/
noncomputable def nestedIntegrand {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Tb : Finset (ℕ × ℕ))
    (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ l, sourceInnerSeries M lam ε₀ (truncationScale p₀ β lam) (Xs l) c) *
    (∏ q ∈ Tb, absEvenWeight M lam ε₀ (truncationScale p₀ β lam) (c q.1) (c q.2)) *
    (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
    ∏ i ∈ X.biUnion id,
      (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) *
        SmallIntegral.cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (c i)

/-- The finite outer series in (4.114), before marking the merged tree. -/
noncomputable def nestedSeries (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ C₀ : ℝ)
    (X : Finset (Finset ℕ)) : ℝ≥0∞ :=
  ∑ n ∈ range (X.card + 1), ((n.factorial : ℝ≥0∞))⁻¹ *
    ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesT X n,
      ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
        ∫⁻ y in boxConfig (X.biUnion id) N,
          ENNReal.ofReal (nestedIntegrand χ p₀ β lam M ε₀ C₀ X Xs Tb
            (extendConfig (X.biUnion id) y))

/-- The two levels merge before integration, as in
proof of Lemma 4.57. The integrated tree-series bound can then be applied to
`treeSeries`, whose groups are fixed during spatial integration. -/
theorem nestedSeries_le_merged {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {p₀ N : ℕ} {β lam M ε₀ C₀ : ℝ} (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    nestedSeries χ N p₀ β lam M ε₀ C₀ X ≤
      ENNReal.ofReal ((2 : ℝ) ^ X.card) * treeSeries χ N p₀ β lam M ε₀ C₀ X := by
  let R := truncationScale p₀ β lam
  let μ := volume.restrict (boxConfig (X.biUnion id) N)
  let D := (range (X.card + 1)).sigma fun n =>
    (UpperBound.SimplifiedUpper.tuplesT X n).sigma fun Xs =>
      relTreePairs₀ (coarsen X (univ.image Xs))
  let E := (range (X.card + 1)).sigma fun n =>
    (UpperBound.SimplifiedUpper.tuplesD X n).sigma fun Xs =>
      (Fintype.piFinset (fun l => relTreePairs (Xs l))).sigma fun _ =>
        relTreePairs₀ (coarsen X (univ.image Xs))
  let f (d : Σ n : ℕ, Σ _ : Fin n → Finset (Finset ℕ), Finset (ℕ × ℕ))
      (y : X.biUnion id → ℂ × ℂ) : ℝ :=
    1 / (d.1.factorial : ℝ) * nestedIntegrand χ p₀ β lam M ε₀ C₀ X d.2.1 d.2.2
      (extendConfig (X.biUnion id) y)
  -- A sigma, rather than a product, keeps the tree index type explicit.
  let g' (d : Σ n : ℕ, Σ _ : Fin n → Finset (Finset ℕ),
      Σ _ : Fin n → Finset (ℕ × ℕ), Finset (ℕ × ℕ))
      (y : X.biUnion id → ℂ × ℂ) : ℝ :=
    1 / (d.1.factorial : ℝ) * UpperBound.AbsoluteUpper.jLargeIntegrand
      χ p₀ β lam M ε₀ C₀ X d.2.1 d.2.2.1 d.2.2.2 (extendConfig (X.biUnion id) y)
  have hf : ∀ d ∈ D, ∀ y, 0 ≤ f d y := by
    intro d _ y
    dsimp only [f, nestedIntegrand]
    exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg
      (prod_nonneg fun l _ => sourceInnerSeries_nonneg _ _ _ _ _ _)
      (prod_nonneg fun q _ => absEvenWeight_nonneg _ _ _ _ _ _))
      (prod_nonneg fun S _ => by split_ifs <;> norm_num))
      (prod_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (div_nonneg
        (mul_pos hε₀ (Appendix.truncationScale_pos hlam)).le (norm_nonneg _)) _)
        (cutDens_nonneg _ _)))
  have hg : ∀ d ∈ E, ∀ y, 0 ≤ g' d y := by
    intro d _ y
    exact mul_nonneg (by positivity)
      (UpperBound.SimplifiedUpper.jLargeIntegrand_nonneg hlam hε₀ _ _ _ _ _)
  have hgm : ∀ d ∈ E, Measurable (g' d) := by
    intro d _
    exact ((UpperBound.SimplifiedUpper.measurable_jLargeIntegrand hχ hlam X
      d.2.1 d.2.2.1 d.2.2.2).comp (measurable_extendConfig _)).const_mul _
  have hleft : (∑ d ∈ D, ∫⁻ y, ENNReal.ofReal (f d y) ∂μ) =
      nestedSeries χ N p₀ β lam M ε₀ C₀ X := by
    dsimp only [D]
    rw [sum_sigma]
    refine sum_congr rfl fun n _ => ?_
    rw [sum_sigma, mul_sum]
    refine sum_congr rfl fun Xs _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun Tb _ => ?_
    dsimp only [f]
    rw [RouteMerge.integral_mul μ _ (by positivity), one_div,
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  have hright : (∑ d ∈ E, ∫⁻ y, ENNReal.ofReal (g' d y) ∂μ) ≤
      treeSeries χ N p₀ β lam M ε₀ C₀ X := by
    dsimp only [E]
    simp only [sum_sigma]
    have heq : (∑ n ∈ range (X.card + 1),
        ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesD X n,
          ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
            ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
              ∫⁻ y, ENNReal.ofReal (g' ⟨n, Xs, Ta, Tb⟩ y) ∂μ) =
        ∑ n ∈ range (X.card + 1), ((n.factorial : ℝ≥0∞))⁻¹ *
          ∑ Xs ∈ UpperBound.SimplifiedUpper.tuplesD X n,
            ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
              ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
                UpperBound.AbsoluteUpper.jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro Xs _
      apply sum_congr rfl
      intro Ta _
      apply sum_congr rfl
      intro Tb _
      dsimp only [g']
      rw [RouteMerge.integral_mul μ _ (by positivity), one_div,
        ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
      rfl
    rw [heq]
    exact ENNReal.sum_le_tsum _
  have hpoint (y : X.biUnion id → ℂ × ℂ) :
      (∑ d ∈ D, f d y) ≤ (2 : ℝ) ^ X.card * ∑ d ∈ E, g' d y := by
    let c := extendConfig (X.biUnion id) y
    let H : ℝ := (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then 1 else 0) *
      ∏ i ∈ X.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) *
        cutDens χ β lam (ε₀ * R) (c i)
    have hH : 0 ≤ H := mul_nonneg (prod_nonneg fun S _ => by split_ifs <;> norm_num)
      (prod_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (div_nonneg
        (mul_pos hε₀ (Appendix.truncationScale_pos hlam)).le (norm_nonneg _)) _) (cutDens_nonneg _ _))
    have hm := mul_le_mul_of_nonneg_right (source_inner_merge hX (M := M) (lam := lam)
      (ε₀ := ε₀) (R := R) c) hH
    dsimp only [D, E, f, g']
    simp only [sum_sigma]
    convert hm using 1
    · simp only [sum_mul, mul_sum]
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro Xs _
      apply sum_congr rfl
      intro Tb _
      dsimp only [nestedIntegrand, H, R, c]
      ring
    · simp only [sum_mul, mul_sum]
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro Xs _
      apply sum_congr rfl
      intro Ta _
      apply sum_congr rfl
      intro Tb _
      dsimp only [UpperBound.SimplifiedUpper.treeProd,
        UpperBound.AbsoluteUpper.jLargeIntegrand, H, R, c]
      ring

  rw [← hleft]
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (∑ d ∈ D, f d y) ∂μ := RouteMerge.sum_integrals_le μ D f hf
    _ ≤ ∫⁻ y, ENNReal.ofReal ((2 : ℝ) ^ X.card * ∑ d ∈ E, g' d y) ∂μ :=
      lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpoint y)
    _ = ENNReal.ofReal ((2 : ℝ) ^ X.card) * ∑ d ∈ E, ∫⁻ y, ENNReal.ofReal (g' d y) ∂μ := by
      rw [RouteMerge.integral_mul μ _ (by positivity), RouteMerge.integral_sum μ E g' hg hgm]
    _ ≤ _ := mul_le_mul_right hright _

end MultipoleBKT.AbsoluteLower

end
