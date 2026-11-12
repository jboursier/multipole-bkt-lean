/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.TreeSum

/-!
# The fixed-group integral after both tree sums

(A.68). The position estimate integrates the positions with groups and trees fixed.
Weighted Cayley then sums the two tree families. The radial exponent is `4C₀/M`.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open MeasureTheory Finset SimpleGraph Set Limits SmallIntegral Multipole SetPartition
open RoutePosition
open UpperBound.AbsoluteUpper (jLarge)
open scoped Classical ENNReal

/-- The coefficient per label in the fixed-group spatial and tree estimates. -/
noncomputable def fixedGroupConstant (p : ℕ) (M a : ℝ) : ℝ :=
  (2 ^ (p + 1) * max 1 (4 * Real.pi * M ^ 2) *
    ((17 : ℝ) ^ a * max 1 (8 * Real.pi * (1 + (Real.log 17)⁻¹)))) *
      (max (4 / a ^ 2) 1 ^ 2 * (17 : ℝ) ^ (2 * a))

private theorem sum_integrals_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    (∑ i ∈ s, ∫⁻ x, f i x ∂μ) ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- (A.68), including its displayed group cardinalities and the exact radial power.
The groups remain fixed throughout this theorem. -/
theorem fixed_groups_tree_sum_le_radial {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {p₀ : ℕ} {β lam M ε₀ C₀ : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M) (hC₀ : 0 < C₀)
    (hh : 0 ≤ ε₀ * truncationScale p₀ β lam) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (hXne : X.Nonempty) {p : ℕ} (hXp : ∀ S ∈ X, S.card ≤ p)
    (N : ℕ) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (hne : ∀ l, (Xs l).Nonempty) :
    (∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
      ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
        jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb) ≤
      (N : ℝ≥0∞) * ENNReal.ofReal
        (fixedGroupConstant p M (C₀ / M) ^ (X.biUnion id).card * groupCardinality X Xs) *
        ∫⁻ u : X.biUnion id → ℂ, ENNReal.ofReal
          ((∏ i, sourceWeight χ β lam (ε₀ * truncationScale p₀ β lam) (4 * C₀ / M) (u i)) *
            radiusFactor lam u) := by
  let h := ε₀ * truncationScale p₀ β lam
  let a := C₀ / M
  let A : Finset (Fin n → Finset (ℕ × ℕ)) := Fintype.piFinset (fun l => relTreePairs (Xs l))
  let B := relTreePairs₀ (coarsen X (Finset.univ.image Xs))
  let F (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ)) (u : X.biUnion id → ℂ) :=
    sourceSpatialWeight χ β lam h a
      (Finset.univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
        (graphOf (X.biUnion id) Tb).edgeFinset) u
  let K := 2 ^ (p + 1) * max 1 (4 * Real.pi * M ^ 2) *
    ((17 : ℝ) ^ a * max 1 (8 * Real.pi * (1 + (Real.log 17)⁻¹)))
  let D := max (4 / a ^ 2) 1 ^ 2 * (17 : ℝ) ^ (2 * a)
  have ha : 0 < a := div_pos hC₀ (by linarith)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hsp : ∀ Ta ∈ A, ∀ Tb ∈ B,
      jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb ≤
        (N : ℝ≥0∞) * ENNReal.ofReal (K ^ (X.biUnion id).card) * ∫⁻ u, ENNReal.ofReal (F Ta Tb u) := by
    intro Ta hTa Tb hTb
    exact fixed_groups_spatial_integral hχ hlam hM hC₀ hh hX hXne hXp N Xs hXs hdisj
      Ta (fun l => Fintype.mem_piFinset.mp hTa l) Tb hTb
  have hI : (∑ Ta ∈ A, ∑ Tb ∈ B, ∫⁻ u, ENNReal.ofReal (F Ta Tb u)) ≤
      ENNReal.ofReal (D ^ (X.biUnion id).card * groupCardinality X Xs) *
        ∫⁻ u : X.biUnion id → ℂ, ENNReal.ofReal
          ((∏ i, sourceWeight χ β lam h (4 * a) (u i)) * radiusFactor lam u) := by
    calc
      _ ≤ ∫⁻ u, ∑ Ta ∈ A, ∑ Tb ∈ B, ENNReal.ofReal (F Ta Tb u) :=
        (sum_le_sum fun Ta _ => sum_integrals_le _ _ _).trans (sum_integrals_le _ _ _)
      _ ≤ ∫⁻ u : X.biUnion id → ℂ,
          ENNReal.ofReal (D ^ (X.biUnion id).card * groupCardinality X Xs) *
            ENNReal.ofReal ((∏ i, sourceWeight χ β lam h (4 * a) (u i)) * radiusFactor lam u) := by
        apply lintegral_mono
        intro u
        have hF0 : ∀ Ta Tb, 0 ≤ F Ta Tb u := fun Ta Tb =>
          sourceSpatialWeight_nonneg hlam hh ha _ u
        simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun Tb _ => hF0 _ Tb)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun Ta _ => sum_nonneg fun Tb _ => hF0 Ta Tb)]
        rw [← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hD _) (groupCardinality_nonneg X Xs))]
        exact ENNReal.ofReal_le_ofReal (fixed_groups_integrand_sum hX Xs hXs hdisj hne hlam hh ha u)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ ≤ ∑ Ta ∈ A, ∑ Tb ∈ B,
        (N : ℝ≥0∞) * ENNReal.ofReal (K ^ (X.biUnion id).card) * ∫⁻ u, ENNReal.ofReal (F Ta Tb u) :=
      sum_le_sum fun Ta hTa => sum_le_sum fun Tb hTb => hsp Ta hTa Tb hTb
    _ = (N : ℝ≥0∞) * ENNReal.ofReal (K ^ (X.biUnion id).card) *
        (∑ Ta ∈ A, ∑ Tb ∈ B, ∫⁻ u, ENNReal.ofReal (F Ta Tb u)) := by simp only [mul_sum]
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (K ^ (X.biUnion id).card) *
        (ENNReal.ofReal (D ^ (X.biUnion id).card * groupCardinality X Xs) *
          ∫⁻ u : X.biUnion id → ℂ, ENNReal.ofReal
            ((∏ i, sourceWeight χ β lam h (4 * a) (u i)) * radiusFactor lam u)) :=
      mul_le_mul' le_rfl hI
    _ = _ := by
      rw [← mul_assoc, mul_assoc (N : ℝ≥0∞), ← ENNReal.ofReal_mul (pow_nonneg hK _)]
      have he : 4 * a = 4 * C₀ / M := by dsimp only [a]; ring
      have hcoef : K ^ (X.biUnion id).card * (D ^ (X.biUnion id).card * groupCardinality X Xs) =
          fixedGroupConstant p M (C₀ / M) ^ (X.biUnion id).card * groupCardinality X Xs := by
        change _ = (K * D) ^ (X.biUnion id).card * groupCardinality X Xs
        rw [mul_pow K D]
        ring
      rw [hcoef, he]

/-- Compare the paper radial integral with the dilated radial API at the same exponent. -/
theorem source_radial_le {ι : Type*} [Fintype ι] {χ : ℂ → ℝ} {β lam h a : ℝ}
    (hlam : 0 < lam) (hh : 0 ≤ h) (ha : 0 ≤ a) :
    (∫⁻ u : ι → ℂ, ENNReal.ofReal
      ((∏ i, sourceWeight χ β lam h a (u i)) * radiusFactor lam u)) ≤
    ∫⁻ u : ι → ℂ, (∏ i, ENNReal.ofReal (dipoleWeight χ β lam h a (u i))) *
      ENNReal.ofReal (radiusFactor lam u) := by
  apply lintegral_mono
  intro u
  dsimp only
  rw [← ENNReal.ofReal_prod_of_nonneg (fun (i : ι) _ => dipoleWeight_nonneg χ β lam hh (u i)),
    ← ENNReal.ofReal_mul (prod_nonneg fun i _ => dipoleWeight_nonneg χ β lam hh _)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (prod_le_prod₀
    (fun i _ => sourceWeight_nonneg χ β lam hh a _) (fun i _ => sourceWeight_le_dipoleWeight hh ha _))
      (radiusFactor_nonneg hlam u)

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
