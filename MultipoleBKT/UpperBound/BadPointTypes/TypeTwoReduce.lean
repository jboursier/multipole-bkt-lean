/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoBlock
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Bound

/-!
# Lemma 5.41: partition decomposition and exponential summation

The paper: Lemma 5.41,
(5.135) and (5.141).
On the type `(2,1)` event every multipole has more than `p(β)` elements
and all dipoles are short. Drop the matching constraints, decompose by the
actual component partition, integrate each block, and enumerate size profiles.
Summing the factorial denominators gives the exponential bound.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset TheoremTwo MultipoleIntegral
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {β lam M : ℝ} {n : ℕ}

/-- On `{I^{2,1}_bad = [n]}` every multipole, computed on all labels, has more than `p(β)`
elements. -/
theorem typeTwoOne_classes {p₀ : ℕ} {ε₀ : ℝ} {d : Fin n → ℂ × ℂ}
    (h : typeTwoOneBad p₀ β lam M ε₀ d = Finset.univ) (i : Fin n) :
    pBeta p₀ β < (multipoleClassOn M lam d Finset.univ i).card := by
  have h1 := badPointsTypeOne_eq_empty_of_typeTwoOneBad h
  have hi : i ∈ typeTwoOneBad p₀ β lam M ε₀ d := h ▸ mem_univ i
  unfold typeTwoOneBad at hi
  rw [h1, sdiff_empty] at hi
  exact (mem_filter.1 hi).2

/-- On `{I^{2,1}_bad = [n]}` every dipole has length at most `ε₀ R̄`. -/
theorem typeTwoOne_short {p₀ : ℕ} {ε₀ : ℝ} {d : Fin n → ℂ × ℂ}
    (h : typeTwoOneBad p₀ β lam M ε₀ d = Finset.univ) (i : Fin n) :
    ‖(d i).1 - (d i).2‖ ≤ cutoff p₀ β lam ε₀ := by
  have h1 := badPointsTypeOne_eq_empty_of_typeTwoOneBad h
  by_contra hlong
  have hmem : i ∈ badPointsTypeOne p₀ β lam ε₀ d := by
    unfold badPointsTypeOne
    refine mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨mem_univ i, ?_⟩))
    exact not_le.1 hlong
  rw [h1] at hmem
  exact Finset.notMem_empty i hmem

open scoped Classical in
/-- The integrand of `Z^{(2,1)}` (on the box) is at most `classWeight (· > p)` with the cut
weight. -/
theorem typeTwoOne_indicator_le (p₀ : ℕ) (ε₀ : ℝ) (Nₐ : ℕ) (d : Fin n → ℂ × ℂ) :
    (boxPi Nₐ n).indicator (fun d =>
      (if typeTwoOneBad p₀ β lam M ε₀ d = Finset.univ ∧ StablePairs d then 1 else 0) *
        ENNReal.ofReal (dipoleWeight χ β lam d)) d ≤
      classWeight M lam (fun m => pBeta p₀ β < m)
        (cutDipoleWeight χ β lam (cutoff p₀ β lam ε₀) Nₐ) Finset.univ d := by
  by_cases hd : d ∈ boxPi Nₐ n
  · rw [Set.indicator_of_mem hd]
    split_ifs with h
    · rw [one_mul]
      unfold classWeight
      rw [ite_eq_left fun i _ => typeTwoOne_classes h.1 i, one_mul, dipoleWeight,
        ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
      refine le_of_eq (prod_congr rfl fun i _ => ?_)
      unfold cutDipoleWeight
      rw [Set.indicator_of_mem (Set.mem_univ_pi.1 hd i), Set.indicator_of_mem]
      rw [Metric.mem_closedBall, dist_zero_right]
      exact typeTwoOne_short h.1 i
    · rw [zero_mul]
      exact zero_le
  · rw [Set.indicator_of_notMem hd]
    exact zero_le

open scoped Classical in
/-- The literal integral partition decomposition (5.135), the paper. Each summand retains the bad-point event and the matching constraints. -/
theorem typeTwoOnePartitionFunction_eq_sum_partitions (p₀ : ℕ) (ε₀ : ℝ) (Nₐ : ℕ) :
    typeTwoOnePartitionFunction χ p₀ β lam M ε₀ Nₐ n =
      ∑ π ∈ (SetPartition.partitions (univ : Finset (Fin n))).filter
        (fun π => ∀ T ∈ π, pBeta p₀ β < T.card),
        ∫⁻ d in boxPi Nₐ n,
          (if componentPartition M lam univ d = π then 1 else 0) *
            ((if typeTwoOneBad p₀ β lam M ε₀ d = univ ∧ StablePairs d then 1 else 0) *
              ENNReal.ofReal (dipoleWeight χ β lam d)) := by
  unfold typeTwoOnePartitionFunction
  rw [lintegral_eq_sum_componentPartition (M := M) (lam := lam) univ _ _]
  symm
  apply sum_filter_of_ne
  intro π _ hne T hT
  by_contra hbad
  apply hne
  have hz : ∀ d : Fin n → ℂ × ℂ,
      (if componentPartition M lam univ d = π then (1 : ℝ≥0∞) else 0) *
        ((if typeTwoOneBad p₀ β lam M ε₀ d = univ ∧ StablePairs d then 1 else 0) *
          ENNReal.ofReal (dipoleWeight χ β lam d)) = 0 := by
    intro d
    by_cases hc : componentPartition M lam univ d = π
    · by_cases hd : typeTwoOneBad p₀ β lam M ε₀ d = univ ∧ StablePairs d
      · have hm : T ∈ componentPartition M lam univ d := hc ▸ hT
        obtain ⟨i, _, hi⟩ := mem_image.1 hm
        exact (hbad (hi ▸ typeTwoOne_classes hd.1 i)).elim
      · rw [ite_eq_right hd, zero_mul, mul_zero]
    · rw [ite_eq_right hc, zero_mul]
  simp_rw [hz, lintegral_zero]

/-- **The exponential bound for `Z^{(2,1)}`**: for every `y > 0`,
`Z^{(2,1)}_{bad,n} ≤ n! y^{-n} exp(∑_{m < n} 𝟙_{m+1 > p} b(m+1) y^{m+1} / (m+1)!)`. -/
theorem typeTwoOnePartitionFunction_le_exp (hχ : IsMollifier χ) (hlam : 0 < lam) (p₀ : ℕ)
    (ε₀ : ℝ) (Nₐ : ℕ) (b : ℕ → ℝ) (hb0 : ∀ m, 0 ≤ b m)
    (hb : ∀ T : Finset (Fin n), pBeta p₀ β < T.card →
      ∫⁻ y : T → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam (cutoff p₀ β lam ε₀) Nₐ) y ≤
        ENNReal.ofReal (b T.card)) {y : ℝ} (hy : 0 < y) :
    typeTwoOnePartitionFunction χ p₀ β lam M ε₀ Nₐ n ≤
      ENNReal.ofReal (n.factorial / y ^ n * Real.exp (∑ m ∈ Finset.range n,
        (if pBeta p₀ β < m + 1 then b (m + 1) else 0) / (m + 1).factorial * y ^ (m + 1))) := by
  classical
  unfold typeTwoOnePartitionFunction
  rw [← lintegral_indicator (measurableSet_boxPi Nₐ n)]
  refine (lintegral_mono fun d => typeTwoOne_indicator_le p₀ ε₀ Nₐ d).trans ?_
  convert lintegral_classWeight_le_exp (fun m => pBeta p₀ β < m)
    (measurable_cutDipoleWeight hχ hlam β _ Nₐ) b hb0 hb hy using 1
  congr 3
  apply sum_congr rfl
  intro m _
  by_cases hm : pBeta p₀ β < m + 1 <;> simp only [hm, ite_true, ite_false]


end BadPointTypes

end MultipoleBKT

end
