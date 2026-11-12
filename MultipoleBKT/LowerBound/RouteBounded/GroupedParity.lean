/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.ExpE11
public import MultipoleBKT.LowerBound.Hierarchical.ActivityIntegral
public import MultipoleBKT.LowerBound.RouteBounded.Counting

/-!
# The bounded grouped expansion and its parity reduction

The proof of Proposition 4.23, (4.73). Retain the Mayer groups and the separate
separation edge family before applying Corollary 4.34 inside each term.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical Multipole Parity
open scoped Classical

variable {ρ : Measure (ℂ × ℂ)} {β M lam : ℝ}
  {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)}

/-- The finite version of the grouped activity expansion. Its groups and
separation edges are those of the grouped identity, before parity.
proof of Proposition 4.23. -/
theorem modelActivity_eq_grouped
    {X : Finset (Finset ℕ)} (h2 : 2 ≤ X.card) :
    modelActivity ρ β w ψ M lam X =
      ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
            ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
              ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
                ∂modelHierarchical ρ β w ψ M lam X := by
  rw [modelActivity, ite_eq_right (by omega : ¬ X.card ≤ 1)]
  apply tsum_eq_sum
  intro n hn
  rw [mem_range, not_lt] at hn
  rw [sum_piFinset_relEdgeSets_eq_zero (by omega), mul_zero]

/-- The written counting reduction before parity. The factorial cancels
orderings of the connected Mayer families, leaving at most one term for
each pair of Mayer-union and separation edge sets.
(4.73), proof of Proposition 4.23. -/
theorem activity_le_of_cluster_integrals
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card)
    {k : ℕ} (hk : (X.biUnion id).card ≤ k) {Q : ℝ} (hQ : 0 ≤ Q)
    (hterm : ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ l m, l ≠ m → Disjoint (Xs l) (Xs m)) →
      ∀ Es : Fin n → Finset (ℕ × ℕ), (∀ l, Es l ∈ relEdgeSets (Xs l)) →
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
      |∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical ρ β w ψ M lam X| ≤ Q) :
    |modelActivity ρ β w ψ M lam X| ≤ 2 ^ (2 * k.choose 2) * Q := by
  rw [modelActivity_eq_grouped h2]
  calc
    _ ≤ ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
            ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)), Q := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro n _
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 / n.factorial by positivity)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro Xs hXs
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro Es hEs
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      exact hterm Xs (fun l => mem_powerset.1 (Fintype.mem_piFinset.1 (mem_filter.1 hXs).1 l))
        (mem_filter.1 hXs).2 Es (Fintype.mem_piFinset.1 hEs)
    _ = (∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
            ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)), (1 : ℝ)) * Q := by
      simp only [sum_mul, mul_assoc, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (factorial_grouped_count_le hX hk) hQ

/-- The maximum norm of the original grouped integrals. This is the
finite supremum in the nonnegative reals, including the length-zero
family. (4.73), proof of Proposition 4.23. -/
noncomputable def clusterIntegralMax (ρ : Measure (ℂ × ℂ)) (β : ℝ)
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ)
    (X : Finset (Finset ℕ)) : NNReal :=
  (range (X.card + 1)).sup fun n =>
    ((Fintype.piFinset fun _ : Fin n => X.powerset).filter
      (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j))).sup fun Xs =>
      (Fintype.piFinset fun l => relEdgeSets (Xs l)).sup fun Es =>
        (relEdgeSets₀ (coarsen X (univ.image Xs))).sup fun F =>
          ‖∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
            ∂modelHierarchical ρ β w ψ M lam X‖₊

/-- The displayed maximum estimate, with the paper's explicit coefficient.
(4.73), proof of Proposition 4.23. -/
theorem activity_le_max_cluster_integrals
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card)
    {k : ℕ} (hk : (X.biUnion id).card = k) :
    |modelActivity ρ β w ψ M lam X| ≤
      2 ^ (2 * k.choose 2) * (clusterIntegralMax ρ β w ψ M lam X : ℝ) := by
  apply activity_le_of_cluster_integrals hX h2 hk.le (NNReal.coe_nonneg _)
  intro n Xs hXs hd Es hEs F hF
  have hn : n < X.card + 1 := by
    by_contra hlt
    obtain ⟨l, hl⟩ := exists_card_le_one_of_card_lt (by omega : X.card < n) hXs hd
    have := hEs l
    rw [relEdgeSets_eq_empty_of_card_le_one hl] at this
    exact notMem_empty _ this
  have hXs' : Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
      (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) :=
    mem_filter.2 ⟨Fintype.mem_piFinset.2 fun l => mem_powerset.2 (hXs l), hd⟩
  have hEs' : Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l) := Fintype.mem_piFinset.2 hEs
  change (‖∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
    ∂modelHierarchical ρ β w ψ M lam X‖₊ : ℝ) ≤ _
  apply NNReal.coe_le_coe.mpr
  unfold clusterIntegralMax
  apply le_sup_of_le (mem_range.2 hn)
  apply le_sup_of_le hXs'
  apply le_sup_of_le hEs'
  exact le_sup (f := fun F => ‖∫ y, clusterTerm β w M lam Xs Es F
    (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X‖₊) hF

/-- The coefficient after the written counting step and the subsequent
parity expansion. The two factors record those separate steps.
(4.73) and the following display, proof of Proposition 4.23. -/
def parityCount (k : ℕ) : ℝ := 2 ^ (2 * k.choose 2) * 2 ^ k.choose 2

/-- Internal summation adapter for bounds on the individual grouped parity
integrals. The paper writes the same finite reduction as a maximum.
Proposition 4.23, (4.73), proof of Proposition 4.23. -/
theorem activity_le_of_grouped_integrals (h : ModelHyp ρ β w ψ K)
    (hρ : MeasurePreserving Prod.swap ρ ρ) (hw₁ : ∀ d e, w d.swap e = -w d e)
    (hw₂ : ∀ d e, w d e.swap = -w d e) (hψ : ∀ d, ψ d.swap = ψ d)
    (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C) (hM : 1 ≤ M)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card)
    {k : ℕ} (hk : (X.biUnion id).card ≤ k) {Q : ℝ} (hQ : 0 ≤ Q)
    (hterm : ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ l m, l ≠ m → Disjoint (Xs l) (Xs m)) →
      ∀ Es : Fin n → Finset (ℕ × ℕ), (∀ l, Es l ∈ relEdgeSets (Xs l)) →
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
      ∀ A ∈ (univ.biUnion Es).powerset.filter (· ∈ relEulerianPairs X),
      |∫ y, eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F
        (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X| ≤ Q) :
    |modelActivity ρ β w ψ M lam X| ≤ parityCount k * Q := by
  have hp : (pairsOn (X.biUnion id)).card ≤ k.choose 2 := by
    rw [card_pairsOn]
    exact Nat.choose_le_choose 2 hk
  have hb := activity_le_of_cluster_integrals (ρ := ρ) (β := β) (M := M) (lam := lam)
    (w := w) (ψ := ψ) hX h2 hk (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ k.choose 2) hQ) ?_
  · simpa only [parityCount, mul_assoc] using hb
  intro n Xs hXs hdisj Es hEs F hF
  rw [h.integral_clusterTerm_eq_sum_relEulerian hρ hw₁ hw₂ hψ hwb hM hX hXs
    (fun l => (mem_relEdgeSets.1 (hEs l)).1) (mem_relEdgeSets₀.1 hF).1]
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum (hterm Xs hXs hdisj Es hEs F hF)).trans
  rw [sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hQ
  have hsub : univ.biUnion Es ⊆ pairsOn (X.biUnion id) := biUnion_subset.2 fun l _ =>
    (mem_relEdgeSets.1 (hEs l)).1.trans ((interPairs_subset_of_subset hX (hXs l)).trans
      interPairs_subset_pairsOn)
  exact_mod_cast (card_filter_le _ _).trans (by
    rw [card_powerset]
    exact Nat.pow_le_pow_right (by norm_num) ((card_le_card hsub).trans hp))

end MultipoleBKT.LowerBound.RouteBounded

end
