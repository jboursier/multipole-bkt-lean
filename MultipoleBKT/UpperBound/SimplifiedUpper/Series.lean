/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.MergeSum
public import MultipoleBKT.UpperBound.SimplifiedUpper.PointBound
public import MultipoleBKT.UpperBound.AbsoluteUpper.Majorant
public import MultipoleBKT.UpperBound.BoundedUpper.JMeasurable

/-!
# The series over the outer groups and the trees (proof of Lemma 5.37)

The paper: proof of Lemma 5.37 ("as in the proof of Lemma 4.57"): the sum over the outer groups `X₁, …, Xₙ` (ordered, with
`1/n!`) of `∑_{T^b} ∏ b^abs ∏ₗ 𝒰(Xₗ)` is at most `2^{|X|} 𝒰(X)` (`sum_tuples_inner_le`, from
`merge_le`), and `𝒰(X)` is at most the series of the tree products of `J_{large,C₀}`
(`innerSeries_le_tuples`):
`𝒰(X) ≤ ∑_{n ≤ |X|} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint} ∑_{Tₗ^a ∈ 𝖳^{Xₗ}} ∑_{T^b ∈ 𝖳_0^{Coarse}}
  ∏_{T^b} b^abs ∏ₗ ∏_{S ∈ Xₗ, S ≠ Ŝₗ} r_S² ∏ₗ ∏_{Tₗ^a} d^{-2} 𝟙 𝟙_{𝓑^c}` (`treeProd`).

This algebra is used after the logarithmic predecessor factors have been absorbed
in `Activity` as in the proof of Lemma 4.57.

Also the measurability of the tree products (`measurable_treeProd`).
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Hierarchical Multipole SetPartition AbsoluteLower Parity

/-! ### Tuples of groups -/

section Tuples

open scoped Classical

/-- The ordered tuples of `n` pairwise disjoint subfamilies of `X`. -/
noncomputable def tuplesD (X : Finset (Finset ℕ)) (n : ℕ) : Finset (Fin n → Finset (Finset ℕ)) :=
  (Fintype.piFinset fun _ : Fin n => X.powerset).filter
    (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j))

/-- The ordered tuples of `n` pairwise disjoint subfamilies of `X` of at least two blocks. -/
noncomputable def tuplesT (X : Finset (Finset ℕ)) (n : ℕ) : Finset (Fin n → Finset (Finset ℕ)) :=
  (Fintype.piFinset fun _ : Fin n => X.powerset).filter
    (fun Xs => (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, 2 ≤ (Xs i).card)

theorem mem_tuplesT {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} :
    Xs ∈ tuplesT X n ↔ (∀ l, Xs l ⊆ X) ∧ (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧
      ∀ i, 2 ≤ (Xs i).card := by
  simp only [tuplesT, mem_filter, Fintype.mem_piFinset, mem_powerset]

theorem tuplesT_subset_tuplesD (X : Finset (Finset ℕ)) (n : ℕ) : tuplesT X n ⊆ tuplesD X n :=
  fun _ hXs => mem_filter.2 ⟨(mem_filter.1 hXs).1, (mem_filter.1 hXs).2.1⟩

theorem tuplesT_eq_empty {X : Finset (Finset ℕ)} {n : ℕ} (hn : X.card < n) : tuplesT X n = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro _ hXs
  obtain ⟨hXs, hdisj, h2⟩ := mem_tuplesT.1 hXs
  obtain ⟨l, hl⟩ := exists_eq_empty_of_card_lt hXs hdisj hn
  have := h2 l
  rw [hl, card_empty] at this
  omega

/-- **Tuples and sets**: for `H` on families of groups,
`∑_{n ≤ |X|} (1/n!) ∑_{(Xₗ) ∈ tuplesT} H({Xₗ}) = ∑_{𝒱 ∈ disjointFamilies} H(𝒱)`. -/
theorem sum_tuplesT_eq {X : Finset (Finset ℕ)} (H : Finset (Finset (Finset ℕ)) → ℝ) :
    ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) * ∑ Xs ∈ tuplesT X n, H (univ.image Xs) =
      ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card), H 𝒱 := by
  have hPne : ∀ Y : Finset (Finset ℕ), 2 ≤ Y.card → Y.Nonempty := fun Y h =>
    card_pos.1 (by omega)
  have key := tsum_tuples_image_eq_sum X.powerset (fun Y => 2 ≤ Y.card) hPne H
  rw [biUnion_powerset_id] at key
  obtain ⟨-, htsum⟩ := summable_and_tsum_eq_of_vanish (K := X.card)
    (f := fun n => 1 / (n.factorial : ℝ) * ∑ Xs ∈ tuplesT X n, H (univ.image Xs))
    fun n hn => by simp only [tuplesT_eq_empty hn, sum_empty, mul_zero]
  rw [← htsum]
  calc ∑' n, 1 / (n.factorial : ℝ) * ∑ Xs ∈ tuplesT X n, H (univ.image Xs)
      = ∑ 𝒱 ∈ (disjointFamilies X fun Y => 2 ≤ Y.card).filter (· ⊆ X.powerset), H 𝒱 := by
        convert key using 7 with n
        ext Xs
        simp only [tuplesT, mem_filter]
    _ = _ := by
        refine sum_congr ?_ fun _ _ => rfl
        exact filter_true_of_mem fun 𝒱 h𝒱 Y hY =>
          mem_powerset.2 ((mem_disjointFamilies.1 h𝒱).1 Y hY)

end Tuples

/-! ### The tree products -/

section TreeProd

open scoped Classical

variable (M lam ε₀ R : ℝ)

/-- The tree product of `J_{large,C₀}`:
`∏_{T^b} b^abs ∏ₗ ∏_{S ∈ Xₗ, S ≠ Ŝₗ} r_S² ∏ₗ ∏_{Tₗ^a} d^{-2} 𝟙_{d ≤ 17 ε₀ R̄} 𝟙_{𝓑^c}`. -/
noncomputable def treeProd {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
    (Tb : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ p ∈ Tb, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) * (∏ l, prodExceptMax c (Xs l)) *
    ∏ l, ∏ p ∈ Ta l, keptPair M lam ε₀ R c p

theorem treeProd_nonneg {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
    (Tb : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : 0 ≤ treeProd M lam ε₀ R Xs Ta Tb c :=
  mul_nonneg (mul_nonneg (prod_nonneg fun _ _ => absEvenWeight_nonneg _ _ _ _ _ _)
    (prod_nonneg fun _ _ => prodExceptMax_nonneg _))
    (prod_nonneg fun _ _ => prod_nonneg fun _ _ => keptPair_nonneg _)

theorem measurable_blockRad' (S : Finset ℕ) :
    Measurable fun c : ℕ → ℂ × ℂ => AbsoluteLower.blockRad c S := by
  unfold AbsoluteLower.blockRad
  refine measurable_coe_nnreal_real.comp (BoundedUpper.measurable_finset_sup_nnreal S fun i _ => ?_)
  exact (((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd).nnnorm)

theorem measurable_prodExceptMax (Y : Finset (Finset ℕ)) :
    Measurable fun c : ℕ → ℂ × ℂ => prodExceptMax c Y := by
  by_cases hY : Y.Nonempty
  · have h : (fun c : ℕ → ℂ × ℂ => prodExceptMax c Y) =
        Y.inf' hY fun S c => ∏ S' ∈ Y.erase S, AbsoluteLower.blockRad c S' ^ 2 := by
      funext c
      rw [prodExceptMax, dite_eq_left hY, Finset.inf'_apply]
    rw [h]
    refine Finset.inf'_induction hY _ (fun _f hf _g hg => hf.inf hg) fun S _ => ?_
    exact Finset.measurable_prod _ fun S' _ => (measurable_blockRad' S').pow_const 2
  · have h : (fun c : ℕ → ℂ × ℂ => prodExceptMax c Y) = fun _ => 1 := by
      funext c
      rw [prodExceptMax, dite_eq_right hY]
    rw [h]
    exact measurable_const

theorem measurable_keptPair (p : ℕ × ℕ) :
    Measurable fun c : ℕ → ℂ × ℂ => keptPair M lam ε₀ R c p := by
  unfold keptPair
  refine (Measurable.mul ?_ ?_).div ((BoundedUpper.measurable_dipoleDist_apply p.1 p.2).pow_const 2)
  · exact Measurable.ite (measurableSet_setOf_multipoleLinked M lam p.1 p.2) measurable_const
      measurable_const
  · exact Measurable.ite (measurableSet_le (BoundedUpper.measurable_dipoleDist_apply p.1 p.2)
      measurable_const) measurable_const measurable_const

theorem measurable_treeProd {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ)) :
    Measurable fun c => treeProd M lam ε₀ R Xs Ta Tb c := by
  unfold treeProd
  exact ((Finset.measurable_prod _ fun p _ => measurable_pairWeight
    (measurable_absEvenWeight M lam ε₀ R) p).mul
    (Finset.measurable_prod _ fun l _ => measurable_prodExceptMax (Xs l))).mul
    (Finset.measurable_prod _ fun l _ => Finset.measurable_prod _ fun p _ =>
      measurable_keptPair M lam ε₀ R p)

end TreeProd

/-! ### The two series bounds -/

section Bounds

open scoped Classical

variable {M lam ε₀ R : ℝ} {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (c : ℕ → ℂ × ℂ)
include hX

/-- **The merge of the outer and inner groups** (proof of Lemma 5.37). -/
theorem sum_tuples_inner_le :
    ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ tuplesT X n, treeWeightB M lam ε₀ R c X (univ.image Xs) *
          ∏ l, innerSeries M lam ε₀ R c (Xs l) ≤
      2 ^ X.card * innerSeries M lam ε₀ R c X := by
  have hterm : ∀ n, ∀ Xs ∈ tuplesT X n, treeWeightB M lam ε₀ R c X (univ.image Xs) *
      ∏ l, innerSeries M lam ε₀ R c (Xs l) =
      treeWeightB M lam ε₀ R c X (univ.image Xs) *
        ∏ X' ∈ univ.image Xs, innerSeries M lam ε₀ R c X' := by
    intro n Xs hXs
    obtain ⟨-, hdisj, h2⟩ := mem_tuplesT.1 hXs
    have hinj := injective_of_disjoint hdisj fun i => card_pos.1 (by have := h2 i; omega)
    rw [prod_image fun i _ j _ h => hinj h]
  rw [sum_congr rfl fun n _ => by rw [sum_congr rfl (hterm n)]]
  rw [sum_tuplesT_eq (fun 𝒲 => treeWeightB M lam ε₀ R c X 𝒲 *
    ∏ X' ∈ 𝒲, innerSeries M lam ε₀ R c X')]
  have h := merge_le hX (treeWeightA M lam ε₀ R c) (treeWeightA_nonneg M lam ε₀ R c)
    (fun q => absEvenWeight M lam ε₀ R (c q.1) (c q.2))
    (fun q => absEvenWeight_nonneg _ _ _ _ _ _)
  unfold innerSeries treeWeightB
  exact h

omit hX in
/-- **The inner series as a series of tree products** (the right-hand side of Lemma 5.37). -/
theorem innerSeries_le_tuples :
    innerSeries M lam ε₀ R c X ≤
      ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)), treeProd M lam ε₀ R Xs Ta Tb c := by
  have hexp : ∀ n, ∀ Xs ∈ tuplesT X n,
      (∏ Y ∈ univ.image Xs, treeWeightA M lam ε₀ R c Y) *
        treeWeightB M lam ε₀ R c X (univ.image Xs) =
      ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
        ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)), treeProd M lam ε₀ R Xs Ta Tb c := by
    intro n Xs hXs
    obtain ⟨-, hdisj, h2⟩ := mem_tuplesT.1 hXs
    have hinj := injective_of_disjoint hdisj fun i => card_pos.1 (by have := h2 i; omega)
    rw [prod_image fun i _ j _ h => hinj h]
    unfold treeWeightA treeWeightB treeProd
    rw [prod_mul_distrib, prod_univ_sum, mul_assoc (∏ l, prodExceptMax c (Xs l)), sum_mul_sum,
      mul_sum]
    refine sum_congr rfl fun Ta _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun Tb _ => ?_
    ring
  have h1 := sum_tuplesT_eq (X := X) (fun 𝒱 => (∏ Y ∈ 𝒱, treeWeightA M lam ε₀ R c Y) *
    treeWeightB M lam ε₀ R c X 𝒱)
  unfold innerSeries
  rw [← h1]
  refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [sum_congr rfl (hexp n)]
  exact sum_le_sum_of_subset_of_nonneg (tuplesT_subset_tuplesD X n) fun Xs _ _ =>
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => treeProd_nonneg _ _ _ _ _ _ _ _

end Bounds

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
