/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.RouteChromatic.Coloring
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The whole connection-graph chromatic polynomial

Rooted incidence-tree coloring gives the product polynomial. Its values at all
positive integers identify it with Whitney's chromatic polynomial. Taking the
linear coefficient proves (4.150), as in the paper.
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph Polynomial

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- Proper coloring of the connection graph means that the colors on every
incidence set are pairwise distinct. -/
theorem proper_connectionGraph_iff_injOn_incidence (X : Fin n → Finset α)
    {β : Type*} (f : Fin n → β) :
    (∀ i j, (connectionGraph X).Adj i j → f i ≠ f j) ↔
      ∀ a : (univ.biUnion X : Finset α), Set.InjOn f (incidence X a.val) := by
  constructor
  · intro h a i hi j hj hij
    by_contra hne
    exact h i j (connectionGraph_adj.mpr
      ⟨hne, a.val, mem_incidence.mp hi, mem_incidence.mp hj⟩) hij
  · intro h i j hij heq
    obtain ⟨hne, a, hai, haj⟩ := connectionGraph_adj.mp hij
    let a' : (univ.biUnion X : Finset α) := ⟨a, mem_biUnion.mpr ⟨i, mem_univ _, hai⟩⟩
    exact hne (h a' (mem_incidence.mpr hai) (mem_incidence.mpr haj) heq)

open scoped Classical in
/-- Count proper colorings along the incidence tree. There are `t` choices for
the root, then `(t-1) ⋯ (t-d_a+1)` choices at each element `a`.
See equation (4.150). -/
theorem card_proper_colorings_of_mem_hypertrees {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) (t : ℕ) :
    (univ.filter fun f : Fin n → Fin t =>
      ∀ i j, (connectionGraph X).Adj i j → f i ≠ f j).card =
      t * ∏ a ∈ univ.biUnion X, (t - 1).descFactorial ((incidence X a).card - 1) := by
  obtain ⟨r⟩ := (connectionGraph_connected_of_mem_hypertrees hX).nonempty
  cases t with
  | zero =>
    have : IsEmpty (Fin n → Fin 0) := ⟨fun f => Fin.elim0 (f r)⟩
    simp
  | succ t =>
    obtain ⟨R⟩ := RouteChromatic.exists_rooting hX r
    have heq : {f : Fin n → Fin (t + 1) //
        ∀ i j, (connectionGraph X).Adj i j → f i ≠ f j} ≃
        {f : Fin n → Fin (t + 1) //
          ∀ a : (univ.biUnion X : Finset α), Set.InjOn f (incidence X a.val)} :=
      Equiv.subtypeEquivRight fun f => proper_connectionGraph_iff_injOn_incidence X f
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      Nat.card_congr heq, R.card_colorings, Nat.add_sub_cancel]
    congr 1
    exact Finset.prod_coe_sort (univ.biUnion X)
      (fun a => t.descFactorial ((incidence X a).card - 1))

/-- The polynomial displayed in the incidence-tree coloring argument. The inner
index `j+1` runs from `1` through `d_a-1`. -/
noncomputable def hypertreeChromaticPoly (X : Fin n → Finset α) : ℤ[X] :=
  Polynomial.X * ∏ a ∈ univ.biUnion X,
    ∏ j ∈ range ((incidence X a).card - 1), (Polynomial.X - C (j + 1 : ℤ))

private theorem eval_hypertreeChromaticPoly_succ (X : Fin n → Finset α) (t : ℕ) :
    (hypertreeChromaticPoly X).eval ((t : ℤ) + 1) =
      ((t + 1) * ∏ a ∈ univ.biUnion X,
        t.descFactorial ((incidence X a).card - 1) : ℕ) := by
  simp only [hypertreeChromaticPoly, eval_mul, eval_X, eval_prod,
    eval_sub, eval_C, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_prod]
  congr 1
  apply prod_congr rfl
  intro a _
  simp only [add_sub_add_right_eq_sub]
  rw [← descPochhammer_eval_eq_prod_range,
    descPochhammer_eval_eq_descFactorial]

/-- The full connection-graph chromatic polynomial of a hypertree is
`T ∏_a ∏_{j=1}^{d_a-1} (T-j)`. It is identified by its coloring counts at all
positive integers, rather than by factoring connected subgraph sums.
See equation (4.150). -/
theorem chromaticPoly_connectionGraph_of_mem_hypertrees {A : Finset α}
    {X : Fin n → Finset α} (hX : X ∈ hypertrees n A) :
    chromaticPoly (connectionGraph X) = hypertreeChromaticPoly X := by
  classical
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective
    (fun i j h => Nat.cast_injective (add_right_cancel h) :
      Function.Injective fun t : ℕ => (t : ℤ) + 1))
  rintro _ ⟨t, rfl⟩
  simp only [Set.mem_ofPred_eq]
  rw [eval_hypertreeChromaticPoly_succ, ← Nat.cast_add_one, eval_chromaticPoly]
  have h := card_proper_colorings_of_mem_hypertrees hX (t + 1)
  simp only [Nat.add_sub_cancel] at h
  convert congrArg (fun k : ℕ => (k : ℤ)) h using 2
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and]

private theorem prod_neg_range (k : ℕ) :
    ∏ j ∈ range k, (-(j + 1 : ℤ)) = (-1) ^ k * (k.factorial : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih, pow_succ, Nat.factorial_succ]
    push_cast
    ring

/-- Extracting the linear coefficient gives the sign and the hypertree weight.
See equation (4.150). -/
theorem coeff_one_hypertreeChromaticPoly {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) :
    (hypertreeChromaticPoly X).coeff 1 = (-1) ^ (n - 1) * (hypertreeWeight X : ℤ) := by
  classical
  have hn : 1 ≤ n := Fin.pos_iff_nonempty.mpr
    (connectionGraph_connected_of_mem_hypertrees hX).nonempty
  have hdeg : ∑ a ∈ univ.biUnion X, ((incidence X a).card - 1) = n - 1 := by
    have hs := sum_card_incidence_sub_one hX
    have hpos : ∀ a ∈ univ.biUnion X, 1 ≤ (incidence X a).card :=
      fun a ha => card_pos.mpr (incidence_nonempty ha)
    have hc : ((∑ a ∈ univ.biUnion X, ((incidence X a).card - 1) : ℕ) : ℤ) =
        ((n - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Nat.cast_sub hn]
      rw [sum_congr rfl fun a ha => Nat.cast_sub (hpos a ha)]
      exact hs
    exact_mod_cast hc
  rw [hypertreeChromaticPoly, coeff_X_mul, coeff_zero_eq_eval_zero]
  simp only [eval_prod, eval_sub, eval_X, eval_C, zero_sub]
  rw [prod_congr rfl fun a _ => prod_neg_range ((incidence X a).card - 1),
    prod_mul_distrib, prod_pow_eq_pow_sum, hdeg, hypertreeWeight, Nat.cast_prod]
  rfl

end MultipoleBKT

end
