/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RoutePrufer.WordCount
public import MultipoleBKT.Appendix.RoutePrufer.Prufer
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma A.9: the weighted Cayley formula

The proof follows Lemma A.9. Group trees by their degree sequences. Prüfer's bijection identifies
trees of degrees `k i + 1` with words having multiplicities `k i`, whose number is
`(|V| - 2)! / ∏ i, (k i)!`. Shift the degrees by one and apply the multinomial theorem.

The encoding, its inverse, and the degree multiplicities are in `RoutePrufer`.
`sum_isTree_prod_pow_degree` holds over every commutative semiring. The real-valued
`sum_isTree_prod_pow_degree_fin` is the paper's normalized form, and
`card_isTree_eq_pow` is its specialization to unit weights.

The instance-free degree `Cayley.deg` avoids dependence on a chosen enumeration
of a neighbour set. `Cayley.deg_eq_degree` identifies it with Mathlib's degree.
-/

@[expose] public section

namespace MultipoleBKT

namespace Cayley

universe u

open SimpleGraph Finset
open scoped Classical

/-- **The degree-sequence count.** The number of trees on a vertex set `V` of size `n + 2` in
which vertex `i` has degree `k i + 1` (with `∑ k i = n`) is the multinomial coefficient
`n! / ∏ (k i)!`. -/
theorem card_degTrees :
    ∀ (n : ℕ) (V : Type u) [Fintype V], Fintype.card V = n + 2 → ∀ k : V → ℕ, ∑ i, k i = n →
      (degTrees k).card = Nat.multinomial univ k := by
  intro n V _ hV k hk
  let : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  calc (degTrees k).card = Fintype.card {T // T ∈ degTrees k} := (Fintype.card_coe _).symm
    _ = Fintype.card (Words n k) := Fintype.card_congr (degreePruferEquiv n V hV k hk)
    _ = Nat.multinomial univ k := card_words n V hV k hk

end Cayley

/-! ### Lemma A.9 -/

section Main

open Cayley
open SimpleGraph Finset
open scoped Classical

universe u v

/-- **Lemma A.9, weighted Cayley formula**. For a finite vertex set `V` with at least two elements, a commutative semiring `R` and weights `x : V → R`,
`∑_{T tree on V} ∏_i x_i ^ deg_T(i) = (∏_i x_i) (∑_i x_i) ^ (|V| - 2)`. -/
theorem sum_isTree_prod_pow_degree {V : Type u} [Fintype V] {R : Type v} [CommSemiring R]
    (hV : 2 ≤ Fintype.card V) (x : V → R) :
    ∑ T ∈ (Finset.univ : Finset (SimpleGraph V)).filter (fun T => T.IsTree),
        ∏ i, x i ^ T.degree i =
      (∏ i, x i) * (∑ i, x i) ^ (Fintype.card V - 2) := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n + 2 := ⟨Fintype.card V - 2, by omega⟩
  have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  simp only [← deg_eq_degree]
  set trees := (Finset.univ : Finset (SimpleGraph V)).filter (fun T => T.IsTree) with htrees
  have hmaps : ∀ T ∈ trees, (fun i => deg T i - 1) ∈ piAntidiag (univ : Finset V) n := by
    intro T hT
    have hT' : T.IsTree := (mem_filter.mp hT).2
    rw [mem_piAntidiag]
    refine ⟨?_, fun i _ => mem_univ i⟩
    have h1 : ∑ i, deg T i = 2 * (Fintype.card V - 1) := by
      have : Nonempty V := inferInstance
      exact sum_deg_of_isTree hT'
    have h2 : ∑ i, (deg T i - 1) = ∑ i, deg T i - ∑ _i : V, 1 :=
      Finset.sum_tsub_distrib _ fun i _ => one_le_deg_of_isTree hT' i
    simp only [sum_const, card_univ, smul_eq_mul, mul_one] at h2
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun T => fun i => deg T i - 1) hmaps]
  have hfiber : ∀ k ∈ piAntidiag (univ : Finset V) n,
      ∑ T ∈ trees with (fun i => deg T i - 1) = k, ∏ i, x i ^ deg T i =
        (Nat.multinomial univ k : R) * ((∏ i, x i) * ∏ i, x i ^ k i) := by
    intro k hk
    have hksum : ∑ i, k i = n := (mem_piAntidiag.mp hk).1
    have hset : trees.filter (fun T => (fun i => deg T i - 1) = k) = degTrees k := by
      ext T
      simp only [mem_filter, htrees, mem_univ, true_and, mem_degTrees]
      constructor
      · rintro ⟨hT, hk'⟩
        refine ⟨hT, fun i => ?_⟩
        have := one_le_deg_of_isTree hT i
        have h3 := congrFun hk' i
        omega
      · rintro ⟨hT, hdeg⟩
        refine ⟨hT, funext fun i => ?_⟩
        simp [hdeg i]
    rw [hset]
    have hterm : ∀ T ∈ degTrees k, ∏ i, x i ^ deg T i = (∏ i, x i) * ∏ i, x i ^ k i := by
      intro T hT
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [(mem_degTrees.mp hT).2 i, pow_succ, mul_comm]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      card_degTrees n V hn k hksum]
  rw [Finset.sum_congr rfl hfiber, show Fintype.card V - 2 = n by omega,
    Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Cayley's formula.** There are `|V| ^ (|V| - 2)` trees on a vertex set `V` with `|V| ≥ 2`
(the case `x = 1` of `sum_isTree_prod_pow_degree`). -/
theorem card_isTree_eq_pow {V : Type u} [Fintype V] (hV : 2 ≤ Fintype.card V) :
    ((Finset.univ : Finset (SimpleGraph V)).filter (fun T => T.IsTree)).card =
      Fintype.card V ^ (Fintype.card V - 2) := by
  have h := sum_isTree_prod_pow_degree (R := ℕ) hV (fun _ => 1)
  simpa using h

/-- **Lemma A.9, paper form.** For `S = {1, …, p}` (here `Fin p`) with `p ≥ 2` and real weights,
`∑_{T tree on S} ∏_{i ∈ S} x_i ^ deg_T(i) = p^(p-2) (∏_{i ∈ S} x_i) ((1/p) ∑_{i ∈ S} x_i)^(p-2)`. -/
theorem sum_isTree_prod_pow_degree_fin (p : ℕ) (hp : 2 ≤ p) (x : Fin p → ℝ) :
    ∑ T ∈ (Finset.univ : Finset (SimpleGraph (Fin p))).filter (fun T => T.IsTree),
        ∏ i, x i ^ T.degree i =
      (p : ℝ) ^ (p - 2) * (∏ i, x i) * ((1 / (p : ℝ)) * ∑ i, x i) ^ (p - 2) := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    exact this.ne'
  have h : ∑ T ∈ (Finset.univ : Finset (SimpleGraph (Fin p))).filter (fun T => T.IsTree),
        ∏ i, x i ^ T.degree i = (∏ i, x i) * (∑ i, x i) ^ (p - 2) := by
    convert sum_isTree_prod_pow_degree (R := ℝ) (V := Fin p) (by simpa using hp) x using 2
    · ext T
      simp
    · rw [Fintype.card_fin]
  have key : (p : ℝ) ^ (p - 2) * ((1 / (p : ℝ)) * ∑ i, x i) ^ (p - 2) = (∑ i, x i) ^ (p - 2) := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [h, mul_assoc, mul_left_comm, key]

end Main

end MultipoleBKT

end
