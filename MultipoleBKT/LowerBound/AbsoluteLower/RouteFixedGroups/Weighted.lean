/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.Endpoints
public import Mathlib.Analysis.MeanInequalities

/-!
# Weighted Cayley and arithmetic-geometric mean for relative trees

(A.65) and
(A.66) in the proof of Lemma 4.58. First sum edge endpoints in their blocks,
then apply weighted Cayley, arithmetic-geometric mean, and exponential absorption.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open Finset SimpleGraph Multipole SetPartition
open scoped Classical

/-- Endpoint summation followed by weighted Cayley, with the block sums retained. -/
theorem relative_weighted_cayley {Q : Finset (Finset ℕ)} (hQ : IsSubpartition Q)
    (hq : 2 ≤ Q.card) (L : ℕ → ℝ) (hL : ∀ i, 0 ≤ L i) :
    (∑ T ∈ relTreePairs₀ Q, ∏ p ∈ T, L p.1 * L p.2) ≤
      (∏ S ∈ Q, ∑ i ∈ S, L i) * (∑ i ∈ Q.biUnion id, L i) ^ (Q.card - 2) := by
  let b := blockOf hQ
  let x : Q.biUnion id → ℝ := fun i => L i
  let A := relTrees₀ Q
  let trees := (univ : Finset (SimpleGraph Q)).filter IsTree
  have hmaps : ∀ E ∈ A, blockQuotient b E ∈ trees := by
    intro E hE
    simp only [trees, mem_filter, mem_univ, true_and]
    rw [← quotientGraph_eq hQ]
    exact (mem_relTrees₀.mp hE).isTree_quotientGraph hQ
  have hprops (E : SimpleGraph (Q.biUnion id)) (hE : E ∈ A) :
      E ≤ crossBlockGraph b ∧ HasUniqueReps b E := by
    obtain ⟨hle, _, hF⟩ := (isRelTree₀_iff hQ).mp (mem_relTrees₀.mp hE)
    rw [interEdges_eq hQ] at hle
    rw [intraEdges_eq hQ] at hF
    exact ⟨hle, ((isRelForest_iff hle).mp hF).2⟩
  have hfiber (q : SimpleGraph Q) :
      (∑ E ∈ A.filter (fun E => blockQuotient b E = q), ∏ i, x i ^ E.degree i) ≤
        ∏ S, (∑ i ∈ univ.filter (fun i => b i = S), x i) ^ q.degree S := by
    let F := A.filter (fun E => blockQuotient b E = q)
    rw [Finset.sum_subtype F (fun _ => Iff.rfl)]
    have hsub : (∑ E : F, ∏ i, x i ^ E.val.degree i) ≤
        ∑ E : Lift b q, ∏ i, x i ^ E.val.degree i := by
      let f : F → Lift b q := fun E => ⟨E.val,
        (hprops E.val (mem_filter.mp E.property).1).1, (mem_filter.mp E.property).2,
        (hprops E.val (mem_filter.mp E.property).1).2⟩
      apply Finset.sum_le_sum_of_injOn f
      · exact fun E _ E' _ h => Subtype.ext (congrArg (fun E : Lift b q => E.val) h)
      · exact subset_univ _
      · exact fun E _ => le_rfl
      · exact fun E _ _ => prod_nonneg fun i _ => pow_nonneg (hL _) _
    exact hsub.trans (by
      convert sum_lifts_le b q x (fun i => hL i) using 1
      simp only [← Cayley.deg_eq_degree]
      apply prod_congr rfl
      intro S _
      congr 1
      apply sum_congr
      · ext i
        simp
      · intro i _
        rfl)
  have hblock (S : Q) : (∑ i ∈ univ.filter (fun i => b i = S), x i) = ∑ i ∈ S.val, L i := by
    apply sum_bij (fun (i : Q.biUnion id) _ => (i : ℕ))
    · intro i hi
      exact (blockOf_eq_iff hQ).mp (mem_filter.mp hi).2
    · exact fun i _ j _ h => Subtype.ext h
    · intro i hi
      refine ⟨⟨i, mem_biUnion.mpr ⟨S.val, S.property, hi⟩⟩,
        mem_filter.mpr ⟨mem_univ _, (blockOf_eq_iff hQ).mpr hi⟩, rfl⟩
    · exact fun _ _ => rfl
  rw [sum_relTreePairs₀_eq]
  have hedge (E : SimpleGraph (Q.biUnion id)) :
      (∏ p ∈ edgesOf E, L p.1 * L p.2) = ∏ i, x i ^ E.degree i := by
    rw [prod_edgesOf]
    exact prod_edges_endpoints E x
  simp_rw [hedge]
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine (sum_le_sum fun q _ => hfiber q).trans_eq ?_
  simp_rw [hblock]
  dsimp only [trees]
  have hc := sum_isTree_prod_pow_degree (by simpa using hq : 2 ≤ Fintype.card Q)
    (fun S : Q => ∑ i ∈ S.val, L i)
  have heq : (∑ T ∈ (univ : Finset (SimpleGraph Q)).filter IsTree,
      ∏ S : Q, (∑ i ∈ S.val, L i) ^ T.degree S) =
      (∏ S : Q, ∑ i ∈ S.val, L i) * (∑ S : Q, ∑ i ∈ S.val, L i) ^ (Q.card - 2) := by
    convert hc using 1
    · apply sum_congr
      · ext T
        simp
      · intro T _
        simp only [← Cayley.deg_eq_degree]
    · simp only [Fintype.card_coe]
  rw [heq]
  have hp := prod_coe_sort Q (fun S : Finset ℕ => ∑ i ∈ S, L i)
  have hs := sum_coe_sort Q (fun S : Finset ℕ => ∑ i ∈ S, L i)
  rw [hp, hs]
  rw [show (∑ S ∈ Q, ∑ i ∈ S, L i) = ∑ i ∈ Q.biUnion id, L i from (sum_biUnion hQ.2).symm]

/-- Arithmetic-geometric mean in the precise cardinality normalization used in the paper. -/
theorem block_amgm {B : Type*} [Fintype B] (hq : 0 < Fintype.card B)
    (x : B → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∏ i, x i) ≤ ((∑ i, x i) / Fintype.card B) ^ Fintype.card B := by
  have hqr : (0 : ℝ) < Fintype.card B := by exact_mod_cast hq
  have hm := Real.geom_mean_le_arith_mean (univ : Finset B) (fun _ => 1) x
    (fun _ _ => zero_le_one) (by simpa using hqr) (fun i _ => hx i)
  simp only [Real.rpow_one, sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul] at hm
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (prod_nonneg fun i _ => hx i) _) hm hqr.le
  rw [← Real.rpow_mul (prod_nonneg fun i _ => hx i), inv_mul_cancel₀ hqr.ne', Real.rpow_one,
    Real.rpow_natCast] at hp
  exact hp

/-- The literal first two bounds in the weighted logarithmic tree calculation. -/
theorem relative_weighted_amgm {Q : Finset (Finset ℕ)} (hQ : IsSubpartition Q)
    (hq : 2 ≤ Q.card) (L : ℕ → ℝ) (hL : ∀ i, 0 ≤ L i) :
    (∑ T ∈ relTreePairs₀ Q, ∏ p ∈ T, L p.1 * L p.2) ≤
      (∑ i ∈ Q.biUnion id, L i) ^ (2 * Q.card - 2) / (Q.card : ℝ) ^ Q.card := by
  have hS : 0 ≤ ∑ i ∈ Q.biUnion id, L i := sum_nonneg fun i _ => hL i
  have hm := block_amgm (B := Q) (by simpa using (by omega : 0 < Q.card))
    (fun S => ∑ i ∈ S.val, L i) (fun S => sum_nonneg fun i _ => hL i)
  have hp := prod_coe_sort Q (fun S : Finset ℕ => ∑ i ∈ S, L i)
  have hs := sum_coe_sort Q (fun S : Finset ℕ => ∑ i ∈ S, L i)
  rw [hp, hs, Fintype.card_coe] at hm
  rw [show (∑ S ∈ Q, ∑ i ∈ S, L i) = ∑ i ∈ Q.biUnion id, L i from
    (sum_biUnion hQ.2).symm] at hm
  refine (relative_weighted_cayley hQ hq L hL).trans ?_
  calc
    _ ≤ ((∑ i ∈ Q.biUnion id, L i) / Q.card) ^ Q.card *
        (∑ i ∈ Q.biUnion id, L i) ^ (Q.card - 2) :=
      mul_le_mul_of_nonneg_right hm (pow_nonneg hS _)
    _ = _ := by
      rw [div_pow, div_mul_eq_mul_div, ← pow_add]
      congr 2
      omega

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
