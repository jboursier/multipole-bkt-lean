/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.RouteDeterminant.Trace
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Incidence matrices for the determinant forest bound

An edge is oriented from its smaller endpoint to its larger endpoint. These integral
columns give the Laplacian as a Gram matrix. This supplies the incidence matrix used
in the proof of (4.71) in the proof of Lemma 4.49.
-/

@[expose] public section

namespace MultipoleBKT.Peeling.RouteDeterminant

open Finset Matrix SimpleGraph

variable {V : Type*} [LinearOrder V] [DecidableEq V]

/-- The smaller endpoint of an unordered pair. -/
def lowerEnd : Sym2 V → V := Sym2.lift ⟨min, min_comm⟩

/-- The larger endpoint of an unordered pair. -/
def upperEnd : Sym2 V → V := Sym2.lift ⟨max, max_comm⟩

omit [DecidableEq V] in
/-- The two ordered endpoints recover the unordered edge. -/
theorem endpoints_pair (e : Sym2 V) : s(lowerEnd e, upperEnd e) = e := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [lowerEnd, upperEnd, Sym2.lift_mk]
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, Sym2.eq_swap]

omit [DecidableEq V] in
/-- The endpoints of an edge are distinct. -/
private theorem endpoints_ne {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeSet) :
    lowerEnd e ≠ upperEnd e := by
  have ha : G.Adj (lowerEnd e) (upperEnd e) := by
    rw [← mem_edgeSet, endpoints_pair]
    exact he
  exact ha.ne

/-- The integral oriented incidence matrix, with one column for each edge of `G`. -/
def incidence (G : SimpleGraph V) : Matrix V G.edgeSet ℤ :=
  fun v e => (if v = lowerEnd e then 1 else 0) - (if v = upperEnd e then 1 else 0)

/-- Summing a column against a vertex function is its endpoint difference. -/
theorem sum_incidence_mul [Fintype V] (G : SimpleGraph V) (e : G.edgeSet) (f : V → ℝ) :
    ∑ v, f v * (incidence G v e : ℝ) = f (lowerEnd e) - f (upperEnd e) := by
  simp [incidence, mul_sub, sum_sub_distrib]

/-- The contribution of one edge to a diagonal entry of the incidence Gram matrix. -/
private theorem incidence_sq (G : SimpleGraph V) (v : V) (e : G.edgeSet) :
    (incidence G v e : ℝ) ^ 2 = if v ∈ e.val then 1 else 0 := by
  have hn := endpoints_ne e.property
  have hp := endpoints_pair e.val
  have hm : v ∈ e.val ↔ v = lowerEnd e.val ∨ v = upperEnd e.val := by
    conv_lhs => rw [← hp]
    exact Sym2.mem_iff
  simp only [hm, incidence, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]
  by_cases hl : v = lowerEnd e.val <;> by_cases hu : v = upperEnd e.val
  · exact False.elim (hn (hl.symm.trans hu))
  all_goals simp [hl, hu, hn, hn.symm]

/-- Off the diagonal only the edge joining the two specified vertices contributes. -/
private theorem incidence_mul_of_ne (G : SimpleGraph V) {u v : V} (huv : u ≠ v) (e : G.edgeSet) :
    (incidence G u e : ℝ) * (incidence G v e : ℝ) =
      if e.val = s(u, v) then -1 else 0 := by
  have hn := endpoints_ne e.property
  have hp := endpoints_pair e.val
  have heq : e.val = s(u, v) ↔
      (lowerEnd e.val = u ∧ upperEnd e.val = v) ∨
      (lowerEnd e.val = v ∧ upperEnd e.val = u) := by
    conv_lhs => rw [← hp]
    exact Sym2.eq_iff
  clear hp
  simp only [heq, incidence, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]
  by_cases hul : u = lowerEnd e.val <;> by_cases huu : u = upperEnd e.val <;>
    by_cases hvl : v = lowerEnd e.val <;> by_cases hvu : v = upperEnd e.val
  all_goals grind

/-- The oriented incidence Gram matrix is the graph Laplacian.
Equation (4.71) in the proof of Lemma 4.49. -/
theorem incidence_mul_transpose [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (incidence G).map (Int.castRingHom ℝ) *
      ((incidence G).map (Int.castRingHom ℝ))ᵀ = G.lapMatrix ℝ := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    change (∑ e : G.edgeSet, (incidence G u e : ℝ) * (incidence G u e : ℝ)) = _
    simp_rw [← sq, incidence_sq]
    rw [sum_boole]
    have hc : Fintype.card {e : G.edgeSet // u ∈ e.val} = G.degree u := by
      let eqv : {e : G.edgeSet // u ∈ e.val} ≃ G.incidenceSet u :=
        ⟨fun e => ⟨e.val.val, e.val.property, e.property⟩,
          fun e => ⟨⟨e.val, e.property.1⟩, e.property.2⟩, fun _ => rfl, fun _ => rfl⟩
      rw [Fintype.card_congr eqv]
      exact G.card_incidenceSet_eq_degree u
    simpa [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      Fintype.card_subtype] using congrArg (fun n : ℕ => (n : ℝ)) hc
  · change (∑ e : G.edgeSet, (incidence G u e : ℝ) * (incidence G v e : ℝ)) = _
    simp_rw [incidence_mul_of_ne G huv]
    calc (∑ e : G.edgeSet, if e.val = s(u, v) then (-1 : ℝ) else 0) =
          ∑ e ∈ G.edgeFinset, if e = s(u, v) then (-1 : ℝ) else 0 :=
        (Finset.sum_subtype G.edgeFinset (fun _ => mem_edgeFinset)
          (fun e => if e = s(u, v) then (-1 : ℝ) else 0)).symm
      _ = G.lapMatrix ℝ u v := by
        simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, huv, neg_ite]

end MultipoleBKT.Peeling.RouteDeterminant
