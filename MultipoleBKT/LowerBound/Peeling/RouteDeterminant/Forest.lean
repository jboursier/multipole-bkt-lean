/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.RouteDeterminant.Incidence
public import MultipoleBKT.LowerBound.Peeling.RouteDeterminant.Minors

/-!
# The forest inequality needed for the tree count

The incidence columns of a forest are independent. Each forest therefore contributes
at least one to the determinant expansion at (4.71) in the proof of Lemma 4.49. We do not evaluate the contribution or
prove a general matrix-forest formula.
-/

@[expose] public section

namespace MultipoleBKT.Peeling.RouteDeterminant

open Finset Matrix SimpleGraph

variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-- Summing over a component after deleting an edge isolates that edge's coefficient.
This proves independence of the incidence columns of a forest. -/
private theorem forest_incidence_injective (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsAcyclic) :
    Function.Injective ((incidence T).map (Int.castRingHom ℝ)).mulVec := by
  classical
  rw [Matrix.mulVec_injective_iff, Fintype.linearIndependent_iff]
  intro c hc e
  let a := lowerEnd e.val
  let b := upperEnd e.val
  have hab : T.Adj a b := by
    rw [← mem_edgeSet, endpoints_pair]
    exact e.property
  let H := T.deleteEdges {e.val}
  have hn : ¬ H.Reachable a b := by
    have hb := (isAcyclic_iff_forall_adj_isBridge.mp hT) hab
    rw [isBridge_iff, endpoints_pair] at hb
    exact hb
  let f : V → ℝ := fun v => if H.Reachable a v then 1 else 0
  have hf : ∀ d : T.edgeSet, f (lowerEnd d.val) - f (upperEnd d.val) =
      if d = e then 1 else 0 := by
    intro d
    by_cases hd : d = e
    · subst d
      simp [f, a, b, H, hn]
    · have hd' : d.val ≠ e.val := fun hh => hd (Subtype.ext hh)
      have ha : H.Adj (lowerEnd d.val) (upperEnd d.val) := by
        rw [deleteEdges_adj, endpoints_pair]
        exact ⟨by simpa only [← mem_edgeSet, endpoints_pair] using d.property,
          by simpa using hd'⟩
      have heq : H.Reachable a (lowerEnd d.val) ↔ H.Reachable a (upperEnd d.val) :=
        ⟨fun h => h.trans ha.reachable, fun h => h.trans ha.symm.reachable⟩
      simp [f, heq, hd]
  have hz : ∀ v, ∑ d : T.edgeSet, c d * (incidence T v d : ℝ) = 0 := by
    intro v
    have hh := congrFun hc v
    simpa [Matrix.col, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using hh
  have hs : ∑ d : T.edgeSet, c d *
      (f (lowerEnd d.val) - f (upperEnd d.val)) = 0 := by
    calc
      ∑ d : T.edgeSet, c d * (f (lowerEnd d.val) - f (upperEnd d.val)) =
          ∑ d : T.edgeSet, ∑ v, f v * (c d * (incidence T v d : ℝ)) := by
        apply sum_congr rfl
        intro d _
        rw [← sum_incidence_mul T d f, mul_sum]
        apply sum_congr rfl
        intro v _
        ring
      _ = ∑ v, f v * (∑ d : T.edgeSet, c d * (incidence T v d : ℝ)) := by
        rw [sum_comm]
        simp only [mul_sum]
      _ = 0 := by simp only [hz, mul_zero, sum_const_zero]
  simpa only [hf, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] using hs

omit [LinearOrder V] [DecidableEq V] in
/-- An independent integral incidence minor has Gram determinant at least one.
Cauchy–Binet supplies nonnegativity, independence excludes zero, and integrality
then gives the lower bound needed in the proof of Lemma 4.49. -/
private theorem one_le_integral_gram_det {E : Type*} [Fintype E] [DecidableEq E]
    (B : Matrix V E ℤ) (hB : Function.Injective (B.map (Int.castRingHom ℝ)).mulVec) :
    1 ≤ ((B.map (Int.castRingHom ℝ))ᵀ * B.map (Int.castRingHom ℝ)).det := by
  let C := B.map (Int.castRingHom ℝ)
  have hpos : 0 < (Cᵀ * C).det := by
    have hp := Matrix.PosDef.conjTranspose_mul_self C hB
    simpa only [conjTranspose_eq_transpose_of_trivial] using hp.det_pos
  have hcast : ((Bᵀ * B).det : ℝ) = (Cᵀ * C).det := by
    change (Int.castRingHom ℝ) (Bᵀ * B).det = _
    rw [RingHom.map_det]
    congr 1
    exact Matrix.map_mul
  have hz : 0 < (Bᵀ * B).det := by
    have hh : (0 : ℝ) < ((Bᵀ * B).det : ℝ) := by rw [hcast]; exact hpos
    exact_mod_cast hh
  have hi : 1 ≤ (Bᵀ * B).det := hz
  rw [← hcast]
  exact_mod_cast hi

open scoped Classical in
/-- The columns of `G` indexed by the edges of a subgraph `T`. -/
noncomputable def edgeIndices (G T : SimpleGraph V) : Finset G.edgeSet :=
  univ.filter fun e => e.val ∈ T.edgeSet

/-- The selected columns are indexed by the edges of the subgraph. -/
private noncomputable def edgeIndicesEquiv (G T : SimpleGraph V) (hTG : T ≤ G) :
    edgeIndices G T ≃ T.edgeSet := by
  classical
  refine
    { toFun := fun e => ⟨e.val.val, ?_⟩
      invFun := fun e => ⟨⟨e.val, SimpleGraph.edgeSet_mono hTG e.property⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · exact (mem_filter.mp e.property).2
  · exact mem_filter.mpr ⟨mem_univ _, e.property⟩

/-- Every forest in `G` contributes a positive integral Gram minor.
Equation (4.71) in the proof of Lemma 4.49. -/
theorem one_le_forest_minor (G T : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel T.Adj] (hTG : T ≤ G) (hT : T.IsAcyclic) :
    1 ≤ ((((incidence G).submatrix id (fun e : edgeIndices G T => e.val)).map
      (Int.castRingHom ℝ))ᵀ *
      ((incidence G).submatrix id (fun e : edgeIndices G T => e.val)).map
        (Int.castRingHom ℝ)).det := by
  apply one_le_integral_gram_det
  rw [Matrix.mulVec_injective_iff]
  have h := (Matrix.mulVec_injective_iff.mp (forest_incidence_injective T hT)).comp
    (edgeIndicesEquiv G T hTG) (edgeIndicesEquiv G T hTG).injective
  exact h

omit [LinearOrder V] [DecidableEq V] in
/-- Distinct subgraphs of `G` select distinct sets of incidence columns. -/
private theorem edgeIndices_eq_imp {G T U : SimpleGraph V}
    (hTG : T ≤ G) (hUG : U ≤ G) (h : edgeIndices G T = edgeIndices G U) : T = U := by
  classical
  apply SimpleGraph.edgeSet_injective
  ext e
  constructor
  · intro he
    have heG := SimpleGraph.edgeSet_mono hTG he
    have hi : (⟨e, heG⟩ : G.edgeSet) ∈ edgeIndices G T := mem_filter.mpr ⟨mem_univ _, he⟩
    rw [h] at hi
    exact (mem_filter.mp hi).2
  · intro he
    have heG := SimpleGraph.edgeSet_mono hUG he
    have hi : (⟨e, heG⟩ : G.edgeSet) ∈ edgeIndices G U := mem_filter.mpr ⟨mem_univ _, he⟩
    rw [← h] at hi
    exact (mem_filter.mp hi).2

/-- The number of forests in any finite family of subgraphs of `G` is bounded by
`det(I + L_G)`. This is the forest inequality used at (4.71) in the proof of Lemma 4.49. It requires no matrix-forest evaluation. -/
theorem card_forests_le_det (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (SimpleGraph V)) (hFG : ∀ T ∈ F, T ≤ G)
    (hF : ∀ T ∈ F, T.IsAcyclic) :
    (F.card : ℝ) ≤ (1 + G.lapMatrix ℝ).det := by
  classical
  let B := (incidence G).map (Int.castRingHom ℝ)
  let minor (s : Finset G.edgeSet) :=
    ((B.submatrix id (fun i : s => i.val))ᵀ * B.submatrix id (fun i : s => i.val)).det
  have hnonneg : ∀ s, 0 ≤ minor s := fun s => gram_det_nonneg _
  have hinj : Set.InjOn (edgeIndices G) F := by
    intro T hT U hU h
    exact edgeIndices_eq_imp (hFG T hT) (hFG U hU) h
  calc
    (F.card : ℝ) = ∑ T ∈ F, (1 : ℝ) := by simp
    _ ≤ ∑ T ∈ F, minor (edgeIndices G T) := by
      apply sum_le_sum
      intro T hT
      exact one_le_forest_minor G T (hFG T hT) (hF T hT)
    _ = ∑ s ∈ F.image (edgeIndices G), minor s := (sum_image hinj).symm
    _ ≤ ∑ s : Finset G.edgeSet, minor s := sum_le_univ_sum_of_nonneg hnonneg
    _ = (1 + B * Bᵀ).det := (det_one_add_gram B).symm
    _ = (1 + G.lapMatrix ℝ).det := by rw [incidence_mul_transpose]

end MultipoleBKT.Peeling.RouteDeterminant
