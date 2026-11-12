/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Compact
public import MultipoleBKT.Multipole.RouteGrouping.Union

/-!
# Reading off the connected weight of the expanded pairs

See the paper, equation (4.36).
The separation edges connect the contracted Mayer components exactly when the
union of both edge families connects the original blocks. The formula retains
singleton Mayer components, whose edge set is empty.
-/

public section

namespace MultipoleBKT.Multipole.RouteGrouping

open Finset SetPartition Hierarchical
open scoped Classical

/-- The separation-edge sum after contracting the Mayer components is the sum
with the connecting condition on the union graph in (4.36). -/
theorem separation_sum_eq_union {D : Finset (Finset ℕ)} (hD : IsSubpartition D)
    {σ : Finset (Finset (Finset ℕ))} (hσ : σ ∈ partitions D)
    {E : Finset (ℕ × ℕ)} (hE : E ⊆ σ.biUnion interPairs)
    (hc : ∀ T ∈ σ, ConnOn (T.biUnion id) ((E ∩ interPairs T) ∪ intraPairs T))
    (b : ℕ × ℕ → ℝ) :
    relConnSum (fun p => -b p) (merge σ) =
      ∑ F ∈ (interPairs (merge σ)).powerset.filter
        (fun F => ConnOn (D.biUnion id) ((E ∪ F) ∪ intraPairs D)), ∏ p ∈ F, -b p := by
  have hU : (merge σ).biUnion id = D.biUnion id :=
    (mem_partitions.1 (merge_mem_partitions hD hσ)).2
  unfold relConnSum
  rw [hU]
  congr 1
  ext F
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => (union_connected_iff hσ hE hc).symm

/-- The weight of a union component is the direct sum over its first connected
edge families and its separation edges. Connectivity is imposed on their union,
as in the displayed definition of `F(X)` following (4.36). -/
theorem groupWeight_eq_expanded_union (f b : ℕ × ℕ → ℝ)
    {D : Finset (Finset ℕ)} (hD : IsSubpartition D) :
    groupWeight f b D =
      ∑ σ ∈ partitions D,
        ∑ Es ∈ Fintype.piFinset (fun T : σ => relEdgeSets₀ T.1),
          ∑ F ∈ (interPairs (merge σ)).powerset.filter
            (fun F => ConnOn (D.biUnion id) (((Finset.univ.biUnion Es) ∪ F) ∪ intraPairs D)),
            (∏ T : σ, (∏ p ∈ Es T, f p) * ∏ p ∈ interPairs T.1, (1 - b p)) *
              ∏ p ∈ F, -b p := by
  unfold groupWeight
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hprod : (∏ T ∈ σ, groupFactor f b T) =
      ∑ Es ∈ Fintype.piFinset (fun T : σ => relEdgeSets₀ T.1),
        ∏ T : σ, (∏ p ∈ Es T, f p) * ∏ p ∈ interPairs T.1, (1 - b p) := by
    rw [← Finset.prod_coe_sort σ (groupFactor f b)]
    simp only [groupFactor, relConnSum_eq_sum_relEdgeSets₀, Finset.sum_mul]
    exact Finset.prod_univ_sum _ _
  rw [hprod, Finset.sum_mul]
  refine Finset.sum_congr rfl fun Es hEs => ?_
  have hconn : ∀ T : σ, ConnOn (T.1.biUnion id) (Es T ∪ intraPairs T.1) :=
    fun T => (mem_relEdgeSets₀.1 (Fintype.mem_piFinset.1 hEs T)).2
  have hsub : ∀ T : σ, Es T ⊆ interPairs T.1 :=
    fun T => (mem_relEdgeSets₀.1 (Fintype.mem_piFinset.1 hEs T)).1
  have hE : Finset.univ.biUnion Es ⊆ σ.biUnion interPairs := by
    intro p hp
    obtain ⟨T, _, hp⟩ := Finset.mem_biUnion.1 hp
    exact Finset.mem_biUnion.2 ⟨T.1, T.2, hsub T hp⟩
  have hc : ∀ T ∈ σ, ConnOn (T.biUnion id)
      (((Finset.univ.biUnion Es) ∩ interPairs T) ∪ intraPairs T) := by
    intro T hT
    refine ⟨(hconn ⟨T, hT⟩).1, fun i hi j hj => ((hconn ⟨T, hT⟩).2 i hi j hj).mono ?_⟩
    apply edgeGraph_mono
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · exact Finset.mem_union_left _ (Finset.mem_inter.2
        ⟨Finset.mem_biUnion.2 ⟨⟨T, hT⟩, Finset.mem_univ _, hp⟩, hsub ⟨T, hT⟩ hp⟩)
    · exact Finset.mem_union_right _ hp
  rw [separation_sum_eq_union hD hσ hE hc b, Finset.mul_sum]

end MultipoleBKT.Multipole.RouteGrouping
