/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.Envelope

/-!
# Combining the allocated tree with the common original factors

See Step 3 of
the proof of Lemma A.7. Support, dipole density and
root gain are multiplied with the spatial estimate before integration.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases
open scoped Classical ENNReal

/-- Internal multiplication of a radius allocation by the original common
support and density. This lemma supplies no model hypotheses. -/
theorem internal_common_normalization {W B : Type*} [Fintype W] [DecidableEq W]
    [Fintype B] [DecidableEq B] (χ : ℂ → ℝ) (β M lam h : ℝ)
    (blk : W → B) (Dn Dz Df : Finset (Sym2 W)) (c : W → ℂ × ℂ)
    {z g : ℝ} {T : ℝ≥0∞} (hg : 0 ≤ g)
    (hn : ENNReal.ofReal z ≤ ENNReal.ofReal (∏ i, rhoD lam (c i) ^ 2) * T) :
    ENNReal.ofReal (clusterSupport M lam blk Dn Dz c * mixedDensity χ β lam h Df c * z * g) ≤
      ENNReal.ofReal g * T * activityDensity χ β lam h c := by
  have hS := clusterSupport_nonneg M lam blk Dn Dz c
  have hD := mixedDensity_nonneg χ β lam h Df c
  have hsp : ENNReal.ofReal (clusterSupport M lam blk Dn Dz c) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (clusterSupport_le_one M lam blk Dn Dz c)
  have hden := ENNReal.ofReal_le_ofReal (mixedDensity_le_cutDens χ β lam h Df c)
  rw [show clusterSupport M lam blk Dn Dz c * mixedDensity χ β lam h Df c * z * g =
      g * (clusterSupport M lam blk Dn Dz c * (mixedDensity χ β lam h Df c * z)) by ring,
    ENNReal.ofReal_mul hg,ENNReal.ofReal_mul hS,ENNReal.ofReal_mul hD]
  have hs := mul_le_mul' (le_refl (ENNReal.ofReal g)) (mul_le_mul' hsp (mul_le_mul' hden hn))
  refine hs.trans_eq ?_
  rw [one_mul]
  calc
    _ = ENNReal.ofReal g * T * (ENNReal.ofReal (∏ i, rhoD lam (c i) ^ 2) *
        ENNReal.ofReal (∏ i, cutDens χ β lam h (c i))) := by ring
    _ = _ := by rw [radial_mul_density]

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- The lifted odd-tree edges are still original odd edges. -/
theorem oddEdges_subset (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) {r : ℕ → ℝ} (F : OddFamily hX hOX hpar r) :
    oddEdges F ⊆ symOf (X.biUnion id) O := by
  intro e he
  obtain ⟨Y,-,he⟩ := mem_biUnion.1 he
  have hs : edgesOf (F.tree Y) ⊆ O := by
    rw [← graphPairs_eq_edgesOf]
    intro p hp
    exact sourceSkeletonEdges_subset hX hOX hpar
      (mem_biUnion.2 ⟨Y,mem_univ _,graphPairs_mono (F.tree_spec Y).2 hp⟩)
  induction e using Sym2.ind with
  | h i j =>
    rcases (mem_edgeFinset_graphOf_mk.1 he).2 with hp | hp
    · have hsort := (mem_pairsOn.1 (interPairs_subset_pairsOn (hOX (hs hp)))).2.2
      exact mem_symOf.2 ⟨i,j,hsort,hs hp,rfl⟩
    · have hsort := (mem_pairsOn.1 (interPairs_subset_pairsOn (hOX (hs hp)))).2.2
      exact mem_symOf.2 ⟨j,i,hsort,hs hp,Sym2.eq_swap⟩

/-- The even-tree ordered-pair carrier is the same symmetric edge carrier. -/
theorem evenEdges_eq_symOf (E : Finset (ℕ × ℕ)) (hE : E ⊆ pairsOn (X.biUnion id)) :
    (graphOf (X.biUnion id) E).edgeFinset = symOf (X.biUnion id) E := by
  ext e
  induction e using Sym2.ind with
  | h i j =>
    rw [mem_edgeFinset_graphOf_mk]
    constructor
    · rintro ⟨-,hp | hp⟩
      · exact mem_symOf.2 ⟨i,j,(mem_pairsOn.1 (hE hp)).2.2,hp,rfl⟩
      · exact mem_symOf.2 ⟨j,i,(mem_pairsOn.1 (hE hp)).2.2,hp,Sym2.eq_swap⟩
    · intro hh
      obtain ⟨a,b,hab,hp,he⟩ := mem_symOf.1 hh
      rcases Sym2.eq_iff.1 he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨fun he => hab.ne (Subtype.ext he),Or.inl hp⟩
      · exact ⟨fun he => hab.ne (Subtype.ext he.symm),Or.inr hp⟩

end MultipoleBKT.ExpansionK.RouteSpatial

end
