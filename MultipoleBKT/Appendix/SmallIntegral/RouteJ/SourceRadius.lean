/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.GroupedRadius
public import MultipoleBKT.LowerBound.Peeling.Quadratic

/-!
# The radius allocation for the subpartition

See Lemma A.4, (A.25).
The tree families, coarse partition and block radii here are those of `J`.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open Finset SimpleGraph Multipole SetPartition Limits Hierarchical Peeling BoundedLowerEps
open scoped Classical

variable {X : Finset (Finset ℕ)}

/-- Select a largest original radius in every block. The maximum agrees with
the paper's `blockRadius`, before regularization by λ. -/
theorem exists_block_radius_roots (hX : IsSubpartition X) (r : X.biUnion id → ℝ) :
    ∃ root : X → X.biUnion id, (∀ S, Limits.blockOf X (root S) = S) ∧
      (∀ S, r (root S) = blockRadius hX r S) ∧
      ∀ S i, Limits.blockOf X i = S → r i ≤ r (root S) := by
  have he (S : X) : ∃ i, MultipoleBKT.blockOf hX i = S ∧ r i = blockRadius hX r S := by
    unfold blockRadius
    obtain ⟨i, hi, heq⟩ := exists_mem_eq_sup'
      (s := univ.filter fun i => MultipoleBKT.blockOf hX i = S)
      (by
        obtain ⟨i, hi⟩ := MultipoleBKT.blockOf_surjective hX S
        exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩) r
    exact ⟨i, (mem_filter.mp hi).2, heq.symm⟩
  choose root hb hr using he
  have hroot (S : X) : Limits.blockOf X (root S) = S :=
    (Limits.blockOf_eq_iff hX _ S).mpr ((MultipoleBKT.blockOf_eq_iff hX).mp (hb S))
  refine ⟨root, hroot, hr, fun S i hi => ?_⟩
  rw [hr]
  unfold blockRadius
  apply le_sup'
  exact mem_filter.mpr ⟨mem_univ _, (MultipoleBKT.blockOf_eq_iff hX).mpr
    ((Limits.blockOf_eq_iff hX i S).mp hi)⟩

/-- The inequality (A.25) for the actual subpartition and tree data.
The output index is a largest original radius among all dipoles. -/
theorem source_radius_allocation (hX : IsSubpartition X) [Nonempty (X.biUnion id)]
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (Ta : Fin n → Finset (ℕ × ℕ)) (hTa : ∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf)
    (Tb : Finset (ℕ × ℕ))
    (hTb : Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf)
    (r : X.biUnion id → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hat : Fin n → X)
    (hhat : ∀ l, hat l ∈ (Xs l).subtype (· ∈ X) ∧
      ∀ S ∈ (Xs l).subtype (· ∈ X), blockRadius hX r S ≤ blockRadius hX r (hat l))
    (R : ∀ S : X, SimpleGraph {i // Limits.blockOf X i = S}) (hR : ∀ S, (R S).IsTree)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ i₀ : X.biUnion id, (∀ i, r i ≤ r i₀) ∧
      (∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hat l), blockRadius hX r S ^ 2) *
        (∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset,
          edgeMin (fun x => max x lam ^ 2) r e) *
        (∏ e ∈ nearForest (Limits.blockOf X) R,
          edgeMin (fun x => max x lam ^ 2) r e) ≤
            ∏ i ∈ univ.erase i₀, max (r i) lam ^ 2 := by
  obtain ⟨hG, hAG, hAc, _, hc, hcard⟩ := trees_structure hX hXs hdisj hTa hTb
  obtain ⟨root, hroot, hradius, hmax⟩ := exists_block_radius_roots hX r
  have hhmax : ∀ l S, S ∈ (Xs l).subtype (· ∈ X) → r (root S) ≤ r (root (hat l)) := by
    intro l S hS
    rw [hradius S, hradius (hat l)]
    exact (hhat l).2 S hS
  have h := grouped_radius_allocation (Limits.blockOf X) root hroot
    (fun l => (Xs l).subtype (· ∈ X)) hG
    (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset)
    (graphOf (X.biUnion id) Tb).edgeFinset hAG hAc hc hcard hat
    (fun l => (hhat l).1) r hr hmax hhmax R hR lam hlam
  simpa only [hradius] using h

end MultipoleBKT.SmallIntegral.RouteJ

end
