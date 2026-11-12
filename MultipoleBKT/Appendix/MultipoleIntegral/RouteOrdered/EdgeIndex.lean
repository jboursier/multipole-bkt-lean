/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.TreeUnion
public import MultipoleBKT.Appendix.MultipoleIntegral.TreeIntegral

/-!
# Indexing tree edges by non-root children

See (A.9) and (A.10). Orient a tree towards its root. The selected endpoint on
an edge is then indexed by its child, without duplicating the root slot.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open Finset SimpleGraph
open scoped Classical ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A decreasing parent map cannot orient the same edge twice. -/
theorem parentEdge_injective {root : ι} {par : ι → ι} (hpar : IsParentMap root par) :
    Function.Injective (fun c : {i // i ≠ root} => s(c.1, par c.1)) := by
  obtain ⟨rank, hrank⟩ := hpar
  intro a b hab
  rcases Sym2.eq_iff.mp hab with h | h
  · exact Subtype.ext h.1
  · have ha := hrank a.1 a.2
    have hb := hrank b.1 b.2
    rw [h.2] at ha
    rw [← h.1] at hb
    omega

/-- Every tree edge occurs exactly once as a child-parent edge. -/
theorem parentEdge_bijective {T : SimpleGraph ι} (hT : T.IsTree)
    {root : ι} {par : ι → ι} (hpar : IsParentMap root par)
    (hadj : ∀ c, c ≠ root → T.Adj c (par c)) :
    Function.Bijective (fun c : {i // i ≠ root} =>
      (⟨s(c.1, par c.1), by simpa using hadj c.1 c.2⟩ : T.edgeSet)) := by
  classical
  have hinj : Function.Injective (fun c : {i // i ≠ root} =>
      (⟨s(c.1, par c.1), by simpa using hadj c.1 c.2⟩ : T.edgeSet)) := by
    intro a b h
    exact parentEdge_injective hpar (congrArg Subtype.val h)
  refine ⟨hinj, (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩ |>.2⟩
  have h1 := hT.card_edgeFinset
  have h2 : Fintype.card {i // i ≠ root} + 1 = Fintype.card ι :=
    by simpa only [← Nat.card_eq_fintype_card] using Cayley.card_subtype_ne_add_one root
  rw [← edgeFinset_card]
  omega

/-- The explicit edge equivalence used to transfer endpoint assignments. -/
noncomputable def parentEdgeEquiv {T : SimpleGraph ι} (hT : T.IsTree)
    {root : ι} {par : ι → ι} (hpar : IsParentMap root par)
    (hadj : ∀ c, c ≠ root → T.Adj c (par c)) : {i // i ≠ root} ≃ T.edgeSet :=
  Equiv.ofBijective _ (parentEdge_bijective hT hpar hadj)

/-- Reindex a tree product along the child-edge bijection. -/
theorem prod_edges_eq_prod_children {T : SimpleGraph ι} (hT : T.IsTree)
    {root : ι} {par : ι → ι} (hpar : IsParentMap root par)
    (hadj : ∀ c, c ≠ root → T.Adj c (par c))
    {R : Type*} [CommMonoid R] (f : Sym2 ι → R) :
    ∏ e ∈ T.edgeFinset, f e = ∏ c ∈ univ.erase root, f s(c, par c) := by
  have h := (parentEdgeEquiv hT hpar hadj).prod_comp (fun e : T.edgeSet => f e.1)
  rw [Finset.prod_subtype (p := fun e => e ∈ T.edgeSet) T.edgeFinset (by simp) f]
  rw [Finset.prod_subtype (p := fun i => i ≠ root) (univ.erase root) (by simp) (fun c => f s(c, par c))]
  exact h.symm

/-- Endpoint assignments on actual edges and on non-root children are
in bijection. The product on each assignment is preserved. -/
theorem sum_endpointAssignments_eq {T : SimpleGraph ι} (hT : T.IsTree)
    {root : ι} {par : ι → ι} (hpar : IsParentMap root par)
    (hadj : ∀ c, c ≠ root → T.Adj c (par c))
    (f : T.edgeSet → Fin 4 → ℝ≥0∞) :
    ∑ l : T.edgeSet → Fin 4, ∏ e, f e (l e) =
      ∑ l : {i // i ≠ root} → Fin 4,
        ∏ c, f (parentEdgeEquiv hT hpar hadj c) (l c) := by
  rw [← Fintype.prod_sum, ← Fintype.prod_sum]
  exact ((parentEdgeEquiv hT hpar hadj).prod_comp (fun e => ∑ l, f e l)).symm

end MultipoleBKT.MultipoleIntegral

end
