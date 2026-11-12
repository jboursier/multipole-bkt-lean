/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.Quadratic
public import MultipoleBKT.Limits.RouteOdd.Assembly

/-!
# Opening the prescribed marked base cycle

See case D of
the proof of Lemma A.7, (A.59) and (A.60).
Choose a strict ear decomposition whose first edge is marked. Delete that edge
from the base cycle and use the endpoint-score rule on every later ear.
The resulting tree excludes the mark. Its bound retains every spatial indicator.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Peeling

variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ]
variable {b : V → κ} {E : SimpleGraph V} {x y : V}

/-- The case-D deletion data. The base deletion is prescribed, while later ears
obey the peeling rule. The marked edge cannot occur in a later ear. -/
structure MarkedEarData (b : V → κ) (E : SimpleGraph V) (r : V → ℝ)
    (d : Sym2 V → ℝ) (R : ℝ) (x y : V)
    (P : Ear V) (Qs : List (Ear V × (V × V))) : Prop where
  first_eq : P.first = (x, y)
  decomp : IsStrictEarDecompOn b E (b x) (P :: Qs.map Prod.fst)
  later_rule : IsPeelingSeq b r d R s(x, y) (P.blocks b) Qs

omit [Fintype V] in
/-- Select the strict ears with the marked edge first. This is the prescribed
choice of Lemma 4.40 used in case D, rather than a tree completion. -/
theorem exists_marked_ears (hb : Function.Surjective b) (hE : E ≤ crossBlockGraph b)
    (hmin : MinTwoEdgeConnOn b E) (hxy : E.Adj x y)
    (r : V → ℝ) (d : Sym2 V → ℝ) (R : ℝ) :
    ∃ P Qs, MarkedEarData b E r d R x y P Qs := by
  obtain ⟨P, Ps, hfirst, hdecomp⟩ := exists_isStrictEarDecompOn_first hb hE hmin hxy
  obtain ⟨Qs, hQs, hrule⟩ := exists_isPeelingSeq (r := r) (d := d) (R := R) (e₀ := s(x, y))
    (subset_union_right : P.blocks b ⊆ {b x} ∪ P.blocks b) hdecomp.isEarSeq.2
  rw [← hQs] at hdecomp
  exact ⟨P, Qs, hfirst, hdecomp, hrule⟩

namespace MarkedEarData

variable {r : V → ℝ} {d : Sym2 V → ℝ} {R : ℝ} {P : Ear V}
variable {Qs : List (Ear V × (V × V))}
variable (h : MarkedEarData b E r d R x y P Qs)

include h

omit [Fintype V]

omit [DecidableEq V] in
/-- The prescribed base deletion together with the later deletions removes one
edge from each ear. -/
theorem isRemoval : IsRemoval ((P, (x, y)) :: Qs) := by
  intro Q hQ
  rcases List.mem_cons.1 hQ with rfl | hQ
  · rw [← h.first_eq]
    exact List.mem_map_of_mem P.first_mem_toList
  · exact h.later_rule.isRemoval Q hQ

omit [DecidableEq V] in
/-- The marked base edge is absent from every later ear. Thus the later peeling
rule always uses item (2), regardless of the length of the marked edge. -/
theorem mark_not_later : s(x, y) ∉ (Qs.map Prod.fst).flatMap Ear.edges := by
  have hnd := h.decomp.nodup
  rw [List.flatMap_cons, List.nodup_append] at hnd
  intro hm
  exact hnd.2.2 s(x, y)
    (by simpa only [h.first_eq, Peeling.edge, Ear.edges] using List.mem_map_of_mem (f := Peeling.edge) P.first_mem_toList) s(x, y) hm rfl

omit [DecidableEq V] in
/-- Every later ear uses the endpoint-score deletion, exactly item (2) of
Definition 4.43. -/
theorem later_score_rule {Q : Ear V × (V × V)} (hQ : Q ∈ Qs) :
    (Q.2 = Q.1.first.swap ∧ peelScore r d (edge Q.1.last) ≤ peelScore r d (edge Q.1.first)) ∨
      (Q.2 = Q.1.last ∧ peelScore r d (edge Q.1.first) ≤ peelScore r d (edge Q.1.last)) := by
  obtain ⟨U, hU⟩ := h.later_rule.exists_rule Q hQ
  rcases hU with ⟨hm, -⟩ | ⟨-, hs⟩
  · exact False.elim (h.mark_not_later
      (List.mem_flatMap.2 ⟨Q.1, List.mem_map_of_mem hQ, hm⟩))
  · exact hs

/-- The case-D kept graph is connected relative to the blocks, has one fewer
edge than blocks, and does not contain the marked edge. -/
theorem tree_facts :
    (keptGraph E ((P, (x, y)) :: Qs) ⊔ sameBlockGraph b).Connected ∧
      Nat.card (keptGraph E ((P, (x, y)) :: Qs)).edgeSet + 1 = Fintype.card κ ∧
      s(x, y) ∉ (keptGraph E ((P, (x, y)) :: Qs)).edgeSet := by
  have hD : IsStrictEarDecompOn b E (b x) (((P, (x, y)) :: Qs).map Prod.fst) := h.decomp
  refine ⟨hD.connected_keptGraph h.isRemoval, hD.natCard_keptGraph h.isRemoval, ?_⟩
  simp [keptGraph, edgeSet_deleteEdges, removedEdges, Peeling.edge]

end MarkedEarData

omit [Fintype V] [Fintype κ] [DecidableEq V] [DecidableEq κ] in
private theorem base_numerator (b : V → κ) (P : Ear V) (r : V → ℝ) (ρ : κ → ℝ)
    (hr : ∀ v, 0 ≤ r v) (hρ : ∀ S, 0 ≤ ρ S) (hrρ : ∀ v, r v ≤ ρ (b v))
    (hchain : P.toList.IsChain (ChainRel b)) (hclose : b P.first.1 = b P.last.2) :
    r P.first.1 * r P.first.2 *
        (((P.mid ++ [P.last]).map fun p => radProd r (edge p)).prod) ≤
      ρ (b P.first.1) ^ 2 * ((P.interior b).map fun S => ρ S ^ 2).prod := by
  have hid : r P.first.1 * r P.first.2 *
      (((P.mid ++ [P.last]).map fun p => radProd r (edge p)).prod) =
      r P.first.1 * innerProd r P.toList * r P.last.2 := by
    simpa only [Ear.toList, List.map_cons, List.prod_cons, radProd_mk, edge_apply]
      using prod_radii_eq r P.first P.mid P.last
  rw [hid]
  have hinner : innerProd r P.toList ≤ ((P.interior b).map fun S => ρ S ^ 2).prod := by
    have hi := innerProd_le ρ hr hrρ P.first (P.mid ++ [P.last]) hchain
    simpa only [← List.cons_append, List.dropLast_concat, Ear.interior_eq, List.map_map, Ear.toList, Function.comp_def] using hi
  have hend : r P.first.1 * r P.last.2 ≤ ρ (b P.first.1) ^ 2 := by
    rw [sq]
    exact mul_le_mul (hrρ _) (by rw [hclose]; exact hrρ _) (hr _) (hρ _)
  calc r P.first.1 * innerProd r P.toList * r P.last.2 =
      (r P.first.1 * r P.last.2) * innerProd r P.toList := by ring
    _ ≤ _ := mul_le_mul hend hinner (innerProd_nonneg hr _) (sq_nonneg _)

omit [Fintype V] [Fintype κ] [DecidableEq V] [DecidableEq κ] in
/-- Opening the marked base cycle fills the two missing endpoint radii.
The other base-cycle blocks contribute their squares. This is the base-cycle
calculation immediately before (A.60). -/
theorem marked_base_cycle (b : V → κ) (P : Ear V) (r : V → ℝ) (ρ : κ → ℝ)
    (d c : Sym2 V → ℝ) (hr : ∀ v, 0 ≤ r v) (hρ : ∀ S, 0 ≤ ρ S)
    (hrρ : ∀ v, r v ≤ ρ (b v)) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e)
    (hchain : P.toList.IsChain (ChainRel b)) (hclose : b P.first.1 = b P.last.2) :
    r P.first.1 * r P.first.2 *
        (((P.mid ++ [P.last]).map fun p => absWeight r d c (edge p)).prod) ≤
      (ρ (b P.first.1) ^ 2 * ((P.interior b).map fun S => ρ S ^ 2).prod) *
        (((P.mid ++ [P.last]).map fun p => keptWeight d c (edge p)).prod) := by
  have hprod : (((P.mid ++ [P.last]).map fun p => absWeight r d c (edge p)).prod) =
      (((P.mid ++ [P.last]).map fun p => radProd r (edge p)).prod) *
        (((P.mid ++ [P.last]).map fun p => kappa r d c (edge p)).prod) := by
    rw [← List.prod_map_mul]
    apply congrArg List.prod
    apply List.map_congr_left
    intro p _
    exact absWeight_edge p
  have hk : (((P.mid ++ [P.last]).map fun p => kappa r d c (edge p)).prod) ≤
      (((P.mid ++ [P.last]).map fun p => keptWeight d c (edge p)).prod) :=
    List.prod_map_le_prod_map₀ _ _ (fun p _ => kappa_nonneg hr hd hc _) (fun p _ => kappa_le_keptWeight hd hc _)
  rw [hprod, ← mul_assoc]
  exact mul_le_mul (base_numerator b P r ρ hr hρ hrρ hchain hclose) hk
    (List.prod_nonneg fun z hz => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hz
      exact kappa_nonneg hr hd hc _)
    (mul_nonneg (sq_nonneg _) (List.prod_nonneg fun z hz => by
      obtain ⟨S, -, rfl⟩ := List.mem_map.1 hz
      exact sq_nonneg _))

end MultipoleBKT.ExpansionK.RouteCases

end
