/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.Cayley
public import MultipoleBKT.LowerBound.AbsoluteLower.Pairs

/-!
# Summing the endpoints of quotient-tree edges

The proof of Lemma 4.58. For a fixed quotient tree,
choose an endpoint in each incident block. These choices are independent.
Their weighted sum is the product of the block sums to the tree degrees.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open Finset SimpleGraph
open scoped Classical

/-- The product over darts groups into the vertex degree product. -/
theorem prod_darts {V R : Type*} [Fintype V] [CommMonoid R]
    (G : SimpleGraph V) (x : V → R) :
    (∏ d : G.Dart, x d.fst) = ∏ i, x i ^ G.degree i := by
  rw [← Finset.prod_fiberwise (univ : Finset G.Dart) (fun d : G.Dart => d.fst)]
  refine prod_congr rfl fun i _ => ?_
  rw [prod_congr rfl (fun d hd => congrArg x (mem_filter.mp hd).2), prod_const,
    G.dart_fst_fiber_card_eq_degree i]

/-- The dart product contains the two endpoint weights of each edge once. -/
theorem prod_edges_endpoints {V R : Type*} [Fintype V] [LinearOrder V] [CommMonoid R]
    (G : SimpleGraph V) (x : V → R) :
    (∏ e ∈ G.edgeFinset, x e.inf * x e.sup) = ∏ i, x i ^ G.degree i := by
  rw [← prod_darts]
  rw [← Finset.prod_fiberwise_of_maps_to
    (show ∀ d ∈ (univ : Finset G.Dart), d.edge ∈ G.edgeFinset from
      fun d _ => mem_edgeFinset.mpr d.edge_mem)]
  refine prod_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | h i j =>
    have hij : G.Adj i j := mem_edgeFinset.mp he
    let d : G.Dart := ⟨(i, j), hij⟩
    have hf : (univ.filter fun d' : G.Dart => d'.edge = s(i, j)) = {d, d.symm} :=
      d.edge_fiber
    rw [hf, prod_insert (by simpa using d.symm_ne.symm), prod_singleton]
    dsimp only [d, Dart.symm, Prod.swap]
    rcases le_total i j with h | h
    · simp only [Sym2.inf_mk, Sym2.sup_mk, inf_of_le_left h, sup_of_le_right h]
    · simp only [Sym2.inf_mk, Sym2.sup_mk, inf_of_le_right h, sup_of_le_left h, mul_comm]

/-- A lift of one fixed quotient graph, with exactly one representative of each edge. -/
def Lift {V B : Type*} (b : V → B) (q : SimpleGraph B) :=
  {E : SimpleGraph V // E ≤ crossBlockGraph b ∧ blockQuotient b E = q ∧ HasUniqueReps b E}

noncomputable instance {V B : Type*} [Fintype V] (b : V → B) (q : SimpleGraph B) :
    Fintype (Lift b q) := by
  classical
  unfold Lift
  exact Fintype.ofFinite _

/-- The uniquely determined ordered endpoints representing a quotient dart. -/
noncomputable def liftEnds {V B : Type*} (b : V → B) (q : SimpleGraph B)
    (E : Lift b q) (d : q.Dart) : V × V :=
  Classical.choose ((E.property.2.2 d.fst d.snd)
    (E.property.2.1.symm ▸ d.adj))

theorem liftEnds_spec {V B : Type*} (b : V → B) (q : SimpleGraph B)
    (E : Lift b q) (d : q.Dart) :
    b (liftEnds b q E d).1 = d.fst ∧ b (liftEnds b q E d).2 = d.snd ∧
      E.val.Adj (liftEnds b q E d).1 (liftEnds b q E d).2 :=
  (Classical.choose_spec ((E.property.2.2 d.fst d.snd)
    (E.property.2.1.symm ▸ d.adj))).1

theorem liftEnds_unique {V B : Type*} (b : V → B) (q : SimpleGraph B)
    (E : Lift b q) (d : q.Dart) (p : V × V)
    (hp : b p.1 = d.fst ∧ b p.2 = d.snd ∧ E.val.Adj p.1 p.2) :
    p = liftEnds b q E d :=
  (Classical.choose_spec ((E.property.2.2 d.fst d.snd)
    (E.property.2.1.symm ▸ d.adj))).2 p hp

/-- Reversing a dart reverses its unique representative. -/
theorem liftEnds_symm {V B : Type*} (b : V → B) (q : SimpleGraph B)
    (E : Lift b q) (d : q.Dart) :
    liftEnds b q E d.symm = (liftEnds b q E d).swap := by
  symm
  exact liftEnds_unique b q E d.symm _
    ⟨(liftEnds_spec b q E d).2.1, (liftEnds_spec b q E d).1,
      (liftEnds_spec b q E d).2.2.symm⟩

/-- The quotient dart and its endpoints determine each dart of the lift. -/
noncomputable def liftDartEquiv {V B : Type*} (b : V → B) (q : SimpleGraph B)
    (E : Lift b q) : q.Dart ≃ E.val.Dart where
  toFun d := ⟨liftEnds b q E d, (liftEnds_spec b q E d).2.2⟩
  invFun d := ⟨(b d.fst, b d.snd), by
    exact (congrArg (fun H : SimpleGraph B => H.Adj (b d.fst) (b d.snd))
      E.property.2.1).mp
        (blockQuotient_adj_of_adj d.adj (crossBlockGraph_adj.mp (E.property.1 d.adj)))⟩
  left_inv d := by
    apply Dart.ext
    exact Prod.ext (liftEnds_spec b q E d).1 (liftEnds_spec b q E d).2.1
  right_inv d := by
    apply Dart.ext
    symm
    exact liftEnds_unique b q E _ _ ⟨rfl, rfl, d.adj⟩

/-- The endpoint assignment determines the whole lifted graph. -/
theorem lift_assignment_injective {V B : Type*} (b : V → B) (q : SimpleGraph B) :
    Function.Injective (fun E : Lift b q => fun d : q.Dart => (liftEnds b q E d).1) := by
  intro E F h
  apply Subtype.ext
  ext i j
  have hdir (E F : Lift b q)
      (h : (fun d => (liftEnds b q E d).1) = fun d => (liftEnds b q F d).1)
      (hij : E.val.Adj i j) : F.val.Adj i j := by
    let d : q.Dart := (liftDartEquiv b q E).symm ⟨(i, j), hij⟩
    have hp : liftEnds b q E d = (i, j) :=
      congrArg Dart.toProd ((liftDartEquiv b q E).apply_symm_apply ⟨(i, j), hij⟩)
    have h1 : (liftEnds b q F d).1 = i := by
      rw [← congrFun h d, hp]
    have h2 : (liftEnds b q F d).2 = j := by
      have he := congrFun h d.symm
      rw [liftEnds_symm, liftEnds_symm, hp] at he
      exact he.symm
    simpa only [h1, h2] using (liftEnds_spec b q F d).2.2
  exact ⟨hdir E F h, hdir F E h.symm⟩

/-- Sum the independent endpoint choices, with the fixed quotient tree visible.
The inequality allows a family containing fewer than all lifts. -/
theorem sum_lifts_le {V B : Type*} [Fintype V] [Fintype B]
    (b : V → B) (q : SimpleGraph B) (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ E : Lift b q, ∏ i, x i ^ E.val.degree i) ≤
      ∏ S, (∑ i ∈ univ.filter (fun i => b i = S), x i) ^ q.degree S := by
  let choices := Fintype.piFinset fun d : q.Dart => univ.filter (fun i : V => b i = d.fst)
  have hmap (E : Lift b q) : (fun d => (liftEnds b q E d).1) ∈ choices := by
    rw [Fintype.mem_piFinset]
    exact fun d => mem_filter.mpr ⟨mem_univ _, (liftEnds_spec b q E d).1⟩
  have hterm (E : Lift b q) : (∏ i, x i ^ E.val.degree i) =
      ∏ d : q.Dart, x (liftEnds b q E d).1 := by
    rw [← prod_darts E.val x]
    exact (Fintype.prod_equiv (liftDartEquiv b q E) _ _ (fun _ => rfl)).symm
  calc
    _ = ∑ E : Lift b q, ∏ d : q.Dart, x (liftEnds b q E d).1 :=
      sum_congr rfl fun E _ => hterm E
    _ ≤ ∑ f ∈ choices, ∏ d : q.Dart, x (f d) := by
      apply Finset.sum_le_sum_of_injOn (fun E : Lift b q => fun d => (liftEnds b q E d).1)
      · exact fun E _ F _ h => lift_assignment_injective b q h
      · exact image_subset_iff.mpr (fun E _ => hmap E)
      · exact fun E _ => le_rfl
      · exact fun f _ _ => prod_nonneg fun d _ => hx _
    _ = ∏ d : q.Dart, ∑ i ∈ univ.filter (fun i => b i = d.fst), x i :=
      (Finset.prod_univ_sum _ _).symm
    _ = _ := prod_darts q (fun S => ∑ i ∈ univ.filter (fun i => b i = S), x i)

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
