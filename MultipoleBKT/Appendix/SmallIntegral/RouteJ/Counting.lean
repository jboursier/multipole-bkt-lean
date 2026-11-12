/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.Cayley

/-!
# The finite tree count in the J bound

See Lemma A.4. This wrapper uses the Prüfer count with an existing decidable
equality on the labels.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open Finset SimpleGraph

private theorem filter_card_eq_nat_card {W : Type*} [Fintype W] (P : W → Prop)
    [DecidablePred P] : ((univ : Finset W).filter P).card = Nat.card {w // P w} := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_of_subtype _ (by simp)).symm

open scoped Classical in
/-- Cayley's count with the label equality retained by the configuration API. -/
theorem card_trees {V : Type*} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) :
    ((univ : Finset (SimpleGraph V)).filter IsTree).card =
      Fintype.card V ^ (Fintype.card V - 2) := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n + 2 := ⟨Fintype.card V - 2, by omega⟩
  let : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  calc
    _ = Nat.card {T : SimpleGraph V // T.IsTree} := filter_card_eq_nat_card IsTree
    _ = Nat.card (Fin n → V) := Nat.card_congr (Cayley.pruferEquiv hn)
    _ = Fintype.card V ^ (Fintype.card V - 2) := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin]
      congr 1
      omega

end MultipoleBKT.SmallIntegral.RouteJ

end
