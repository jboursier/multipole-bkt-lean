/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.FamilyNormalization
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.Envelope

/-!
# Original long marks and symmetric label edges

See Lemma A.7. Erasing an original long mark
erases precisely its symmetric edge, without a multiplicity loss.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

/-- The symmetric carrier commutes with erasing an ordered original mark. -/
theorem symOf_erase {V : Finset ℕ} (D : Finset (ℕ × ℕ)) {i j : V} (hij : i < j) :
    symOf V (D.erase ((i:ℕ),(j:ℕ))) = (symOf V D).erase s(i,j) := by
  have hs : symOf V {((i:ℕ),(j:ℕ))} = {s(i,j)} := by
    ext e
    simp only [mem_symOf,Finset.mem_singleton]
    constructor
    · rintro ⟨a,b,-,hp,rfl⟩
      have ha : a = i := Subtype.ext (Prod.mk.inj hp).1
      have hb : b = j := Subtype.ext (Prod.mk.inj hp).2
      rw [ha,hb]
    · intro he
      exact ⟨i,j,hij,rfl,he⟩
  rw [← sdiff_singleton_eq_erase,symOf_sdiff,hs,sdiff_singleton_eq_erase]

/-- Zero common factors force the actual omitted term to vanish in either alternative. -/
theorem internal_zero {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}
    {hX : IsSubpartition X} {hOX : O ⊆ interPairs X} {hpar : IsParityPair X O ∅}
    {lam M H t : ℝ} {c : ℕ → ℂ × ℂ} {T : Finset (ℕ × ℕ)}
    (h : OmittedPointwise hX hOX hpar lam M H c T 0 t) : t = 0 := by
  rcases h with ⟨F,hh⟩ | ⟨F,p,-,-,hh⟩
  all_goals
    simp only [zero_mul] at hh
    exact abs_nonpos_iff.1 hh

end MultipoleBKT.ExpansionK.RouteOmitted

end
