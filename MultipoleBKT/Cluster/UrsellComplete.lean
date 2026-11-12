/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Ursell
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The chromatic polynomial and its Ursell coefficient

See the proof of
(4.150).

Colorings constant along graph edges are functions on connected components.
Inclusion-exclusion gives Whitney's subgraph expansion for proper colorings.
Its polynomial has linear coefficient equal to the Ursell function. The whole
connection graph is evaluated from its rooted incidence tree in `RouteChromatic`.
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph Polynomial

variable {V : Type*} [Fintype V]

section Coloring

omit [Fintype V] in
/-- A function constant along the edges of `H` is constant along its walks. -/
theorem eq_of_walk_of_constant_on_adj {β : Type*} {H : SimpleGraph V} {f : V → β}
    (hf : ∀ u v, H.Adj u v → f u = f v) {u v : V} (p : H.Walk u v) : f u = f v := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hf _ _ hadj).trans ih

/-- Colourings constant along the edges of `H` are the colourings of its connected
components. -/
noncomputable def constantOnAdjEquiv (H : SimpleGraph V) (t : ℕ) :
    {f : V → Fin t // ∀ u v, H.Adj u v → f u = f v} ≃ (H.ConnectedComponent → Fin t) where
  toFun f := ConnectedComponent.lift f.1 fun _ _ p _ => eq_of_walk_of_constant_on_adj f.2 p
  invFun g := ⟨g ∘ H.connectedComponentMk, fun _ _ huv =>
    congrArg g (ConnectedComponent.sound huv.reachable)⟩
  left_inv f := by
    ext v
    rfl
  right_inv g := by
    funext c
    induction c using ConnectedComponent.ind with
    | h v => rfl

/-- The number of colourings `V → Fin t` constant along the edges of `H` is `t ^ c(H)`. -/
theorem card_constant_on_adj (H : SimpleGraph V) (t : ℕ) :
    Nat.card {f : V → Fin t // ∀ u v, H.Adj u v → f u = f v} =
      t ^ Nat.card H.ConnectedComponent := by
  rw [Nat.card_congr (constantOnAdjEquiv H t), Nat.card_fun, Nat.card_eq_fintype_card,
    Fintype.card_fin]

open scoped Classical in
/-- Whitney's expansion of the number of proper colourings with `t` colours (inclusion–
exclusion over the monochromatic edges). -/
theorem card_proper_colorings (G : SimpleGraph V) (t : ℕ) :
    ((univ.filter fun f : V → Fin t => ∀ u v, G.Adj u v → f u ≠ f v).card : ℤ) =
      ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (· ≤ G),
        (-1) ^ H.edgeFinset.card * (t : ℤ) ^ Nat.card H.ConnectedComponent := by
  -- the graph of monochromatic pairs of a colouring
  let mono : (V → Fin t) → SimpleGraph V := fun f => SimpleGraph.fromRel fun u v => f u = f v
  have hle_mono : ∀ (f : V → Fin t) (H : SimpleGraph V),
      H ≤ mono f ↔ ∀ u v, H.Adj u v → f u = f v := by
    intro f H
    refine ⟨fun h u v huv => ?_, fun h u v huv => ?_⟩
    · have := h huv
      simp only [mono, fromRel_adj] at this
      exact this.2.elim id Eq.symm
    · simp only [mono, fromRel_adj]
      exact ⟨huv.ne, Or.inl (h u v huv)⟩
  have hproper : ∀ f : V → Fin t,
      (if ∀ u v, G.Adj u v → f u ≠ f v then (1 : ℤ) else 0) =
        ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (· ≤ G),
          if H ≤ mono f then (-1) ^ H.edgeFinset.card else 0 := by
    intro f
    rw [← Finset.sum_filter, Finset.filter_filter]
    have hfilt : (univ : Finset (SimpleGraph V)).filter (fun H => H ≤ G ∧ H ≤ mono f) =
        (univ : Finset (SimpleGraph V)).filter (· ≤ G ⊓ mono f) := by
      ext H
      simp
    rw [hfilt, sum_neg_one_pow_edges_le]
    congr 1
    apply propext
    rw [eq_bot_iff]
    constructor
    · intro h u v huv
      have : (G ⊓ mono f).Adj u v ↔ False := by
        refine ⟨fun hadj => ?_, False.elim⟩
        rw [inf_adj] at hadj
        exact h u v hadj.1
          ((hle_mono f (G ⊓ mono f)).mp inf_le_right u v ((inf_adj _ _ _ _).mpr hadj))
      exact this.mp huv
    · intro h u v huv hfuv
      have hadj : (G ⊓ mono f).Adj u v := by
        rw [inf_adj]
        exact ⟨huv, by simp only [mono, fromRel_adj]; exact ⟨huv.ne, Or.inl hfuv⟩⟩
      exact h hadj
  rw [Finset.natCast_card_filter, Finset.sum_congr rfl fun f _ => hproper f, Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [← Nat.cast_pow, ← card_constant_on_adj H t, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  rw [Finset.filter_congr fun f _ => hle_mono f H]

end Coloring

section Chromatic

open scoped Classical

/-- The chromatic polynomial of `G`, in Whitney's subgraph expansion
`∑_{H ≤ G} (-1)^{|E(H)|} X^{c(H)}`. Its values at natural numbers count proper colourings
(`MultipoleBKT.eval_chromaticPoly`). -/
noncomputable def chromaticPoly (G : SimpleGraph V) : ℤ[X] :=
  ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (· ≤ G),
    C ((-1) ^ H.edgeFinset.card) * X ^ Nat.card H.ConnectedComponent

/-- The chromatic polynomial evaluated at `t` counts the proper colourings with `t` colours. -/
theorem eval_chromaticPoly (G : SimpleGraph V) (t : ℕ) :
    (chromaticPoly G).eval (t : ℤ) =
      (univ.filter fun f : V → Fin t => ∀ u v, G.Adj u v → f u ≠ f v).card := by
  rw [card_proper_colorings, chromaticPoly, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]

omit [Fintype V] in
/-- A graph is connected iff it has exactly one connected component. -/
theorem connected_iff_natCard_connectedComponent_eq_one (H : SimpleGraph V) :
    H.Connected ↔ Nat.card H.ConnectedComponent = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · intro h
    have := h.nonempty
    exact ⟨h.preconnected.subsingleton_connectedComponent, inferInstance⟩
  · rintro ⟨hsub, ⟨c⟩⟩
    have : Nonempty V := by
      induction c using ConnectedComponent.ind with
      | h v => exact ⟨v⟩
    exact ⟨fun u v => ConnectedComponent.exact (Subsingleton.elim _ _)⟩

/-- The coefficient of `X` in the chromatic polynomial is the Ursell function. -/
theorem coeff_one_chromaticPoly (G : SimpleGraph V) :
    (chromaticPoly G).coeff 1 = ursell G := by
  rw [chromaticPoly, finsetSum_coeff, ursell_eq_sum, sum_filter_le_and]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [coeff_C_mul_X_pow]
  by_cases h : H.Connected
  · rw [ite_eq_left ((connected_iff_natCard_connectedComponent_eq_one H).mp h).symm,
      ite_eq_left h]
  · rw [ite_eq_right fun h' => h ((connected_iff_natCard_connectedComponent_eq_one H).mpr
      h'.symm), ite_eq_right h]

end Chromatic

end MultipoleBKT

end
