/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Frozen: `MultipoleBKT.greedyMatching`

See the paper, Definition 4.1.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- labels `Fin N` (0-based, order preserving), so the lexicographic
-- tie-break is the paper's.
-- the literal greedy rule; helper of `stableMatching` (the recursion
-- needs the general state `(A, B)` of remaining labels).
/-- One run of the stable-matching procedure (Definitions 2.1 and 4.1) on the remaining positive labels `A` and negative labels `B`, `|A| = |B| = k`: match
the pair `(i, j) ∈ A × B` that minimises `(|x_i - y_j|, i, j)` lexicographically (the first
contact, simultaneous contacts broken by the lexicographically smallest `(i, j)`), remove
`x_i` and `y_j`, and repeat on `A ∖ {i}`, `B ∖ {j}`. The result is the bijection `A ≃ B`,
`i ↦ σ(i)`. -/
noncomputable def greedyMatching {N : ℕ} (c : Fin N → ℂ × ℂ) :
    (k : ℕ) → (A B : Finset (Fin N)) → A.card = k → B.card = k → (A ≃ B)
  | 0, A, B, hA, hB =>
    haveI : IsEmpty A := ⟨fun a => by simpa [Finset.card_eq_zero.1 hA] using a.2⟩
    haveI : IsEmpty B := ⟨fun b => by simpa [Finset.card_eq_zero.1 hB] using b.2⟩
    Equiv.equivOfIsEmpty A B
  | k + 1, A, B, hA, hB =>
    let keys : Finset (ℝ ×ₗ (Fin N ×ₗ Fin N)) :=
      (A ×ˢ B).image fun ij => toLex (‖(c ij.1).1 - (c ij.2).2‖, toLex ij)
    have hkeys : keys.Nonempty :=
      ((Finset.card_pos.1 (by omega)).product (Finset.card_pos.1 (by omega))).image _
    -- the matched pair of this iteration
    let ij : Fin N × Fin N := ofLex (ofLex (keys.min' hkeys)).2
    have hij : ij ∈ A ×ˢ B := by
      obtain ⟨ij', hmem, heq⟩ := Finset.mem_image.1 (keys.min'_mem hkeys)
      have : ij = ij' := by simp only [ij, ← heq]; rfl
      exact this ▸ hmem
    have hi : ij.1 ∈ A := (Finset.mem_product.1 hij).1
    have hj : ij.2 ∈ B := (Finset.mem_product.1 hij).2
    -- the later iterations
    let e := greedyMatching c k (A.erase ij.1) (B.erase ij.2)
      (by rw [Finset.card_erase_of_mem hi, hA]; rfl) (by rw [Finset.card_erase_of_mem hj, hB]; rfl)
    { toFun := fun a =>
        if h : (a : Fin N) = ij.1 then ⟨ij.2, hj⟩
        else ⟨e ⟨a, Finset.mem_erase.2 ⟨h, a.2⟩⟩, (Finset.mem_erase.1 (e _).2).2⟩
      invFun := fun b =>
        if h : (b : Fin N) = ij.2 then ⟨ij.1, hi⟩
        else ⟨e.symm ⟨b, Finset.mem_erase.2 ⟨h, b.2⟩⟩, (Finset.mem_erase.1 (e.symm _).2).2⟩
      left_inv := by
        intro a
        by_cases h : (a : Fin N) = ij.1
        · simp [h]; exact Subtype.ext h.symm
        · have hne : (e ⟨a, Finset.mem_erase.2 ⟨h, a.2⟩⟩ : Fin N) ≠ ij.2 :=
            (Finset.mem_erase.1 (e _).2).1
          simp [h, hne]
      right_inv := by
        intro b
        by_cases h : (b : Fin N) = ij.2
        · simp [h]; exact Subtype.ext h.symm
        · have hne : (e.symm ⟨b, Finset.mem_erase.2 ⟨h, b.2⟩⟩ : Fin N) ≠ ij.1 :=
            (Finset.mem_erase.1 (e.symm _).2).1
          simp [h, hne] }

end MultipoleBKT

end
