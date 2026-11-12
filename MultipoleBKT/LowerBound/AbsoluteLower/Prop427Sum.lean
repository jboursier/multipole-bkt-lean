/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Integral
public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Levels

/-!
# Finite integral and disjoint-group summation helpers

proof of
Lemma 4.57, and the group enumeration
(4.124) through (4.125) in the proof of Lemma 4.59.

Finite sums of nonnegative integrals move inside the integral. Nonempty,
pairwise disjoint groups have number bounded by the size of their ambient
family. These helpers support the merger and the written group enumeration.
The logarithmic tree estimates are in `RouteFixedGroups`.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open MeasureTheory Finset SimpleGraph Multipole SetPartition Limits SmallIntegral Parity
open UpperBound.AbsoluteUpper (jLargeIntegrand jLarge simplifiedMajorant)
open scoped ENNReal

variable {M lam ε₀ : ℝ} {χ : ℂ → ℝ} {p₀ : ℕ} {β C₀ : ℝ} {X : Finset (Finset ℕ)}

/-- A sum of integrals is at most the integral of the sum. -/
theorem sum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- Nonempty, pairwise disjoint subfamilies of `X` are at most `|X|` in number. -/
theorem card_le_of_disjoint_nonempty {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    (hXsX : ∀ l, Xs l ⊆ X) (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (hne : ∀ l, (Xs l).Nonempty) : n ≤ X.card := by
  choose f hf using hne
  have hinj : Function.Injective fun l => (⟨f l, hXsX l (hf l)⟩ : X) := by
    intro l l' h
    by_contra hll'
    have h' : f l = f l' := congrArg Subtype.val h
    exact Finset.disjoint_left.1 (hdisj l l' hll') (hf l) (h' ▸ hf l')
  have := Fintype.card_le_of_injective _ hinj
  simpa using this

theorem nonempty_of_mem_relTreePairs {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)
    {T : Finset (ℕ × ℕ)} (hT : T ∈ relTreePairs Y) : Y.Nonempty := by
  have := (relTree_pairs hY hT).2.2
  exact card_pos.1 (by omega)

end AbsoluteLower

end MultipoleBKT

end
