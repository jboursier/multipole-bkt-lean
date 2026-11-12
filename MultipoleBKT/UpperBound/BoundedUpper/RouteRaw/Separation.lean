/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.NonEmptyMarks.Compare

/-!
# Separation inherited by the odd components of raw groups

The paper: Proposition 5.18. Every odd component is contained in one original Mayer
group. Its full separation indicators are therefore retained on the support
of the raw term, including pairs that are absent from the odd graph.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open MeasureTheory Finset Hierarchical Multipole Parity NonEmptyMarks SetPartition
open scoped Classical

variable {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}

/-- A walk using raw odd edges and intra-block edges stays in its Mayer group. -/
theorem raw_group_closed (hX : IsSubpartition X) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m))
    {E₁ : Finset (ℕ × ℕ)} (hE₁ : E₁ ⊆ univ.biUnion fun l => interPairs (Xs l))
    (l : Fin n) {i j : ℕ} (hi : i ∈ (Xs l).biUnion id)
    (hij : (edgeGraph (E₁ ∪ intraPairs X)).Reachable i j) :
    j ∈ (Xs l).biUnion id := by
  apply mem_of_reachable_of_closed (fun u v huv hu => ?_) hi hij
  have hp : ∀ p ∈ E₁ ∪ intraPairs X,
      p.1 ∈ (Xs l).biUnion id → p.2 ∈ (Xs l).biUnion id := by
    intro p hp hu
    rcases mem_union.1 hp with hp | hp
    · obtain ⟨m, _, hm⟩ := mem_biUnion.1 (hE₁ hp)
      have hends := mem_pairsOn.1 (interPairs_subset_pairsOn hm)
      have hml : m = l := by
        by_contra hne
        exact Finset.disjoint_left.1
          (disjoint_biUnion_of_disjoint hX (hXs m) (hXs l) (hdisj m l hne)) hends.1 hu
      exact hml ▸ hends.2.1
    · obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
      obtain ⟨C, hC, huC⟩ := mem_biUnion_id.1 hu
      have heq := eq_of_isSubpartition hX hB (hXs l hC) (mem_pairsOn.1 hpB).1 huC
      exact subset_biUnion_of_mem id hC (heq ▸ (mem_pairsOn.1 hpB).2.1)
  rcases exists_mem_of_edgeGraph_adj huv with hp' | hp'
  · exact hp _ hp' hu
  · have hp_rev : (v, u) ∈ E₁ ∪ intraPairs X := hp'
    rcases mem_union.1 hp_rev with hpE | hpI
    · obtain ⟨m, _, hm⟩ := mem_biUnion.1 (hE₁ hpE)
      have hends := mem_pairsOn.1 (interPairs_subset_pairsOn hm)
      have hml : m = l := by
        by_contra hne
        exact Finset.disjoint_left.1
          (disjoint_biUnion_of_disjoint hX (hXs m) (hXs l) (hdisj m l hne)) hends.2.1 hu
      exact hml ▸ hends.1
    · obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hpI
      obtain ⟨C, hC, huC⟩ := mem_biUnion_id.1 hu
      have heq := eq_of_isSubpartition hX hB (hXs l hC) (mem_pairsOn.1 hpB).2.1 huC
      exact subset_biUnion_of_mem id hC (heq ▸ (mem_pairsOn.1 hpB).1)

/-- Each nontrivial odd component belongs to one raw Mayer group.
This is the containment needed to retain all its separation indicators. -/
theorem odd_component_subset_raw_group (hX : IsSubpartition X) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m))
    {E₁ : Finset (ℕ × ℕ)} (hE₁ : E₁ ⊆ univ.biUnion fun l => interPairs (Xs l))
    {Y : Finset (Finset ℕ)} (hY : Y ∈ oddComponents X E₁) :
    ∃ l, Y ⊆ Xs l := by
  have hEX : E₁ ⊆ interPairs X := hE₁.trans (biUnion_subset.2 fun l _ =>
    interPairs_subset_of_subset hX (hXs l))
  have hconn := isRelConnected_pairGraph hX hEX hY
  obtain ⟨e, he⟩ := hconn.2.1
  obtain ⟨p, hp, hpY⟩ : ∃ p ∈ E₁, p ∈ interPairs Y := by
    induction e using Sym2.ind with
    | h i j =>
      rcases (pairGraph_adj.1 he).2 with hp | hp
      · exact ⟨_, (mem_inter.1 hp).1, (mem_inter.1 hp).2⟩
      · exact ⟨_, (mem_inter.1 hp).1, (mem_inter.1 hp).2⟩
  obtain ⟨l, _, hpl⟩ := mem_biUnion.1 (hE₁ hp)
  have hpi := (mem_pairsOn.1 (interPairs_subset_pairsOn hpl)).1
  obtain ⟨a, _, ha⟩ := mem_relComponents.1 (oddComponents_subset E₁ hY)
  obtain ⟨B, hB, hpB⟩ := mem_biUnion_id.1 (mem_pairsOn.1 (interPairs_subset_pairsOn hpY)).1
  have hreach : reachedBlocks X E₁ p.1 = Y := by
    rw [← ha] at hB
    exact (reachedBlocks_eq_of_mem hB hpB).trans ha
  refine ⟨l, fun C hC => ?_⟩
  rw [← hreach] at hC
  obtain ⟨hCX, j, hj, hpj⟩ := mem_reachedBlocks_iff.1 hC
  have hjl := raw_group_closed hX hXs hdisj hE₁ l hpi hpj
  obtain ⟨D, hD, hjD⟩ := mem_biUnion_id.1 hjl
  have hCD := eq_of_isSubpartition hX hCX (hXs l hD) hj hjD
  exact hCD ▸ hD

/-- On the support of a raw marked term every inter-block pair inside an
odd component is separated, whether or not that pair is an odd edge. -/
theorem raw_marked_separation {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hX : IsSubpartition X) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m))
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l))
    {E₁ : Finset (ℕ × ℕ)} (hE₁ : E₁ ⊆ univ.biUnion Es)
    (F : Finset (ℕ × ℕ)) (U U₁ : Finset ℕ) (c : ℕ → ℂ × ℂ)
    (hne : markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c ≠ 0)
    {Y : Finset (Finset ℕ)} (hY : Y ∈ oddComponents X E₁)
    {p : ℕ × ℕ} (hp : p ∈ interPairs Y) :
    ¬ MultipoleLinked M lam (c p.1) (c p.2) := by
  obtain ⟨l, hYl⟩ := odd_component_subset_raw_group hX hXs hdisj
    (hE₁.trans (biUnion_mono fun l _ => hEs l)) hY
  have hp' : p ∈ univ.biUnion fun l => interPairs (Xs l) :=
    mem_biUnion.2 ⟨l, mem_univ _, interPairs_subset_of_subset
      (isSubpartition_mono hX (hXs l)) hYl hp⟩
  intro hlink
  apply hne
  have hs : sepFactor M lam Xs F c = 0 := by
    unfold sepFactor
    rw [Finset.prod_eq_zero hp' (show (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) = 0 by rw [ite_eq_left hlink]), zero_mul]
  unfold markedTerm
  rw [hs, mul_zero, zero_mul, zero_mul]

/-- All separation indicators within odd components can be kept as an
explicit factor of the raw term, as required in proof of Proposition 5.18. -/
theorem abs_markedTerm_eq_mul_oddSeparation {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hX : IsSubpartition X) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m))
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l))
    {E₁ : Finset (ℕ × ℕ)} (hE₁ : E₁ ⊆ univ.biUnion Es)
    (F : Finset (ℕ × ℕ)) (U U₁ : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c| =
      |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c| *
        ∏ Y ∈ oddComponents X E₁, ∏ p ∈ interPairs Y,
          (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) := by
  by_cases hz : markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c = 0
  · rw [hz, abs_zero, zero_mul]
  · have hs : (∏ Y ∈ oddComponents X E₁, ∏ p ∈ interPairs Y,
        (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1)) = 1 := by
      apply prod_eq_one
      intro Y hY
      apply prod_eq_one
      intro p hp
      exact ite_eq_right (raw_marked_separation hX hXs hdisj hEs hE₁ F U U₁ c hz hY hp)
    rw [hs, mul_one]

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
