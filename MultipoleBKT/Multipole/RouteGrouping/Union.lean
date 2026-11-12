/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Multipole.EdgeSets

/-!
# Connectivity of the union of the expanded edge families

See the paper, equation (4.36),
and Step 5 of the proof of Lemma 5.16. Contracting the first connected
components preserves connectivity of the union with the separation edges.
-/

public section

namespace MultipoleBKT.Multipole.RouteGrouping

open Finset SetPartition
open scoped Classical

private theorem reachable_of_adj_reachable {G H : SimpleGraph ℕ}
    (h : ∀ i j, G.Adj i j → H.Reachable i j) {i j : ℕ} (hij : G.Reachable i j) :
    H.Reachable i j := by
  obtain ⟨w⟩ := hij
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj w ih => exact (h _ _ hadj).trans ih

/-- Contracting the Mayer components preserves every reachability relation in `E ∪ F`.
The first partition includes singleton blocks unused by the Mayer edges. -/
theorem union_reachable_iff {D : Finset (Finset ℕ)}
    {σ : Finset (Finset (Finset ℕ))} (hσ : σ ∈ partitions D)
    {E F : Finset (ℕ × ℕ)} (hE : E ⊆ σ.biUnion interPairs)
    (hc : ∀ T ∈ σ, ConnOn (T.biUnion id) ((E ∩ interPairs T) ∪ intraPairs T))
    (i j : ℕ) :
    (edgeGraph ((E ∪ F) ∪ intraPairs D)).Reachable i j ↔
      (edgeGraph (F ∪ intraPairs (σ.image fun T => T.biUnion id))).Reachable i j := by
  let G := edgeGraph ((E ∪ F) ∪ intraPairs D)
  let H := edgeGraph (F ∪ intraPairs (σ.image fun T => T.biUnion id))
  have hEG : ∀ p ∈ E, p ∈ intraPairs (σ.image fun T => T.biUnion id) := by
    intro p hp
    obtain ⟨T, hT, hpT⟩ := Finset.mem_biUnion.1 (hE hp)
    exact mem_intraPairs.2 ⟨T.biUnion id, Finset.mem_image_of_mem _ hT,
      interPairs_subset_pairsOn hpT⟩
  have hIG : ∀ p ∈ intraPairs D, p ∈ intraPairs (σ.image fun T => T.biUnion id) := by
    intro p hp
    obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
    obtain ⟨T, hT, hBT⟩ := exists_mem_of_mem_partitions hσ hB
    exact mem_intraPairs.2 ⟨T.biUnion id, Finset.mem_image_of_mem _ hT,
      pairsOn_mono (subset_biUnion_of_mem hBT) hpB⟩
  have hGH : G ≤ H := by
    apply edgeGraph_mono
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · rcases Finset.mem_union.1 hp with hp | hp
      · exact Finset.mem_union_right _ (hEG p hp)
      · exact Finset.mem_union_left _ hp
    · exact Finset.mem_union_right _ (hIG p hp)
  have hF : edgeGraph F ≤ G := edgeGraph_mono (by
    intro p hp
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hp))
  have hHG : ∀ a b, H.Adj a b → G.Reachable a b := by
    intro a b hab
    have hp : ∀ p ∈ F ∪ intraPairs (σ.image fun T => T.biUnion id),
        G.Reachable p.1 p.2 := by
      intro p hp
      rcases Finset.mem_union.1 hp with hp | hp
      · by_cases heq : p.1 = p.2
        · rw [heq]
        · exact (edgeGraph_adj.2 ⟨heq, Or.inl hp⟩).reachable.mono hF
      · obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hB
        have hTG : edgeGraph ((E ∩ interPairs T) ∪ intraPairs T) ≤ G := by
          apply edgeGraph_mono
          intro q hq
          rcases Finset.mem_union.1 hq with hq | hq
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.1 hq).1)
          · obtain ⟨B, hB, hqB⟩ := mem_intraPairs.1 hq
            exact Finset.mem_union_right _ (mem_intraPairs.2
              ⟨B, subset_of_mem_partitions hσ hT hB, hqB⟩)
        have hpair := mem_pairsOn.1 hpB
        exact ((hc T hT).2 _ hpair.1 _ hpair.2.1).mono hTG
    rcases exists_mem_of_edgeGraph_adj hab with hab | hab
    · exact hp _ hab
    · exact (hp _ hab).symm
  exact ⟨fun h => h.mono hGH, reachable_of_adj_reachable hHG⟩

/-- The connecting condition in (4.36) is exactly connectivity after contraction
of the first components. This also holds when the first family has no nontrivial component. -/
theorem union_connected_iff {D : Finset (Finset ℕ)}
    {σ : Finset (Finset (Finset ℕ))} (hσ : σ ∈ partitions D)
    {E F : Finset (ℕ × ℕ)} (hE : E ⊆ σ.biUnion interPairs)
    (hc : ∀ T ∈ σ, ConnOn (T.biUnion id) ((E ∩ interPairs T) ∪ intraPairs T)) :
    ConnOn (D.biUnion id) ((E ∪ F) ∪ intraPairs D) ↔
      ConnOn (D.biUnion id) (F ∪ intraPairs (σ.image fun T => T.biUnion id)) := by
  simp only [ConnOn, union_reachable_iff hσ hE hc]

end MultipoleBKT.Multipole.RouteGrouping
