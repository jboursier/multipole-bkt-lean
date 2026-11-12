/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Mobius

/-!
# Explicit inversion of component expansions

See the paper, equation (5.165). Apply Lemma 4.60 (1) to products of connected weights on partitions.
The one-block partition gives the connected weight itself.
-/

public section

namespace MultipoleBKT.Multipole.RouteGrouping

open Finset SetPartition
open scoped Classical

/-- The connected coefficient of a partition expansion is its explicit Möbius sum.
This is Lemma 4.60 (1) at the one-block partition. -/
theorem connectedWeight_mobius {α R : Type*} [DecidableEq α] [CommRing R]
    (K : Finset α → R) {D : Finset α} (hD : D.Nonempty) :
    K D = ∑ π ∈ (partitions D).filter (Refines · {D}),
      (mobius π {D} : R) * ∏ B ∈ π, partitionSum K B := by
  have h := lemma_4_60_1 D (fun σ => ∏ B ∈ σ, K B)
    (fun π => ∏ B ∈ π, partitionSum K B)
    (fun π hπ => (sum_partitions_refines_prod hπ K).symm)
    {D} (singleton_mem_partitions hD)
  simpa only [Finset.prod_singleton] using h

end MultipoleBKT.Multipole.RouteGrouping
