/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.CanonicalPartition
public import MultipoleBKT.Frozen.IsSubpartition

/-!
# The canonical partition `Y(m_1, …, m_p)`

Basic facts about the frozen `MultipoleBKT.canonicalPartition` (Definition 2.14): its blocks are nonempty and pairwise disjoint,
so that every family of its blocks is a subpartition
(`MultipoleBKT.isSubpartition_of_subset_canonicalPartition`), and it has `m_1 + ⋯ + m_p` blocks
(`MultipoleBKT.card_canonicalPartition`).
-/

@[expose] public section

namespace MultipoleBKT

open Finset

variable {p : ℕ}

/-- The offset `o_i = ∑_{l < i} (l + 1) m_l` of the blocks of size `i + 1` in `Y(m)`. -/
private def canonicalOffset (m : Fin p → ℕ) (i : Fin p) : ℕ :=
  ∑ l with l < i, ((l : ℕ) + 1) * m l

/-- The `j`-th block of size `i + 1` of `Y(m)`. -/
private def canonicalBlock (m : Fin p → ℕ) (i : Fin p) (j : ℕ) : Finset ℕ :=
  Ico (canonicalOffset m i + j * ((i : ℕ) + 1)) (canonicalOffset m i + (j + 1) * ((i : ℕ) + 1))

private theorem canonicalPartition_eq (m : Fin p → ℕ) :
    canonicalPartition m = univ.biUnion fun i => (range (m i)).image (canonicalBlock m i) :=
  rfl

private theorem card_canonicalBlock (m : Fin p → ℕ) (i : Fin p) (j : ℕ) :
    (canonicalBlock m i j).card = (i : ℕ) + 1 := by
  rw [canonicalBlock, Nat.card_Ico]
  rw [add_mul, one_mul]
  omega

private theorem canonicalOffset_add_le {m : Fin p → ℕ} {i i' : Fin p} (h : i < i') :
    canonicalOffset m i + ((i : ℕ) + 1) * m i ≤ canonicalOffset m i' := by
  unfold canonicalOffset
  have hsub : insert i (univ.filter fun l : Fin p => l < i) ⊆ univ.filter fun l => l < i' := by
    intro l hl
    rw [mem_insert, mem_filter] at hl
    rw [mem_filter]
    rcases hl with rfl | ⟨-, hl⟩
    · exact ⟨mem_univ _, h⟩
    · exact ⟨mem_univ _, hl.trans h⟩
  have hnot : i ∉ univ.filter fun l : Fin p => l < i := by simp
  calc ∑ l with l < i, ((l : ℕ) + 1) * m l + ((i : ℕ) + 1) * m i
      = ∑ l ∈ insert i (univ.filter fun l : Fin p => l < i), ((l : ℕ) + 1) * m l := by
        rw [sum_insert hnot, add_comm]
    _ ≤ _ := sum_le_sum_of_subset hsub

private theorem mem_canonicalBlock {m : Fin p → ℕ} {i : Fin p} {j x : ℕ} :
    x ∈ canonicalBlock m i j ↔ canonicalOffset m i + j * ((i : ℕ) + 1) ≤ x ∧
      x < canonicalOffset m i + (j + 1) * ((i : ℕ) + 1) := by
  rw [canonicalBlock, mem_Ico]

private theorem disjoint_canonicalBlock {m : Fin p → ℕ} {i i' : Fin p} {j j' : ℕ}
    (hj : j < m i) (hj' : j' < m i') (h : (i, j) ≠ (i', j')) :
    Disjoint (canonicalBlock m i j) (canonicalBlock m i' j') := by
  rw [disjoint_left]
  intro x hx hx'
  rw [mem_canonicalBlock] at hx hx'
  rcases lt_trichotomy i i' with hii | rfl | hii
  · have h1 := canonicalOffset_add_le (m := m) hii
    have h2 : (j + 1) * ((i : ℕ) + 1) ≤ ((i : ℕ) + 1) * m i := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ hj
    have h3 : 0 ≤ j' * ((i' : ℕ) + 1) := Nat.zero_le _
    omega
  · have hjj : j ≠ j' := fun hjj => h (by rw [hjj])
    rcases lt_or_gt_of_ne hjj with hjj | hjj
    · have : (j + 1) * ((i : ℕ) + 1) ≤ j' * ((i : ℕ) + 1) := Nat.mul_le_mul_right _ hjj
      omega
    · have : (j' + 1) * ((i : ℕ) + 1) ≤ j * ((i : ℕ) + 1) := Nat.mul_le_mul_right _ hjj
      omega
  · have h1 := canonicalOffset_add_le (m := m) hii
    have h2 : (j' + 1) * ((i' : ℕ) + 1) ≤ ((i' : ℕ) + 1) * m i' := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ hj'
    have h3 : 0 ≤ j * ((i : ℕ) + 1) := Nat.zero_le _
    omega

private theorem mem_canonicalPartition_iff {m : Fin p → ℕ} {S : Finset ℕ} :
    S ∈ canonicalPartition m ↔ ∃ i : Fin p, ∃ j < m i, canonicalBlock m i j = S := by
  rw [canonicalPartition_eq, mem_biUnion]
  simp only [mem_univ, true_and, mem_image, mem_range]

/-- The blocks of `Y(m)` are nonempty. -/
theorem nonempty_of_mem_canonicalPartition {m : Fin p → ℕ} {S : Finset ℕ}
    (hS : S ∈ canonicalPartition m) : S.Nonempty := by
  obtain ⟨i, j, -, rfl⟩ := mem_canonicalPartition_iff.mp hS
  rw [← card_pos, card_canonicalBlock]
  exact Nat.succ_pos _

/-- Distinct blocks of `Y(m)` are disjoint. -/
theorem disjoint_of_mem_canonicalPartition {m : Fin p → ℕ} {S T : Finset ℕ}
    (hS : S ∈ canonicalPartition m) (hT : T ∈ canonicalPartition m) (hST : S ≠ T) :
    Disjoint S T := by
  obtain ⟨i, j, hj, rfl⟩ := mem_canonicalPartition_iff.mp hS
  obtain ⟨i', j', hj', rfl⟩ := mem_canonicalPartition_iff.mp hT
  refine disjoint_canonicalBlock hj hj' fun h => hST ?_
  simp only [Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- Every family of blocks of `Y(m)` is a subpartition. -/
theorem isSubpartition_of_subset_canonicalPartition {m : Fin p → ℕ}
    {X : Finset (Finset ℕ)} (hX : X ⊆ canonicalPartition m) : IsSubpartition X :=
  ⟨fun _ hS => nonempty_of_mem_canonicalPartition (hX hS),
    fun _ hS _ hT hST => disjoint_of_mem_canonicalPartition (hX hS) (hX hT) hST⟩

private theorem canonicalBlock_injective (m : Fin p → ℕ) (i : Fin p) :
    Function.Injective (canonicalBlock m i) := by
  intro j j' h
  have hj : canonicalOffset m i + j * ((i : ℕ) + 1) ∈ canonicalBlock m i j' := by
    rw [← h, mem_canonicalBlock]
    constructor
    · exact le_rfl
    · rw [add_mul, one_mul]
      omega
  have hj' : canonicalOffset m i + j' * ((i : ℕ) + 1) ∈ canonicalBlock m i j := by
    rw [h, mem_canonicalBlock]
    constructor
    · exact le_rfl
    · rw [add_mul, one_mul]
      omega
  rw [mem_canonicalBlock] at hj hj'
  have h1 : j * ((i : ℕ) + 1) ≤ j' * ((i : ℕ) + 1) := by omega
  have h2 : j' * ((i : ℕ) + 1) ≤ j * ((i : ℕ) + 1) := by omega
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) (le_antisymm h1 h2)

/-- `Y(m_1, …, m_p)` has `m_1 + ⋯ + m_p` blocks. -/
theorem card_canonicalPartition (m : Fin p → ℕ) :
    (canonicalPartition m).card = ∑ i, m i := by
  rw [canonicalPartition_eq, card_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [card_image_of_injective _ (canonicalBlock_injective m i), card_range]
  · intro i _ i' _ hii
    rw [Function.onFun, disjoint_left]
    intro S hS hS'
    rw [mem_image] at hS hS'
    obtain ⟨j, -, rfl⟩ := hS
    obtain ⟨j', -, h⟩ := hS'
    have := congrArg card h
    rw [card_canonicalBlock, card_canonicalBlock] at this
    exact hii (Fin.ext (by omega))

end MultipoleBKT

end
