/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteProfiles.Entropy
public import MultipoleBKT.Main.PropFiveFortyFive.Counting

/-!
# Global and prescribed-block profile counts

Lemma 4.59,
Steps 1 and 4, (4.120). The anchored count retains
the exact prescribed-block factor. The finite profile sets also make
explicit the exponential cost of summing profiles of a fixed total size.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteProfiles

open Finset PropFiveFortyFive
open scoped Classical

/-- Total number of labels in a multipole profile. -/
def degree {p : ℕ} (m : Fin p → ℕ) : ℕ := ∑ i : Fin p, ((i : ℕ) + 1) * m i

/-- All profiles with total number of labels `k`. -/
noncomputable def profiles (p k : ℕ) : Finset (Fin p → ℕ) :=
  (Fintype.piFinset fun _ : Fin p => range (k + 1)).filter fun m => degree m = k

theorem sum_le_degree {p : ℕ} (m : Fin p → ℕ) : (∑ i, m i) ≤ degree m :=
  sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (by omega)

theorem coordinate_le_degree {p : ℕ} (m : Fin p → ℕ) (i : Fin p) : m i ≤ degree m :=
  (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans (sum_le_degree m)

theorem mem_profiles {p k : ℕ} {m : Fin p → ℕ} : m ∈ profiles p k ↔ degree m = k := by
  simp only [profiles, mem_filter, Fintype.mem_piFinset, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨fun i => by have := coordinate_le_degree m i; omega, h⟩⟩

/-- At most exponentially many profiles of total size `k`. -/
theorem card_profiles_le (p k : ℕ) : (profiles p k).card ≤ (2 ^ p) ^ k := by
  have hk : k + 1 ≤ 2 ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  calc (profiles p k).card ≤ (Fintype.piFinset fun _ : Fin p => range (k + 1)).card :=
      card_filter_le _ _
    _ = (k + 1) ^ p := by simp
    _ ≤ (2 ^ k) ^ p := Nat.pow_le_pow_left hk p
    _ = (2 ^ p) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem degree_blockCount {p : ℕ} {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (hp : ∀ S ∈ X, S.card ≤ p) : degree (blockCount p X) = (X.biUnion id).card := by
  rw [degree, sum_mul_blockCount (fun S hS => ⟨(hX.1 S hS).card_pos, hp S hS⟩),
    card_biUnion (fun S hS T hT hST => hX.2 hS hT hST)]
  rfl

/-- A sum over clusters of size `k`, grouped by their literal size profiles. -/
theorem sum_by_profile {p k : ℕ} {π : Finset (Finset ℕ)} (hπ : IsSubpartition π)
    (hp : ∀ S ∈ π, S.card ≤ p) (f : Finset (Finset ℕ) → ℝ) :
    ∑ X ∈ π.powerset.filter (fun X => (X.biUnion id).card = k), f X =
      ∑ m ∈ profiles p k, ∑ X ∈ π.powerset.filter (fun X => blockCount p X = m), f X := by
  rw [← sum_fiberwise_of_maps_to (g := blockCount p)
    (s := π.powerset.filter fun X => (X.biUnion id).card = k) (t := profiles p k) (by
      intro X hX
      obtain ⟨hX, hk⟩ := mem_filter.mp hX
      have hsub := mem_powerset.mp hX
      rw [mem_profiles, degree_blockCount
        ⟨fun S hS => hπ.1 S (hsub hS), hπ.2.subset (by exact_mod_cast hsub)⟩
        (fun S hS => hp S (hsub hS)), hk])]
  refine sum_congr rfl fun m hm => ?_
  congr 1
  ext X
  simp only [mem_filter, mem_powerset, and_assoc]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨hsub, he⟩
    refine ⟨hsub, ?_, he⟩
    rw [← degree_blockCount
      ⟨fun S hS => hπ.1 S (hsub hS), hπ.2.subset (by exact_mod_cast hsub)⟩
      (fun S hS => hp S (hsub hS)), he, mem_profiles.mp hm]

/-- Fixing a profile makes the product weight constant. The remaining factor
is exactly the product of binomial coefficients in Step 1. -/
theorem sum_fixed_profile {p : ℕ} {π : Finset (Finset ℕ)}
    (hp : ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ p) (m : Fin p → ℕ) (v : ℕ → ℝ) :
    ∑ X ∈ π.powerset.filter (fun X => blockCount p X = m),
        (X.card : ℝ) ^ X.card * ∏ S ∈ X, v S.card =
      ((∑ i, m i : ℕ) : ℝ) ^ (∑ i, m i) *
        ∏ i, ((blockCount p π i).choose (m i) : ℝ) * v ((i : ℕ) + 1) ^ m i := by
  have he : ∀ X ∈ π.powerset.filter (fun X => blockCount p X = m),
      (X.card : ℝ) ^ X.card * ∏ S ∈ X, v S.card =
        ((∑ i, m i : ℕ) : ℝ) ^ (∑ i, m i) * ∏ i : Fin p, v ((i : ℕ) + 1) ^ m i := by
    intro X hX
    obtain ⟨hsub, hm⟩ := mem_filter.mp hX
    have hpX := fun S hS => hp S (mem_powerset.mp hsub hS)
    rw [← sum_blockCount hpX, prod_card_eq_prod_blockCount hpX, hm]
  rw [sum_congr rfl he, sum_const, nsmul_eq_mul, card_powerset_filter_blockCount hp, Nat.cast_prod,
    prod_mul_distrib]
  ring

/-- Erasing the prescribed block counts the anchored profile exactly. -/
theorem card_anchored_profile {p : ℕ} {π : Finset (Finset ℕ)} {S : Finset ℕ}
    (hS : S ∈ π) (hp : ∀ T ∈ π, 1 ≤ T.card ∧ T.card ≤ p) (m : Fin p → ℕ) :
    ((π.powerset.filter fun X => S ∈ X).filter
      fun X => blockCount p X = m + sizeIndicator p S.card).card =
        ∏ i, (blockCount p (π.erase S) i).choose (m i) := by
  rw [← card_powerset_filter_blockCount (fun T hT => hp T (mem_erase.mp hT).2) m]
  refine card_nbij' (fun X => X.erase S) (fun Y => insert S Y) ?_ ?_ ?_ ?_
  · intro X hX
    obtain ⟨hX, hm⟩ := mem_filter.mp hX
    obtain ⟨hX, hSX⟩ := mem_filter.mp hX
    rw [mem_powerset] at hX
    rw [mem_coe, mem_filter, mem_powerset]
    refine ⟨erase_subset_erase S hX, ?_⟩
    have he := blockCount_insert (p := p) (notMem_erase S X)
    rw [insert_erase hSX, hm] at he
    exact add_right_cancel he.symm
  · intro Y hY
    obtain ⟨hY, hm⟩ := mem_filter.mp hY
    have hYsub := mem_powerset.mp hY
    have hSY : S ∉ Y := fun h => (mem_erase.mp (hYsub h)).1 rfl
    simp only [mem_coe, mem_filter, mem_powerset]
    exact ⟨⟨insert_subset hS (hYsub.trans (erase_subset _ _)), mem_insert_self _ _⟩,
      by rw [blockCount_insert hSY, hm]⟩
  · intro X hX
    exact insert_erase (mem_filter.mp (mem_filter.mp hX).1).2
  · intro Y hY
    have hYsub := mem_powerset.mp (mem_filter.mp hY).1
    exact erase_insert (fun h => (mem_erase.mp (hYsub h)).1 rfl)

/-- The exact factor `n'_r/n_r`, without division. Here `m` is the
profile after removing the prescribed block. -/
theorem anchored_profile_factor {p : ℕ} {π : Finset (Finset ℕ)} {S : Finset ℕ}
    (hS : S ∈ π) (hp : ∀ T ∈ π, 1 ≤ T.card ∧ T.card ≤ p) (m : Fin p → ℕ)
    (r : Fin p) (hr : S.card = (r : ℕ) + 1) :
    blockCount p π r *
        ((π.powerset.filter fun X => S ∈ X).filter
          fun X => blockCount p X = m + sizeIndicator p S.card).card =
      (m r + 1) *
        (π.powerset.filter fun X => blockCount p X = m + sizeIndicator p S.card).card := by
  have hind : ∀ i : Fin p, sizeIndicator p S.card i = if i = r then 1 else 0 := by
    intro i
    simp only [sizeIndicator, hr]
    by_cases hi : i = r
    · subst i
      simp
    · rw [ite_eq_right (fun he => hi (Fin.ext (by omega))), ite_eq_right hi]
  have hn : blockCount p π = blockCount p (π.erase S) + sizeIndicator p S.card := by
    rw [← blockCount_insert (notMem_erase S π), insert_erase hS]
  rw [card_anchored_profile hS hp, card_powerset_filter_blockCount hp,
    hn, Pi.add_apply, hind r, ite_eq_left rfl]
  rw [← mul_prod_erase _ _ (mem_univ r), ← mul_prod_erase _ _ (mem_univ r)]
  have hrest : (∏ i ∈ univ.erase r, ((blockCount p (π.erase S) + sizeIndicator p S.card) i).choose
      ((m + sizeIndicator p S.card) i)) =
        ∏ i ∈ univ.erase r, (blockCount p (π.erase S) i).choose (m i) := by
    apply prod_congr rfl
    intro i hi
    simp [hind i, ne_of_mem_erase hi]
  rw [hrest]
  simp only [Pi.add_apply, hind r, ite_true]
  have h := Nat.add_one_mul_choose_eq (blockCount p (π.erase S) r) (m r)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun t => t * ∏ i ∈ univ.erase r, (blockCount p (π.erase S) i).choose (m i)) h

end MultipoleBKT.AbsoluteLower.RouteProfiles

end
